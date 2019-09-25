open Util
open Pp
open Constrexpr
open Tacexpr
open Misctypes
open Genarg
open Genredexpr
open Tok (* necessary for camlp5 *)
open Names

open Pcoq
open Pcoq.Constr
open Pcoq.Vernac_
open Pcoq.Prim
open Pltac
open Tacenv

open Stdarg
open Genarg
open Geninterp

open Knn

module TacticNaiveKnn = MakeNaiveKnn (struct
                                          type feature = int
                                          type obj = (Tacexpr.raw_tactic_expr * string)
                                          let compare = Int.compare
                                          let equal = Int.equal
                                          let hash = Hashtbl.hash
                                      end)

module Knn = TacticNaiveKnn

(*
let vernac_solve n info tcom b =
  let tcom = recorder tcom in
  let status = Proof_global.with_current_proof (fun etac p ->
    let with_end_tac = if b then Some etac else None in
    let global = match n with SelectAll | SelectList _ -> true | _ -> false in
    let info = Option.append info !print_info_trace in
    let (p,status) =
      Pfedit.solve n info (Tacinterp.hide_interp global tcom None) ?with_end_tac p
    in
    (* in case a strict subtree was completed,
       go back to the top of the prooftree *)
    let p = Proof.maximal_unfocus Vernacentries.command_focus p in
    p,status) in
    if not status then Feedback.feedback Feedback.AddedAxiom
*)


(*
let db = Summary.ref ~name:"ltacrecord-db" (Knn.create ())

type data_in = int list * string
let in_db : data_in Libobject.obj = Libobject.(declare_object { (default_object "LTACRECORD") with
  cache_function = (fun (_,(x : data_in)) -> db := Knn.add x !db)
})

let add_to_db (x : data_in) =
  Lib.add_anonymous_leaf (in_db x)
*)
let db = Knn.create ()

let requires : string list ref = ref []

let history_count : (int, int) Hashtbl.t = Hashtbl.create 100

let lmax ls = List.fold_left (fun m c -> if Stateid.newer_than c m then c else m) (List.hd ls) ls

let rec find_last_state doc id =
  match Hashtbl.find_opt history_count (Stateid.to_int id) with
  | Some n -> n
  | None ->
    let nbs = Stm.neighbors ~doc:doc id in
    if List.is_empty nbs then 0 else
    let max = lmax nbs in
    find_last_state doc max

let append file str =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc str;
  close_out oc

let write_db file =
    let oc = open_out ((String.sub file 0 (String.length file - 2)) ^ "feat") in
    let requires_string = "![" ^ (String.concat ", " !requires) ^ "]\n" in
    let db_list = Knn.tolist db in
    let h s = string_of_int (Hashtbl.hash s) in
    let l2s fs = "[" ^ (String.concat ", " (List.map string_of_int fs)) ^ "]" in
    let entry (feats, (raw_tac, obj)) =
      if String.equal obj "endproof" then "#flush\n" else (l2s feats ^ " : " ^ (*Base64.encode_string*) h obj ^ "\n") in
    let write_entry arg =
      output_string oc (entry arg) in
    output_string oc requires_string;
    List.iter write_entry db_list;
    List.iter (fun args -> append "all.feat" (entry args)) db_list;
    close_out oc

let () = Coqtop.ltacrecordhook := (fun file -> write_db file)

let () = Vernacentries.requirehook := (fun files ->
  let newrequires = List.map (fun (pair) -> CUnix.canonical_path_name (snd pair)) files in
  let newrequires = List.map (fun (file) -> (String.sub file 0 (String.length file - 2)) ^ "feat") newrequires in
  requires := List.append newrequires !requires
)

let firstn n l =
  let rec aux acc n l =
    match n, l with
    | 0, _ -> List.rev acc
    | n, h::t -> aux (h::acc) (pred n) t
    | _ -> List.rev acc
  in
  aux [] n l

let get_k_str ranking comp =
    let rec get_k' acc ranking =
    match ranking with
    | (_, f, o) :: r -> if String.equal o comp then acc else get_k' (1 + acc) r
    | [] -> -1
    in get_k' 0 ranking

let mk_ml_tac tac = fun args is -> tac

let register tac name =
  let fullname = {mltac_plugin = "recording"; mltac_tactic = name} in
  register_ml_tactic fullname [| tac |]

let run_ml_tac name = TacML (None, ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = name}; mltac_index = 0}, []))

let features term = Features.extract_features (Hh_term.hhterm_of (Hh_term.econstr_to_constr term))

let print_rank rank =
    let rank = firstn 10 rank in
    let strs = List.map (fun (x, f, o) -> (Pp.str (Float.to_string x)) ++ (Pp.str " ") ++ (Pp.str o) ++ (Pp.str "\n")) rank in
    Pp.seq strs

(** Goal printing tactic *)

let goal_to_features gl =
       let goal = Proofview.Goal.concl gl in
       let hyps = Proofview.Goal.hyps gl in
       let hyps_features =
          List.map
            (fun pt -> match pt with
                 | Context.Named.Declaration.LocalAssum (id, typ) ->
                   features typ
                 | Context.Named.Declaration.LocalDef (id, term, typ) ->
                   List.append (features term) (features typ))
            hyps in
       let feats = (List.append (features goal) (List.concat hyps_features)) in
       let feats = List.map Hashtbl.hash feats in
       List.sort(*_uniq*) Int.compare feats

let print_goal = Proofview.Goal.enter
    (fun gl ->
       let goal = Proofview.Goal.concl gl in
       let hyps = Proofview.Goal.hyps gl in
       let hyps_str =
          List.map
            (fun pt -> match pt with
                 | Context.Named.Declaration.LocalAssum (id, typ) ->
                   (Pp.str "\n") ++ (Names.Id.print id) ++
                   (Pp.str " : ") ++ (Printer.pr_econstr typ)
                 | Context.Named.Declaration.LocalDef (id, term, typ) ->
                   (Pp.str "\n") ++ (Names.Id.print id) ++ (Pp.str "term") ++
                   (Pp.str " : ") ++ (Printer.pr_econstr typ)) (* TODO: Deal with the term in this case *)
            hyps in
       Proofview.tclTHEN
       (Proofview.tclLIFT (Proofview.NonLogical.print_warning (Printer.pr_econstr (goal))))
       (Proofview.tclTHEN
        (Proofview.tclLIFT (Proofview.NonLogical.print_warning (Pp.seq hyps_str)))
        (Proofview.tclLIFT (Proofview.NonLogical.print_warning (Pp.seq (List.map (fun s -> Pp.pr_comma () ++ (Pp.int s)) (goal_to_features gl)))))))

let () = register (mk_ml_tac print_goal) "printgoal"

let ml_print_goal () = run_ml_tac "printgoal"

let hash_hash : (int, string) Hashtbl.t = Hashtbl.create 100

let add_hash_hash tac = Hashtbl.replace hash_hash (Hashtbl.hash tac) tac; (Hashtbl.hash tac)

let find_tac num = Hashtbl.find hash_hash num

(* Tactic printing tactic *)

let print_tac tac =
  Proofview.tclLIFT (Proofview.NonLogical.print_warning (Pp.str tac))

let print_tac tac_num = print_tac (find_tac tac_num)

let ml_print_tac args is =
  let str = Tacinterp.Value.cast (Genarg.topwit Stdarg.wit_int) (List.hd args) in
  print_tac str

let () = register ml_print_tac "printtac"

(*let () = append "count.txt" "newfile\n"**)

let run_print_tac tac =
  let hash = add_hash_hash tac in
  let enc = Genarg.in_gen (Genarg.rawwit Stdarg.wit_int) hash in
  TacML (None, ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "printtac"}; mltac_index = 0},
                [TacGeneric enc]))

(* Running predicted tactics *)

exception PredictionsEnd

let parse_tac tac =
   Tacinterp.hide_interp false tac None

let rec tclInterleaveCaseTacs (tacs : unit Proofview.case Proofview.tactic) =
    let open Proofview in
    let open Notations in
    tclCASE tacs >>= function
    | Fail (iexn, info) -> tclZERO ~info:info iexn
    | Next (tac1case, resttacs) ->
      match tac1case with
      | Fail e -> (tclInterleaveCaseTacs (resttacs e))
      | Next ((), tac1') ->
        tclOR (tclUNIT ())
              (fun e -> (tclInterleaveCaseTacs (tclOR (resttacs e)
                                                      (fun e -> (tclCASE (tac1' e))))))

let tclInterleave tac1 tac2 =
    let open Proofview in
    let open Notations in
    tclInterleaveCaseTacs ((tclCASE tac1) <+> (tclCASE tac2))

let tclInterleaveList (tacs : unit Proofview.tactic list) : unit Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclInterleaveCaseTacs
      (List.fold_right (fun tac acc -> (tclCASE tac) <+> acc) tacs (tclZERO PredictionsEnd))

let rec tclInterleaveCaseTacsSpecial start (tacs : bool Proofview.case Proofview.tactic) =
    let open Proofview in
    let open Notations in
    tclCASE tacs >>= function
    | Fail (iexn, info) -> tclZERO ~info:info iexn
    | Next (tac1case, resttacs) ->
      match tac1case with
      | Fail e -> (tclInterleaveCaseTacsSpecial start (resttacs e))
      | Next (b, tac1') ->
        if (start && b) then Tacticals.New.tclZEROMSG (Pp.str "Ran out of tactics") else
        tclOR (if b then tclUNIT () else Tacticals.New.tclCOMPLETE (tclUNIT ()))
              (fun e -> (tclInterleaveCaseTacsSpecial b (tclOR (resttacs e)
                                                               (fun e -> (tclCASE (tac1' e))))))

let rec tclInfiniteTrue () =
    let open Proofview in
    let open Notations in
    tclOR (tclUNIT true) (fun _ -> tclInfiniteTrue ())

let tclInterleaveListSpecial (tacs : unit Proofview.tactic list) : unit Proofview.tactic =
    let open Proofview in
    let open Notations in
    let tacs = List.map (fun t -> t <*> tclUNIT false) tacs in
    tclInterleaveCaseTacsSpecial true
      (List.fold_right (fun tac acc -> (tclCASE tac) <+> acc) tacs (tclCASE (tclInfiniteTrue ())))

let tclInterleaveSpecial tac1 tac2 =
    tclInterleaveListSpecial [tac1; tac2]

let rec tclInterleaveWrong tac1 tac2 =
    let open Proofview in
    let open Notations in
    tclCASE tac1 >>= function
    | Fail iexn -> tac2
    | Next ((), tac1') -> tclOR (tclUNIT ()) (fun e -> (tclInterleaveWrong tac2 (tac1' e)))

let predict gl =
  let feat = goal_to_features gl in
  List.map (fun (a, b, (c, d)) -> c ) (Knn.knn db feat)

let print_goal_short = Proofview.Goal.enter
    (fun gl ->
       let goal = Proofview.Goal.concl gl in
       (Proofview.tclLIFT (Proofview.NonLogical.print_info (Printer.pr_econstr (goal)))))

let rec tclSearch limit : unit Proofview.tactic =
    let open Proofview in
    let open Notations in
    Goal.enter (fun gl ->
        let predictions = predict gl in
        tclSearchGoal predictions limit)
and tclSearchGoal ps limit =
    let open Proofview in
    let open Notations in
    if limit == 0 then Tacticals.New.tclZEROMSG (Pp.str "No more predicted tactics") else
    match ps with
    | [] -> Tacticals.New.tclZEROMSG (Pp.str "No more predicted tactics")
    | tac::ps ->
      let tac2 = parse_tac tac in
      tclUNIT () <+> tclInterleaveSpecial
        ((*(tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pptactic.pr_raw_tactic tac)))) <*>*)
         (*print_goal_short <*>*)
         tclPROGRESS tac2 <*> tclSearch (limit - 0)) (tclSearchGoal ps (limit - 0))

  let tclTIMEOUT2 n t =
    Proofview.tclOR
      (Timeouttac.ptimeout n t)
      begin function (e, info) -> match e with
        | Proofview.Timeout -> Tacticals.New.tclZEROMSG (Pp.str "timout")
        | e -> Tacticals.New.tclZEROMSG (Pp.str "haha")
      end

let searched = ref false

let start_proof_hook_fun id =
    Knn.add db [] (TacId [], "endproof");

    searched := false;
    print_endline ("Proof: " ^ Names.Id.to_string id);
    append "proofs.txt" ("\t" ^ Names.Id.to_string id ^ "\n")

(*let () = Proof_global.start_proof_hook := start_proof_hook_fun*)

(*let () = Vernacentries.vernac_end_proof_hook := start_proof_hook_fun*)

let finalSearch () : unit Proofview.tactic =
    let open Proofview in
    let open Notations in
    let print_success = NonLogical.make (fun () -> append "proofs.txt" "1") in
    if !searched then Tacticals.New.tclZEROMSG (Pp.str "Already searched") else
    (searched := true;
    tclTIMEOUT2 1 (tclLIFT (NonLogical.print_info (Pp.str "Proof search start")) <*>
    tclONCE (Tacticals.New.tclCOMPLETE (tclSearch 10) <*>
    tclLIFT (NonLogical.(>>) print_success (NonLogical.print_info (Pp.str "Proof found!"))) <*>
    Tacticals.New.tclZEROMSG (Pp.str "Proof search does not find proofs"))))

let deleteDups ls =
    let ls = List.sort_uniq (fun (_, _, s) (_, _, u) -> String.compare s u) ls in
    List.sort (fun (x, _, _) (y, _, _) -> Float.compare y x) ls

let userPredict = Proofview.Goal.enter
    (fun gl ->
    let feat = goal_to_features gl in
    (* Make predictions *)
    let r = Knn.knn db feat in
    let r = List.map (fun (x, y, (z, q)) -> (x, y, q)) r in
    let r = deleteDups r in
    (* Print predictions *)
    (Proofview.tclLIFT (Proofview.NonLogical.print_info (print_rank r))))

let userSearch =
    let open Proofview in
    let open Notations in
    tclONCE (Tacticals.New.tclCOMPLETE (tclSearch 3)) <*>
    tclLIFT (NonLogical.print_info (Pp.str "Proof found!"))

let ml_finalSearch args is = finalSearch ()

let () = register ml_finalSearch "finalsearchtac"

let run_finalSearch =
  TacML (None, ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "finalsearchtac"}; mltac_index = 0}, []))

(* Tactic recording tactic *)

let record_tac (tac : glob_tactic_expr) = Proofview.Goal.enter
    (fun gl ->
    let env = Proofview.Goal.env gl in

    let tac_str = Pp.string_of_ppcmds (Pptactic.pr_glob_tactic env tac) in
    if (String.equal tac_str "predict" || String.equal tac_str "search") then Proofview.tclUNIT () else

    let feat = goal_to_features gl in

    (* Make predictions *)
    (*let r = Knn.knn db feat in
    let r = List.map (fun (x, y, (z, q)) -> (x, y, q)) r in
    let pp_str = Pp.int (get_k_str r tac) ++ (*(Pp.str " ") ++ (Pptactic.pr_raw_tactic tac) ++*) (Pp.str "\n") in
    append "count.txt" (Pp.string_of_ppcmds pp_str);*)

    (* Parse into raw tactic and store in db *)
    try
      let raw_tac = Pcoq.parse_string Pltac.tactic_eoi tac_str in
      Knn.add db feat (raw_tac, tac_str);
      Proofview.tclUNIT ()
    with
      | Stream.Error txt -> append "parse_errors.txt" (txt ^ " : " ^ tac_str ^ "\n"); Proofview.tclUNIT ())

    (* Print predictions *)
    (*(Proofview.tclTHEN (Proofview.tclLIFT (Proofview.NonLogical.print_info (pp_str)))
                      (Proofview.tclLIFT (Proofview.NonLogical.print_info (print_rank r))))))*)

let wit_ours : (raw_tactic_expr, glob_tactic_expr, glob_tactic_expr) genarg_type =
  make0 "ours"

let lift intern = (); fun ist x -> (ist, intern ist x)

let out_ty : glob_tactic_expr Geninterp.Val.typ = Geninterp.Val.create "leave_me_alone"

let lifts f = (); fun ist x -> Ftactic.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let (sigma, v) = f ist env sigma x in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
  (Ftactic.return v)
end

let () =
  Genintern.register_intern0 wit_ours (lift Tacintern.intern_tactic_or_tacarg);
  Genintern.register_subst0 wit_ours Tacsubst.subst_tactic;
  register_interp0 wit_ours (lifts  (fun _ _ sigma gtac -> (sigma, gtac)));
  register_val0 wit_ours None

(*
let my_ty : glob_tactic_expr Geninterp.Val.typ = Geninterp.Val.create "leave_me_alone"
let in_f c = Geninterp.Val.Dyn (my_ty, c)

let prj : Val.t -> glob_tactic_expr =
fun v -> let Val.Dyn (t', x) = v in
  match Val.eq my_ty t' with
  | None -> assert false
  | Some Refl -> x


let ml_record_tac args is =
  let t = prj (List.hd args) in record_tac t

let () = register ml_record_tac "recordtac"

let run_record_tac env (tac : glob_tactic_expr) : glob_tactic_expr =
  (*let tac_glob = Tacintern.intern_pure_tactic*)
  let tac_str = Pp.string_of_ppcmds (Pptactic.pr_glob_tactic env tac) in
  (*let hash = add_hash_hash tac_str in*)
  let enc = in_f tac in
  TacML (None, ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "recordtac"}; mltac_index = 0},
                [TacGeneric enc]))

let record_tac_complete env tac : glob_tactic_expr =
  (*TacOr (
    run_finalSearch,*)
    TacThen (TacThen (TacThen (run_record_tac env tac, TacId [] (*ml_print_goal ()*)), TacId [] (*run_print_tac tac*)), TacThen (tac, TacId [] (*ml_print_goal()*)))

let rec history doc ids =
  if List.is_empty ids then () else
  begin
  print_endline (String.concat " " (List.map Stateid.to_string ids));
  history doc (List.flatten (List.map (Stm.neighbors ~doc:doc) ids))
  end

let docidtest () =
  let doc = Stm.get_doc 0 in
  let state = Stm.get_current_state ~doc:doc in
  print_endline "start";
  history doc [state];
  print_endline "end"

let reset () =
  let doc = Stm.get_doc 0 in
  let state = Stm.get_current_state ~doc:doc in
  let laststate = find_last_state doc state in
  Knn.backto db laststate(*;
  print_endline (String.ordinal laststate*)

let update_history () =
  let doc = Stm.get_doc 0 in
  let state = Stm.get_current_state ~doc:doc in
  Hashtbl.add history_count (Stateid.to_int state) (Knn.count db)

let update_history_tac = Proofview.tclBIND (Proofview.tclUNIT ()) (fun _ -> update_history(); Proofview.tclUNIT ())

let ml_update_history_tac args is = update_history_tac

let () = register ml_update_history_tac "updatehistorytac"

let run_update_history_tac =
  TacML (None, ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "updatehistorytac"}; mltac_index = 0}, []))

(* Name globalization *)

open Declarations

let id_of_global env = function
  | ConstRef kn -> Label.to_id (Constant.label kn)
  | IndRef (kn,0) -> Label.to_id (MutInd.label kn)
  | IndRef (kn,i) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_typename
  | ConstructRef ((kn,i),j) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_consnames.(j-1)
  | VarRef v -> v

let rec dirpath_of_mp = function
  | MPfile sl -> sl
  | MPbound uid -> DirPath.make [MBId.to_id uid]
  | MPdot (mp,l) ->
    Libnames.add_dirpath_suffix (dirpath_of_mp mp) (Label.to_id l)

let dirpath_of_global = function
  | ConstRef kn -> dirpath_of_mp (Constant.modpath kn)
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
    dirpath_of_mp (MutInd.modpath kn)
  | VarRef _ -> DirPath.empty

let qualid_of_global env r =
  Libnames.make_qualid (dirpath_of_global r) (id_of_global env r)

(* End name globalization *)

let recorder env tac :  glob_tactic_expr =
  (*let extern_ref ?loc vars r =
      try CAst.make ?loc @@ Libnames.Qualid (qualid_of_global env r)
      with Not_found -> print_endline "error"; CAst.make (Libnames.Qualid (Libnames.qualid_of_string "blupblupblup")) in
  Constrextern.set_extern_reference extern_ref;*)
  (*let tac = Globalize.globalize_glob_tactic_expr tac in*)
  (*print_endline (Pp.string_of_ppcmds (Pptactic.pr_glob_tactic env tac));*)
  let record_tac_complete tac = record_tac_complete env tac in
  let rec annotate tcom : glob_tactic_expr =
    match tcom with
    | TacAtom _         ->                 record_tac_complete tcom (*TacAtom (intros, destruct, etc)*)
    | TacThen (t1, t2)  ->                 TacThen (annotate t1, annotate t2) (*TacThen (a; b)*)
    | TacDispatch tl    ->                 TacDispatch (List.map annotate tl) (*TacDispatch ([> a | b | c])*)
    | TacExtendTac (tl1, t, tl2) ->        TacExtendTac (Array.map annotate tl1, annotate t, Array.map annotate tl2)
                                           (*TacExtendTac ([> a | b .. | c])*)
    | TacThens (t1, tl) ->                 TacThens (annotate t1, List.map annotate tl) (*TacThens (a; [b | c| d])*)
    | TacThens3parts (t1, tl1, t2, tl2) -> TacThens3parts (annotate t1, Array.map annotate tl1,
                                                           annotate t2, Array.map annotate tl2)
                                           (*TacThens3parts (a; [b | c .. | d])*)
    | TacFirst _        ->                 record_tac_complete tcom (*TacFirst (first [a | b | c])*)
    | TacComplete _     ->                 assert false (*TacComplete ?*)
    | TacSolve _        ->                 record_tac_complete tcom (*TacSolve (solve [auto])*)
    | TacTry _          ->                 record_tac_complete tcom (*TacTry (try intros)*)
    | TacOr _           ->                 record_tac_complete tcom (*TacOr (intros + intros)*)
    | TacOnce _         ->                 record_tac_complete tcom (*TacOnce (once intros)*)
    | TacExactlyOnce _  ->                 record_tac_complete tcom (*TacExactlyOnce (exactly_once intros)*)
    | TacIfThenCatch _  ->                 record_tac_complete tcom (*TacIfThenCatch (tryif intros then intros else intros)*)
    | TacOrelse _       ->                 record_tac_complete tcom (*TacOrelse (intros || intros)*)
    | TacDo _           ->                 record_tac_complete tcom (*TacDo (do 5 intros)*)
    | TacTimeout _      ->                 record_tac_complete tcom (*TacTimeout (timeout 5 intros)*)
    | TacTime _         ->                 record_tac_complete tcom (*TacTime (time intros)*)
    | TacRepeat _       ->                 record_tac_complete tcom (*TacRepeat (repeat intros)*)
    | TacProgress _     ->                 record_tac_complete tcom (*TacProgress (progress intros)*)
    | TacShowHyps _     ->                 assert false (*TacShowHyps ?*)
    | TacAbstract _     ->                 record_tac_complete tcom (*TacAbstract (abstract auto)*)
    | TacId _           ->                 record_tac_complete tcom (*TacId (idtac)*)
    | TacFail _         ->                 record_tac_complete tcom (*TacFail (fail)*)
    | TacInfo _         ->                 record_tac_complete tcom (*TacInfo (info auto)*)
    | TacLetIn _        ->                 record_tac_complete tcom (*TacLetIn (let x:= intros in x)*)
    | TacMatch _        ->                 record_tac_complete tcom (*TacMatch (match False with _ => intros end)*)
    | TacMatchGoal _    ->                 record_tac_complete tcom (*TacMatchGoal (match goal with |- _ => intros end)*)
    | TacFun _          ->                 record_tac_complete tcom (*TacFun (fun x => intros)*)
    | TacArg _          ->                 record_tac_complete tcom (*TacArg (split, fresh, context f [_], eval simpl in 5, type of 5, type_term 5, numgoals)*)
    | TacSelect _       ->                 assert false (*TacSelect (only 1: intros)*)
    | TacML _           ->                 record_tac_complete tcom (*TacML ?*)
    | TacAlias _        ->                 record_tac_complete tcom (*TacAlias (guard 1<=1, auto, assert_fails auto, assert_succeeds auto)*)
    in
  reset (); (*docidtest ();*)
  let res = annotate tac in
  TacThen (res, run_update_history_tac)
