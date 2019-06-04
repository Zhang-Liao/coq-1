open Tacexpr
open Misctypes
open Glob_term
open Evar_kinds

let globalize_evar_kind t =
match t with
| ImplicitArg (gr, x, b) -> ImplicitArg (Globnames.canonical_gr gr, x, b)
| BinderType name -> t
| NamedHole id -> t
| QuestionMark (s, name) -> t
| CasesType b -> t
| InternalHole -> t
| TomatchTypeParameter ((i, n1), n2) -> TomatchTypeParameter (((Names.MutInd.make1 (Names.MutInd.canonical i)), n1), n2)
| GoalEvar -> t
| ImpossibleCase -> t
| MatchingVar m -> t
| VarInstance id -> t
| SubEvar e -> t

let rec globalize_cases_pattern_r pat =
match pat with
| PatVar n -> pat
| PatCstr (((mn, n1), n2), ps, n) ->
    PatCstr (((Names.MutInd.make1 (Names.MutInd.canonical mn), n1), n2), List.map globalize_cases_pattern_g ps, n)
and globalize_cases_pattern_g pat = DAst.map globalize_cases_pattern_r pat

let rec globalize_glob_constr_r constr =
match constr with
| GRef (gref, glevel) -> GRef (Globnames.canonical_gr gref, glevel) (* TODO: It seems that glob_level cannot be canonicalized *)
| GVar id -> constr
| GEvar (ename, ls) -> GEvar (ename, List.map (fun (id, c) -> (id, globalize_glob_constr_g c)) ls)
| GPatVar x -> constr
| GApp (c1, cs) -> GApp (globalize_glob_constr_g c1, List.map globalize_glob_constr_g cs)
| GLambda (name, bk, c1, c2) -> GLambda (name, bk, globalize_glob_constr_g c1, globalize_glob_constr_g c2)
| GProd (name, bk, c1, c2) -> GProd (name, bk, globalize_glob_constr_g c1, globalize_glob_constr_g c2)
| GLetIn (name, c1, c2, c3) -> GLetIn (name, globalize_glob_constr_g c1, Option.map globalize_glob_constr_g c2, globalize_glob_constr_g c3)
| GCases (s, c1, tup, claus) ->
    GCases (s, Option.map globalize_glob_constr_g c1, globalize_tomach_tuples_g tup, globalize_cases_clauses_g claus)
| GLetTuple (name, (name2, c1), c2, c3) ->
    GLetTuple (name, (name2, Option.map globalize_glob_constr_g c1), globalize_glob_constr_g c2, globalize_glob_constr_g c3)
| GIf (c1, (name, c2), c3, c4) ->
    GIf (globalize_glob_constr_g c1, (name, Option.map globalize_glob_constr_g c2), globalize_glob_constr_g c3, globalize_glob_constr_g c4)
| GRec (kind, ids, decls, constrs1, constrs2) ->
    GRec (globalize_fix_kind_g kind,
          ids,
          Array.map (List.map globalize_glob_decl_g) decls,
          Array.map globalize_glob_constr_g constrs1,
          Array.map globalize_glob_constr_g constrs2)
| GSort s -> constr (* TODO glob_sort cannot be globalized? *)
| GHole (ev, pat, generic) -> GHole (globalize_evar_kind ev, globalize_intro_pattern_naming_expr pat, generic) (* TODO: Deal with generic arguments *)
| GCast (c1, ctype) -> GCast (globalize_glob_constr_g c1, globalize_cast_type ctype)
and globalize_glob_constr_g constr = DAst.map globalize_glob_constr_r constr
and globalize_glob_decl_g (name, bk, constr1, constr2) =
  (name, bk, Option.map globalize_glob_constr_g constr1, globalize_glob_constr_g constr2)
and globalize_fix_recursion_order_g ro =
match ro with
| GStructRec -> ro
| GWfRec constr -> GWfRec (globalize_glob_constr_g constr)
| GMeasureRec (constr1, constr2) -> GMeasureRec (globalize_glob_constr_g constr1, Option.map globalize_glob_constr_g constr2)
and globalize_fix_kind_g k =
match k with
| GFix (arr, n) -> GFix (Array.map (fun (n, ro) -> (n, globalize_fix_recursion_order_g ro)) arr, n)
| GCoFix n -> k
and globalize_predicate_pattern_g (name, x) : 'a predicate_pattern_g =
  (name, Option.map (CAst.map (fun ((ind_name, n), ns) ->
                                 ((Names.MutInd.make1 (Names.MutInd.canonical ind_name), n), ns))) x)
and globalize_tomach_tuple_g (constr, pred_patt) : 'a tomatch_tuple_g =
  (globalize_glob_constr_g constr, globalize_predicate_pattern_g pred_patt)
and globalize_tomach_tuples_g tup : 'a tomatch_tuples_g = List.map globalize_tomach_tuple_g tup
and globalize_case_clauses_g x =
  CAst.map (fun (ids, patg, constr) ->
    (ids, List.map globalize_cases_pattern_g patg, globalize_glob_constr_g constr)) x
and globalize_cases_clauses_g x = List.map globalize_case_clauses_g x
and globalize_constr_and_expr (glob_constr, constr_expr) = (globalize_glob_constr_g glob_constr, constr_expr)

and globalize_cast_type t =
match t with
| CastConv constr -> CastConv (globalize_glob_constr_g constr)
| CastVM constr -> CastVM (globalize_glob_constr_g constr)
| CastCoerce -> t
| CastNative constr -> CastNative (globalize_glob_constr_g constr)

and globalize_intro_pattern_expr expr =
match expr with
| IntroForthcoming b -> expr
| IntroNaming naming_expr -> IntroNaming (globalize_intro_pattern_naming_expr naming_expr)
| IntroAction action_expr -> IntroAction (globalize_intro_pattern_action_expr action_expr)
and globalize_intro_pattern_naming_expr expr =
match expr with
| IntroIdentifier id -> expr
| IntroFresh id -> expr
| IntroAnonymous -> expr
and globalize_intro_pattern_action_expr expr =
match expr with
| IntroWildcard -> expr
| IntroOrAndPattern or_and_pattern -> IntroOrAndPattern (globalize_or_and_intro_pattern_expr or_and_pattern)
| IntroInjection intro_pattern -> IntroInjection (List.map (CAst.map globalize_intro_pattern_expr) intro_pattern)
| IntroApplyOn (constr, pat) -> IntroApplyOn (CAst.map globalize_constr_and_expr constr, CAst.map globalize_intro_pattern_expr pat)
| IntroRewrite b -> expr
and globalize_or_and_intro_pattern_expr expr =
match expr with
| IntroOrPattern ls -> IntroOrPattern (List.map (List.map (CAst.map globalize_intro_pattern_expr)) ls)
| IntroAndPattern ls -> IntroAndPattern (List.map (CAst.map globalize_intro_pattern_expr) ls)

let globalize_explicit_bindings hs = List.map (CAst.map (fun (h, constr) -> (h, globalize_constr_and_expr constr))) hs

let globalize_bindings b =
match b with
| ImplicitBindings bs -> ImplicitBindings (List.map globalize_constr_and_expr bs)
| ExplicitBindings bs -> ExplicitBindings (globalize_explicit_bindings bs)
| NoBindings -> b

let globalize_with_bindings (constr, cb) = (globalize_constr_and_expr constr, globalize_bindings cb)

let globalize_with_bindings_arg (flg, b) = (flg, globalize_with_bindings b)

let globalize_with_occurrences (oexpr, constr) = (oexpr, globalize_constr_and_expr constr)

let rec globalize_atomic_tactic_expr atac =
match atac with
| TacIntroPattern (eflg, intropattern) -> TacIntroPattern (eflg, List.map (CAst.map globalize_intro_pattern_expr) intropattern)
| TacApply (advanced, eflg, trm, intropattern) -> print_endline "apply";
    TacApply (advanced, eflg,
              List.map globalize_with_bindings_arg trm,
              Option.map (fun (name, pat) -> (name, Option.map (CAst.map globalize_intro_pattern_expr) pat)) intropattern)
| TacElim (eflg, trm1, trm2) -> TacElim (eflg, globalize_with_bindings_arg trm1, Option.map globalize_with_bindings trm2)
| TacCase (eflg, trm) -> TacCase (eflg, globalize_with_bindings_arg trm)
| TacMutualFix (id, n, ls) -> TacMutualFix (id, n, List.map (fun (id, n, trm) -> (id, n, globalize_constr_and_expr trm)) ls)
| TacMutualCofix (id, ls) -> TacMutualCofix (id, List.map (fun (id, trm) -> (id, globalize_constr_and_expr trm)) ls)
| TacAssert (eflg, b, expr, intropattern, trm) ->
    TacAssert (eflg, b,
               Option.map (Option.map globalize_glob_tactic_expr) expr,
               Option.map (CAst.map globalize_intro_pattern_expr) intropattern,
               globalize_constr_and_expr trm)
| TacGeneralize (ls) -> TacGeneralize (List.map (fun (trm, name) -> (globalize_with_occurrences trm, name)) ls)
| TacLetTac (eflg, name, trm, clause, letinflag, intropattern) ->
     TacLetTac (eflg, name,
                globalize_constr_and_expr trm,
                clause, letinflag,
                Option.map (CAst.map globalize_intro_pattern_naming_expr) intropattern)
| TacInductionDestruct (recflg, eflg, ls) -> atac
| TacReduce (red, clause) -> atac
| TacChange (pat, trm, clause) -> atac
| TacRewrite (eflg, ls, clause, expr) -> atac
| TacInversion (is, hyp) -> atac
and globalize_glob_tactic_expr tcom : glob_tactic_expr =
match tcom with
| TacAtom (l, atac)         ->         TacAtom (l, globalize_atomic_tactic_expr atac) (*TacAtom (intros, destruct, etc)*)
| TacThen (t1, t2)  ->                 TacThen (globalize_glob_tactic_expr t1, globalize_glob_tactic_expr t2) (*TacThen (a; b)*)
| TacDispatch tl    ->                 TacDispatch (List.map globalize_glob_tactic_expr tl) (*TacDispatch ([> a | b | c])*)
| TacExtendTac (tl1, t, tl2) ->        TacExtendTac (Array.map globalize_glob_tactic_expr tl1, globalize_glob_tactic_expr t, Array.map globalize_glob_tactic_expr tl2)
                                       (*TacExtendTac ([> a | b .. | c])*)
| TacThens (t1, tl) ->                 TacThens (globalize_glob_tactic_expr t1, List.map globalize_glob_tactic_expr tl) (*TacThens (a; [b | c| d])*)
| TacThens3parts (t1, tl1, t2, tl2) -> TacThens3parts (globalize_glob_tactic_expr t1, Array.map globalize_glob_tactic_expr tl1,
                                                       globalize_glob_tactic_expr t2, Array.map globalize_glob_tactic_expr tl2)
                                       (*TacThens3parts (a; [b | c .. | d])*)
| TacFirst _        ->                 tcom (*TacFirst (first [a | b | c])*)
| TacComplete _     ->                 tcom (*TacComplete ?*)
| TacSolve _        ->                 tcom (*TacSolve (solve [auto])*)
| TacTry _          ->                 tcom (*TacTry (try intros)*)
| TacOr _           ->                 tcom (*TacOr (intros + intros)*)
| TacOnce _         ->                 tcom (*TacOnce (once intros)*)
| TacExactlyOnce _  ->                 tcom (*TacExactlyOnce (exactly_once intros)*)
| TacIfThenCatch _  ->                 tcom (*TacIfThenCatch (tryif intros then intros else intros)*)
| TacOrelse _       ->                 tcom (*TacOrelse (intros || intros)*)
| TacDo _           ->                 tcom (*TacDo (do 5 intros)*)
| TacTimeout _      ->                 tcom (*TacTimeout (timeout 5 intros)*)
| TacTime _         ->                 tcom (*TacTime (time intros)*)
| TacRepeat _       ->                 tcom (*TacRepeat (repeat intros)*)
| TacProgress _     ->                 tcom (*TacProgress (progress intros)*)
| TacShowHyps _     ->                 tcom (*TacShowHyps ?*)
| TacAbstract _     ->                 tcom (*TacAbstract (abstract auto)*)
| TacId _           ->                 tcom (*TacId (idtac)*)
| TacFail _         ->                 tcom (*TacFail (fail)*)
| TacInfo _         ->                 tcom (*TacInfo (info auto)*)
| TacLetIn _        ->                 tcom (*TacLetIn (let x:= intros in x)*)
| TacMatch _        ->                 tcom (*TacMatch (match False with _ => intros end)*)
| TacMatchGoal _    ->                 tcom (*TacMatchGoal (match goal with |- _ => intros end)*)
| TacFun _          ->                 tcom (*TacFun (fun x => intros)*)
| TacArg _          ->                 tcom (*TacArg (split, fresh, context f [_], eval simpl in 5, type of 5, type_term 5, numgoals)*)
| TacSelect _       ->                 tcom (*TacSelect (only 1: intros)*)
| TacML _           ->                 tcom (*TacML ?*)
| TacAlias _        ->                 tcom (*TacAlias (guard 1<=1, auto, assert_fails auto, assert_succeeds auto)*)
