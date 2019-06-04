open Printf
open Knn

let read_file filename =
let lines = ref [] in
let chan = open_in filename in
try
  while true; do
    lines := input_line chan :: !lines
  done; !lines
with End_of_file ->
  close_in chan;
  List.rev !lines

let get_k_str ranking comp =
    let rec get_k' acc ranking =
    match ranking with
    | (_, f, o) :: r -> if String.equal o comp then acc else get_k' (1 + acc) r
    | [] -> -1
    in get_k' 0 ranking

let parse_line line =
    let split1 = String.split_on_char ':' line in
    let sfeats = String.sub (List.nth split1 0) 1 (String.length (List.nth split1 0) - 3) in
    let sobj = String.sub (List.nth split1 1) 1 (String.length (List.nth split1 1) - 1) in
    let feats = String.split_on_char ',' sfeats in
    let feats = List.map String.trim feats in
    (feats, sobj)

let eval ls =
    let db = StringNaiveKnn.create () in
    let f (fs, o) =
        let ranking = StringNaiveKnn.knn db fs in
        print_endline (string_of_int (get_k_str ranking o));
        StringNaiveKnn.add db fs o in
    List.iter f ls

let () =
    for i = 1 to Array.length Sys.argv - 1 do
        let lines = (List.tl (read_file Sys.argv.(i))) in
        let parse = List.map parse_line lines in
        eval parse
    done
