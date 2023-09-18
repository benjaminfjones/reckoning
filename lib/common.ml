(* ========================================================================= *)
(* Common utility functions and data structures.                             *)
(*                                                                           *)
(* Most of the content is copied or adapted from John Harrison's book,       *)
(* The Handbook of Practical Logic and Automated Reasoning.                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* (See "LICENSE_Orig.txt" for details.)                                     *)
(*                                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Misc Alias                                                                *)
(* ------------------------------------------------------------------------- *)

let id x = x

(* ------------------------------------------------------------------------- *)
(* Explosion and implosion of strings.                                       *)
(* ------------------------------------------------------------------------- *)

(* Explode a string into a list of single-char strings *)
let explode s =
  let rec exap n l =
    if n < 0 then l else exap (n - 1) (String.sub s n 1 :: l)
  in
  exap (String.length s - 1) []

(* Inverse of `explode` *)
let implode l = List.fold_right ( ^ ) l ""

(* ------------------------------------------------------------------------- *)
(* Set operations on ordered lists.                                          *)
(* ------------------------------------------------------------------------- *)

(* Remove consequtive duplicates from a list; on sorted lists this returns
   the set of unique elements *)
let rec uniq l =
  match l with
  | x :: (y :: _ as t) ->
      let t' = uniq t in
      if Stdlib.compare x y = 0 then t' else if t' == t then l else x :: t'
  | _ -> l

(* Merging of sorted lists (maintaining repetitions) *)
let rec merge ord l1 l2 =
  match l1 with
  | [] -> l2
  | h1 :: t1 -> (
      match l2 with
      | [] -> l1
      | h2 :: t2 ->
          if ord h1 h2 then h1 :: merge ord t1 l2 else h2 :: merge ord l1 t2)

(* Bottom-up mergesort *)
let sort ord =
  let rec mergepairs l1 l2 =
    match (l1, l2) with
    | [ s ], [] -> s
    | l, [] -> mergepairs [] l
    | l, [ s1 ] -> mergepairs (s1 :: l) []
    | l, s1 :: s2 :: ss -> mergepairs (merge ord s1 s2 :: l) ss
  in
  fun l -> if l = [] then [] else mergepairs [] (List.map (fun x -> [ x ]) l)

(* Construct a set, represented as a canonical list *)
let setify =
  let rec canonical lis =
    match lis with
    | x :: (y :: _ as rest) -> Stdlib.compare x y < 0 && canonical rest
    | _ -> true
  in
  fun l ->
    if canonical l then l
    else uniq (sort (fun x y -> Stdlib.compare x y <= 0) l)

(* Construct the union of two lists, as a canonical set *)
let union =
  let rec union l1 l2 =
    match (l1, l2) with
    | [], l2 -> l2
    | l1, [] -> l1
    | (h1 :: t1 as l1), (h2 :: t2 as l2) ->
        if h1 = h2 then h1 :: union t1 t2
        else if h1 < h2 then h1 :: union t1 l2
        else h2 :: union l1 t2
  in
  fun s1 s2 -> union (setify s1) (setify s2)

(* ------------------------------------------------------------------------- *)
(* Common Lexer and Parser helper functions.                                 *)
(* ------------------------------------------------------------------------- *)

(* Lexing Expressions                                                        *)

let matches (parent_str : string) (char : string) =
  let chars = explode parent_str in
  List.mem char chars

let space = matches " \t\r\n"
and punctuation = matches "(){}[],"
and symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"
and numeric = matches "0123456789"

and alphanumeric =
  matches "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

let rec lexwhile (prop : string -> bool) (inp : string list) :
    string * string list =
  match inp with
  | c :: cs when prop c ->
      let tok, rest = lexwhile prop cs in
      (c ^ tok, rest)
  | _ -> ("", inp)

(* lexer *)
let rec lex (inp : string list) : string list =
  match snd (lexwhile space inp) with
  | [] -> []
  | c :: cs ->
      let prop =
        if alphanumeric c then alphanumeric
        else if symbolic c then symbolic
        else fun _ -> false (* for punctuation we stop at one char *)
      in
      let tok, rest = lexwhile prop cs in
      (c ^ tok) :: lex rest

(* lexer example tests *)
let%test _ =
  lex (explode "2*((var_1 + x') + 11)")
  = [ "2"; "*"; "("; "("; "var_1"; "+"; "x'"; ")"; "+"; "11"; ")" ]

let%test _ =
  lex (explode "if (*p1-- == *p2++) then f() else g()")
  = [
      "if";
      "(";
      "*";
      "p1";
      "--";
      "==";
      "*";
      "p2";
      "++";
      ")";
      "then";
      "f";
      "(";
      ")";
      "else";
      "g";
      "(";
      ")";
    ]

(* Wrap a parser function along with the lexer *)
let make_parser pfn inp =
  let toks = lex (explode inp) in
  match pfn toks with e, [] -> e | _ -> failwith "unexpected trailing input"
