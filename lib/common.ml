(* ========================================================================= *)
(* Common utility functions and data structures.                             *)
(*                                                                           *)
(* Most of the content is copied or adapted from John Harrison's book,       *)
(* The Handbook of Practical Logic and Automated Reasoning. Adaptations      *)
(* mostly involve use of modern Ocaml Stdlib and best practices.             *)
(*                                                                           *)
(* Original code is copyright (c) 2003-2007, John Harrison.                  *)
(* (See "LICENSE_Orig.txt" for details.)                                     *)
(*                                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Misc Alias                                                                *)
(* ------------------------------------------------------------------------- *)

let id x = x

(* ------------------------------------------------------------------------- *)
(* Handy list helpers                                                        *)
(* ------------------------------------------------------------------------- *)

(* List.fold_right but fails on the empty list *)
let rec end_itlist f l =
  match l with
  | [] -> failwith "end_itlist"
  | [ x ] -> x
  | h :: t -> f h (end_itlist f t)

(* Apply f to all pairs of elements from the two input lists *)
let rec allpairs f l1 l2 =
  match l1 with
  | h1 :: t1 -> List.fold_right (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> []

(* Construct a list of all distinct pairs of list elements (not values) from
   the input list *)
let rec distinctpairs l =
  match l with
  | x :: t -> List.fold_right (fun y a -> (x, y) :: a) t (distinctpairs t)
  | [] -> []

let rec ( -- ) i j =
  match (i, j) with i, j when j < i -> [] | i, j -> i :: (i + 1 -- j)

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

let rec allsubsets (size : int) (set : 'a list) : 'a list list =
  let set = setify set in
  match size with
  | k when k <= 0 -> [ [] ]
  | k when k > List.length set -> []
  | k -> (
      match set with
      | [] -> []
      | s :: rest ->
          union
            (List.map (union [ s ]) (allsubsets (k - 1) rest))
            (allsubsets k rest))

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

(* ------------------------------------------------------------------------- *)
(* Polymorphic finite partial functions via Patricia trees.                  *)
(*                                                                           *)
(* The point of this strange representation is that it is canonical (equal   *)
(* functions have the same encoding) yet reasonably efficient on average.    *)
(*                                                                           *)
(* Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* ------------------------------------------------------------------------- *)

type ('a, 'b) func =
  | Empty
  | Leaf of int * ('a * 'b) list
  | Branch of int * int * ('a, 'b) func * ('a, 'b) func

(* ------------------------------------------------------------------------- *)
(* Undefined function.                                                       *)
(* ------------------------------------------------------------------------- *)

let undefined = Empty

(* ------------------------------------------------------------------------- *)
(* In case of equality comparison worries, better use this.                  *)
(* ------------------------------------------------------------------------- *)

let is_undefined f = match f with Empty -> true | _ -> false

(* ------------------------------------------------------------------------- *)
(* Operation analogous to "map" for lists.                                   *)
(* ------------------------------------------------------------------------- *)

let mapf =
  let rec map_list f l =
    match l with [] -> [] | (x, y) :: t -> (x, f y) :: map_list f t
  in
  let rec mapf f t =
    match t with
    | Empty -> Empty
    | Leaf (h, l) -> Leaf (h, map_list f l)
    | Branch (p, b, l, r) -> Branch (p, b, mapf f l, mapf f r)
  in
  mapf

(* ------------------------------------------------------------------------- *)
(* Operations analogous to "fold" for lists.                                 *)
(* ------------------------------------------------------------------------- *)

let foldl =
  let rec foldl_list f a l =
    match l with [] -> a | (x, y) :: t -> foldl_list f (f a x y) t
  in
  let rec foldl f a t =
    match t with
    | Empty -> a
    | Leaf (_h, l) -> foldl_list f a l
    | Branch (_p, _b, l, r) -> foldl f (foldl f a l) r
  in
  foldl

let foldr =
  let rec foldr_list f l a =
    match l with [] -> a | (x, y) :: t -> f x y (foldr_list f t a)
  in
  let rec foldr f t a =
    match t with
    | Empty -> a
    | Leaf (_h, l) -> foldr_list f l a
    | Branch (_p, _b, l, r) -> foldr f l (foldr f r a)
  in
  foldr

(* ------------------------------------------------------------------------- *)
(* Mapping to sorted-list representation of the graph, domain and range.     *)
(* ------------------------------------------------------------------------- *)

let graph f = setify (foldl (fun a x y -> (x, y) :: a) [] f)
let dom f = setify (foldl (fun a x _y -> x :: a) [] f)
let ran f = setify (foldl (fun a _x y -> y :: a) [] f)

(* ------------------------------------------------------------------------- *)
(* Application.                                                              *)
(* ------------------------------------------------------------------------- *)

(* FPF application with a function to apply on failure *)
let applyd =
  let rec apply_listd l d x =
    match l with
    | (a, b) :: t ->
        let c = Stdlib.compare x a in
        if c = 0 then b else if c > 0 then apply_listd t d x else d x
    | [] -> d x
  in
  fun f d x ->
    let k = Hashtbl.hash x in
    let rec look t =
      match t with
      | Leaf (h, l) when h = k -> apply_listd l d x
      | Branch (p, b, l, r) when k lxor p land (b - 1) = 0 ->
          look (if k land b = 0 then l else r)
      | _ -> d x
    in
    look f

(* FPF application with possible failure *)
let apply f = applyd f (fun _ -> failwith "apply")

(* FPF application with default value upon failure *)
let tryapplyd f a d = applyd f (fun _ -> d) a

(* FPF application with empty list upon failure *)
let tryapplyl f x = tryapplyd f x []

(* Is the FPF defined at `x`? *)
let defined f x =
  try
    apply f x;
    true
  with Failure _ -> false

(* ------------------------------------------------------------------------- *)
(* Undefinition.                                                             *)
(* ------------------------------------------------------------------------- *)

(* Remove the mapping for the given domain element *)
let undefine =
  let rec undefine_list x l =
    match l with
    | ((a, _b) as ab) :: t ->
        let c = Stdlib.compare x a in
        if c = 0 then t
        else if c < 0 then l
        else
          let t' = undefine_list x t in
          if t' == t then l else ab :: t'
    | [] -> []
  in
  fun x ->
    let k = Hashtbl.hash x in
    let rec und t =
      match t with
      | Leaf (h, l) when h = k ->
          let l' = undefine_list x l in
          if l' == l then t else if l' = [] then Empty else Leaf (h, l')
      | Branch (p, b, l, r) when k land (b - 1) = p -> (
          if k land b = 0 then
            let l' = und l in
            if l' == l then t
            else match l' with Empty -> r | _ -> Branch (p, b, l', r)
          else
            let r' = und r in
            if r' == r then t
            else match r' with Empty -> l | _ -> Branch (p, b, l, r'))
      | _ -> t
    in
    und

(* ------------------------------------------------------------------------- *)
(* Redefinition and combination.                                             *)
(* ------------------------------------------------------------------------- *)

(* Redefine an FPF with a new point mapping, combine FPFs in order *)
let ( |-> ), combine =
  let newbranch p1 t1 p2 t2 =
    let zp = p1 lxor p2 in
    let b = zp land -zp in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch (p, b, t1, t2) else Branch (p, b, t2, t1)
  in
  let rec define_list ((x, _y) as xy) l =
    match l with
    | ((a, _b) as ab) :: t ->
        let c = Stdlib.compare x a in
        if c = 0 then xy :: t
        else if c < 0 then xy :: l
        else ab :: define_list xy t
    | [] -> [ xy ]
  and combine_list op z l1 l2 =
    match (l1, l2) with
    | [], _ -> l2
    | _, [] -> l1
    | ((x1, y1) as xy1) :: t1, ((x2, y2) as xy2) :: t2 ->
        let c = Stdlib.compare x1 x2 in
        if c < 0 then xy1 :: combine_list op z t1 l2
        else if c > 0 then xy2 :: combine_list op z l1 t2
        else
          let y = op y1 y2 and l = combine_list op z t1 t2 in
          if z y then l else (x1, y) :: l
  in
  let ( |-> ) x y =
    let k = Hashtbl.hash x in
    let rec upd t =
      match t with
      | Empty -> Leaf (k, [ (x, y) ])
      | Leaf (h, l) ->
          if h = k then Leaf (h, define_list (x, y) l)
          else newbranch h t k (Leaf (k, [ (x, y) ]))
      | Branch (p, b, l, r) ->
          if k land (b - 1) <> p then newbranch p t k (Leaf (k, [ (x, y) ]))
          else if k land b = 0 then Branch (p, b, upd l, r)
          else Branch (p, b, l, upd r)
    in
    upd
  in
  let rec combine op z t1 t2 =
    match (t1, t2) with
    | Empty, _ -> t2
    | _, Empty -> t1
    | Leaf (h1, l1), Leaf (h2, l2) ->
        if h1 = h2 then
          let l = combine_list op z l1 l2 in
          if l = [] then Empty else Leaf (h1, l)
        else newbranch h1 t1 h2 t2
    | (Leaf (k, _lis) as lf), (Branch (p, b, l, r) as br) ->
        if k land (b - 1) = p then
          if k land b = 0 then
            match combine op z lf l with
            | Empty -> r
            | l' -> Branch (p, b, l', r)
          else
            match combine op z lf r with
            | Empty -> l
            | r' -> Branch (p, b, l, r')
        else newbranch k lf p br
    | (Branch (p, b, l, r) as br), (Leaf (k, _lis) as lf) ->
        if k land (b - 1) = p then
          if k land b = 0 then
            match combine op z l lf with
            | Empty -> r
            | l' -> Branch (p, b, l', r)
          else
            match combine op z r lf with
            | Empty -> l
            | r' -> Branch (p, b, l, r')
        else newbranch p br k lf
    | Branch (p1, b1, l1, r1), Branch (p2, b2, l2, r2) ->
        if b1 < b2 then
          if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
          else if p2 land b1 = 0 then
            match combine op z l1 t2 with
            | Empty -> r1
            | l -> Branch (p1, b1, l, r1)
          else
            match combine op z r1 t2 with
            | Empty -> l1
            | r -> Branch (p1, b1, l1, r)
        else if b2 < b1 then
          if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
          else if p1 land b2 = 0 then
            match combine op z t1 l2 with
            | Empty -> r2
            | l -> Branch (p2, b2, l, r2)
          else
            match combine op z t1 r2 with
            | Empty -> l2
            | r -> Branch (p2, b2, l2, r)
        else if p1 = p2 then
          match (combine op z l1 l2, combine op z r1 r2) with
          | Empty, r -> r
          | l, Empty -> l
          | l, r -> Branch (p1, b1, l, r)
        else newbranch p1 t1 p2 t2
  in
  (( |-> ), combine)

(* ------------------------------------------------------------------------- *)
(* Special case of point function.                                           *)
(* ------------------------------------------------------------------------- *)

let ( |=> ) x y = (x |-> y) undefined

(* ------------------------------------------------------------------------- *)
(* Idiom for a mapping zipping domain and range lists.                       *)
(* ------------------------------------------------------------------------- *)

(* Construct a FPF from a pair of lists [domain elts] [values] *)
let fpf xs ys = List.fold_right2 ( |-> ) xs ys undefined

(* ------------------------------------------------------------------------- *)
(* Grab an arbitrary element.                                                *)
(* ------------------------------------------------------------------------- *)

let rec choose t =
  match t with
  | Empty -> failwith "choose: completely undefined function"
  | Leaf (_h, l) -> List.hd l
  | Branch (_b, _p, t1, _t2) -> choose t1


(* ------------------------------------------------------------------------- *)
(* Timing; useful for tests                                                  *)
(* ------------------------------------------------------------------------- *)

let time f x =
  let start_time = Sys.time() in
  let result = f x in
  let finish_time = Sys.time() in
  print_string
    ("CPU time (user): "^(string_of_float(finish_time -. start_time)));
  print_newline();
  result;