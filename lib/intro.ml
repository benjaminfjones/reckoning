open Common

(* ------------------------------------------------------------------------- *)
(* Simple Arithmetic Expressions                                             *)
(* ------------------------------------------------------------------------- *)

type expression =
  | Const of int
  | Var of string
  | Add of expression * expression
  | Mul of expression * expression

let simplify1 expr =
  match expr with
  | Add (Const n, Const m) -> Const (n + m)
  | Mul (Const n, Const m) -> Const (n * m)
  | Add (Const 0, x) -> x
  | Mul (Const 0, _) -> Const 0
  | Mul (_, Const 0) -> Const 0
  | Mul (Const 1, x) -> x
  | Mul (x, Const 1) -> x
  | _ -> expr

let rec simplify expr =
  match expr with
  | Add (x, y) -> simplify1 (Add (simplify x, simplify y))
  | Mul (x, y) -> simplify1 (Mul (simplify x, simplify y))
  | _ -> simplify1 expr

let e0 = Add (Mul (Add (Mul (Const 0, Var "x"), Const 1), Const 3), Const 12)
let%test _ = simplify e0 = Const 15

(* ------------------------------------------------------------------------- *)
(* Parsing Expressions                                                       *)
(* ------------------------------------------------------------------------- *)

let matches s =
  let chars = explode s in
  fun c -> List.mem c chars

let space = matches " \t\r\n"
and punctuation = matches "(){}[],"
and symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"
and numberic = matches "0123456789"

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

(*
  Right Factored Grammar:

  expression = product
             | product + expression
  product    = atom
             | atom * product
  atom       = ( expression )
             | constant
             | variable
  constant   = numeric+
  variable   = alphanumeric+
*)

(* TODO: parser *)
