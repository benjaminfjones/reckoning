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
  (* constant propagation *)
  | Add (Const n, Const m) -> Const (n + m)
  | Mul (Const n, Const m) -> Const (n * m)
  (* unit laws *)
  | Add (Const 0, x) -> x
  | Add (x, Const 0) -> x
  | Mul (Const 0, _) -> Const 0
  | Mul (_, Const 0) -> Const 0
  | Mul (Const 1, x) -> x
  | Mul (x, Const 1) -> x
  (* right associate to cannonical form *)
  | Add (Add (x, y), z) -> Add (x, Add (y, z))
  | Mul (Mul (x, y), z) -> Mul (x, Mul (y, z))
  | _ -> expr

let rec simplify expr =
  match expr with
  | Add (x, y) -> simplify1 (Add (simplify x, simplify y))
  | Mul (x, y) -> simplify1 (Mul (simplify x, simplify y))
  | _ -> simplify1 expr

(* a not much more smarter traversal ? *)
let rec sm_simplify expr =
  match expr with
  | Add (x, y) -> simplify1 (Add (sm_simplify x, sm_simplify y))
  | Mul (x, y) ->
      let lhs = sm_simplify x in
      if lhs == Const 0 then Const 0 else simplify1 (Mul (lhs, sm_simplify y))
  | _ -> simplify1 expr

let e0 = Add (Mul (Add (Mul (Const 0, Var "x"), Const 1), Const 3), Const 12)
let%test _ = simplify e0 = Const 15

(* ------------------------------------------------------------------------- *)
(* Parsing Arithmetic Expressions                                            *)
(* ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
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
   ------------------------------------------------------------------------- *)

(* Start *)
let rec parse_expression (inp : string list) : expression * string list =
  match parse_product inp with
  | e1, "+" :: inp' ->
      let e2, inp'' = parse_expression inp' in
      (Add (e1, e2), inp'')
  | r -> r

and parse_product (inp : string list) : expression * string list =
  match parse_atom inp with
  | e1, "*" :: inp' ->
      let e2, inp'' = parse_atom inp' in
      (Mul (e1, e2), inp'')
  | r -> r

and parse_atom (inp : string list) : expression * string list =
  match inp with
  | "(" :: rest -> (
      let e, rest' = parse_expression rest in
      match rest' with
      | ")" :: rest'' -> (e, rest'')
      | _ -> failwith "expected closing paren")
  | tok :: rest when List.for_all numeric (explode tok) ->
      (Const (int_of_string tok), rest)
  | tok :: rest -> (Var tok, rest)
  | _ -> failwith "expected atom"

let expression_parser = make_parser parse_expression

let%test _ =
  expression_parser "1 + (2 + 3) * y"
  = Add (Const 1, Mul (Add (Const 2, Const 3), Var "y"))

let%test _ =
  expression_parser "1 + 2 + 3" = Add (Const 1, Add (Const 2, Const 3))

let%test _ =
  expression_parser "1 + 3 * y" = Add (Const 1, Mul (Const 3, Var "y"))

(* ------------------------------------------------------------------------- *)
(* Pretty Pringing Expressions                                               *)
(* ------------------------------------------------------------------------- *)

(* Pretty print an expression.

   Internally, precedence is used to parenthesize sub-expressions. Precendence
   table is:
   - Add: 2
   - Mul: 4
*)
let string_of_expression (expr : expression) : string =
  let paren s = "(" ^ s ^ ")" in
  (* `pr` is the precendence level of the parent expression *)
  let rec fmt pr e =
    match e with
    | Const n -> string_of_int n
    | Var x -> x
    | Add (e1, e2) ->
        let substr = fmt 3 e1 ^ " + " ^ fmt 2 e2 in
        if pr > 2 then paren substr else substr
    | Mul (e1, e2) ->
        let substr = fmt 5 e1 ^ " * " ^ fmt 4 e2 in
        if pr > 4 then paren substr else substr
  in
  fmt 0 expr

let print_expr e = Format.print_string (string_of_expression e)

let%expect_test "print expr better" =
  print_expr (expression_parser "1 + (2 + 3) * y");
  [%expect {| 1 + (2 + 3) * y |}]

let%expect_test "print def assoc adds" =
  print_expr (expression_parser "1 + 2 + 3");
  [%expect {| 1 + 2 + 3 |}]

let%expect_test "print left assoc adds" =
  print_expr (expression_parser "(1 + 2) + 3");
  [%expect {| (1 + 2) + 3 |}]

let%expect_test "print add of mul" =
  print_expr (expression_parser "1 + 3 * x");
  [%expect {| 1 + 3 * x |}]

let%expect_test "print mul of add" =
  print_expr (expression_parser "(x+y)*(z+w)");
  [%expect {| (x + y) * (z + w) |}]

let%expect_test "lots o parens" =
  print_expr (expression_parser "(((1 + ((2)))))");
  [%expect {| 1 + 2 |}]

(* Expression generator *)

(* A simple random expression generator *)
let rec rnd_expression sz cbound =
  let rnd_var pre = Var (pre ^ string_of_int @@ Random.int 10) in
  if sz <= 0 then
    match Random.int 2 with
    | 0 -> Const (Random.int cbound)
    | 1 -> rnd_var "x"
    | _ -> failwith "unreachable"
  else
    match Random.int 2 with
    | 0 ->
        let e1 = rnd_expression (sz - 1) cbound in
        let e2 = rnd_expression (sz - 1) cbound in
        Add (e1, e2)
    | 1 ->
        let e1 = rnd_expression (sz - 1) cbound in
        let e2 = rnd_expression (sz - 1) cbound in
        Mul (e1, e2)
    | _ -> failwith "unreachable"

(* Interactive exampels *)

(*
  $ dune utop lib
  utop # open Reckoning.Intro;;

  utop # let e5 = rnd_expression 5 3;;
  val e5 : expression =
    Add
     (Mul
       (Mul (Mul (Mul (Var "x1", Var "x9"), Mul (Const 2, Const 2)),
         Mul (Mul (Const 0, Var "x5"), Add (Var "x4", Const 0))),
       Add (Add (Add (Const 2, Var "x2"), Add (Var "x9", Const 0)),
        Mul (Add (Const 1, Var "x6"), Add (Var "x0", Var "x2")))),
     Add
      (Mul (Add (Mul (Var "x3", Const 2), Mul (Var "x0", Var "x0")),
        Mul (Add (Var "x2", Const 1), Add (Const 2, Var "x3"))),
      Add (Mul (Mul (Var "x9", Const 1), Mul (Var "x8", Var "x1")),
       Mul (Add (Var "x7", Var "x9"), Add (Var "x4", Var "x1")))))

  utop # print_expr (simplify e5);;
  (x3 * 2 + x0 * x0) * (x2 + 1) * (2 + x3) + x9 * x8 * x1 + (x7 + x9) * (x4 + x1)

*)
