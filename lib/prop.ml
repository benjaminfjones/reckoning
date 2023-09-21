(* ========================================================================= *)
(* Propositial Logic                                                         *)
(* ========================================================================= *)

open Common
open Formulas

type prop = P of string

let pname (P s) = s

(* ------------------------------------------------------------------------- *)
(* Parsing of propositional formulas.                                        *)
(* ------------------------------------------------------------------------- *)

let parse_propvar _vs inp =
  match inp with
  | p :: oinp when p <> "(" -> (Atom (P p), oinp)
  | _ -> failwith "parse_propvar"

(* Parse a prop formula.contents
 *
 * Note the `inp` parser just fails since we don't expect atomic predicates
 *)
let parse_prop_formula =
  make_parser (parse_formula ((fun _ _ -> failwith ""), parse_propvar) [])

let pp = parse_prop_formula (* short alias *)

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

let print_propvar _prec p = print_string (pname p)
let print_prop_formula = print_qformula print_propvar
let prp = print_prop_formula (* short alias for tests/interactive *)

(* ------------------------------------------------------------------------- *)
(* Printing / Parsing Tests                                                  *)
(* ------------------------------------------------------------------------- *)

let%expect_test "round trip" =
  prp (pp "p /\\ q");
  [%expect {| <<p /\ q>> |}]

let%expect_test "round trip forall" =
  prp (pp "forall p. p \\/ q");
  [%expect {| <<forall p. p \/ q>> |}]

let%expect_test "round trip forall exists" =
  prp (pp "forall p. (exists q. (p \\/ ~p) /\\ (p \\/ q))");
  [%expect {| <<forall p. exists q. (p \/ ~p) /\ (p \/ q)>> |}]

let%expect_test "atoms" =
  let ats = atoms (pp "forall p. (exists q. (p \\/ ~p) /\\ (p \\/ q))") in
  print_string (String.concat ", " (List.map pname ats));
  [%expect {| p, q |}]

(* ------------------------------------------------------------------------- *)
(* Valuations                                                                *)
(* ------------------------------------------------------------------------- *)

(* Evaluate a prop formula under a valuation.
 *
 * Valuations are partial maps from `atoms fm` -> bool
 *)
let rec eval fm v =
  match fm with
  | False -> false
  | True -> true
  | Atom p -> v p
  | Not f -> not (eval f v)
  | And (f, g) -> eval f v && eval g v
  | Or (f, g) -> eval f v || eval g v
  | Imp (f, g) -> (not (eval f v)) || eval g v
  | Iff (f, g) -> eval f v = eval g v
  | _ -> failwith "eval undefined"

(* Evaluate `subfn : valuation -> bool` over all possible valuations of the atoms of `fm`.
 *
 * The evaluation over all valuations short circuits as soon as `subfn` returns false.
 *)
let rec onallvaluations subfn fm v ats =
  match ats with
  | [] -> subfn v
  | p :: ps ->
      (* new valuation: (p |-> t) v *)
      let v' t q = if p = q then t else v q in
      onallvaluations subfn fm (v' false) ps
      && onallvaluations subfn fm (v' true) ps

let print_truthtable fm =
  let ats = atoms fm in
  let width =
    1 + List.fold_left (fun w a -> max w (String.length (pname a))) 5 ats
  in
  let fixw s = s ^ String.make (width - String.length s) ' ' in
  let truthstring p = fixw (if p then "true" else "false") in
  (* prints a row of evaluations over `v`; does not short circuit `onallvaluations` *)
  let mk_row v =
    let lis = List.map (fun x -> truthstring (v x)) ats
    and ans = truthstring (eval fm v) in
    print_string (List.fold_left ( ^ ) "" lis ^ "| " ^ ans);
    print_newline ();
    true
  in
  let separator = String.make ((width * List.length ats) + 9) '-' in
  print_string
    (List.fold_left (fun t s -> t ^ fixw (pname s)) "" ats ^ "| formula");
  print_newline ();
  print_string separator;
  print_newline ();
  let _ = onallvaluations mk_row fm (fun _ -> false) ats in
  print_string separator;
  print_newline ()

(* Decide if a prop formula is a tautology by evaluating it against all
   possible valuations of its atoms.

   The only optimization is that the procedure short-circuits as soon as a valuation
   is encountered where `fm` evaluated to `false`.
*)
let tautology fm = onallvaluations (eval fm) fm (fun _ -> false) (atoms fm)
let unsatisfiable fm = tautology (mk_not fm)
let satisfiable fm = not (unsatisfiable fm)

(* ------------------------------------------------------------------------- *)
(* Tests                                                                     *)
(* ------------------------------------------------------------------------- *)

let%test "eval p and q -> false" =
  not
    (eval (pp "p /\\ q") (function
      | P "p" -> true
      | P "q" -> false
      | _ -> true))

let%test "eval p and q -> true" =
  eval (pp "p /\\ q") (function P "p" -> true | P "q" -> true | _ -> true)

let%test "eval q and p -> true" =
  eval (pp "q /\\ p") (function P "p" -> true | P "q" -> true | _ -> true)

let%test "eval p nor q -> false" =
  not
    (eval (pp "~(p \\/ q)") (function
      | P "p" -> true
      | P "q" -> false
      | _ -> true))

let%test "eval p nor q -> true" =
  eval (pp "~(p \\/ q)") (function
    | P "p" -> false
    | P "q" -> false
    | _ -> true)

let%test "eval pqr v1" =
  eval (pp "p /\\ q ==> q /\\ r") (function
    | P "p" -> true
    | P "q" -> false
    | P "r" -> true
    | _ -> true)

let%test "eval pqr v2" =
  eval (pp "p /\\ q ==> q /\\ r") (function
    | P "p" -> true
    | P "q" -> false
    | P "r" -> false
    | _ -> true)

let%test "eval iff -> false" =
  not
    (eval (pp "p <=> q") (function
      | P "p" -> true
      | P "q" -> false
      | _ -> true))

let%test "eval iff -> true" = eval (pp "p <=> q") (function _ -> true)
let%test "eval p iff p -> true" = eval (pp "p <=> p") (function _ -> true)

let%test "eval q iff q -> true" =
  eval (pp "q <=> q") (function P "q" -> false | _ -> true)

let%expect_test "truth table q and p" =
  print_truthtable (pp "q /\\ p");
  [%expect
    {|
    p     q     | formula
    ---------------------
    false false | false
    false true  | false
    true  false | false
    true  true  | true
    --------------------- |}]

let%expect_test "truth table p and q" =
  print_truthtable (pp "p /\\ q");
  [%expect
    {|
    p     q     | formula
    ---------------------
    false false | false
    false true  | false
    true  false | false
    true  true  | true
    --------------------- |}]

let%expect_test "truth table iff" =
  print_truthtable (pp "p <=> q");
  [%expect
    {|
    p     q     | formula
    ---------------------
    false false | true
    false true  | false
    true  false | false
    true  true  | true
    --------------------- |}]

let%expect_test "truth table impl" =
  print_truthtable (pp "q ==> r");
  [%expect
    {|
    q     r     | formula
    ---------------------
    false false | true
    false true  | true
    true  false | false
    true  true  | true
    --------------------- |}]

let%expect_test "truth table and_comm" =
  print_truthtable (pp "p /\\ q <=> q /\\ p");
  [%expect
    {|
    p     q     | formula
    ---------------------
    false false | true
    false true  | true
    true  false | true
    true  true  | true
    --------------------- |}]

let%expect_test "truth table and_comm not quite" =
  print_truthtable (pp "p /\\ q ==> q /\\ r");
  [%expect
    {|
    p     q     r     | formula
    ---------------------------
    false false false | true
    false false true  | true
    false true  false | true
    false true  true  | true
    true  false false | true
    true  false true  | true
    true  true  false | false
    true  true  true  | true
    --------------------------- |}]

(* Lots of tautologies *)

let%test "tautology: and_comm" = tautology (pp "p /\\ q <=> q /\\ p")

let%test "not tautology: and_comm mystery variable" =
  not (tautology (pp "p /\\ q <=> q /\\ r"))

let%test "tautology: p or not p" = tautology (pp "p \\/ ~p")

let%test "not tautology: p or q implies p" =
  not (tautology (pp "p \\/ q ==> p"))

let%test "tautology: p or q implies stuff" =
  not (tautology (pp "p \\/ q ==> q \\/ (p <=> q)"))

let%test "satisfiable: p or q implies stuff" =
  satisfiable (pp "p \\/ q ==> q \\/ (p <=> q)")

let%test "tautology: p or q and not (p and q)" =
  tautology (pp "(p \\/ q) /\\ ~(p /\\ q) ==> (~p <=> q)")

(* ------------------------------------------------------------------------- *)
(* Failed attempt at setting up a PPX, in-module, for parsing prop formulas  *)
(* ------------------------------------------------------------------------- *)

(* TODO: figure out if a PPX can be used here instead of a camlp* preprocessor *)
(* Set this up as default for quotations.                                    *)
(* let default_parser = parse_prop_formula *)
(* #install_printer print_prop_formula *)

(* open Ppxlib *)
(* open Ppxlib_metaquot *)
(**)
(* let expand ~ctxt formula_str = *)
(*   let loc = Expansion_context.Extension.extension_point_loc ctxt in *)
(*   Ast_helper.with_default_loc loc (fun () -> *)
(*       [%expr parse_prop_formula [%e formula_str]]) *)
(**)
(* let my_extension = *)
(*   Extension.V3.declare "pp" Extension.Context.expression *)
(*     Ast_pattern.(single_expr_payload (estring __)) *)
(*     expand *)
(**)
(* let rule = Ppxlib.Context_free.Rule.extension my_extension *)
(* let () = Driver.register_transformation ~rules:[ rule ] "pp" *)
