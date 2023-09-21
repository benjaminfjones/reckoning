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

(* Substitute a prop formula for an atomic variable.
 *
 * `subfn` is a finite partial function from a prop atom to a prop formula
 *)
let psubst subfn = onatoms (fun p -> tryapplyd subfn p (Atom p))

(* ------------------------------------------------------------------------- *)
(* Simplification and Normal Forms                                           *)
(* ------------------------------------------------------------------------- *)

let psimplify1 fm =
  match fm with
  | Not False -> True
  | Not True -> False
  | Not (Not p) -> p
  | And (_p, False) | And (False, _p) -> False
  | And (p, True) | And (True, p) -> p
  | Or (p, False) | Or (False, p) -> p
  | Or (_p, True) | Or (True, _p) -> True
  | Imp (False, _p) | Imp (_p, True) -> True
  | Imp (True, p) -> p
  | Imp (p, False) -> Not p
  | Iff (p, True) | Iff (True, p) -> p
  | Iff (p, False) | Iff (False, p) -> Not p
  | _ -> fm

let rec psimplify fm =
  match fm with
  | Not p -> psimplify1 (Not (psimplify p))
  | And (p, q) -> psimplify1 (And (psimplify p, psimplify q))
  | Or (p, q) -> psimplify1 (Or (psimplify p, psimplify q))
  | Imp (p, q) -> psimplify1 (Imp (psimplify p, psimplify q))
  | Iff (p, q) -> psimplify1 (Iff (psimplify p, psimplify q))
  | _ -> fm

(* Is the literal negative (must be applied only to literals) *)
let negative = function Not _ -> true | _ -> false
let positive lit = not (negative lit)
let negate = function Not p -> p | p -> Not p

let nnf fm =
  let rec nnf_aux fm =
    match fm with
    | And (p, q) -> And (nnf_aux p, nnf_aux q)
    | Or (p, q) -> Or (nnf_aux p, nnf_aux q)
    | Imp (p, q) -> Or (nnf_aux (Not p), nnf_aux q)
    | Iff (p, q) ->
        Or (And (nnf_aux p, nnf_aux q), And (nnf_aux (Not p), nnf_aux (Not q)))
    | Not (Not p) -> nnf_aux p
    | Not (And (p, q)) -> Or (nnf_aux (Not p), nnf_aux (Not q))
    | Not (Or (p, q)) -> And (nnf_aux (Not p), nnf_aux (Not q))
    | Not (Imp (p, q)) -> And (nnf_aux p, nnf_aux (Not q))
    | Not (Iff (p, q)) ->
        Or (And (nnf_aux p, nnf_aux (Not q)), And (nnf_aux (Not p), nnf_aux q))
    | _ -> fm
  in
  nnf_aux (psimplify fm)

let list_conj = function [] -> True | l -> end_itlist mk_and l
and list_disj = function [] -> False | l -> end_itlist mk_or l

(* Given a list of formulas, make a conjunction of "literals" according to
 * whether each is satisfied by valuation `v`.
 *
 * This is meant to be called on a list of Atomic formulas.
 *)
let mk_lits pvs v =
  list_conj (List.map (fun p -> if eval p v then p else Not p) pvs)

(* Collect valuations which hold on `subfn`
 *
 * The formulas `fms` are meant to be atomic formulas. An example * `subfn :
 * valuation -> bool` tha is useful is evaluation of a top-level formula using
 * the current valuation being explored.
 *)
let rec allsatvaluations subfn v fms =
  match fms with
  | [] -> if subfn v then [ v ] else []
  | p :: ps ->
      let v' t q = if p = q then t else v q in
      allsatvaluations subfn (v' false) ps @ allsatvaluations subfn (v' true) ps

(* Disjunctive Normal Form
 *
 * DNF is computed via truth table enumeration. Worst-case complexity is
 * O(2^num_atoms) ~= O(2^size_formula) .
 *)
let dnf fm =
  let pvs = atoms fm in
  let satvals = allsatvaluations (eval fm) (fun _ -> false) pvs in
  let atoms = List.map (fun p -> Atom p) pvs in
  list_disj (List.map (mk_lits atoms) satvals)

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

(* Surprising tautologies, including Dijkstra's Golden Rule *)

let%test "tautology: counter intuitive" =
  tautology (pp "(p ==> q) \\/ (q ==> p)")

let%test "tautology: Dijkstra Scholten" =
  tautology (pp "p \\/ (q <=> r) <=> (p \\/ q <=> p \\/ r)")

(* "Golden Rule" *)
let%test "tautology: golden rule 1" =
  tautology (pp "p /\\ q <=> ((p <=> q) <=> p \\/ q)")

let%test "tautology: contrapositive 1" =
  tautology (pp "(p ==> q) <=> (~q ==> ~p)")

let%test "tautology: contrapositive 2" =
  tautology (pp "(p ==> ~q) <=> (q ==> ~p)")

let%test "common fallacy: implies not symmetric" =
  not (tautology (pp "(p ==> q) <=> (q ==> p)"))

(* Some logical equivalences allowing elimination of connectives *)

let%test "eliminate logical connectives: {==>, false} are adequate" =
  List.for_all tautology
    [
      pp "true <=> false ==> false";
      pp "~p <=> p ==> false";
      pp "p /\\ q <=> (p ==> q ==> false) ==> false";
      pp "p \\/ q <=> (p ==> false) ==> q";
      pp "(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false";
    ]

let%test "montonicity of and" =
  tautology (pp "(p ==> p') /\\ (q ==> q') ==> ((p /\\ q) ==> (p' /\\ q'))")

let%test "montonicity of or" =
  tautology (pp "(p ==> p') /\\ (q ==> q') ==> ((p \\/ q) ==> (p' \\/ q'))")

(* Substitution tests *)

let%test "psubst tautology" =
  tautology (psubst (P "p" |=> pp "p /\\ q") (pp "p /\\ q <=> q /\\ p"))

(* Simplification tests *)

let%expect_test "simplify 1" =
  prp (psimplify (pp "(true ==> (x <=> false)) ==> ~(y \\/ false /\\ z)"));
  [%expect {| <<~x ==> ~y>> |}]

let%expect_test "simplify 2" =
  prp (psimplify (pp "((x ==> y) ==> true) \\/ ~false"));
  [%expect {| <<true>> |}]

(* Example of proving a formula is equivalent to its NNF form *)

let%test "fm <=> nnf fm" =
  let fm = pp "(p <=> q) <=> ~(r ==> s)" in
  let fm' = nnf fm in
  tautology (Iff (fm, fm'))

let%expect_test "dnf corresponds to truth table" =
  let fm = pp "(p \\/ q /\\ r) /\\ (~p \\/ ~r)" in
  prp (dnf fm);
  [%expect {| <<~p /\ q /\ r \/ p /\ ~q /\ ~r \/ p /\ q /\ ~r>> |}]
(* dnf fm = pp "(~p /\\ q /\\ r) \\/ (p /\\ ~q /\\ ~r) \\/ (p /\\ q /\\ ~r)" *)

let%expect_test "truth table of previous formula" =
  print_truthtable (pp "(p \\/ q /\\ r) /\\ (~p \\/ ~r)");
  [%expect
    {|
    p     q     r     | formula
    ---------------------------
    false false false | false
    false false true  | false
    false true  false | false
    false true  true  | true
    true  false false | true
    true  false true  | false
    true  true  false | true
    true  true  true  | false
    --------------------------- |}]

let%expect_test "dnf takes a long time" =
  let fm = pp "(p /\\ q /\\ r /\\ s /\\ t /\\ u) \\/ (u /\\ v)" in
  prp (dnf fm);
  [%expect
    {| <<~p /\ ~q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ ~p /\ ~q /\ ~r /\ ~s /\ t /\ u /\ v \/ ~p /\ ~q /\ ~r /\ s /\ ~t /\ u /\ v \/ ~p /\ ~q /\ ~r /\ s /\ t /\ u /\ v \/ ~p /\ ~q /\ r /\ ~s /\ ~t /\ u /\ v \/ ~p /\ ~q /\ r /\ ~s /\ t /\ u /\ v \/ ~p /\ ~q /\ r /\ s /\ ~t /\ u /\ v \/ ~p /\ ~q /\ r /\ s /\ t /\ u /\ v \/ ~p /\ q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ ~p /\ q /\ ~r /\ ~s /\ t /\ u /\ v \/ ~p /\ q /\ ~r /\ s /\ ~t /\ u /\ v \/ ~p /\ q /\ ~r /\ s /\ t /\ u /\ v \/ ~p /\ q /\ r /\ ~s /\ ~t /\ u /\ v \/ ~p /\ q /\ r /\ ~s /\ t /\ u /\ v \/ ~p /\ q /\ r /\ s /\ ~t /\ u /\ v \/ ~p /\ q /\ r /\ s /\ t /\ u /\ v \/ p /\ ~q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ p /\ ~q /\ ~r /\ ~s /\ t /\ u /\ v \/ p /\ ~q /\ ~r /\ s /\ ~t /\ u /\ v \/ p /\ ~q /\ ~r /\ s /\ t /\ u /\ v \/ p /\ ~q /\ r /\ ~s /\ ~t /\ u /\ v \/ p /\ ~q /\ r /\ ~s /\ t /\ u /\ v \/ p /\ ~q /\ r /\ s /\ ~t /\ u /\ v \/ p /\ ~q /\ r /\ s /\ t /\ u /\ v \/ p /\ q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ p /\ q /\ ~r /\ ~s /\ t /\ u /\ v \/ p /\ q /\ ~r /\ s /\ ~t /\ u /\ v \/ p /\ q /\ ~r /\ s /\ t /\ u /\ v \/ p /\ q /\ r /\ ~s /\ ~t /\ u /\ v \/ p /\ q /\ r /\ ~s /\ t /\ u /\ v \/ p /\ q /\ r /\ s /\ ~t /\ u /\ v \/ p /\ q /\ r /\ s /\ t /\ u /\ ~v \/ p /\ q /\ r /\ s /\ t /\ u /\ v>> |}]
(* dnf is 1255 bytes *)

(* BIG print_truthtable dnf <<p /\ q /\ r /\ s /\ t /\ u \/ u /\ v>>;; *)
