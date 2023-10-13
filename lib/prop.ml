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
  | Iff (False, False) -> True (* not in the original text *)
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

(* Simple negation-pushing; does not eliminate Iff. *)
let nenf formula =
  let rec nenf_aux fm =
    match fm with
    | Not (Not p) -> nenf_aux p
    | Not (And (p, q)) -> Or (nenf_aux (Not p), nenf_aux (Not q))
    | Not (Or (p, q)) -> And (nenf_aux (Not p), nenf_aux (Not q))
    | Not (Imp (p, q)) -> And (nenf_aux p, nenf_aux (Not q))
    | Not (Iff (p, q)) -> Iff (nenf_aux p, nenf_aux (Not q))
    | And (p, q) -> And (nenf_aux p, nenf_aux q)
    | Or (p, q) -> Or (nenf_aux p, nenf_aux q)
    | Imp (p, q) -> Or (nenf_aux (Not p), nenf_aux q)
    | Iff (p, q) -> Iff (nenf_aux p, nenf_aux q)
    | _ -> fm
  in
  nenf_aux (psimplify formula)

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
let truthdnf fm =
  let pvs = atoms fm in
  let satvals = allsatvaluations (eval fm) (fun _ -> false) pvs in
  let atoms = List.map (fun p -> Atom p) pvs in
  list_disj (List.map (mk_lits atoms) satvals)

(* DNF by transformation *)

(* `distrib` assumes the intermediate formulas (the p, q, r in the match) are
 * already in DNF. Calling distrib once, or even repeatedly calling it does not
 * result in DNF form in general.
 *)
let rec distrib fm =
  (* print_string "dist: "; *)
  (* prp fm; *)
  (* print_newline (); *)
  match fm with
  | And (p, Or (q, r)) -> Or (distrib (And (p, q)), distrib (And (p, r)))
  | And (Or (p, q), r) -> Or (distrib (And (p, r)), distrib (And (q, r)))
  | _ -> fm

(* In this example, distrib produces DNF *)
(* let%test "debug" = *)
(*   let res = distrib (pp "(p \\/ q \\/ r) /\\ (~p \\/ ~r)") in *)
(*   prp res; *)
(*   print_newline (); *)
(*   true *)

(* In this example, distrib **does not** produce DNF *)
(* let%test "debug" = *)
(*   let res = distrib (pp "(p /\\ (q \\/ (r /\\ (s \\/ (t /\\ u)))))") in *)
(*   prp res; *)
(*   print_newline (); *)
(*   true *)

(* Convert to (ugly, mis-associated) DNF by transformation *)
let rec rawdnf fm =
  (* print_string "raw: "; *)
  (* prp fm; *)
  (* print_newline (); *)
  match fm with
  (* Note the call to distrib occurs with intermediate formulas in DNF *)
  | And (p, q) -> distrib (And (rawdnf p, rawdnf q))
  | Or (p, q) -> Or (rawdnf p, rawdnf q)
  | _ -> fm

(* let%test "debug" = *)
(*   let res = rawdnf (pp "(p \\/ q \\/ r) /\\ (~p \\/ ~r)") in *)
(*   prp res; *)
(*   print_newline (); *)
(*   true *)

(* let%test "debug" = *)
(*   let res = rawdnf (pp "(p /\\ (q \\/ (r /\\ (s \\/ (t /\\ u)))))") in *)
(*   prp res; *)
(*   print_newline (); *)
(*   true *)

(* This version of distrib fully recurses, making no assumptions about
 * intermediate sub-formulas.
 *)
let rec full_distrib fm =
  (* print_string "full_dist: "; *)
  (* prp fm; *)
  (* print_newline (); *)
  match fm with
  | And (p, Or (q, r)) ->
      Or
        ( full_distrib (And (full_distrib p, full_distrib q)),
          full_distrib (And (full_distrib p, full_distrib r)) )
  | And (Or (p, q), r) ->
      Or
        ( full_distrib (And (full_distrib p, full_distrib r)),
          full_distrib (And (full_distrib q, full_distrib r)) )
  | _ -> fm

(* on (p \\/ q \\/ r) /\\ (~p \\/ ~r),           full_distrib called 32 times *)
(* on (p /\\ (q \\/ (r /\\ (s \\/ (t /\\ u))))), full_distrib called 20 times *)
(* let%test "debug" = *)
(*   let res = full_distrib (pp "(p /\\ (q \\/ (r /\\ (s \\/ (t /\\ u)))))") in *)
(*   prp res; *)
(*   print_newline (); *)
(*   true *)

(* Distribute for the set of sets representation *)
let pure_distrib s1 s2 = setify (allpairs union s1 s2)

(* Convert to DNF, by transformation, in set of sets form *)
let rec purednf fm =
  match fm with
  | And (p, q) -> pure_distrib (purednf p) (purednf q)
  | Or (p, q) -> union (purednf p) (purednf q)
  | _ -> [ [ fm ] ]

(* Determine if the disjuction of literals is trivial, i.e. contains both p and ~p for
   some atomic prop p.
*)
let trivial lits =
  let pos, neg = List.partition positive lits in
  intersect pos (List.map negate neg) <> []

let simpdnf fm =
  match fm with
  | False -> []
  | True -> [ [] ]
  | _ ->
      (* Filter out trivial disjuncts *)
      let djs = List.filter (non trivial) (purednf (nnf fm)) in
      (* Filter out subsumed disjuncts *)
      List.filter (fun d -> not (exists (fun d' -> psubset d' d) djs)) djs

(* The ultimate evolution of DNF *)
let dnf fm = list_disj (List.map list_conj (simpdnf fm))

let print_pfll ds =
  let string_of_lit = function
    | Atom p -> pname p
    | Not (Atom p) -> "~" ^ pname p
    | _ -> failwith "not an atom"
  in
  let pfl ps = "[" ^ String.concat "; " (List.map string_of_lit ps) ^ "]" in
  print_string ("[" ^ String.concat "; " (List.map pfl ds) ^ "]")

(* ------------------------------------------------------------------------- *)
(* Conjuctive Normal Form (CNF)                                              *)
(* ------------------------------------------------------------------------- *)

(* Compute a CNF representation, in set of sets form.contents

   Note: the structure is almost exactly the same as `purednf` modulo swapping
   And/Or by duality.

   For example:

   purecnf (p /\\ q) => union [[p]] [[q]]
                     => [[p]; [q]]

   purecnf (p \\/ q) => pure_distrib [[p]] [[q]]
                     => setify (allpairs union [[p]] [[q]])
                     => setify ([[p; q]])
                     => [[p; q]]
*)
let rec purecnf fm =
  match fm with
  | And (p, q) -> union (purecnf p) (purecnf q)
  | Or (p, q) -> pure_distrib (purecnf p) (purecnf q)
  | _ -> [ [ fm ] ]

let simpcnf fm =
  match fm with
  | False -> [ [] ]
  | True -> []
  | _ ->
      (* Filter out trivial conjuncts (i.e. ones that are tautologies) *)
      let cjs = List.filter (non trivial) (purecnf (nnf fm)) in
      (* Filter out subsumed conjuncts *)
      List.filter (fun c -> not (exists (fun c' -> psubset c' c) cjs)) cjs

(* The ultimate evolution of CNF *)
let cnf fm = list_conj (List.map list_disj (simpcnf fm))

(* ------------------------------------------------------------------------- *)
(* Definitional Conjuctive Normal Form (Tseitin Transformation)              *)
(* ------------------------------------------------------------------------- *)

let freshprop n = (Atom (P ("p_" ^ string_of_int n)), n + 1)

(* defcnf_inner and defstep are mutually recursive functions used in the
   state transformer loop that produces definitional CNF. The state being
   transformed is the triple (formula, definitions so far, fresh prop index)*)
let rec defcnf_inner ((fm, _defs, _n) as trip) =
  (* assumption: `fm` is in NENF form *)
  match fm with
  | And (p, q) -> defstep mk_and (p, q) trip
  | Or (p, q) -> defstep mk_or (p, q) trip
  | Iff (p, q) -> defstep mk_iff (p, q) trip
  | _ -> trip

(* perform a definition Tseitin step *)
and defstep op (p, q) (_fm, defs, n) =
  let fm1, defs1, n1 = defcnf_inner (p, defs, n) in
  let fm2, defs2, n2 = defcnf_inner (q, defs1, n1) in
  let fm' = op fm1 fm2 in
  try (fst (apply defs2 fm'), defs2, n2)
  with Failure _ ->
    let v, n3 = freshprop n2 in
    (v, (v |-> (fm', Iff (v, fm'))) defs2, n3)

(* Helper function for finding the next unsed prop variable index.

   It returns the max of `n` and the smallest non-negative integer `k` such
   that `str` is `prefix ^ suffix`, `suffix` represents an int, and
   `int_of_string suffix <= k`. `n` is the default
*)
let max_varindex prefix =
  let m = String.length prefix in
  fun str n ->
    let l = String.length str in
    if l <= m || String.sub str 0 m <> prefix then n
    else
      let s' = String.sub str m (l - m) in
      if List.for_all numeric (explode s') then Int.max n (int_of_string s')
      else n

let mk_defcnf fn fm =
  let fm' = nenf fm in
  let n = 1 + overatoms (fun p n -> max_varindex "p_" (pname p) n) fm' 0 in
  let fm'', defs, _ = fn (fm', undefined, n) in
  let deflist = List.map (snd ** snd) (graph defs) in
  unions (simpcnf fm'' :: List.map simpcnf deflist)

let defcnf_sets fm = mk_defcnf defcnf_inner fm
let defcnf fm = list_conj (List.map list_disj (defcnf_sets fm))

(* Optimized version of defcnf

   1. preserve outter conjunctive structure: only defcnf the conjuncts
   2. in a conjunct, leave atomic parts of disjunts alone (do not make new definitions for them)
*)

(* The state transformer part of `defcnf_inner` above, but without intro'ing new
   definitions.
*)
let subcnf sfn op (p, q) (_fm, defs, n) =
  let fm1, defs1, n1 = sfn (p, defs, n) in
  let fm2, defs2, n2 = sfn (q, defs1, n1) in
  (op fm1 fm2, defs2, n2)

let rec orcnf ((fm, _defs, _n) as trip) =
  match fm with
  | Or (p, q) -> subcnf orcnf mk_or (p, q) trip
  | _ -> defcnf_inner trip

let rec andcnf ((fm, _defs, _n) as trip) =
  match fm with
  | And (p, q) -> subcnf andcnf mk_and (p, q) trip
  | _ -> orcnf trip

(* Optimized defcnf from (prop formula) -> set of sets *)
let defcnf_opt_sets fm = mk_defcnf andcnf fm

(* Optimized defcnf from (prop formula) -> (prop formula) *)
let defcnf_opt fm = list_conj (List.map list_disj (defcnf_opt_sets fm))

(* ========================================================================= *)
(* ========================================================================= *)
(* Tests                                                                     *)
(* ========================================================================= *)
(* ========================================================================= *)

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
  prp (truthdnf fm);
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

(* DNF tests *)

let%expect_test "truthdnf takes a long time" =
  let fm = pp "(p /\\ q /\\ r /\\ s /\\ t /\\ u) \\/ (u /\\ v)" in
  prp (truthdnf fm);
  [%expect
    {| <<~p /\ ~q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ ~p /\ ~q /\ ~r /\ ~s /\ t /\ u /\ v \/ ~p /\ ~q /\ ~r /\ s /\ ~t /\ u /\ v \/ ~p /\ ~q /\ ~r /\ s /\ t /\ u /\ v \/ ~p /\ ~q /\ r /\ ~s /\ ~t /\ u /\ v \/ ~p /\ ~q /\ r /\ ~s /\ t /\ u /\ v \/ ~p /\ ~q /\ r /\ s /\ ~t /\ u /\ v \/ ~p /\ ~q /\ r /\ s /\ t /\ u /\ v \/ ~p /\ q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ ~p /\ q /\ ~r /\ ~s /\ t /\ u /\ v \/ ~p /\ q /\ ~r /\ s /\ ~t /\ u /\ v \/ ~p /\ q /\ ~r /\ s /\ t /\ u /\ v \/ ~p /\ q /\ r /\ ~s /\ ~t /\ u /\ v \/ ~p /\ q /\ r /\ ~s /\ t /\ u /\ v \/ ~p /\ q /\ r /\ s /\ ~t /\ u /\ v \/ ~p /\ q /\ r /\ s /\ t /\ u /\ v \/ p /\ ~q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ p /\ ~q /\ ~r /\ ~s /\ t /\ u /\ v \/ p /\ ~q /\ ~r /\ s /\ ~t /\ u /\ v \/ p /\ ~q /\ ~r /\ s /\ t /\ u /\ v \/ p /\ ~q /\ r /\ ~s /\ ~t /\ u /\ v \/ p /\ ~q /\ r /\ ~s /\ t /\ u /\ v \/ p /\ ~q /\ r /\ s /\ ~t /\ u /\ v \/ p /\ ~q /\ r /\ s /\ t /\ u /\ v \/ p /\ q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ p /\ q /\ ~r /\ ~s /\ t /\ u /\ v \/ p /\ q /\ ~r /\ s /\ ~t /\ u /\ v \/ p /\ q /\ ~r /\ s /\ t /\ u /\ v \/ p /\ q /\ r /\ ~s /\ ~t /\ u /\ v \/ p /\ q /\ r /\ ~s /\ t /\ u /\ v \/ p /\ q /\ r /\ s /\ ~t /\ u /\ v \/ p /\ q /\ r /\ s /\ t /\ u /\ ~v \/ p /\ q /\ r /\ s /\ t /\ u /\ v>> |}]
(* dnf is 1255 bytes *)

(* BIG print_truthtable dnf <<p /\ q /\ r /\ s /\ t /\ u \/ u /\ v>>;; *)

let distrib_ex1 = pp "(p \\/ q /\\ r) /\\ (~p \\/ ~r)"

(* In this example, distrib produces DNF *)
let distrib_ex2 = pp "(p \\/ q \\/ r) /\\ (~p \\/ ~r)"

let%expect_test "distrib does produce DNF" =
  prp (distrib distrib_ex2);
  [%expect
    {| <<(p /\ ~p \/ q /\ ~p \/ r /\ ~p) \/ p /\ ~r \/ q /\ ~r \/ r /\ ~r>> |}]

(* In this example, distrib produces DNF *)
let%expect_test "rawdnf distrib_ex" =
  prp (distrib distrib_ex2);
  [%expect
    {| <<(p /\ ~p \/ q /\ ~p \/ r /\ ~p) \/ p /\ ~r \/ q /\ ~r \/ r /\ ~r>> |}]

let nested_and_or = pp "(p /\\ (q \\/ (r /\\ (s \\/ (t /\\ u)))))"

let%expect_test "distrib does not produce DNF" =
  prp (distrib nested_and_or);
  [%expect {| <<p /\ q \/ p /\ r /\ (s \/ t /\ u)>> |}]

let%expect_test "rawdnf does produce DNF" =
  prp (rawdnf nested_and_or);
  [%expect {| <<p /\ q \/ p /\ r /\ s \/ p /\ r /\ t /\ u>> |}]

let%expect_test "purednf distrib_ex1" =
  print_pfll (purednf distrib_ex1);
  [%expect {| [[p; ~p]; [p; ~r]; [q; r; ~p]; [q; r; ~r]] |}]

let%expect_test "purednf distrib_ex2" =
  print_pfll (purednf distrib_ex2);
  [%expect {| [[p; ~p]; [p; ~r]; [q; ~p]; [q; ~r]; [r; ~p]; [r; ~r]] |}]

let%expect_test "trivial @@ purednf" =
  print_pfll (List.filter (non trivial) (purednf distrib_ex1));
  [%expect {| [[p; ~r]; [q; r; ~p]] |}]

let%expect_test "simpdnf distrib_ex1" =
  print_pfll (simpdnf distrib_ex1);
  [%expect {| [[p; ~r]; [q; r; ~p]] |}]

let%expect_test "simpdnf takes less time?" =
  let fm = pp "(p /\\ q /\\ r /\\ s /\\ t /\\ u) \\/ (u /\\ v)" in
  (* print_pfll (time simpdnf fm); *)
  (* time = 4e-06 *)
  print_pfll (simpdnf fm);
  [%expect {| [[p; q; r; s; t; u]; [u; v]] |}]

let%expect_test "dnf distrib_ex1" =
  prp (dnf distrib_ex1);
  [%expect {| <<p /\ ~r \/ q /\ r /\ ~p>> |}]

let%expect_test "dnf distrib_ex2" =
  prp (dnf distrib_ex2);
  [%expect {| <<p /\ ~r \/ q /\ ~p \/ q /\ ~r \/ r /\ ~p>> |}]

let%test "tautology Iff(fm, dnf fm)" =
  tautology (Iff (distrib_ex1, dnf distrib_ex1))

(* CNF tests *)

let%expect_test "purecnf of and" =
  print_pfll (purecnf (pp "p /\\ q"));
  [%expect {| [[p]; [q]] |}]

let%expect_test "purecnf of or" =
  print_pfll (purecnf (pp "p \\/ q"));
  [%expect {| [[p; q]] |}]

let%expect_test "cnf distrib_ex1" =
  prp (cnf distrib_ex1);
  [%expect {| <<(p \/ q) /\ (p \/ r) /\ (~p \/ ~r)>> |}]

let%expect_test "cnf distrib_ex2" =
  prp (cnf distrib_ex2);
  [%expect {| <<(p \/ q \/ r) /\ (~p \/ ~r)>> |}]

let%test "tautology Iff(fm, cnf fm)" =
  tautology (Iff (distrib_ex1, cnf distrib_ex1))

(* Tseitin transformation of Iff results in 11 logical connectives *)
let%expect_test "worst case Tseitin transformation" =
  prp (cnf (pp "(p <=> (q <=> r))"));
  [%expect
    {| <<(p \/ q \/ r) /\ (p \/ ~q \/ ~r) /\ (q \/ ~p \/ ~r) /\ (r \/ ~p \/ ~q)>> |}]

(* NENF of the worst case above *)
let%expect_test "nenf worst case" =
  prp (nenf (pp "~(p <=> (q <=> r))"));
  [%expect {| <<p <=> q <=> ~r>> |}]

(* NENF alone gives CNF in some cases *)
let%expect_test "nenf is cnf example" =
  prp (nenf (pp "~(p \\/ q /\\ r)"));
  [%expect {| <<~p /\ (~q \/ ~r)>> |}]

let defcnf_example1 = pp "(p \\/ (q /\\ ~r)) /\\ s"

let%expect_test "defcnf example 1" =
  prp (defcnf defcnf_example1);
  [%expect
    {| <<(p \/ p_1 \/ ~p_2) /\ (p_1 \/ r \/ ~q) /\ (p_2 \/ ~p) /\ (p_2 \/ ~p_1) /\ (p_2 \/ ~p_3) /\ p_3 /\ (p_3 \/ ~p_2 \/ ~s) /\ (q \/ ~p_1) /\ (s \/ ~p_3) /\ (~p_1 \/ ~r)>> |}]

let%expect_test "defcnf_opt example 1" =
  prp (defcnf_opt defcnf_example1);
  [%expect
    {| <<(p \/ p_1) /\ (p_1 \/ r \/ ~q) /\ (q \/ ~p_1) /\ s /\ (~p_1 \/ ~r)>> |}]

let%test "defcnf ==> defcnf_opt in example 1" =
  let dcnf = defcnf defcnf_example1 in
  let dcnf_opt = defcnf_opt defcnf_example1 in
  tautology (Imp (dcnf, dcnf_opt))

let%test "(defcnf_opt fm) does not imply (defcnf fm" =
  let dcnf = defcnf defcnf_example1 in
  let dcnf_opt = defcnf_opt defcnf_example1 in
  not (tautology (Imp (dcnf_opt, dcnf)))
