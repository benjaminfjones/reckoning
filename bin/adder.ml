(*
   Verification of adder circuit equivalence
*)

open Reckoning.Common
open Reckoning.Formulas
open Reckoning.Prop
open Reckoning.Dpll

(* ------------------------------------------------------------------------- *)
(* Half & Full Adders                                                        *)
(* ------------------------------------------------------------------------- *)

(* Half sum & carry table

   x  | y  | s  | c  |
   -------------------
   0  | 0  | 0  | 0  |
   0  | 1  | 1  | 0  |
   1  | 0  | 1  | 0  |
   1  | 1  | 0  | 1  |
*)
let halfsum x y = Not (Iff (x, y))
let halfcarry x y = And (x, y)

(* Relation encoding the half adder in terms of inputs / outputs.

   s <=> halfsum x y /\\ c <=> halfcarry x y
*)
let _halfadd x y sumout cout =
  And (Iff (sumout, halfsum x y), Iff (cout, halfcarry x y))

(* Full sum and carry take two inputs bits and an input carry *)
let fullsum x y cin = halfsum (halfsum x y) cin

(* There is an output carry <=> 2 of 3 inputs are true *)
let fullcarry x y cin = Or (And (x, y), And (Or (x, y), cin))

(* Relation encoding the full carry *)
let fulladd x y cin sumout cout =
  And (Iff (sumout, fullsum x y cin), Iff (cout, fullcarry x y cin))

let conjoin f idxs = list_conj (List.map f idxs)

(* ------------------------------------------------------------------------- *)
(* Ripple Carry Adder                                                        *)
(* ------------------------------------------------------------------------- *)

(* Relation encoding a ripplecarry adder over `n` bits.

   The inputs `x`, `y`, etc are functions from bit index -> atomic proposition
*)
let ripplecarry n x y cin sumout =
  let mkconj i = fulladd (x i) (y i) (cin i) (sumout i) (cin (i + 1)) in
  conjoin mkconj (0 -- (n - 1))

(* Ripple carry with input carry = 0 *)
let ripplecarry0 n x y cin sumout =
  psimplify (ripplecarry n x y (fun i -> if i = 0 then False else cin i) sumout)

(* Ripple carry with input carry = 1 *)
let ripplecarry1 n x y cin sumout =
  psimplify (ripplecarry n x y (fun i -> if i = 0 then True else cin i) sumout)

let mk_bit prefix i = Atom (P (prefix ^ "_" ^ string_of_int i))

let _mk_bit2 prefix i j =
  Atom (P (prefix ^ "_" ^ string_of_int i ^ "_" ^ string_of_int j))

(* ------------------------------------------------------------------------- *)
(* Carry-select adder                                                        *)
(*                                                                           *)
(* Carry-select is an optimization that reduces the number of cycles needed  *)
(* to compute an n-bit add circuit.                                          *)
(*                                                                           *)
(* Carry-select performs a k-bit ripple carry for each possible carry input, *)
(* muxes the result based on the actual carry input, and repeats for each k  *)
(* (or less) bit block of the n total bits.                                  *)
(* ------------------------------------------------------------------------- *)

(* Multiplex the input formulas based on a selector proposition *)
let mux sel in0 in1 = Or (And (Not sel, in0), And (sel, in1))

(* Apply a proposition maker function with bits offset by n *)
let offset n x i = x (n + i)

(* I weep at the signature of this function *)
let rec carryselect n k x y c0 c1 s0 s1 c s =
  let k' = min n k in
  let fm =
    And
      ( And (ripplecarry0 k' x y c0 s0, ripplecarry1 k' x y c1 s1),
        And
          ( Iff (c k', mux (c 0) (c0 k') (c1 k')),
            conjoin (fun i -> Iff (s i, mux (c 0) (s0 i) (s1 i))) (0 -- (k' - 1))
          ) )
  in
  if k' < k then fm
  else
    And
      ( fm,
        carryselect (n - k) k (offset k x) (offset k y) (offset k c0)
          (offset k c1) (offset k s0) (offset k s1) (offset k c) (offset k s) )

(* ------------------------------------------------------------------------- *)
(* Tests                                                                     *)
(* ------------------------------------------------------------------------- *)

let[@warning "-partial-match"] [ x; y; cin; sumout ] =
  List.map mk_bit [ "X"; "Y"; "CIN"; "S" ]

let ripple3 =
  psimplify
    (ripplecarry0 3 x y (fun i -> if i = 0 then False else cin i) sumout)

let stats_ripple n =
  let p =
    time psimplify
      (ripplecarry0 n x y (fun i -> if i = 0 then False else cin i) sumout)
  in
  print_endline ("\n\nripple " ^ string_of_int n);
  prp p;
  print_endline "";
  print_endline ("number of variables: " ^ string_of_int (List.length (atoms p)))

let () = stats_ripple 1
let () = stats_ripple 2
let () = stats_ripple 3

let () =
  print_endline "\n\nripple 3 DNF foo:";
  prp (dnf ripple3)

let () =
  print_endline "\n\nripple 3 CNF:";
  let p = time cnf ripple3 in
  let ps = time simpcnf ripple3 in
  prp p;
  print_endline "";
  print_endline ("number of variables: " ^ string_of_int (List.length (atoms p)));
  print_endline ("number of clauses:   " ^ string_of_int (List.length ps))

let () =
  print_endline "\n\nripple 3 DEF CNF:";
  let p = time defcnf ripple3 in
  let ps = time defcnf_sets ripple3 in
  prp p;
  print_endline "";
  print_endline ("number of variables: " ^ string_of_int (List.length (atoms p)));
  print_endline ("number of clauses:   " ^ string_of_int (List.length ps))

let () =
  print_endline "\n\nripple 3 DEF CNF OPT:";
  let p = time defcnf_opt ripple3 in
  let ps = time defcnf_opt_sets ripple3 in
  prp p;
  print_endline "";
  print_endline ("number of variables: " ^ string_of_int (List.length (atoms p)));
  print_endline ("number of clauses:   " ^ string_of_int (List.length ps))

let stats_carryselect n k =
  let[@warning "-partial-match"] [ x; y; c; s; c0; c1; s0; s1 ] =
    List.map mk_bit [ "x"; "y"; "c"; "s"; "c0"; "c1"; "s0"; "s1" ]
  in
  let p = time psimplify (carryselect n k x y c0 c1 s0 s1 c s) in
  print_endline ("\n\ncarryselect " ^ string_of_int n ^ " " ^ string_of_int k);
  prp p;
  print_endline "";
  print_endline ("number of variables: " ^ string_of_int (List.length (atoms p)))

let () = stats_carryselect 1 1
let () = stats_carryselect 2 1
let () = stats_carryselect 3 1
let () = stats_carryselect 3 2

(* ------------------------------------------------------------------------- *)
(* Equivalence problems for carry-select vs ripple carry adders.             *)
(* ------------------------------------------------------------------------- *)

let mk_adder_test n k =
  let[@warning "-partial-match"] [ x; y; c; s; c0; s0; c1; s1; c2; s2 ] =
    List.map mk_bit [ "x"; "y"; "c"; "s"; "c0"; "s0"; "c1"; "s1"; "c2"; "s2" ]
  in
  Imp
    ( And
        ( And (carryselect n k x y c0 c1 s0 s1 c s, Not (c 0)),
          ripplecarry0 n x y c2 s2 ),
      And (Iff (c n, c2 n), conjoin (fun i -> Iff (s i, s2 i)) (0 -- (n - 1)))
    )

(* Truth table is 2**21 ~= 2 M rows *)
let () =
  let fm = mk_adder_test 2 1 in
  print_endline "\n\nequivalence of ripplecarry2 <=> carryselect21";
  print_endline
    ("number of variables: " ^ string_of_int (List.length (atoms fm)));
  print_endline (string_of_bool (time tautology fm))

(* Truth table is 2**21 ~= 2 M rows *)
let () =
  let fm = mk_adder_test 2 2 in
  print_endline "\n\nequivalence of ripplecarry2 <=> carryselect22";
  print_endline
    ("number of variables: " ^ string_of_int (List.length (atoms fm)));
  print_endline (string_of_bool (time tautology fm))

(* Truth table is 2**30 ~= 1.07 B rows !? *)
let () =
  let fm = mk_adder_test 3 2 in
  print_endline "\n\nequivalence of ripplecarry3 <=> carryselect32";
  print_endline
    ("number of variables: " ^ string_of_int (List.length (atoms fm)));
  print_endline "(too large for naive tautology prover)"
(* ;print_endline (string_of_bool (tautology fm)) *)

(* ------------------------------------------------------------------------- *)
(* Adder Equivalence Proofs Using the DP algorithm                           *)
(* ------------------------------------------------------------------------- *)

(* Time: 0.027 s, 63x speedup over tautology! *)
let () =
  let fm = mk_adder_test 2 1 in
  print_endline "\n\ndptaut: equivalence of ripplecarry2 <=> carryselect21";
  print_endline
    ("number of variables: " ^ string_of_int (List.length (atoms fm)));
  print_endline (string_of_bool (time dptaut fm))

(* 31 variables *)
(* 296 clauses *)
(* Time: 0.082 s, practically impossible with tautology *)
let () =
  let fm = mk_adder_test 3 1 in
  let ps = defcnf_opt_sets fm in
  print_endline "\n\ndptaut: equivalence of ripplecarry3 <=> carryselect31";
  print_endline
    ("number of variables: " ^ string_of_int (List.length (atoms fm)));
  print_endline ("number of clauses:   " ^ string_of_int (List.length ps));
  print_endline (string_of_bool (time dptaut fm))

(* 30 variables *)
(* 290 clauses *)
(* Time: 0.076 s, practically impossible with tautology *)
let () =
  let fm = mk_adder_test 3 2 in
  let ps = defcnf_opt_sets fm in
  print_endline "\n\ndptaut: equivalence of ripplecarry3 <=> carryselect32";
  print_endline
    ("number of variables: " ^ string_of_int (List.length (atoms fm)));
  print_endline ("number of clauses:   " ^ string_of_int (List.length ps));
  print_endline (string_of_bool (time dptaut fm))
