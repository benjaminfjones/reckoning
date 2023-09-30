(*
   Verification of adder circuit equivalence
*)

open Reckoning.Common
open Reckoning.Formulas
open Reckoning.Prop

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

(* ------------------------------------------------------------------------- *)
(* Ripple Carry Adder                                                        *)
(* ------------------------------------------------------------------------- *)

(* Relation encoding a ripplecarry adder over `n` bits.

   The inputs `x`, `y`, etc are functions from bit index -> atomic proposition
*)
let ripplecarry n x y cin sumout =
  let conjoin f idxs = list_conj (List.map f idxs) in
  let mkconj i = fulladd (x i) (y i) (cin i) (sumout i) (cin (i + 1)) in
  conjoin mkconj (0 -- (n - 1))

let mk_bit prefix i = Atom (P (prefix ^ "_" ^ string_of_int i))

let _mk_bit2 prefix i j =
  Atom (P (prefix ^ "_" ^ string_of_int i ^ "_" ^ string_of_int j))

(* ------------------------------------------------------------------------- *)
(* Tests                                                                     *)
(* ------------------------------------------------------------------------- *)

let[@warning "-partial-match"] [ x; y; cin; sumout ] =
  List.map mk_bit [ "X"; "Y"; "CIN"; "S" ]

let ripple3 =
  psimplify (ripplecarry 3 x y (fun i -> if i = 0 then False else cin i) sumout)

let () =
  print_endline "\n\nripple 3:";
  prp ripple3

let () =
  print_endline "\n\nripple 3 DNF foo:";
  prp (dnf (nnf ripple3))

let () =
  print_endline "\n\nripple 3 CNF:";
  prp (cnf (nnf ripple3))
