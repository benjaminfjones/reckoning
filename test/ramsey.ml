(* ------------------------------------------------------------------------- *)
(* Tests of an encoding of a Ramsey-like Theorem                             *)
(* ------------------------------------------------------------------------- *)

open Reckoning.Common
open Reckoning.Formulas
open Reckoning.Prop

(* Encodes a prop formula expressing the property that
   there exists a graph of size `n` having either a fully
   connected subgraph of size `s`, or having a fully disconnected
   subgraph of size `t`.

   If `ramsey s t n` is satisfiable, then R(s,t), the size of the minimal such
   graph is  <= n.
*)
let ramsey s t n =
  let verts = 1 -- n in
  let conn_grps = allsubsets s verts in
  let dis_grps = allsubsets t verts in
  let pairs_of_grp = distinctpairs in
  let atom_of_pair (i, j) =
    Atom (P ("p" ^ string_of_int i ^ string_of_int j))
  in
  let comp_connected grp =
    List.fold_right mk_and (List.map atom_of_pair (pairs_of_grp grp)) True
  in
  let comp_disconnected grp =
    List.fold_right mk_and
      (List.map (fun p -> Not (atom_of_pair p)) (pairs_of_grp grp))
      True
  in
  Or
    ( List.fold_right mk_or (List.map comp_connected conn_grps) False,
      List.fold_right mk_or (List.map comp_disconnected dis_grps) False )

let () =
  if satisfiable (ramsey 3 3 6) then print_string "SAT"
  else print_string "UNSAT"
