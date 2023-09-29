(* ------------------------------------------------------------------------- *)
(* Tests of an encoding of a Ramsey-like Theorem                             *)
(* ------------------------------------------------------------------------- *)

open Reckoning.Common
open Reckoning.Formulas
open Reckoning.Prop

(* Encodes a prop formula expressing the property that
   in an arbitrary graph of size `n` there is either a fully
   connected subgraph of size `s`, or a fully disconnected
   subgraph of size `t`.

   If `ramsey s t n` is a tautology, then R(s,t), the size of the minimal such
   graph, is  <= n.
   
   Note: R(s, t) <= R(s, t-1) + R(s-1, t)
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

(* Prove that R(3, 3) = 6 *)
(*
   
Ramsey instance: R(3, 3) = 6
s=3, t=3, n=1: false                
CPU time (user): 4.2e-05
s=3, t=3, n=2: false
CPU time (user): 2e-06
s=3, t=3, n=3: false
CPU time (user): 8e-06
s=3, t=3, n=4: false
CPU time (user): 2.3e-05
s=3, t=3, n=5: false
CPU time (user): 0.000505
s=3, t=3, n=6: true
CPU time (user): 0.108766

*)
let () =
  let ps = List.map (fun n -> (3, 3, n)) (1 -- 6) in
  let pres (s, t, n) =
    Printf.printf "s=%d, t=%d, n=%d: %s\n" s t n (string_of_bool (tautology (ramsey s t n))) in
  print_endline "\nRamsey instance: R(3, 3) = 6\n";
  List.iter (fun t -> time pres t) ps

(*

utop # time tautology (ramsey 2 4 3);;
CPU time (user): 1.29999999956e-05
- : bool = false

==> R(3, 4) <= 6 + 4

utop # time tautology (ramsey 3 4 6);;
CPU time (user): 0.002881
- : bool = false

utop # time tautology (ramsey 3 4 7);;
CPU time (user): 0.435133
- : bool = false

utop # time tautology (ramsey 3 4 8);;
CPU time (user): 110.858693
- : bool = false   

utop # time tautology (ramsey 3 4 9);;
- killed after 13 hours

*)