(* ------------------------------------------------------------------------- *)
(* Tests of an encoding of a Ramsey-like Theorem                             *)
(* ------------------------------------------------------------------------- *)

open Reckoning.Common
open Reckoning.Formulas
open Reckoning.Prop
open Reckoning.Dpll

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
    Printf.printf "s=%d, t=%d, n=%d: %s\n" s t n
      (string_of_bool (tautology (ramsey s t n)))
  in
  print_endline "\nRamsey instance: prove R(3, 3) = 6\n";
  (* uncomment for timing *)
  (* List.iter (fun t -> time pres t) ps *)
  List.iter (fun t -> pres t) ps

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

(* Prove R(3,4) = ??? using the more efficient DP tautology prover *)
(* This can only be run up to n = 7 with DP. It allocates > 25 GB after 15
   minutes while trying to prove n=7

   s=3, t=4, n=8
   time to compute formula: CPU time (user): 0.000122
   time to defcnf_opt: CPU time (user): 0.003065
   number of varibles: 28
   number of clauses: 1762
   #clauses: 126
   #clauses: 165
   #clauses: 213
   #clauses: 270
   #clauses: 336
   #clauses: 1080
   #clauses: 6083
   #clauses: 49089
   ...
*)

let () =
  let ps = List.map (fun n -> (3, 4, n)) (1 -- 7) in
  let pres (s, t, n) =
    Printf.printf "\n\ns=%d, t=%d, n=%d\n" s t n;

    Printf.printf "time to compute formula: ";
    let ram = time (ramsey s t) n in

    Printf.printf "time to defcnf_opt: ";
    let cnf = time defcnf_sets ram in

    Printf.printf "number of varibles: %d\n" (List.length (atoms ram));
    Printf.printf "number of clauses: %d\n" (List.length cnf);
    Printf.printf "s=%d, t=%d, n=%d: %s\n" s t n (string_of_bool (dptaut ram))
  in
  print_endline
    "\nRamsey instance: prove R(3, 4) = ???\n===========================\n";
  List.iter (fun t -> time pres t) ps
