(* ========================================================================= *)
(* The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.           *)
(*                                                                           *)
(* Adapted from original work, Copyright (c) 2003-2007, John Harrison.       *)
(* See "LICENSE_Orig.txt" for details.                                       *)
(* ========================================================================= *)

open Common
open Formulas
open Prop

type prop_cnf = prop formula list list

(* ------------------------------------------------------------------------- *)
(* The Davis-Putnam procedure.                                               *)
(* ------------------------------------------------------------------------- *)

let one_literal_rule (clauses : prop_cnf) : prop_cnf =
  let u = List.hd (List.find (fun cl -> List.length cl = 1) clauses) in
  let u' = negate u in
  let clauses1 = List.filter (fun cl -> not (List.mem u cl)) clauses in
  set_image (fun cl -> subtract cl [ u' ]) clauses1

let affirmative_negative_rule (clauses : prop_cnf) : prop_cnf =
  let lits = unions clauses in
  let neg', pos = List.partition negative lits in
  let neg = set_image negate neg' in
  (* find lits that only appear positively or only appear negatively *)
  let pos_only = subtract pos neg and neg_only = subtract neg pos in
  let pure = union pos_only (set_image negate neg_only) in
  if pure = [] then failwith "affirmative_negative_rule"
  else List.filter (fun cl -> intersect cl pure = []) clauses

let resolve_on (p : prop formula) (clauses : prop_cnf) : prop_cnf =
  let p' = negate p and pos, notpos = List.partition (List.mem p) clauses in
  let neg, other = List.partition (List.mem p') notpos in
  let pos' = set_image (List.filter (fun l -> l <> p)) pos
  and neg' = set_image (List.filter (fun l -> l <> p')) neg in
  let res0 = allpairs union pos' neg' in
  union other (List.filter (non trivial) res0)

(* Heuristic for determing how large the formula blow-up is when applying
   `resolve_on` to a given literal. *)
let resolution_blowup (cls : prop_cnf) (l : prop formula) : int =
  let m = List.length (List.filter (List.mem l) cls)
  and n = List.length (List.filter (List.mem (negate l)) cls) in
  (m * n) - m - n

(* Apply `resolve_on` for the best literal according to heuristics *)
let resolution_rule clauses =
  let pvs = List.filter positive (unions clauses) in
  let p = minimize (resolution_blowup clauses) pvs in
  resolve_on p clauses

(* ------------------------------------------------------------------------- *)
(* Overall procedure.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec dp clauses =
  if clauses = [] then true
  else if List.mem [] clauses then false
  else
    try dp (one_literal_rule clauses)
    with Failure _ | Not_found -> (
      try dp (affirmative_negative_rule clauses)
      with Failure _ -> dp (resolution_rule clauses))

(* ------------------------------------------------------------------------- *)
(* Davis-Putnam satisfiability tester and tautology checker.                 *)
(* ------------------------------------------------------------------------- *)

let dpsat fm = dp (defcnf_opt_sets fm)
let dptaut fm = not (dpsat (Not fm))
