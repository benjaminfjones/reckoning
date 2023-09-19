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

let parse_prop_formula =
  make_parser (parse_formula ((fun _ _ -> failwith ""), parse_propvar) [])

(* ------------------------------------------------------------------------- *)
(* Set this up as default for quotations.                                    *)
(* ------------------------------------------------------------------------- *)

let default_parser = parse_prop_formula

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

let print_propvar _prec p = print_string (pname p)
let print_prop_formula = print_qformula print_propvar

(* TODO: figure out if a PPX can be used here instead of a camlp* preprocessor *)
(* #install_printer print_prop_formula *)
