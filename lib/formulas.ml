(* ========================================================================= *)
(* Polymorphic type of formulas with parser and printer.                     *)
(* ========================================================================= *)

open Common

(* First order logical formula paramterized by the type of propositions *)
type 'a formula =
  | False
  | True
  | Atom of 'a
  | Not of 'a formula
  | And of 'a formula * 'a formula
  | Or of 'a formula * 'a formula
  | Imp of 'a formula * 'a formula
  | Iff of 'a formula * 'a formula
  | Forall of string * 'a formula
  | Exists of string * 'a formula

(*
 * General parsing of iterated infixes
 *
 *   Conventions:
 *   - opsym : string -- operator symbol
 *   - opcon : 'a formula * 'a formula -> 'a formula -- binary operator constructor
 *   - opupdate : ('a formula -> 'a formula) -> 'a formula -> 'a formula -> 'b
 *       where 'b is typically either 'a formula or an aggregate like ('a formula) list
 *   - sof : 'a formula -> 'b -- used in the opupdater to go from formulas to aggregates
 *   - subparser : parser -- parser of the infix operator's arguments
 *)

(* Parse a general infix operator, parametrized on the syntax, the constructor and the type and construction
   of the final AST. *)
let rec parse_ginfix opsym opupdate sof subparser inp =
  let e1, inp1 = subparser inp in
  if inp1 <> [] && List.hd inp1 = opsym then
    parse_ginfix opsym opupdate (opupdate sof e1) subparser (List.tl inp1)
  else (sof e1, inp1)

let parse_right_infix opsym opcon =
  parse_ginfix opsym (fun f e1 e2 -> f (opcon (e1, e2))) id

(* Unsed for now

   let parse_left_infix opsym opcon =
     parse_ginfix opsym (fun f e1 e2 -> opcon (f e1, e2)) id

   let parse_list opsym =
     parse_ginfix opsym (fun f e1 e2 -> f e1 @ [ e2 ]) (fun x -> [ x ])
*)

(* ------------------------------------------------------------------------- *)
(* Other general parsing combinators.                                        *)
(* ------------------------------------------------------------------------- *)

let papply f (ast, rest) = (f ast, rest)

(* Token `tok` is next in the input stream `inp` *)
let nextin inp tok = inp <> [] && List.hd inp = tok

let parse_bracketed subparser bra_tok inp =
  let ast, rest = subparser inp in
  if nextin rest bra_tok then (ast, List.tl rest)
  else failwith "Closing bracket expected"

(* Parsing of formulas, parametrized by atom parser "pfn".
 *
 *  Conventions:
    - type parser : string list -> 'a formula * string list
 *  - ifn : 'context -> parser for "infix atoms", e.g. in Fol these are atomic predicates like "x < 2" in "x < 2 /\ y > 1"
 *  - afn : 'context -> parser for general atoms, e.g. in Prop these are just propositional variables
 *  - vs  : 'context is the context (unused for now)
 *)

let rec parse_atomic_formula (ifn, afn) vs inp =
  match inp with
  | [] -> failwith "formula expected"
  | "false" :: rest -> (False, rest)
  | "true" :: rest -> (True, rest)
  | "(" :: rest -> (
      try ifn vs inp
      with Failure _ -> parse_bracketed (parse_formula (ifn, afn) vs) ")" rest)
  | "~" :: rest ->
      papply (fun p -> Not p) (parse_atomic_formula (ifn, afn) vs rest)
  | "forall" :: x :: rest ->
      parse_quant (ifn, afn) (x :: vs) (fun (x, p) -> Forall (x, p)) x rest
  | "exists" :: x :: rest ->
      parse_quant (ifn, afn) (x :: vs) (fun (x, p) -> Exists (x, p)) x rest
  | _ -> afn vs inp

and parse_quant (ifn, afn) vs qcon x inp =
  match inp with
  | [] -> failwith "Body of quantified term expected"
  | y :: rest ->
      papply
        (fun fm -> qcon (x, fm))
        (if y = "." then parse_formula (ifn, afn) vs rest
         else parse_quant (ifn, afn) (y :: vs) qcon y rest)

and parse_formula (ifn, afn) vs inp =
  parse_right_infix "<=>"
    (fun (p, q) -> Iff (p, q))
    (parse_right_infix "==>"
       (fun (p, q) -> Imp (p, q))
       (parse_right_infix "\\/"
          (fun (p, q) -> Or (p, q))
          (parse_right_infix "/\\"
             (fun (p, q) -> And (p, q))
             (parse_atomic_formula (ifn, afn) vs))))
    inp

(* ------------------------------------------------------------------------- *)
(* Printing of formulas, parametrized by atom printer.                       *)
(* ------------------------------------------------------------------------- *)

let bracket p n f x y =
  if p then print_string "(" else ();
  Format.open_box n;
  f x y;
  Format.close_box ();
  if p then print_string ")" else ()

let rec strip_quant fm =
  match fm with
  | Forall (x, (Forall (_y, _p) as yp)) | Exists (x, (Exists (_y, _p) as yp)) ->
      let xs, q = strip_quant yp in
      (x :: xs, q)
  | Forall (x, p) | Exists (x, p) -> ([ x ], p)
  | _ -> ([], fm)

(* Print a formula given a (precision) printer for propositions *)
let print_formula pfn =
  let rec aux_print_formula pr fm =
    match fm with
    | False -> print_string "false"
    | True -> print_string "true"
    | Atom pargs -> pfn pr pargs
    | Not p -> bracket (pr > 10) 1 (print_prefix 10) "~" p
    | And (p, q) -> bracket (pr > 8) 0 (print_infix 8 "/\\") p q
    | Or (p, q) -> bracket (pr > 6) 0 (print_infix 6 "\\/") p q
    | Imp (p, q) -> bracket (pr > 4) 0 (print_infix 4 "==>") p q
    | Iff (p, q) -> bracket (pr > 2) 0 (print_infix 2 "<=>") p q
    | Forall (_x, _p) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
    | Exists (_x, _p) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
  and print_qnt qname (bvs, bod) =
    print_string qname;
    List.iter
      (fun v ->
        print_string " ";
        print_string v)
      bvs;
    print_string ". ";
    (* Format.print_space (); *)
    Format.open_box 0;
    aux_print_formula 0 bod;
    Format.close_box ()
  and print_prefix newpr sym p =
    print_string sym;
    aux_print_formula (newpr + 1) p
  and print_infix newpr sym p q =
    aux_print_formula (newpr + 1) p;
    print_string (" " ^ sym);
    (* Format.print_space (); *)
    print_string " ";
    aux_print_formula newpr q
  in
  aux_print_formula 0

let print_qformula pfn fm =
  Format.open_box 0;
  print_string "<<";
  Format.open_box 0;
  print_formula pfn fm;
  Format.close_box ();
  print_string ">>";
  Format.close_box ()

(* ------------------------------------------------------------------------- *)
(* Constructor Aliases                                                       *)
(* ------------------------------------------------------------------------- *)

let mk_and p q = And (p, q)
and mk_or p q = Or (p, q)
and mk_imp p q = Imp (p, q)
and mk_iff p q = Iff (p, q)
and mk_forall x p = Forall (x, p)
and mk_exists x p = Exists (x, p)

(* ------------------------------------------------------------------------- *)
(* Destructors.                                                              *)
(* ------------------------------------------------------------------------- *)

let dest_iff fm =
  match fm with Iff (p, q) -> (p, q) | _ -> failwith "dest_iff"

let dest_and fm =
  match fm with And (p, q) -> (p, q) | _ -> failwith "dest_and"

let rec conjuncts fm =
  match fm with And (p, q) -> conjuncts p @ conjuncts q | _ -> [ fm ]

let dest_or fm = match fm with Or (p, q) -> (p, q) | _ -> failwith "dest_or"

let rec disjuncts fm =
  match fm with Or (p, q) -> disjuncts p @ disjuncts q | _ -> [ fm ]

let dest_imp fm =
  match fm with Imp (p, q) -> (p, q) | _ -> failwith "dest_imp"

(* More fine grained destructors for Imp *)
let antecedent fm = fst (dest_imp fm)
let consequent fm = snd (dest_imp fm)

(* ------------------------------------------------------------------------- *)
(* Apply a function to the atoms, otherwise keeping structure.               *)
(* ------------------------------------------------------------------------- *)

let rec onatoms f fm =
  match fm with
  | Atom a -> f a
  | Not p -> Not (onatoms f p)
  | And (p, q) -> And (onatoms f p, onatoms f q)
  | Or (p, q) -> Or (onatoms f p, onatoms f q)
  | Imp (p, q) -> Imp (onatoms f p, onatoms f q)
  | Iff (p, q) -> Iff (onatoms f p, onatoms f q)
  | Forall (x, p) -> Forall (x, onatoms f p)
  | Exists (x, p) -> Exists (x, onatoms f p)
  | _ -> fm

(* Formula analog of list iterator "iList.tlist" *)
let rec overatoms f fm b =
  match fm with
  | Atom a -> f a b
  | Not p -> overatoms f p b
  | And (p, q) | Or (p, q) | Imp (p, q) | Iff (p, q) ->
      overatoms f p (overatoms f q b)
  | Forall (_, p) | Exists (_, p) -> overatoms f p b
  | _ -> b

(* Special case of a union of the results of a function over the atoms *)
let atom_union f fm = setify (overatoms (fun h t -> f h @ t) fm [])
let atoms fm = atom_union (fun a -> [ a ]) fm
