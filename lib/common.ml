(* ========================================================================= *)
(* Common utility functions and data structures.                             *)
(*                                                                           *)
(* Most of the content is copied or adapted from John Harrison's book,       *)
(* The Handbook of Practical Logic and Automated Reasoning.                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* (See "LICENSE_Orig.txt" for details.)                                     *)
(*                                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Explosion and implosion of strings.                                       *)
(* ------------------------------------------------------------------------- *)

let explode s =
  let rec exap n l =
    if n < 0 then l else exap (n - 1) (String.sub s n 1 :: l)
  in
  exap (String.length s - 1) []

let implode l = List.fold_right ( ^ ) l ""
