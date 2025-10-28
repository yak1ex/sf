(* This file is extracted from the TLC library.
   http://github.com/charguer/tlc
   DO NOT EDIT. *)

(**************************************************************************
* TLC: A library for Coq                                                  *
* Strings                                                                 *
**************************************************************************)

Set Implicit Arguments.
From SLF Require Import LibTactics LibReflect.
From Stdlib Require Export String.

(* ********************************************************************** *)
(* ################################################################# *)
(** * Inhabited *)

#[global]
Instance Inhab_string : Inhab string.
Proof using. apply (Inhab_of_val EmptyString). Qed.

(* 2025-08-24 14:03 *)
