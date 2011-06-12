(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job589to610.
Require Import job611to617.
Require Import job618to622.
Require Import job623to633.

Lemma red588to633 : reducible_in_range 588 633 the_configs.
Proof.
have red633: (reducible_in_range 633 633 the_configs).
  by apply check_reducible_in_range; left.
CatReducible red588to610 red610to617 red617to622 red622to633 red633.
(*
  CatReducible red588to610 red610to617 red617to622 red622to633.
*)
Qed.
