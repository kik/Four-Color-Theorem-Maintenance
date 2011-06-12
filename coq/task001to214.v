(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job001to106.
Require Import job107to164.
Require Import job165to189.
Require Import job190to206.
Require Import job207to214.

Lemma red000to214 : reducible_in_range 0 214 the_configs.
Proof.
CatReducible red000to106 red106to164 red164to189 red189to206 red206to214.
Qed.
