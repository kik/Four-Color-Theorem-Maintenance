(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job303to306.
Require Import job307to310.
Require Import job311to314.
Require Import job315to318.
Require Import job319to322.

Lemma red302to322 : reducible_in_range 302 322 the_configs.
Proof.
CatReducible red302to306 red306to310 red310to314 red314to318 red318to322.
Qed.
