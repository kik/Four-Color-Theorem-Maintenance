(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job235to238.
Require Import job239to253.
Require Import job254to270.
Require Import job271to278.
Require Import job279to282.

Lemma red234to282 : reducible_in_range 234 282 the_configs.
Proof.
CatReducible red234to238 red238to253 red253to270 red270to278 red278to282.
Qed.
