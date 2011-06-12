(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job283to286.
Require Import job287to290.
Require Import job291to294.
Require Import job295to298.
Require Import job299to302.

Lemma red282to302 : reducible_in_range 282 302 the_configs.
Proof.
CatReducible red282to286 red286to290 red290to294 red294to298 red298to302.
Qed.
