(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job323to383.
Require Import job384to398.
Require Import job399to438.
Require Import job439to465.
Require Import job466to485.

Lemma red322to485 : reducible_in_range 322 485 the_configs.
Proof.
CatReducible red322to383 red383to398 red398to438 red438to465 red465to485.
Qed.
