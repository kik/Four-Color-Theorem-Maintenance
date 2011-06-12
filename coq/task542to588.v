(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job542to545.
Require Import job546to549.
Require Import job550to553.
Require Import job554to562.
Require Import job563to588.

Lemma red541to588 : reducible_in_range 541 588 the_configs.
Proof.
CatReducible red541to545 red545to549 red549to553 red553to562 red562to588.
Qed.
