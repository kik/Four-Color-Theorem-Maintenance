(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job486to489.
Require Import job490to494.
Require Import job495to498.
Require Import job499to502.
Require Import job503to506.

Lemma red485to506 : reducible_in_range 485 506 the_configs.
Proof.
CatReducible red485to489 red489to494 red494to498 red498to502 red502to506.
Qed.
