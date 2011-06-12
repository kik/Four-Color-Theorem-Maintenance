(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.

Lemma red502to506 : reducible_in_range 502 506 the_configs.
Proof. CheckReducible. Qed.
