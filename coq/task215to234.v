(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job215to218.
Require Import job219to222.
Require Import job223to226.
Require Import job227to230.
Require Import job231to234.

Lemma red214to234 : reducible_in_range 214 234 the_configs.
Proof.
CatReducible red214to218 red218to222 red222to226 red226to230 red230to234.
Qed.
