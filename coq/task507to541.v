(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import job507to510.
Require Import job511to516.
Require Import job517to530.
Require Import job531to534.
Require Import job535to541.

Lemma red506to541 : reducible_in_range 506 541 the_configs.
Proof.
CatReducible red506to510 red510to516 red516to530 red530to534 red534to541.
Qed.
