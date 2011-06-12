(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrnat.
Require Import seq.
Require Import cfmap.
Require Import cfreducible.
Require Import configurations.
Require Import present.
Require Import task001to214.
Require Import task215to234.
Require Import task235to282.
Require Import task283to302.
Require Import task303to322.
Require Import task323to485.
Require Import task486to506.
Require Import task507to541.
Require Import task542to588.
Require Import task589to633.

Lemma the_reducibility : reducibility.
Proof.
rewrite /reducibility; apply cat_reducible_range with 322.
  CatReducible red000to214 red214to234 red234to282 red282to302 red302to322.
CatReducible red322to485 red485to506 red506to541 red541to588 red588to633.
(* CatReducible red000to214 red214to234 red234to282 red282to302 red302to322
             red322to485 red485to506 red506to541 red541to588 red588to633.
             *)
Qed.
