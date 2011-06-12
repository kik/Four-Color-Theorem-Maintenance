(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import paths.
Require Import finset.
Require Import connect.
Require Import hypermap.
Require Import geometry.
Require Import color.
Require Import coloring.
Require Import cube.
Require Import present.
Require Import unavoidability.
Require Import reducibility.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Theorem four_color_hypermap : forall g, planar_bridgeless g -> four_colorable g.
Proof.
move=> g Hg; apply cube_colorable.
have Hqg: planar_bridgeless_plain_precubic (cube g).
  split; last by apply cubic_precubic; exact: cubic_cube.
  split; last exact: plain_cube.
  split; [rewrite planar_cube | rewrite bridgeless_cube]; exact Hg.
pose n := S (card (cube g)); move: Hqg (leqnn n); rewrite {1}/n.
elim: {g Hg}n (cube g) => // n Hrec g Hg Hgn.
rewrite ltnS leq_eqVlt in Hgn; case/orP: Hgn; auto.
move/eqP=> Dn; rewrite -{n}Dn in Hrec.
case: (decide_colorable g) => Hkg; first done.
case: (@unavoidability the_reducibility g); split; auto.
Qed.

Set Strict Implicit.
Unset Implicit Arguments.