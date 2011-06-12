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
Require Import coloring.
Require Import birkhoff.
Require Import znat.
Require Import part.
Require Import discharge.
Require Import hubcap.
Require Import configurations.
Require Import present.
Require Import present5.
Require Import present6.
Require Import present7.
Require Import present8.
Require Import present9.
Require Import present10.
Require Import present11.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma unavoidability : reducibility -> forall g, ~ minimal_counter_example g.
Proof.
move=> Hred g Hg; case: (posz_dscore Hg) => x Hx.
have Hgx: valid_hub x by split.
have := (Hg : pentagonal g) x; rewrite 7!leq_eqVlt leqNgt.
rewrite exclude5 ?exclude6 ?exclude7 ?exclude8 ?exclude9 ?exclude10 ?exclude11 //.
case/idP; apply: (@dscore_cap1 g 5) => {x n Hn Hx Hgx}// y.
pose x := inv_face2 y; pose n := arity x.
have ->: y = face (face x) by rewrite /x /inv_face2 !Enode.
rewrite (dbound1_eq (DruleFork (DruleForkValues n))) // leqz_nat.
case Hn: (negb (Pr58 n)); first by rewrite source_drules_range //.
have Hrp := no_fit_the_redpart Hred Hg.
apply: (check_dbound1P (Hrp the_quiz_tree) _ (exact_fitp_pcons_ Hg x)) => //.
rewrite -/n; move: n Hn; do 9 case=> //.
Qed.

Set Strict Implicit.
Unset Implicit Arguments.