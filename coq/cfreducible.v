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
Require Import chromogram.
Require Import coloring.
Require Import kempe.
Require Import cfmap.
Require Import cfcolor.
Require Import cfcontract.
Require Import ctree.
Require Import kempetree.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* We only use C-reductibility; the source data has been completed *)
(* with an arbitrary contraction. *)

Section CfReducible.

Variable cf : config.

Definition check_reducible :=
  if contract_ctree cf is Some cct then
    ctree_disjoint (kempe_tree (cfprog cf)) cct
  else false.

Definition cfreducible := c_reducible (cfring cf) (cfcontract cf).

Lemma check_reducible_valid : check_reducible -> cfreducible.
Proof.
rewrite /check_reducible /cfreducible; move: (contract_ctreeP cf).
move: (cfcontract cf) (contract_ctree cf) => cc.
case=> // [cct] [Hcc Hkcc] Hkg; split; first done.
move=> et Het; case: Het (ctree_mem_disjoint Hkg (Hkcc _ Het)) => [k _ Det].
have Eet: size (behead et) = pred (cprsize (cfprog cf)).
  rewrite size_behead Det size_trace size_maps.
  by rewrite /cfring rev_rev -size_ring_cpmap.
move/(kempe_treeP Eet) {Eet Hkg Hkcc}; rewrite -/(cfmap cf).
have <-: rot 1 et = ctrace (behead et).
  have: sumt et =d Color0 by apply/eqP; rewrite Det; apply: sumt_trace.
  case Det': et => [|e et'] /=.
    move: (congr1 size Det'); rewrite Det size_trace size_maps /cfring rev_rev.
    by rewrite head_cpring.
  by rewrite -eq_addc0 rot1_adds /ctrace; move/eqcP=> <-.
move{k Det} => Het P HP HPet; pose P' (et' : colseq) := P (rotr 1 et').
have HP': kempe_closed P'.
  move=> et'; case/HP=> [HPet'h [w Het'w HwPet']].
  split; first by move=> h; rewrite /P' /permt -maps_rotr; apply: HPet'h.
  exists (gram_rot w); first by rewrite -(rot_rotr 1 et') match_gram_rot.
  move=> et''; rewrite -{1}(rot_rotr 1 et'') match_gram_rot; exact: HwPet'.
rewrite -(rotr_rot 1 et) in HPet.
case: {et Het HP' HPet}(Het _ HP' HPet) => [et [k Hk Det] HP'et].
exists (rotr 1 et); last done; exists k; first done.
by rewrite /cfring rev_rev Det maps_rot trace_rot rotr_rot.
Qed.

End CfReducible.

(* This predicate hides the (expensive) reducibility evaluation. *)

Section IndexConfig.

Import ConfigSyntax.

Definition cf000 := Config 0 H.

End IndexConfig.

Definition reducible_in_range j1 j2 (cfs : configseq) :=
  forall i, j1 <= i -> i < j2 -> cfreducible (sub cf000 cfs i).

Lemma check_reducible_in_range : forall j1 j2 (cfs : configseq),
   (forall i, let n := j2 - j1 in
    n <= i \/ check_reducible (sub cf000 (take n (drop j1 cfs)) i)) ->
 reducible_in_range j1 j2 cfs.
Proof.
move=> j1 j2 cfs Hcfs i Hij1 Hij2; set n := j2 - j1; set i' := i - j1.
have Hj12: j1 <= j2 by apply ltnW; apply: leq_trans Hij2.
have Hi'n: i' < n by rewrite /i' -(leq_subS Hij1) leq_sub_add /n leq_add_sub.
case: {Hcfs}(Hcfs i'); rewrite -/n; first by rewrite leqNgt Hi'n.
rewrite sub_take // sub_drop /i' leq_add_sub //; exact: check_reducible_valid.
Qed.

Ltac CheckReducible :=
  apply check_reducible_in_range; simpl;
  repeat (case; [right; by compute | try by left]).

Lemma cat_reducible_range : forall j1 j2 cfs,
 reducible_in_range j1 j2 cfs ->
 forall j3, reducible_in_range j2 j3 cfs -> reducible_in_range j1 j3 cfs.
Proof. move=> j1 j2 cfs Hj12 j3 Hj23 i Hij1 Hij3; case (ltnP i j2); auto. Qed.

Ltac CatReducible h1 h2 h3 h4 h5 :=
  apply (cat_reducible_range h1); apply (cat_reducible_range h2);
  apply (cat_reducible_range h3); apply (cat_reducible_range h4);
  exact h5.

Set Strict Implicit.
Unset Implicit Arguments.
