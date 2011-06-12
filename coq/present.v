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
Require Import embed.
Require Import quiz.
Require Import quiztree.
Require Import part.
Require Import redpart.
Require Import znat.
Require Import discharge.
Require Import hubcap.
Require Import cfmap.
Require Import cfcontract.
Require Import cfreducible.
Require Import configurations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* We bring together almost all the elements of graph theory that have been     *)
(* developped so far, to build up the shell that will run all the canned        *)
(* unavoidability proof scripts.                                                *)

(* Presentations are implemented directly as Coq scripts. This file contains    *)
(* the lemmas and special tactics that allow to handle concisely the four       *)
(* types of steps (split, symmetry, reducibility and hubcap), as well as the    *)
(* general setup for a particular hub size (such as generating the quiz tree    *)
(* and the discharge rules).                                                    *)

(* We need to provide additional staging for the quiz fork computation: Coq's   *)
(* reduction algorithm goes berserk when the full config list appears as an     *)
(* explicit parameter of a dependent predicate (!).                             *)

Definition reducibility := reducible_in_range 0 (size the_configs) the_configs.

(* Resources: configuration matching and rule forks.                            *)

Inductive the_quiz_tree_value : quiz_tree -> Prop :=
  TheQuizTreeValue : the_quiz_tree_value (locked cfquiz_tree the_configs).

Lemma the_unlocked_quiz_tree_value : the_quiz_tree_value (cfquiz_tree the_configs).
Proof. by rewrite [cfquiz_tree]lock. Qed.

Record the_quiz_tree_only : Set := TheQuizTree {
   the_quiz_tree_only_tree :> quiz_tree;
   the_quiz_tree_only_value : the_quiz_tree_value the_quiz_tree_only_tree
}.

(* The actual quiz tree is computed near the end of this file, because undo     *)
(* slows down considerably with such a large term in the context.               *)

Definition valid_hub g x := minimal_counter_example g /\ posz (@dscore g x).

Definition excluded_arity n :=
  forall g x, @valid_hub g x -> (n =d arity x) = false.

Definition successful p := forall g x, @valid_hub g x -> negb (exact_fitp x p).

Definition forced_part p0 p :=
  forall g x, @valid_hub g x -> exact_fitp x p0 -> exact_fitp x p.

Definition succeeds_in p0 p := forced_part p0 p -> successful p.

(* Presentation. *)
Lemma exclude_arity : forall n,
  succeeds_in (pcons_ n) (pcons_ n) -> excluded_arity n.
Proof.
move=> n Hp0 g x Hx; move: (Hx) => [Hg _]; apply/eqP => Hxn.
by case/idPn: (exact_fitp_pcons_ Hg x); rewrite -{}Hxn; apply: Hp0 => //; move.
Qed.

Section Succeed.

(* Tactic parameters come first. *)

(* Parameters for Pcase and Similar. *)
Variables (i : subpart_loc) (j k : nat) (mir lo : bool).

(* Parameter for Reducible & Hubcap. *)
Variable qt : the_quiz_tree_only.

(* Parameters for Hubcap. *)
Variables (rf : forall n, drule_fork n) (hc : hubcap).

(* Implicit parameter and explicit assumption for Similar. *)
Variable ps : part.
Hypothesis Hps : successful ps.

(* Implicit goal parameters. *)
Variable p0 p : part.

(* Pcase Ln_m: i[j] <= k. or Pcase Ln_m: i[j] > k. *)
Lemma succeed_by_split :
 let pl := split_part i j k lo p in
 let pr := split_part i j k (negb lo) p in
 let p0l := if good_split i j k p0 then split_part i j k lo p0 else pl in
   good_split i j k p -> succeeds_in p0l pl ->
 (successful p0l -> succeeds_in p0 pr) -> succeeds_in p0 p.
Proof.
move=> pl pr p0l Hpijk Hp0lpl Hp0pr Hp0p.
have Hpl: successful pl.
  apply Hp0lpl; rewrite /p0l /pl; case Hp0s: (good_split i j k p0) => g x //.
  move=> Hx; move: (Hx) => [Hg _]; rewrite !(fitp_split Hg) //.
  by case/andP=> *; apply/andP; auto.
have Hpr: successful pr.
  apply: Hp0pr; rewrite /pr ?size_split_part // => g x Hx;
    move: Hx {Hpl}(Hpl _ _ Hx) {Hp0p}(Hp0p _ _ Hx) => [Hg _].
  - rewrite /p0l; case Hp0s: (good_split i j k p0) => //.
    rewrite /pl !(fitp_split Hg) //.
    by move=> H Hp0p; apply/andP => [[Hkx Hxp0]]; case/andP: H; auto.
  rewrite /pl !(fitp_split Hg) // -(addTb lo) -addbA.
  by move=> H Hp0p Hp0x; rewrite (Hp0p Hp0x) !andbT in H |- *.
move=> g x Hx; move: Hx (Hpl _ _ Hx) (Hpr _ _ Hx) => [Hg _].
rewrite /pl /pr !(fitp_split Hg) // -(addTb lo) -addbA.
by move=> H H'; apply/idP => Hxp; case/idP: H'; rewrite Hxp !andbT in H |- *.
Qed.

(* Similar to Ln_m[j]. or Similar to *Ln_m[j]. *)
Lemma succeed_by_similarity :
  let p1 := if mir then mirror_part p else p in
  let p2 := rot_part j p1 in
  size_part ps = size_part p2 /\ cmp_part p2 ps = Psubset -> succeeds_in p0 p.
Proof.
move=> p1 p2 [Eps2 Hps2] _ g x Hx; apply/idP => Hxp.
pose g' := if mir then mirror g else g.
have [x1 Hx1 Hxp1]: exists2 x1 : g', valid_hub x1 & exact_fitp x1 p1.
  move: (Hx) => [Hg Hxs].
  rewrite /g' /p1; case mir; [ exists x | by exists x ].
    split;
     first by apply minimal_counter_example_mirror.
    by rewrite (dscore_mirror Hg).
  by rewrite -(fitp_mirror Hg) mirror_mirror_part //.
have [x2 Hx2 Hxp2]: (exists2 x2 : g', valid_hub x2 & exact_fitp x2 p2).
  case: (ltnP (size_part p1) j) => Hj.
    exists x1; first done; move: Hxp1; rewrite /p2 /exact_fitp size_rot_part.
    apply: etrans; congr andb; rewrite -{2}(cat_take_drop_part j p1) /rot_part.
    move: (ltnW Hj); rewrite -eqn_sub0 -size_drop_part !fitp_cat andbC.
    by case (drop_part j p1).
  case: Hx1 => [Hg' Hx1]; exists (iter j face x1); last by rewrite /p2 -fitp_rot.
  by split; auto; rewrite -(dscore_cface (x := x1)) // fconnect_iter.
case/andP: Hxp2 => [Ep2 Hxp2]; case/idP: (Hps Hx2); rewrite /exact_fitp.
by rewrite Eps2 Ep2 (fitp_cmp Hxp2 ps) Hps2.
Qed.

(* Implicit assumption for Reducible and Similar. *)
Hypothesis Hred : reducibility.

Lemma no_fit_the_redpart : forall g, minimal_counter_example g ->
  forall (x : g) p', redpart qt p' -> negb (exact_fitp x p').
Proof.
move=> g Hg x p' Hp'; apply: (no_fit_redpart Hg) p' Hp' x => x.
case: qt => [qt' Dqt'] /=; case: {qt'}Dqt'; rewrite -lock.
move: Hred; rewrite /reducibility; move Dcfs: the_configs => cfs Hcfs.
apply/idP; case/(qzt_fit_cfquiz Hg)=> [cf Hcf [qz Hgqz [Hgc [u Hu]]]].
suffice: forall g', minimal_counter_example g' -> ~ exists y : g', fitqz y qz.
  by move=> H; case: Hgqz; apply: H; try apply minimal_counter_example_mirror.
move{g Hg x Hgqz}=> gm Hgm [x Hxqz].
have Hcc: cfreducible cf.
  by move: (Hred (leq0n (index cf cfs))); rewrite Dcfs index_mem sub_index; auto.
exact (not_embed_reducible Hgm Hgc (quiz_preembedding Hgm Hgc Hu Hxqz) Hcc).
Qed.

(* Reducible. *)
Lemma succeed_by_reducibility : redpart qt p -> succeeds_in p0 p.
Proof. move=> Hp _ g x [Hg Hxn]; exact: no_fit_the_redpart. Qed.

(* Hubcap T[j1,j2]<=b1 ... [] *)
Lemma succeed_by_hubcap :
  let n := size_part p in
  hubcap_cover n hc && hubcap_fit (redpart qt) (rf n) p hc -> succeeds_in p0 p.
Proof.
move=> n Hhc _ g x [Hg Hx].
exact: (hubcap_fit_bound Hg (no_fit_the_redpart Hg)) Hhc.
Qed.

End Succeed.

Implicit Arguments succeed_by_split [p0 p g x].
Implicit Arguments succeed_by_similarity [ps p0 p g x].
Implicit Arguments succeed_by_reducibility [p0 p g x].
Implicit Arguments succeed_by_hubcap [p0 p g x].

(* Actual resources.                         *)

Definition the_quiz_tree :=
  Eval compute in TheQuizTree the_unlocked_quiz_tree_value.

Definition the_drule_fork_template : forall n, drule_fork n.
do 12 (case; first exact: (DruleFork (DruleForkValues _))).
move=> n; abstract exact: (DruleFork (DruleForkValues _)).
Defined.

Definition the_drule_fork := Eval compute in the_drule_fork_template.

(* Tactic extensions for the presentations. *)

Export PartSyntax.

Arguments Scope succeeds_in [part_scope part_scope].
Arguments Scope successful [part_scope].

Notation "'Check' p1 'in' p0" := (succeeds_in p0 p1)
  (at level 10, p1, p0 at level 9,
   format "'[v' 'Check'  p1 '/'    'in'  p0 ']'").

Ltac Presentation := apply exclude_arity; simpl.

Ltac Reducible :=
  apply (succeed_by_reducibility the_quiz_tree); [assumption | by compute].

Export HubcapSyntax.

Ltac Hubcap hc :=
  apply (succeed_by_hubcap the_quiz_tree the_drule_fork hc);
    [assumption | by compute]. 

Tactic Notation "Similar" "to" "*" ident(lab) "[" constr(n) "]" :=
  apply (succeed_by_similarity $n true $lab); compute; do 2 split.
Tactic Notation "Similar" "to" ident(lab) "[" constr(n) "]" :=
  apply (succeed_by_similarity $n false $lab); compute; do 2 split.

Export SublocSyntax.

Tactic Notation
  "Pcase" ident(label) " : " constr(i) "[" constr(j) "]" "<=" constr(k) :=
  apply (succeed_by_split $i (pred $j) $k true);
   [ split | simpl | simpl; intros label ].
Tactic Notation
  "Pcase" ident(label) " : " constr(i) "[" constr(j) "]" ">" constr(k) :=
  apply (succeed_by_split $i (pred $j) $k false);
   [ split | simpl | simpl; intros label ].
Tactic Notation
  "Pcase" " : " constr(i) "[" constr(j) "]" "<=" constr(k) :=
  apply (succeed_by_split $i (pred $j) $k true);
   [ split | simpl | clear; simpl ].
Tactic Notation
  "Pcase" " : " constr(i) "[" constr(j) "]" ">" constr(k) :=
  apply (succeed_by_split i (pred $j) $k false);
   [ split | simpl | clear; simpl ].

Set Strict Implicit.
Unset Implicit Arguments.