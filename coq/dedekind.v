(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import znat.
Require Import frac.
Require Import Setoid.
Require Import real.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Construcion of R = complete totally ordered field.         *)
(* We use the standard Dedekind cut construction.             *)
(* We actually make R into a setoid, taking non-comparability *)
(* as equality. This allows the construction of an internal   *)
(* model in the calculus of constructions, assuming only the  *)
(* classical excluded middle.                                 *)

Section DedekindReals.

Hypothesis Hclassical : excluded_middle.

(* We use nontrivial open upper order ideals of frac to represent the reals. *)

Notation ddseg := (frac -> Prop).

Definition ideals (x : ddseg) := forall f1 f2, leqf f1 f2 -> x f1 -> x f2.

Definition opens (x : ddseg) := forall f, x f -> exists2 f', ltf f' f & x f'.

Definition hass (x : ddseg) := exists f, x f.

Definition hasNs (x : ddseg) := exists f, ~ x f.

Record dreal : Type := Dreal {
  dd_seg : ddseg;
  dd_ideal : ideals dd_seg;
  dd_open : opens dd_seg;
  dd_ub : hass dd_seg;
  dd_lb : hasNs dd_seg
}.

Coercion dd_seg : dreal >-> Funclass.

Definition leqdr (x1 x2 : dreal) := forall f, x2 f -> x1 f.

Definition eqdr (x1 x2 : dreal) := leqdr x1 x2 /\ leqdr x2 x1.

Lemma leqdrr : forall x, leqdr x x. Proof. by move=> x f. Qed.
Implicit Arguments leqdrr [].
Hint Resolve leqdrr.

Lemma eqdr_refl : forall x, eqdr x x. Proof. by split. Qed.
Hint Resolve eqdr_refl.

Lemma eqdr_sym : forall x1 x2, eqdr x1 x2 -> eqdr x2 x1.
Proof. by move=> x1 x2 [Hx12 Hx21]; split. Qed.
Hint Immediate eqdr_sym.

Lemma leqdr_trans : forall x1 x2 x3, leqdr x1 x2 -> leqdr x2 x3 -> leqdr x1 x3.
Proof. by rewrite /leqdr; auto. Qed.

Lemma eqdr_trans : forall x1 x2 x3, eqdr x1 x2 -> eqdr x2 x3 -> eqdr x1 x3.
Proof.
by move=> x1 x2 x3 [Hx12 Hx21] [Hx23 Hx32]; split; apply leqdr_trans with x2.
Qed.

Lemma eqdr_theory : Setoid_Theory dreal eqdr.
Proof. split; auto; exact eqdr_trans. Qed.

Add Setoid dreal eqdr eqdr_theory.

Add Morphism dd_seg : dd_seg_morphism.
Proof. by move=> x y f [_ Hyx]; auto. Qed.

Add Morphism leqdr : leqdr_morphism.
Proof. by move=> x1 y1 x2 y2 Dx1 Dx2 H f; move: (H f); rewrite Dx1 Dx2. Qed.

Lemma eqf_dr : forall (x : dreal) f1 f2, eqf f1 f2 -> (x f1 <-> x f2).
Proof. by move=> x f1 f2; case/andP; split; apply: dd_ideal. Qed.

Section RealFrac.

Variable f : frac.

Definition fracs : ddseg := fun f' => ltf f f'.

Lemma ideals_frac : ideals fracs.
Proof. rewrite /fracs; move=> f1 f2 /= *; eapply ltf_leq_trans; eauto. Qed.

Lemma opens_frac : opens fracs.
Proof. by move=> f3; case/frac_dense=> f2; exists f2. Qed.

Lemma hass_frac : hass fracs.
Proof.
by exists (addf F1 f); rewrite addfC /fracs /ltf -{2}[f]addF0 leqf_add2l.
Qed.

Lemma hasNs_frac : hasNs fracs.
Proof. by exists f; rewrite /fracs ltff. Qed.

Definition fracdr := Dreal ideals_frac opens_frac hass_frac hasNs_frac.

End RealFrac.

Coercion fracdr : frac >-> dreal.

Section RealSup.

Variable E : dreal -> Prop.

Definition supds0 : ddseg := fun f => exists2 f', ltf f' f & forall x, E x -> x f'.

Definition has_supdr0 := hass supds0 /\ hasNs supds0.

Definition supds : ddseg := fun f => IF has_supdr0 then supds0 f else ltf F0 f.

Lemma ideals_sup : ideals supds.
Proof.
move=> f1 f2 Hf12 [] [HE Hf1]; [ left | right ]; split; auto.
  by move: Hf1 => [f Hf HfE]; exists f; first by apply: ltf_leq_trans Hf12.
by apply: ltf_leq_trans Hf12.
Qed.

Lemma opens_sup : opens supds.
Proof.
move=> f [] [HE Hf].
case: Hf => [f2 Hff2 Hf2]; case: (frac_dense Hff2) => [f1 Hff1 Hf12].
  by exists f1; first done; left; split; first done; exists f2.
by case: (frac_dense Hf) => [f1 Hff1 Hf1]; exists f1; first done; right; split.
Qed.

Lemma hass_sup : hass supds.
Proof.
case: (Hclassical has_supdr0) => HE; last by exists F1; right; split.
by case: (HE) => [] [f Hf] _; exists f; left; split.
Qed.

Lemma hasNs_sup : hasNs supds.
Proof.
case: (Hclassical has_supdr0) => HE; last by exists F0; do 2 case; auto.
by case: (HE) => _ [f Hf]; exists f; do 2 case; auto.
Qed.

Definition supdr : dreal := Dreal ideals_sup opens_sup hass_sup hasNs_sup.

End RealSup.

Lemma eqdr_sup : forall E E',
  (forall x x', eqdr x x' -> (E x <-> E' x')) -> eqdr (supdr E) (supdr E').
Proof.
move=> E E' DE; have Esup: forall f, supds0 E f <-> supds0 E' f.
  move=> f; rewrite /supds0; split=> [] [f' Hff' Hf']; 
  by exists f'; last by move=> x; case (DE x x); auto.
have Ehas: hass (supds0 E) <-> hass (supds0 E').
  by split=> [] [f Hf]; exists f; move: Hf; rewrite (Esup f).
have EhasN: (hasNs (supds0 E) <-> hasNs (supds0 E')).
  by split=> [][f Hf]; exists f; move: Hf; rewrite (Esup f).
by split=> f;
  rewrite /leqdr /= /supds /has_supdr0 /IF_then_else Ehas EhasN (Esup f).
Qed.

Let hasdr E := exists x : dreal, E x.

Let ubdr E z :=  forall y, (E y : Prop) -> leqdr y z.

Let has_supdr E := hasdr E /\ hasdr (ubdr E).

Let boundeddr x E :=  exists2 y, E y & leqdr x y.

Remark has_supdr0I : forall E, has_supdr E -> has_supdr0 E.
Proof.
move=> E [[x Hx] [z Hz]]; split.
move: (dd_ub z) {x Hx} => [f Hf]; case: (dd_ub f) => [f1].
  move/dd_open=> [f2 Hf12 Hff2]; exists f1; exists f2; first done.
  by move=> x Hx; apply Hz; last by apply: dd_ideal Hf; exact: ltfW.
move: (dd_lb x) {z Hz} => [f Hf]; exists f=> [] [f1 Hff1 Hf1]; case: Hf.
by apply: dd_ideal (Hf1 _ Hx); exact: ltfW.
Qed.
Hint Resolve has_supdr0I.

Lemma ubdr_sup : forall E, has_supdr E -> ubdr E (supdr E).
Proof.
move=> E HE x Hx f [[_ [f' Hff' Hf']]|[[]]]; auto.
apply: (dd_ideal (ltfW Hff')); auto.
Qed.

Lemma leqdr_sup_ub : forall E, has_supdr E ->
  forall x, ubdr E x -> leqdr (supdr E) x.
Proof.
move=> E HE x Hx f; move/dd_open=> [f1 Hff1 Hf1].
by left; split; auto; exists f1; last by move=> y Hy; exact: Hx.
Qed.

Lemma supdr_total : forall x E, has_supdr E -> boundeddr x E \/ leqdr (supdr E) x.
Proof.
move=> x E HE; case: (Hclassical (boundeddr x E)); first by left.
move=> HxE; right; apply leqdr_sup_ub; auto; move=> y Hy f Hxf.
case: (Hclassical (exists2 f', ltf f' f & y f')) => [[f' Hf'f]|Hxy].
  by apply: dd_ideal; apply ltfW.
case: HxE; exists y; move=> // f' Hyf'.
by case: (leqf_cases f f') => *; [ apply: dd_ideal Hxf | case Hxy; exists f' ].
Qed.

Section RealSelect.

(* definition by cases *)

Variables (P : Prop) (x1 x2 : dreal).

Definition selectdr_set x := IF P then eqdr x x1 else eqdr x x2.
Definition selectdr := supdr selectdr_set.

Lemma selectdr_cases : IF P then eqdr selectdr x1 else eqdr selectdr x2.
Proof.
case: (Hclassical P) => HP; [ left | right ]; split=> //.
  have Hsup: has_supdr0 selectdr_set.
    case: (dd_lb x1) (dd_ub x1) => [f1 Hf1] [f2 Hf2]; split.
      case/dd_open: Hf2 => [f3 Hf23 Hf3]; exists f2; exists f3; first done.
      by move=> x [[_ Dx]|[[]]] //; rewrite Dx.
    exists f1; move=> [f3 Hf13 Hf3]; case: Hf1; apply: (dd_ideal (ltfW Hf13)).
    by apply Hf3; left; split.
  split=> f.
    case/dd_open=> [f1 Hff1 Hf1]; left; split=> //; exists f1 => //.
    by move=> x [[_ Dx]|[[]]] //; rewrite Dx.
  case=> [[_ [f1 Hf1f Hf1]]|[[]]] //; apply: (dd_ideal (ltfW Hf1f)).
  by apply Hf1; left; split.
have Hsup: has_supdr0 selectdr_set.
  case: (dd_lb x2) (dd_ub x2) => [f1 Hf1] [f2 Hf2]; split.
    case/dd_open: Hf2 => [f3 Hf23 Hf3]; exists f2; exists f3=> //.
    move=> x [[H _]|[_ Dx]]; try rewrite Dx; tauto.
  exists f1; move=> [f3 Hf13 Hf3]; case: Hf1; apply: (dd_ideal (ltfW Hf13)).
  by apply Hf3; right; split.
split; move=> f.
  case/dd_open=> [f1 Hff1 Hf1]; left; split=> //; exists f1=> //.
  move=> x [[H' _]|[_ Dx]]; rewrite ?Dx; tauto.
case=> [[_ [f1 Hf1f Hf1]]|[[]]] //; apply: (dd_ideal (ltfW Hf1f)).
by apply Hf1; right; split.
Qed.

End RealSelect.

Add Morphism selectdr : selectdr_morphism.
Proof.
move=> P Q x1 y1 x2 y2 DP Dx1 Dx2; apply: eqdr_sup => [x3 y3 Dx3].
rewrite /selectdr_set /IF_then_else DP Dx1 Dx2 Dx3; tauto.
Qed.

Section RealSign.

(* opposite and absolute value. *)

Variable x : dreal.

(* opposite *)

Definition oppds : ddseg := fun f => exists2 f', ltf f' f & ~ x (oppf f').

Lemma ideals_opp : ideals oppds.
Proof.
by move=> f1 f2 Hf12 [f3 Hf23 Hf3]; exists f3; first exact: ltf_leq_trans Hf12.
Qed.

Lemma opens_opp : opens oppds.
Proof.
move=> f1 [f3 Hf13 Hf3]; case/frac_dense: Hf13 => [f2 Hf12 Hf23].
by exists f2; last by exists f3.
Qed.

Lemma hass_opp : hass oppds.
Proof.
move: (dd_lb x) => [f1]; exists (oppf (addf (oppf F1) f1)).
exists (oppf f1); last by rewrite /= oppf_opp.
by rewrite /ltf leqf_opp2 -{1}[f1]addF0 addfC leqf_add2r.
Qed.

Lemma hasNs_opp : hasNs oppds.
Proof.
move: (dd_ub x) => [f Hxf]; exists (oppf f); move=> [f1 Hff1 []].
by apply: dd_ideal Hxf; rewrite -leqf_opp2 oppf_opp ltfW.
Qed.

Definition oppdr := Dreal ideals_opp opens_opp hass_opp hasNs_opp.

(* absolute value *)

Definition absds : ddseg := fun f => x f /\ oppdr f.

Lemma ideals_abs : ideals absds.
Proof.
move=> f1 f2 Hf12 [Hf1 Hf1'].
split; [ exact: dd_ideal Hf1 | exact: ideals_opp Hf1' ].
Qed.

Lemma opens_abs : opens absds.
Proof.
move=> f; case; move/dd_open=> [f1 Hff1 Hf1]; move/opens_opp=> [f2 Hff2 Hf2].
case: (leqf_cases f1 f2) => Hf12.
  by exists f2; last by split; first exact: dd_ideal Hf1.
by exists f1; last by split; last by apply: ideals_opp Hf2; exact: ltfW.
Qed.

Lemma hass_abs : hass absds.
Proof.
move: (dd_ub x) hass_opp => [f1 Hf1] [f2 Hf2].
case: (leqf_cases f1 f2) => Hf12.
  by exists f2; split; first exact: dd_ideal Hf1.
by exists f1; split; last by apply: ideals_opp Hf2; exact: ltfW.
Qed.

Lemma posf_absdr : forall f, absds f -> posf f.
Proof.
move=> f [Hf [f1 Hff1 Hf1]]; rewrite -posfI; apply/idP => [Hf0]; case: Hf1.
apply: dd_ideal Hf; apply: (leqf_trans Hf0); rewrite -oppF0 leqf_opp2.
by apply: leqf_trans Hf0; exact: ltfW.
Qed.

Lemma hasNs_abs : hasNs absds.
Proof. by exists F0; move; move/posf_absdr. Qed.

Definition absdr := Dreal ideals_abs opens_abs hass_abs hasNs_abs.

End RealSign.

Add Morphism oppdr : oppdr_morphism.
Proof.
move=> x y Dx.
split=> f [f' Hff' Hf']; by exists f'; last by move: Hf'; rewrite Dx.
Qed.

Add Morphism absdr : absdr_moprphism.
Proof. move=> x y Dx; split; move=> f; rewrite /= /absds Dx; tauto. Qed.

Lemma oppdr_opp : forall x, eqdr (oppdr (oppdr x)) x.
Proof.
move=> x; split=> f.
  move/dd_open=> [f1 Hff1 Hf1]; exists f1=> // [] [f2 Hf12 []].
  by apply: dd_ideal Hf1; rewrite -leqf_opp2 oppf_opp ltfW.
case: (Hclassical (x f)) => Hf // [f1 Hff1 []].
by exists (oppf f); rewrite /ltf ?leqf_opp2 ?oppf_opp.
Qed.

Lemma absdr_opp : forall x, eqdr (absdr (oppdr x)) (absdr x).
Proof. move=> x; split; move=> f; rewrite /= /absds (oppdr_opp x); tauto. Qed.

Section RealArith.

Variable x1 x2 : dreal.

Definition addds : ddseg := fun f => exists2 f1, x1 f1 & x2 (addf (oppf f1) f).

Lemma ideals_add : ideals addds.
Proof.
move=> f1 f2 Hf12 [f11 Hf11 Hf1']; exists f11=> //.
by apply: dd_ideal Hf1'; rewrite leqf_add2l.
Qed.

Lemma opens_add : opens addds.
Proof.
move=> f2 [f1 Hf1]; move/dd_open=> [f3 Hf23 Hf3]; exists (addf f1 f3).
  by rewrite /ltf -(leqf_eql (addf_inv f1 f2)) addfCA leqf_add2l.
by exists f1; rewrite // (eqf_dr x2 (addf_inv f1 f3)).
Qed.

Lemma hass_add : hass addds.
Proof.
move: (dd_ub x1) (dd_ub x2) => [f1 Hf1] [f2 Hf2]; exists (addf f1 f2).
by exists f1; auto; apply: dd_ideal Hf2; case/andP: (addf_inv f1 f2).
Qed.

Lemma hasNs_add : hasNs addds.
Proof.
move: (dd_lb x1) (dd_lb x2) => [f1 Hf1] [f2 Hf2].
exists (addf f1 f2)=> [] [f3 Hf3 Hf312]; case: Hf2; apply: dd_ideal Hf312.
rewrite -(leqf_eqr (addf_inv f3 f2)) leqf_add2l leqf_add2r.
by apply ltfW; apply/idP => [Hf13]; case Hf1; exact: dd_ideal Hf3.
Qed.

(* x1 + x2 *)
Definition adddr := Dreal ideals_add opens_add hass_add hasNs_add.

Definition amulds : ddseg :=
  fun f => exists2 f1, absdr x1 f1 & absdr x2 (mulf (invf f1) f).

Lemma ideals_amul : ideals amulds.
Proof.
move=> f1 f2 Hf12 [f Hx1f Hx2f]; exists f => //; apply: ideals_abs Hx2f.
rewrite leqf_pmul2l // posf_inv; exact (posf_absdr Hx1f).
Qed.

Lemma opens_amul : opens amulds.
Proof.
move=> f2 [f1 Hxf1]; move/dd_open=> [f3 Hf23 Hf3]; have Hf1 := posf_absdr Hxf1.
exists (mulf f1 f3).
  by rewrite /ltf -(leqf_eql (pmulf_inv f2 Hf1)) mulfCA leqf_pmul2l.
by exists f1; rewrite // (eqf_dr (absdr x2) (pmulf_inv f3 Hf1)).
Qed.

Lemma hass_amul : hass amulds.
Proof.
move: (hass_abs x1) (hass_abs x2) => [f1 Hxf1] [f2 Hxf2].
have Hf1 := posf_absdr Hxf1; exists (mulf f1 f2); exists f1=> //.
by apply: ideals_abs Hxf2; case/andP: (pmulf_inv f2 Hf1).
Qed.

Lemma hasNs_amul : hasNs amulds.
Proof.
by exists F0 => [[f _]]; move/posf_absdr; rewrite -posfI /ltf (leqf_eql (mulF0 _)).
Qed.

(* |x1| * |x2| *)
Definition amuldr := Dreal ideals_amul opens_amul hass_amul hasNs_amul.

Definition pos_muldr := x1 F0 <-> x2 F0.

(* x1 * x2 *)
Definition muldr : dreal := selectdr pos_muldr amuldr (oppdr amuldr).

End RealArith.

(* 1 / |x1| *)
Definition ainvdr x1 := supdr (fun x => amuldr x x1 F1).

(* 1 / x1 *)
Definition invdr (x1 : dreal) := selectdr (x1 F0) (oppdr (ainvdr x1)) (ainvdr x1).

Add Morphism adddr : adddr_morphism.
Proof.
move=> x1 y1 x2 y2 Dx1 Dx2.
by split; move=> f [f' Hf1 Hf2]; exists f'; move: Hf1 Hf2; rewrite ?Dx1 ?Dx2.
Qed.

Add Morphism amuldr : amuldr_morphism.
Proof.
move=> x1 y1 x2 y2 Dx1 Dx2.
by split; move=> f [f' Hf1 Hf2]; exists f'; move: Hf1 Hf2; rewrite ?Dx1 ?Dx2.
Qed.

Add Morphism pos_muldr : pos_muldr_morphism.
Proof. by move=> x1 y1 x2 y2 Dx1 Dx2; rewrite /pos_muldr Dx1 Dx2. Qed.

Add Morphism muldr : muldr_morphism.
Proof. move=> x1 y1 x2 y2 Dx1 Dx2; split=> f; rewrite /muldr Dx1 Dx2; tauto. Qed.

Lemma adddrC : forall x1 x2 : dreal, eqdr (adddr x1 x2) (adddr x2 x1).
Proof.
suffice: forall x1 x2, leqdr (adddr x2 x1) (adddr x1 x2) by split.
move=> x1 x2 f [f' Hf' Hf]; exists (addf (oppf f') f) => //.
apply: dd_ideal Hf'; rewrite oppf_add oppf_opp -addfA addfC -addfA.
by case/andP: (addf_inv f f').
Qed.

Lemma adddrA : forall x1 x2 x3,
  eqdr (adddr x1 (adddr x2 x3)) (adddr (adddr x1 x2) x3).
Proof.
suffice: forall x1 x2 x3, leqdr (adddr (adddr x1 x2) x3) (adddr x1 (adddr x2 x3)).
  split; auto; rewrite (adddrC x1 (adddr x2 x3)) (adddrC (adddr x1 x2) x3).
  by rewrite (adddrC x1 x2) (adddrC x2 x3); auto.
move=> x1 x2 x3 f3 [f1 Hf1 [f2 Hf2 Hf3]].
exists (addf f1 f2); last by rewrite oppf_add -addfA addfCA.
by exists f1=> //; apply: dd_ideal Hf2; case/andP: (addf_inv f1 f2).
Qed.

Lemma adddrI : forall x, eqdr (adddr x (oppdr x)) F0.
Proof.
move=> x; apply eqdr_sym; split=> f.
  move=> [f1 Hf1 [f2 Hf12 Hf2]]; apply/idP => [Hf]; case: Hf2; apply: dd_ideal Hf1.
  rewrite -leqf_opp2 oppf_opp; apply: (leqf_trans (ltfW Hf12)).
  by rewrite -{2}[oppf f1]addF0 leqf_add2l.
rewrite /= /fracs posfI; move=> Hf; pose fn (n : nat) := Frac 0 n.
have [n Hn]: exists n, absdr x (mulf f (fn n)).
  case: (hass_abs x) => [f1 Hxf1].
  case Dn: (mulf (invf f) f1) => [d [n|n]].
    exists n; apply: ideals_abs Hxf1.
    rewrite -(leqf_eql (pmulf_inv f1 Hf)) mulfCA leqf_pmul2l // {}Dn /fn /=.
    by rewrite scalez_pos leqz_nat /= leq_addr.
  by move: (posf_absdr Hxf1); rewrite -(@posf_pmull (invf f) f1) ?posf_inv ?Dn.
elim: n Hn => [|n].
  by move/posf_absdr; rewrite /fn -/F0 -posfI /ltf (leqf_eql (mulF0 f)).
set f' := mulf f (fn n) => Hrec Hn.
have Hff': absdr x (addf f f').
  by apply: dd_ideal Hn; rewrite -{2}[f]mulf1; case/andP: (mulf_addr f F1 (fn n)).
case/dd_open: Hff' => [f1 Hff1 [Hf1 Hf1']]; set f2 := addf (oppf f) f1.
case: (Hclassical (x f')) {Hn Hf} => Hf'.
  case: (Hclassical (x (oppf f2))) => Hf2.
    exists (oppf f2) => //.
    by rewrite oppf_opp addfC /f2 addfCA (eqf_dr (oppdr x) (addf_inv f f1)).
  apply Hrec; split=> //.
  by exists f2; rewrite // /ltf -(leqf_eql (addf_inv f f')) /f2 leqf_add2l.
exists f1 => //; exists (oppf f'); last by rewrite oppf_opp.
rewrite /ltf -[f]oppf_opp -oppf_add leqf_opp2 addfC.
by rewrite -(leqf_eql (addf_inv f f')) leqf_add2l.
Qed.

Lemma add0dr : forall x, eqdr (adddr F0 x) x.
Proof.
move=> x; split=> f.
  move/dd_open=> [f1 Hf1 Hxf1]; exists (addf (oppf f1) f).
    by rewrite /= /fracs /ltf -(leqf_eqr (addf_inv f1 F0)) addF0 leqf_add2l.
  by rewrite oppf_add oppf_opp -addfA addfC -addfA (eqf_dr x (addf_inv f f1)).
move=> [f1 Hf1]; apply: dd_ideal; rewrite -{2}[f]addF0 addfC leqf_add2l.
by rewrite -oppF0 leqf_opp2 ltfW.
Qed.

Lemma oppdr_add : forall x1 x2,
   eqdr (oppdr (adddr x1 x2)) (adddr (oppdr x1) (oppdr x2)).
Proof.
move=> x1 x2; set y1 := oppdr x1; set y2 := oppdr x2.
set y := oppdr (adddr x1 x2); rewrite -(add0dr (adddr y1 y2)) -(adddrI y).
rewrite -(adddrA y (oppdr y) (adddr y1 y2)) (adddrA (oppdr y) y1 y2).
rewrite {3}/y (oppdr_opp (adddr x1 x2)) (adddrC x1 x2) -(adddrA x2 x1 y1).
rewrite /y1 (adddrI x1) (adddrC x2 F0) (add0dr x2) /y2 (adddrI x2).
by rewrite (adddrC y F0) (add0dr y).
Qed.

Lemma adddr_monotony : forall x1 x2 x3, leqdr x2 x3 ->
  leqdr (adddr x1 x2) (adddr x1 x3).
Proof. move=> x1 x2 x3 Hx12 f2 [f1 Hf1 Hf2]; exists f1; auto. Qed.

Lemma amuldrC : forall x1 x2 : dreal, eqdr (amuldr x1 x2) (amuldr x2 x1).
Proof.
suffice: forall x1 x2, leqdr (amuldr x2 x1) (amuldr x1 x2) by split.
move=> x1 x2 f [f' Hf' Hf]; exists (mulf (invf f') f) => //.
apply: dd_ideal (Hf'); move/posf_absdr: Hf => Hf.
rewrite -(leqf_pmul2l Hf) mulfCA (leqf_eqr (pmulf_inv f Hf)).
by rewrite mulfC mulfCA; case/andP: (pmulf_inv f (posf_absdr Hf')).
Qed.

Lemma pos_muldrC : forall x1 x2, pos_muldr x1 x2 <-> pos_muldr x2 x1.
Proof. by split; case; split. Qed.

Lemma muldrC : forall x1 x2, eqdr (muldr x1 x2) (muldr x2 x1).
Proof. by move=> x1 x2; rewrite /muldr (pos_muldrC x1 x2) (amuldrC x1 x2). Qed.

Lemma amuldr_opp : forall x1 x2, eqdr (amuldr (oppdr x1) x2) (amuldr x1 x2).
Proof.
suffice: forall x1 x2, leqdr (amuldr x1 x2) (amuldr (oppdr x1) x2).
  by move=> Hrec x1 x2; split=> // f Hf; apply Hrec; rewrite (oppdr_opp x1).
by move=> x1 x2 f [f' Hf' Hf]; exists f'; rewrite // -(absdr_opp x1).
Qed.

Lemma pos_absdr : forall x : dreal, ~ x F0 -> eqdr (absdr x) x.
Proof.
move=> x Hx; split=> f Hf; last by case Hf.
by split=> //; exists F0=> //; apply/idP => Hf0; case: Hx; exact: dd_ideal Hf.
Qed.

Lemma oppdr0 : eqdr (oppdr F0) F0.
Proof. by set f0 := oppdr F0; rewrite -(adddrI F0) -/f0 (add0dr f0). Qed.

Lemma leqdr_opp2 : forall x1 x2, leqdr x1 x2 -> leqdr (oppdr x2) (oppdr x1).
Proof. move=> x1 x2 Hx12 f1 [f2 Hf12 Hf2]; exists f2; auto. Qed.

Lemma pos_leqdr : forall x : dreal, ~ x F0 -> leqdr F0 x.
Proof. by move=> x Hx f Hxf; apply/idP => Hf; case: Hx; exact: dd_ideal Hxf. Qed.

Lemma pos_oppdr1 : forall x : dreal, x F0 -> ~ oppdr x F0.
Proof.
by move=> x Hx [f Hf []]; apply: dd_ideal Hx; rewrite -oppF0 leqf_opp2 ltfW.
Qed.

Lemma pos_oppdr2 : forall x : dreal, ~ x F0 -> ~ oppdr x F0 -> eqdr x F0.
Proof.
move: pos_leqdr; split; auto.
by rewrite -(oppdr_opp x) -oppdr0; apply leqdr_opp2; auto.
Qed.

Lemma pos_amuldr : forall x1 x2, ~ amuldr x1 x2 F0.
Proof.
move=> x1 x2 [] f _; move/posf_absdr; rewrite -posfI; case/idP.
by case/andP: (mulF0 (invf f)).
Qed.

Lemma oppdr_cases : forall P : dreal -> Prop,
   (forall x, P (oppdr x) -> P x) -> (forall x : dreal, ~ x F0 -> P x) ->
  forall x, P x.
Proof. move=> P Hopp H0 x; case: (Hclassical (x F0)) pos_oppdr1; auto. Qed.

Lemma amul0dr : forall x, eqdr (amuldr F0 x) F0.
Proof.
move=> x; split=> f; last by apply pos_leqdr; apply pos_amuldr.
case: (dd_ub (absdr x)) => [f1 Hxf1] Hf.
have Hf1 := posf_absdr Hxf1; pose f2 := mulf (invf f1) f.
have Hf2: posf f2 by rewrite /f2 posf_pmull ?posf_inv // -posfI.
exists f2; first by rewrite /= /absds oppdr0; rewrite -posfI in Hf2; split.
apply: dd_ideal Hxf1; rewrite -(leqf_eql (pmulf_inv f1 Hf2)).
rewrite leqf_pmul2l ?posf_inv // /f2 mulfC mulfCA.
by case/andP: (pmulf_inv f Hf1).
Qed.

Lemma muldr_oppl : forall x1 x2, eqdr (muldr (oppdr x1) x2) (oppdr (muldr x1 x2)).
Proof.
move=> x1 x2; elim/oppdr_cases: x1 => x1 Hx1.
  by rewrite -(oppdr_opp (muldr (oppdr x1) x2)) -Hx1 (oppdr_opp x1).
rewrite /muldr (amuldr_opp x1 x2); set y := amuldr x1 x2.
case: (selectdr_cases (pos_muldr x1 x2) y (oppdr y)) => [] [Hx12 Dy];
  case: (selectdr_cases (pos_muldr (oppdr x1) x2) y (oppdr y)) => [] [Hx21 Dy'];
  rewrite Dy Dy' ?(oppdr_opp y) //; rewrite /pos_muldr /= -/F0 in Hx12 Hx21.
- have Dx1: eqdr x1 F0 by apply: pos_oppdr2; rewrite //= Hx21 -Hx12.
  by rewrite /y Dx1 (amul0dr x2) oppdr0.
have Dx1: eqdr x1 F0 by apply: pos_oppdr2 => // Hx1'; case: Hx12; tauto.
by rewrite /y Dx1 (amul0dr x2) oppdr0.
Qed.

Lemma muldr_oppr : forall x1 x2, eqdr (muldr x1 (oppdr x2)) (oppdr (muldr x1 x2)).
Proof.
by move=> x1 x2; rewrite (muldrC x1 (oppdr x2)) (muldr_oppl x2 x1) (muldrC x2 x1).
Qed.

Lemma absdr_amul : forall x1 x2, eqdr (absdr (amuldr x1 x2)) (amuldr x1 x2).
Proof.
move=> x1 x2; split=> f Hf; last by case Hf.
split=> //; case/dd_open: Hf => [f' Hff' Hf']; exists f' => //.
case=> f1; move/posf_absdr=> Hf1; move/posf_absdr.
rewrite posf_pmull ?posf_inv // posf_opp nnegf_0Vpos; case/orP; right.
case: Hf' => f2; move/posf_absdr=> Hf2; move/posf_absdr.
by rewrite posf_pmull ?posf_inv.
Qed.

Lemma amuldrA : forall x1 x2 x3,
  eqdr (amuldr x1 (amuldr x2 x3)) (amuldr (amuldr x1 x2) x3).
Proof.
suffice: forall x1 x2 x3,
   leqdr (amuldr (amuldr x1 x2) x3) (amuldr x1 (amuldr x2 x3)).
- move=> Hrec x1 x2 x3; split=> //.
  rewrite (amuldrC (amuldr x1 x2) x3) (amuldrC x1 (amuldr x2 x3)).
  by rewrite (amuldrC x2 x3) (amuldrC x1 x2).
move=> x1 x2 x3 f3 [f1 Hf1 [[f2 Hf2 Hf3] _]]; exists (mulf f1 f2).
  rewrite (absdr_amul x1 x2); exists f1 => //.
  by apply: ideals_abs Hf2; case/andP: (pmulf_inv f2 (posf_absdr Hf1)).
move/posf_absdr: Hf1 => Hf1; move/posf_absdr: Hf2 => Hf2.
apply: ideals_abs Hf3; rewrite -(leqf_pmul2l Hf2) mulfCA.
rewrite (leqf_eql (pmulf_inv _ Hf2)) -(leqf_pmul2l Hf1) mulfCA.
rewrite (leqf_eql (pmulf_inv f3 Hf1)) mulfA mulfCA.
by rewrite -(posf_pmull f2 Hf1) in Hf2; case/andP: (pmulf_inv f3 Hf2).
Qed.

Lemma eqdr_opp2 : forall x1 x2, eqdr (oppdr x1) (oppdr x2) -> eqdr x1 x2.
Proof. move=> x1 x2 Hx12; rewrite -(oppdr_opp x1) Hx12; exact: oppdr_opp. Qed.

Lemma pos_muldr2 : forall x1 x2 : dreal, ~ x1 F0 -> ~ x2 F0 ->
  eqdr (muldr x1 x2) (amuldr x1 x2).
Proof.
move=> x1 x2 Hx1 Hx2; rewrite /muldr; move: (amuldr x1 x2) => y.
case: (selectdr_cases (pos_muldr x1 x2) y (oppdr y)) => [[_ Dy]|[[]]] //.
split; tauto.
Qed.

Lemma muldrA : forall x1 x2 x3,
  eqdr (muldr x1 (muldr x2 x3)) (muldr (muldr x1 x2) x3).
Proof.
elim/oppdr_cases=> x1 Hx1 x2 x3.
  apply eqdr_opp2; rewrite -(muldr_oppl x1 (muldr x2 x3)).
  by rewrite -(muldr_oppl (muldr x1 x2) x3) -(muldr_oppl x1 x2).
elim/oppdr_cases: x2 => x2 Hx2.
  apply eqdr_opp2; rewrite -(muldr_oppr x1 (muldr x2 x3)).
  rewrite -(muldr_oppl (muldr x1 x2) x3) -(muldr_oppr x1 x2).
  by rewrite -(muldr_oppl x2 x3).
elim/oppdr_cases: x3 => x3 Hx3.
  apply eqdr_opp2; rewrite -(muldr_oppr x1 (muldr x2 x3)).
  by rewrite -(muldr_oppr (muldr x1 x2) x3) -(muldr_oppr x2 x3).
rewrite (pos_muldr2 Hx2 Hx3) (pos_muldr2 Hx1 (@pos_amuldr x2 x3)).
rewrite (pos_muldr2 Hx1 Hx2) (pos_muldr2 (@pos_amuldr x1 x2) Hx3); apply amuldrA.
Qed.

Lemma muldr_addr : forall x1 x2 x3,
 eqdr (muldr x1 (adddr x2 x3)) (adddr (muldr x1 x2) (muldr x1 x3)).
Proof.
move=> x1 x2 x3; set x := adddr x2 x3; elim/oppdr_cases: x1 => x1 Hx1.
  rewrite -(oppdr_opp x1); set y1 := oppdr x1.
  rewrite (muldr_oppl y1 x) (muldr_oppl y1 x2) (muldr_oppl y1 x3).
  rewrite /y1 {}Hx1; exact: oppdr_add.
have Dx: eqdr x (adddr x2 x3) by done.
elim/oppdr_cases: {x2 x3}x (x2) (x3) Dx => x Hx x2 x3 Dx.
  have Dnx: eqdr (oppdr x) (adddr (oppdr x2) (oppdr x3)).
    rewrite Dx; exact: oppdr_add.
  rewrite -(oppdr_opp x) (muldr_oppr x1 (oppdr x)) (Hx _ _ Dnx).
  rewrite (muldr_oppr x1 x2) (muldr_oppr x1 x3).
  rewrite -(oppdr_add (muldr x1 x2) (muldr x1 x3)); exact: oppdr_opp.
move: Hx; rewrite {x}Dx; move: x2 x3.
suffice Hrec: forall x2 x3 : dreal, ~ x2 F0 -> ~ x3 F0 ->
    eqdr (muldr x1 (adddr x2 x3)) (adddr (muldr x1 x2) (muldr x1 x3)).
- suffice Hneg: forall x2 x3 : dreal, x2 F0 -> ~ adddr x2 x3 F0 ->
      eqdr (muldr x1 (adddr x2 x3)) (adddr (muldr x1 x2) (muldr x1 x3)).
  + move=> x2 x3; case (Hclassical (x3 F0)); case (Hclassical (x2 F0)); eauto.
    move=> Hx2 Hx3; rewrite (adddrC (muldr x1 x2) (muldr x1 x3)) (adddrC x2 x3).
    by eauto.
  move=> x2 x3; set x := adddr x2 x3; move/pos_oppdr1=> Hx2 Hx.
  rewrite -(add0dr x3) -(adddrI x2) (adddrC x2 (oppdr x2)).
  rewrite -(adddrA (oppdr x2) x2 x3) -/x (Hrec _ _ Hx2 Hx) (muldr_oppr x1 x2).
  move: (muldr x1 x2) (muldr x1 x) => y2 y.
  by rewrite (adddrA y2 (oppdr y2) y) (adddrI y2) (add0dr y).
move=> x2 x3 Hx2 Hx3; have Hx23: ~ adddr x2 x3 F0.
  move=> [f1 Hx2f1 Hx3f1]; case: Hx3; apply: dd_ideal Hx3f1.
  rewrite addF0 -oppF0 leqf_opp2; apply ltfW; apply/idP => [Hf1].
  by case: Hx2; exact: dd_ideal Hx2f1.
rewrite (pos_muldr2 Hx1 Hx23) (pos_muldr2 Hx1 Hx2) (pos_muldr2 Hx1 Hx3).
apply eqdr_sym; split=> f.
  case=> f1; rewrite (pos_absdr Hx23); move=> Hxf1 [f2 Hf2 Hf3].
  have Hf1 := posf_absdr Hxf1; exists (mulf f1 f2).
    by exists f1; rewrite // (pos_absdr Hx2) (eqf_dr x2 (pmulf_inv f2 Hf1)).
  exists f1; rewrite // (pos_absdr Hx3); apply: dd_ideal Hf3.
  rewrite (leqf_eqr (mulf_addr (invf f1) (oppf (mulf f1 f2)) f)) leqf_add2r.
  by rewrite -mulf_oppr; case/andP: (pmulf_inv (oppf f2) Hf1).
case=> f2; case=> f12; rewrite (pos_absdr Hx2) => Hxf12 Hxf2.
case=> f13; rewrite (pos_absdr Hx3) => Hxf13 Hxf3.
have [f1 Hxf1 [Hf12 Hf13]]: exists2 f1, absdr x1 f1 & leqf f1 f12 /\ leqf f1 f13.
  case: (leqf_cases f12 f13) => Hf123.
    by exists f12; last by split; first exact: leqff.
  by exists f13; last by split; [ exact: ltfW | exact: leqff ].
exists f1; rewrite // (pos_absdr Hx23); have Hf1 := posf_absdr Hxf1.
exists (mulf (invf f1) f2).
  have Hf120 := posf_absdr Hxf12; have Hf2: posf f2.
    move: Hxf2; rewrite -(pos_absdr Hx2); move/posf_absdr.
    by rewrite posf_pmull ?posf_inv.
  apply: dd_ideal Hxf2; rewrite -(leqf_pmul2l Hf120) mulfCA.
  rewrite (leqf_eql (pmulf_inv f2 Hf120)) -(leqf_pmul2l Hf1) !mulfA -!(mulfC f2).
  by rewrite (leqf_pmul2l Hf2) mulfC (leqf_eqr (pmulf_inv f12 Hf1)).
apply: dd_ideal (Hxf3); move: Hxf3; rewrite -(pos_absdr Hx3); move/posf_absdr.
rewrite -mulf_oppr -(leqf_eqr (mulf_addr (invf f1) (oppf f2) f)).
move: (addf (oppf f2) f) => f3 Hf3'; have Hf130 := posf_absdr Hxf13.
have Hf3: posf f3 by move: Hf3'; rewrite posf_pmull ?posf_inv.
rewrite -(leqf_pmul2l Hf130) mulfCA.
rewrite (leqf_eql (pmulf_inv f3 Hf130)) -(leqf_pmul2l Hf1) !mulfA -!(mulfC f3).
by rewrite (leqf_pmul2l Hf3) mulfC (leqf_eqr (pmulf_inv f13 Hf1)).
Qed.

Lemma mul1dr : forall x, eqdr (muldr F1 x) x.
Proof.
elim/oppdr_cases=> x Hx; first by apply eqdr_opp2; rewrite -Hx (muldr_oppr F1 x).
have HpF1: ~ fracdr F1 F0 by done.
rewrite (pos_muldr2 HpF1 Hx); split=> f.
  move/dd_open=> [f1 Hff1 Hx1]; rewrite (amuldrC F1 x).
  exists f1; first by rewrite (pos_absdr Hx).
  have Hf1: (posf f1) by move: Hx1; rewrite -(pos_absdr Hx); exact: posf_absdr.
  rewrite (pos_absdr HpF1) /= /fracs /ltf -(leqf_eqr (pmulf_inv F1 Hf1)).
  by rewrite mulf1 leqf_pmul2l ?posf_inv.
case=> [f1 Hxf1 Hxf]; move: (Hxf); rewrite (pos_absdr Hx); apply: dd_ideal.
rewrite -(leqf_eqr (pmulf_inv f (posf_absdr Hxf1))) mulfCA.
move: (mulf (invf f1) f) (posf_absdr Hxf) Hxf1 => y Hy.
rewrite (pos_absdr HpF1) mulfC -{1}[y]mulf1 leqf_pmul2l //; exact: ltfW.
Qed.

Lemma muldr_monotony : forall x x1 x2, leqdr F0 x -> leqdr x1 x2 ->
  leqdr (muldr x x1) (muldr x x2).
Proof.
move=> /= x x1 x2 Hx Hx12; set y1 := muldr x x1; set y2 := muldr x x2.
rewrite -(add0dr y2) -(adddrI y1) -(adddrA y1 (oppdr y1) y2) {2 3}/y1 -(add0dr y1).
rewrite -(muldr_oppr x x1) -/y1 (adddrC F0 y1); apply adddr_monotony.
move: {y1 Hx12}(adddr_monotony (x1 := oppdr x1) Hx12).
rewrite {}/y2 -(muldr_addr x (oppdr x1) x2) (adddrC (oppdr x1) x1) (adddrI x1).
move: {x1 x2}(adddr (oppdr x1) x2) => y Hy.
have Hp0: forall z, leqdr F0 z -> ~ z F0.
  by move=> z Hz Hz0; move: (Hz _ Hz0); rewrite /= /fracs ltff.
rewrite (pos_muldr2 (Hp0 _ Hx) (Hp0 _ Hy)); apply pos_leqdr; exact: pos_amuldr.
Qed.

Lemma invdr_opp : forall x, eqdr (invdr (oppdr x)) (oppdr (invdr x)).
Proof.
move=> x; rewrite /invdr; set y := ainvdr x.
have Dy': eqdr (ainvdr (oppdr x)) y.
  apply: {y}eqdr_sup => y z Dy.
  rewrite (amuldrC y (oppdr x)) (amuldr_opp x y) (amuldrC x y) Dy; tauto.
rewrite {}Dy'; case: (selectdr_cases (x F0) (oppdr y) y) => [] [Hx Ey];
  case: (selectdr_cases (oppdr x F0) (oppdr y) y) => [] [Hx' Ey'];
  rewrite {}Ey {}Ey' ?(oppdr_opp y) //; try by case/pos_oppdr1: Hx.
suffice ->: eqdr y F0 by rewrite oppdr0.
suffice HxF1: ~ has_supdr0 (fun z => amuldr z x F1).
  split=> f; rewrite /y /ainvdr /= /supds /IF_then_else; tauto.
move=> [[f [f' Hff' Hf']] _]; case/idP: Hff'; apply ltfW; apply (Hf' f).
by rewrite (amuldrC f x) (pos_oppdr2 Hx Hx') (amul0dr f).
Qed.

Lemma muldrI : forall x, ~ eqdr x F0 -> eqdr (muldr x (invdr x)) F1.
Proof.
elim/oppdr_cases=> x Hx Hx0.
  rewrite -(oppdr_opp (invdr x)) -(invdr_opp x) (muldr_oppr x (invdr (oppdr x))).
  rewrite -(muldr_oppl x (invdr (oppdr x))); apply: Hx => Hx'.
  by case: Hx0; apply: eqdr_opp2; rewrite oppdr0.
rewrite /invdr; set y := ainvdr x.
case: (selectdr_cases (x F0) (oppdr y) y) => [[Hx' _]|[_ Dy]]; first by case Hx.
rewrite Dy; case: (Hclassical (exists2 f, posf f & ~ x f));
  last by move=> Hx'; case: Hx0; apply: (pos_oppdr2 Hx) => [[f Hf Hxf]];
          case: Hx'; exists (oppf f); first by rewrite posf_opp -nnegfI.
move=> [f0 Hf0 Hxf0]; pose aix z := amuldr z x F1.
have Haix0: aix F0 by rewrite /aix (amul0dr x).
have Haix: has_supdr aix.
  split; first by exists (F0 : dreal).
  exists (invf f0 : dreal)=> x'; rewrite /aix (amuldrC x' x).
  move=> [f Hxf]; have Hf := posf_absdr Hxf.
  move=> [H _] f' Hf'; apply: dd_ideal H; move/ltfW: Hf'; apply: leqf_trans.
  rewrite mulf1 -(leqf_pmul2l Hf) -(leqf_pmul2l Hf0) mulfC -mulfA mulfCA.
  rewrite (leqf_eql (pmulf_inv f0 Hf)) (mulfC f) mulfCA.
  rewrite (leqf_eqr (pmulf_inv f Hf0)); apply ltfW; apply/idP => [Hff0].
  by case: Hxf0; case: Hxf => [H _]; exact: dd_ideal H.
have Hyub: ubdr aix y by exact: ubdr_sup.
have Hysup: forall z, ubdr aix z -> leqdr y z by move=> z Hz; exact: leqdr_sup_ub.
have Hy0: ~ y F0.
  by move/dd_open=> [f' Hf'0 Hyf']; case/idP: (Hyub _ Haix0 _ Hyf'); exact: ltfW.
rewrite (pos_muldr2 Hx Hy0); split=> f.
  move=> Hf; have Hpf: posf f by rewrite -posfI; exact: leqf_lt_trans Hf.
  pose e := addf F1 (oppf (invf f)); have He: posf e.
    rewrite -posfI /ltf /e addfC -(leqf_eqr (addf_inv (invf f) F0)) leqf_add2l.
    rewrite addF0 -[invf f]mulf1 -(leqf_pmul2l Hpf) mulf1 mulfCA.
    by rewrite (leqf_eqr (pmulf_inv F1 Hpf)).
  pose e0 := mulf e f0.
  have: fracdr F0 e0 by rewrite /= /fracs posfI /e0 posf_pmull.
  rewrite -(adddrI x); move=> [f1 Hxf1 [f2 Hf12 Hxf2]].
  have Hf10: ltf f0 f1 by apply/idP => [Hf10]; case: Hxf0; exact: dd_ideal Hxf1.
  exists f1; first by rewrite (pos_absdr Hx).
  have Hf1: posf f1.
    by move: Hf0 (ltfW Hf10); rewrite -!posfI; exact: ltf_leq_trans.
  have Hf2: posf (oppf f2).
    rewrite posf_opp -nnegfI; apply: (ltf_leq_trans Hf12).
    rewrite -(leqf_eqr (addf_inv f1 F0)) addF0 leqf_add2l.
    apply: leqf_trans (ltfW Hf10); rewrite -[f0]addF0 /e0 mulfC.
    rewrite /e (leqf_eql (mulf_addr f0 F1 (oppf (invf f)))) mulf1 leqf_add2l.
    rewrite mulf_oppr -oppF0 leqf_opp2; apply ltfW.
    by rewrite posfI posf_pmull ?posf_inv.
  suffice: ubdr aix (invf (oppf f2)).
    rewrite (pos_absdr Hy0); move/Hysup; apply.
    rewrite /= /fracs /ltf -(leqf_pmul2l Hf1) mulfCA (leqf_eql (pmulf_inv f Hf1)).
    rewrite mulfC -(leqf_eql (pmulf_inv f Hf2)) leqf_pmul2l ?posf_inv //.
    rewrite mulfC -(leqf_eqr (pmulf_inv f1 Hpf)) mulfCA leqf_pmul2l ?posf_inv //.
    rewrite -leqf_opp2 oppf_opp -mulf_oppl mulfC; apply: (ltf_leq_trans Hf12).
    rewrite -(leqf_add2l f1) addfCA (leqf_eql (addf_inv f1 e0)).
    rewrite -{1}[f1]mulf1 -(leqf_eqr (mulf_addr f1 F1 (oppf (invf f)))) -/e.
    by rewrite mulfC /e0 leqf_pmul2l // ltfW.
  move=> z; rewrite /aix (amuldrC z x); move=> [f3 Hxf3 [Hf3 _]] f4 Hf4.
  apply: dd_ideal Hf3; move/ltfW: Hf4; apply: {f4}leqf_trans.
  have Hf3 := posf_absdr Hxf3; rewrite -(leqf_pmul2l Hf3) mulfCA.
  rewrite (leqf_eql (pmulf_inv F1 Hf3)) mulfC -(leqf_eql (pmulf_inv F1 Hf2)).
  rewrite mulf1 leqf_pmul2l ?posf_inv //; apply ltfW; apply/idP => Hf23.
  by case: Hxf2; apply: (dd_ideal Hf23); case: Hxf3.
move=> [f1 Hxf1]; set f2 := mulf (invf f1) f => Hyf2; apply/idP => Hf.
have Hf1 := posf_absdr Hxf1; have Hf2 := posf_absdr Hyf2.
suffice: aix f2.
  by case: Hyf2 => [Hyf2 _] Hxf2; case/idP: (Hyub _ Hxf2 _ Hyf2); exact: leqff.
rewrite /aix (amuldrC f2 x); move/dd_open: Hxf1 => [f3 Hf13 Hxf3].
have Hf3 := posf_absdr Hxf3.
have Hf20: ~ f2 F0 by case/idP; apply ltfW; rewrite posfI.
exists f3; rewrite // (pos_absdr Hf20) /= /fracs /ltf.
rewrite -(leqf_pmul2l Hf3) mulfCA (leqf_eql (pmulf_inv F1 Hf3)).
apply: ltf_leq_trans Hf; rewrite /ltf -(leqf_eql (pmulf_inv f Hf1)) mulfCA -/f2.
by rewrite -!(mulfC f2) leqf_pmul2l.
Qed.

Theorem dedekind_reals : real_model.
Proof.
apply: (RealModel
          (@RealAxioms (RealStructure _ _ _ _ _ _ _ _) leqdrr leqdr_trans
             ubdr_sup supdr_total adddr_monotony adddrC adddrA add0dr adddrI
             muldr_monotony muldrC muldrA muldr_addr mul1dr muldrI _)) => /=.
by case=> [H _]; move: (H (invf F2) (erefl _)).
Qed.

End DedekindReals.

Set Strict Implicit.
Unset Implicit Arguments.


