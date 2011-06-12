(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import znat.
Require Import frac.
Require Import real.
Require Import realsyntax.
Require Import Setoid.
Require Import realprop.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* A proof that the real axiomatisation is categorical -- i.e., *)
(* that the result dedekind construction is essentially unique. *)

Section RealsCategorical.

Hint Resolve eqr_refl leqrr.
Notation fracr_leqP := (fracr_leqPx _ _ _).

Open Scope real_scope.

Section RealMorphismLiftsAxioms.

(* A monomorphism lifts back the real axioms, and preserves the rationals *)

Variables (R : real_structure) (R' : real_model) (phi : R -> R').
Hypothesis Hphi : real_structure_morphism phi.

Remark phi_leq : forall x1 x2, phi x1 <= phi x2 <-> x1 <= x2.
Proof. by case Hphi. Qed.

Remark phi_leq_inj : forall x1 x2, phi x1 <= phi x2 -> x1 <= x2.
Proof. by move=> x1 x2; rewrite (phi_leq x1 x2). Qed.

Lemma morphr_eq : forall x1 x2, phi x1 == phi x2 <-> x1 == x2.
Proof. move=> x1 x2; rewrite /eqr (phi_leq x1 x2) (phi_leq x2 x1); tauto. Qed.

Notation phi_eq := morphr_eq.

Remark phi_eq_inj : forall x1 x2, phi x1 == phi x2 -> x1 == x2.
Proof. by move=> x1 x2; rewrite (phi_eq x1 x2). Qed.

Remark phi_add : forall x1 x2, phi (x1 + x2) == phi x1 + phi x2.
Proof. by case Hphi. Qed.

Remark phi_opp : forall x, phi (- x) == - phi x.
Proof. by case Hphi. Qed.

Remark phi_mul : forall x1 x2 : R, phi (x1 * x2) == phi x1 * phi x2.
Proof. by case Hphi. Qed.

Remark axphi0 : phi 0 == 0.
Proof. by case Hphi. Qed.
Let phi0 := axphi0.

Remark axphi1 : phi 1 == 1.
Proof. by case Hphi. Qed.
Let phi1 := axphi1.

Remark phi_leqrr : forall x : R, x <= x.
Proof. move=> x; apply phi_leq_inj; apply leqrr. Qed.

Remark phi_leqr_trans : forall x1 x2 x3 : R, x1 <= x2 -> x2 <= x3 -> x1 <= x3.
Proof.
move=> x1 x2 x3; rewrite -(phi_leq x1 x2) -(phi_leq x2 x3) -(phi_leq x1 x3).
apply: leqr_trans.
Qed.

Lemma morphr_has_sup : forall E : R -> Prop, has_supr E -> has_supr (imager phi E).
Proof.
move=> E [[x Hx] [z Hz]]; split; first by exists (phi x); exists x.
by exists (phi z); move=> _ [y <- Hy]; rewrite (phi_leq y z); exact: Hz.
Qed.
Hint Resolve morphr_has_sup.

Remark phi_ubr_sup : forall E : R -> Prop, has_supr E -> ubr E (sup E).
Proof.
move=> E HE x Hx.
have [_ HE'E]: phi (sup E) == sup (imager phi E) by case Hphi; auto.
apply phi_leq_inj; apply: leqr_trans HE'E; apply (supr_upper_bound R'); auto.
by exists x.
Qed.

Remark phi_leqr_total : forall x1 x2 : R, x1 <= x2 \/ x2 <= x1.
Proof.
move=> x1 x2; rewrite -(phi_leq x1 x2) -(phi_leq x2 x1); exact:leqr_total.
Qed.

Remark phi_supr_total : forall (x : R) E, has_supr E -> boundedr x E \/ sup E <= x.
Proof.
move=> x E HE.
have [HEE' _]: phi (sup E) == sup (imager phi E) by case Hphi; auto.
case: (supr_total (phi x) (morphr_has_sup HE)).
  by move=> [_ [y <- Hy]]; rewrite (phi_leq x y) => Hxy; left; exists y.
by move/(leqr_trans HEE'); rewrite (phi_leq (sup E) x); right.
Qed.

Remark phi_addr_monotony : forall x1 x2 x3 : R, x2 <= x3 -> x1 + x2 <= x1 + x3.
Proof.
move=> x1 x2 x3 Hx23; apply phi_leq_inj.
case: (phi_add x1 x3) => [_]; apply: leqr_trans.
case: (phi_add x1 x2) => [H _]; apply: leqr_trans H _.
by apply (addr_monotony R'); rewrite (phi_leq x2 x3).
Qed.

Remark phi_mulr_monotony : forall x1 x2 x3 : R, x1 >= 0 -> x2 <= x3 ->
  x1 * x2 <= x1 * x3.
Proof.
move=> x1 x2 x3 Hx1 Hx23; apply phi_leq_inj.
case: (phi_mul x1 x3) => _; apply: leqr_trans.
case: (phi_mul x1 x2) => H _; apply: leqr_trans H _.
apply (mulr_monotony R'); last by rewrite (phi_leq x2 x3).
by case: phi0 => _ H; apply: leqr_trans H _; rewrite (phi_leq 0 x1).
Qed.

Remark phi_add0r : forall x : R, 0 + x == x.
Proof.
move=> x; apply phi_eq_inj; apply: eqr_trans (add0r (phi x)).
apply: (eqr_trans (phi_add 0 x)).
apply addr_morphism; [ exact phi0 | exact: eqr_refl ].
Qed.

Remark phi_addrC : forall x1 x2 : R, x1 + x2 == x2 + x1.
Proof.
move=> x1 x2; apply phi_eq_inj; apply: (eqr_trans (phi_add x1 x2)).
apply: (eqr_trans (addrC _ _)); apply eqr_sym; exact: phi_add.
Qed.

Remark phi_addrA : forall x1 x2 x3 : R, x1 + (x2 + x3) == x1 + x2 + x3.
Proof.
move=> x1 x2 x3; apply phi_eq_inj; apply: (eqr_trans (phi_add _ _)).
apply: eqr_trans  (eqr_sym (phi_add _ _)).
apply: (eqr_trans (addr_morphism (eqr_refl _) (phi_add _ _))).
apply: eqr_trans  (eqr_sym (addr_morphism (phi_add _ _) (eqr_refl _))).
exact: addrA.
Qed.

Remark phi_subrr : forall x : R, x - x == 0.
Proof.
move=> x; apply phi_eq_inj; apply: (eqr_trans (phi_add _ _)).
apply: (eqr_trans _ (eqr_sym phi0)); apply: eqr_trans (subrr (phi x)).
by apply addr_morphism; [ exact: eqr_refl | exact: phi_opp ].
Qed.

Remark phi_mulrC : forall x1 x2 : R, x1 * x2 == x2 * x1.
Proof.
move=> x1 x2; apply phi_eq_inj; apply: (eqr_trans (phi_mul x1 x2)).
apply: (eqr_trans (mulrC _ _)); apply eqr_sym; exact: phi_mul.
Qed.

Remark phi_mulrA : forall x1 x2 x3 : R, x1 * (x2 * x3) == x1 * x2 * x3.
Proof.
move=> x1 x2 x3; apply phi_eq_inj; apply: (eqr_trans (phi_mul _ _)).
apply: eqr_trans  (eqr_sym (phi_mul _ _)).
apply: (eqr_trans (mulr_morphism (eqr_refl _) (phi_mul _ _))).
apply: eqr_trans (eqr_sym (mulr_morphism (phi_mul _ _) (eqr_refl _))).
exact: mulrA.
Qed.

Remark phi_mulr_addr : forall x1 x2 x3 : R, x1 * (x2 + x3) == x1 * x2 + x1 * x3.
Proof.
move=> x1 x2 x3; apply phi_eq_inj; apply: (eqr_trans (phi_mul _ _)).
apply: eqr_trans (eqr_sym (phi_add _ _)).
apply: (eqr_trans (mulr_morphism (eqr_refl _) (phi_add _ _))).
apply: eqr_trans (eqr_sym (addr_morphism (phi_mul _ _) (phi_mul _ _))).
exact: mulr_addr.
Qed.

Remark phi_mul1r : forall x : R, 1 * x == x.
Proof.
move=> x; apply phi_eq_inj; apply: (eqr_trans (phi_mul _ _)).
apply: eqr_trans (mul1r (phi x)).
apply mulr_morphism; [ exact phi1 | exact: eqr_refl ].
Qed.

Lemma morphr_neq0 : forall x, x != 0 -> phi x != 0.
Proof.
by move=> x H H'; case: H; apply phi_eq_inj; apply: eqr_trans (eqr_sym phi0).
Qed.

Remark phi_divrr : forall x : R, x != 0 -> x / x == 1.
Proof.
move=> x Hx; apply phi_eq_inj; apply: (eqr_trans (phi_mul _ _)).
apply: (eqr_trans _ (eqr_sym phi1)); apply: eqr_trans (divrr (morphr_neq0 Hx)).
by apply mulr_morphism; [ exact: eqr_refl | case Hphi; auto ].
Qed.

Remark phi_neqr10 : (1 : R) != 0.
Proof.
rewrite /= -(phi_eq (real1 _) (real0 _)); move=> H10; case (neqr10 R').
apply: eqr_trans phi0; apply: eqr_trans H10; apply eqr_sym; exact phi1.
Qed.

Theorem real_morphism_lifts_axioms : real_axioms R.
Proof.
exact
 (RealAxioms phi_leqrr phi_leqr_trans phi_ubr_sup phi_supr_total
    phi_addr_monotony phi_addrC phi_addrA phi_add0r phi_subrr
    phi_mulr_monotony phi_mulrC phi_mulrA phi_mulr_addr phi_mul1r phi_divrr
    phi_neqr10).
Qed.

Lemma morphr_nat : forall n, phi (natr R n) == natr R' n.
Proof.
move=> [|n] /=; first by exact phi0.
elim: n (1 : R) (1 : R') phi1 => [|n Hrec] x x' Dx' //=; apply: Hrec.
by apply: (eqr_trans (phi_add _ _)); apply addr_morphism; first exact phi1.
Qed.

Lemma morphr_znat : forall m, phi (znatr R m) == znatr R' m.
Proof.
move=> [n|n]; rewrite /znatr; first exact: morphr_nat.
apply: (eqr_trans (phi_opp _)); apply oppr_morphism; exact: morphr_nat.
Qed.

Lemma morphr_frac : forall f, eqr (phi (fracr R f)) (fracr R' f).
Proof.
move=> [d m]; apply: (eqr_trans (phi_mul _ _)).
apply: mulr_morphism; first exact: morphr_znat.
set dd := natr R (S d); set dd' := natr R' (S d).
have Hdd': dd' > 0 by exact: ltr0Sn.
have Edd': phi dd == dd' by exact: morphr_nat.
have Hdd: phi dd > 0 by apply: (ltr_leq_trans Hdd'); case Edd'.
apply: (pmulr_injl Hdd'); apply eqr_sym.
apply: (eqr_trans (divrr (gtr_neq Hdd'))).
apply: (eqr_trans (eqr_sym (divrr (gtr_neq Hdd)))); apply: (mulr_morphism Edd').
suffice Hdd0: dd != 0 by apply eqr_sym; case Hphi; auto.
rewrite -(phi_eq dd 0) => Hdd0; case/gtr_neq: Hdd; exact: eqr_trans phi0.
Qed.

End RealMorphismLiftsAxioms.

(* The categorical structure of the models of the reals. *)

Theorem real_morphism_comp : forall (R R' : real_structure) (R'' : real_model)
                                    (phi1 : R -> R') (phi2 : R' -> R''),
  real_structure_morphism phi1 -> real_structure_morphism phi2 ->
  real_structure_morphism (fun x => phi2 (phi1 x)).
Proof.
move=> R R' R'' phi1 phi2 Hphi1 Hphi2; move: phi1 (phi2) Hphi1 (Hphi2).
pose R'S := RealModel (real_morphism_lifts_axioms Hphi2).
rewrite -[R']/(R'S : real_structure).
move: {R' phi2 Hphi2}R'S => R' phi1 phi2 Hphi1 Hphi2.
set phi := fun x => phi2 (phi1 x).
have Ephi: forall x1 x2 x3, phi1 x1 == x2 -> phi2 x2 == x3 -> phi x1 == x3.
  move=> x1 x2 x3 Dx1.
  apply: eqr_trans; case (morphr_eq Hphi2 (phi1 x1) x2); tauto.
have Hsup: forall E, has_supr E -> phi (sup E) == sup (imager phi E).
  move=> E HE; apply: (Ephi _ _ _ (morphr_sup Hphi1 HE)).
  set E' := imager phi1 E; have HE': has_supr E' by exact: morphr_has_sup.
  apply: (eqr_trans (morphr_sup Hphi2 HE')).
  apply supr_morphism; first exact: morphr_has_sup.
  move=> x''; split; first by move=> [_ <- [x <- Hx]] {x''}; exists x.
  by move=> [x <- Hx]; exists (phi1 x); last by exists x.
split; auto.
- move=> x1 x2; rewrite -(morphr_leq Hphi1 x1 x2); exact: (morphr_leq Hphi2).
- move=> x1 x2; exact: Ephi (morphr_add Hphi1 _ _) (morphr_add Hphi2 _ _).
- exact: Ephi (morphr_0 Hphi1) (morphr_0 Hphi2).
- move=> x; exact: Ephi (morphr_opp Hphi1 _) (morphr_opp Hphi2 _).
- move=> x1 x2; exact: Ephi (morphr_mul Hphi1 _ _) (morphr_mul Hphi2 _ _).
- exact: Ephi (morphr_1 Hphi1) (morphr_1 Hphi2).
move=> x Hx; apply: (Ephi _ _ _ (morphr_inv Hphi1 Hx) (morphr_inv Hphi2 _)).
exact: (morphr_neq0 Hphi1).
Qed.

Theorem real_morphism_id : forall R : real_model,
  real_structure_morphism (fun x : R => x).
Proof.
move=> R; split; try tauto; auto; move=> E HE; apply supr_morphism; auto.
by move=> x; split; [ exists x | move=> [x' <-] ].
Qed.

Section CanonicalRealMorphism.

(* There is a (canonical) monomorphism between two real structures. *)

Variable R R' : real_model.

Inductive morphr_segment (x : R) : R' -> Prop :=
  Morphr_segment : forall f, fracr R f < x -> morphr_segment x (fracr R' f).

Let psi x := sup (morphr_segment x).

Remark psi_has_sup : forall x, has_supr (morphr_segment x).
Proof.
move=> x; split.
  by case: (fracr_dense (ltPrr x)) => [f _ Hfx]; exists (fracr R' f); split.
case: (fracr_dense (ltrSr x)) => [f Hxf _].
exists (fracr R' f); move=> _ [f' Hf']; apply: fracr_leqP.
by apply/(fracr_leqPx R _ _); apply ltrW; exact: ltr_trans Hxf.
Qed.

Remark psi_is_ub : forall x f, fracr R f < x -> fracr R' f < psi x.
Proof.
move=> x f; move/fracr_dense=> [f' Hff' Hf'x].
apply: (ltr_leq_trans (elimN fracr_leqP (introN fracr_leqP Hff'))).
by case: (psi_has_sup x) => [_ Hhi]; apply: (ubr_sup Hhi); split.
Qed.

Remark psi_leq_ub : forall x y', ubr (morphr_segment x) y' -> psi x <= y'.
Proof. by move=> x y'; apply: leqr_sup_ub; case: (psi_has_sup x). Qed.

Remark psi_frac : forall f, psi (fracr R f) == fracr R' f.
Proof.
move=> f; have Hf: psi (fracr R f) <= fracr R' f.
  apply: psi_leq_ub => [_ [f' Hf']]; apply: fracr_leqP.
  by apply/(fracr_leqPx R _ _); exact: ltrW.
move: Hf; rewrite (leqr_eqVlt (psi (fracr R f)) (fracr R' f)).
case; first done; case/fracr_dense=> [f' Hf'f Hff'].
case: Hf'f; apply ltrW; apply psi_is_ub.
by move/(fracr_leqPx R _ _): (introN fracr_leqP Hff').
Qed.

Remark psi_leq : forall x1 x2, psi x1 <= psi x2 <-> x1 <= x2.
Proof.
move=> x1 x2; split=> Hx12.
  case: (reals_classic R (x1 <= x2)); first done.
  move/fracr_dense=> [f Hx2f Hfx1].
  case/psi_is_ub: Hfx1; apply: (leqr_trans Hx12).
  apply: psi_leq_ub => [y [f' Hf']] {y}.
  apply: fracr_leqP; apply/(fracr_leqPx R _ _).
  by apply ltrW; exact: ltr_trans Hx2f.
apply: psi_leq_ub => [y [f Hf]] {y}.
by apply ltrW; apply psi_is_ub; exact: ltr_leq_trans Hx12.
Qed.

Remark psi_eq : forall x1 x2, psi x1 == psi x2 <-> x1 == x2.
Proof.
move=> x1 x2; rewrite /eqr (psi_leq x1 x2) (psi_leq x2 x1); tauto.
Qed.

Remark psi_0 : psi 0 == 0.
Proof.
apply: eqr_trans (fracr0 R'); apply: eqr_trans (psi_frac F0).
rewrite (psi_eq 0 (fracr R F0)); apply: eqr_sym; exact: fracr0.
Qed.

Remark psi_pos : forall x, psi x <= 0 <-> x <= 0.
Proof.
by move=> x; rewrite -(psi_leq x 0); case: psi_0 leqr_trans; split; eauto.
Qed.

Remark psi_opp : forall x, psi (- x) == - psi x.
Proof.
move=> x; split.
  apply: psi_leq_ub => [_ [f Hf]]; case: (fracr_opp R' (oppf f)); rewrite oppf_opp.
  move=> H _; apply: leqr_trans H _.
  rewrite (leqr_opp2 (fracr R' (oppf f)) (psi x)).
  case: (psi_frac (oppf f)) => [H _]; apply: leqr_trans H.
  rewrite (psi_leq x (fracr R (oppf f))).
  rewrite -(leqr_opp2 (fracr R (oppf f)) x); apply: leqr_trans (ltrW Hf).
  by case (fracr_opp R (oppf f)); rewrite oppf_opp.
case: (reals_classic R (- psi x <= psi (- x))); first done.
move/fracr_dense=> [f Hxf []]; rewrite -[f]oppf_opp.
case: (fracr_opp R' (oppf f)) => _; apply: leqr_trans.
rewrite (leqr_opp2 (psi x) (fracr R' (oppf f))).
apply: ltrW; apply psi_is_ub; rewrite -(leqr_opp2 (fracr R (oppf f)) x).
case: (fracr_opp R (oppf f)) => [H _]; apply: ltr_leq_trans H.
rewrite oppf_opp -(psi_leq (fracr R f) (oppr x)).
by apply: (ltr_leq_trans Hxf); case: (psi_frac f).
Qed.

Remark psi_add : forall x1 x2, psi (x1 + x2) ==  psi x1 + psi x2.
Proof.
suffice Hrec: forall x1 x2, psi (x1 + x2) <= psi x1 + psi x2.
  move=> x1 x2; split; auto.
  rewrite -(leqr_add2r (psi (- x2)) (psi x1 + psi x2) (psi (x1 + x2))).
  apply: leqr_trans (Hrec _ _); apply leqr_trans with (psi x1).
    apply: eqr_leq; apply: (eqr_trans (eqr_sym (addrA _ _ _))).
    apply: eqr_trans (eqr_trans (addrC _ _) (add0r _)).
    apply addr_morphism; auto; apply: eqr_trans (subrr (psi x2)).
    by apply addr_morphism; last exact: psi_opp.
  rewrite (psi_leq x1 (x1 + x2 - x2)).
  apply: eqr_leq; apply: eqr_trans (addrA _ _ _); apply: eqr_sym.
  apply: eqr_trans (eqr_trans (addrC _ _) (add0r _)).
  by apply addr_morphism; last exact: subrr.
move=> x1 x2; apply: psi_leq_ub => [_ [f Hf]]; pose y1 := fracr R f - x2.
have Hy: y1 < x1.
  rewrite -(leqr_add2r x2 x1 y1); apply: leqr_lt_trans Hf; apply eqr_leq.
  apply: (eqr_trans (eqr_sym (addrA _ _ _))); apply: (eqr_trans (addrC _ _)).
  apply: (eqr_trans (eqr_sym (addrA _ _ _))); exact: addr_inv.
case: (fracr_dense Hy) => [f1 Hy1f1 Hf1x1].
pose f2 := addf f (oppf f1); have Hf2: fracr R f2 < x2.
  case: (fracr_add R f (oppf f1)) => H _; apply: leqr_lt_trans H _.
  rewrite -(leqr_add2l (fracr R f1) x2 (fracr R f + fracr R (oppf f1))).
  apply leqr_lt_trans with (fracr R f).
    apply eqr_leq; apply: (eqr_trans (addrA _ _ _)).
    apply: eqr_trans (addr_inv (fracr R f1) _).
    by apply: (eqr_trans (addrC _ _)); apply addr_morphism; first exact: fracr_opp.
  rewrite -(leqr_add2r (- x2) (fracr R f1 + x2) (fracr R f)).
  apply: (ltr_leq_trans Hy1f1); apply eqr_leq; apply eqr_sym.
  apply: (eqr_trans (eqr_sym (addrA _ _ _))); apply: (eqr_trans (addrC _ _)).
  apply: (eqr_trans (eqr_sym (addrA _ _ _))); apply: (eqr_trans (addrCA _ _ _)).
  exact: addr_inv.
apply leqr_trans with (fracr R' f1 + fracr R' f2).
case: (fracr_add R' f1 f2) => [H _]; apply: leqr_trans H; apply: fracr_leqP.
  by rewrite /f2 addfA addfC; case/andP: (addf_inv f1 f).
apply leqr_trans with (psi x1 + fracr R' f2).
  rewrite (leqr_add2r (fracr R' f2) (fracr R' f1) (psi x1)).
  by apply: ltrW; exact: psi_is_ub.
rewrite (leqr_add2l (psi x1) (fracr R' f2) (psi x2)).
by apply: ltrW; exact: psi_is_ub.
Qed.

Remark psi_1 : psi 1 == 1.
Proof.
apply: eqr_trans (fracr1 R'); apply: eqr_trans (psi_frac F1).
rewrite (psi_eq 1 (fracr R F1)); apply: eqr_sym; exact: fracr1.
Qed.

Remark psi_pinv : forall x, x > 0 -> psi (/ x) == / psi x.
Proof.
move=> x Hx; have Hx': 0 < psi x by rewrite (psi_pos x).
split.
  apply: psi_leq_ub => [_ [f Hfx]].
  case Hf: (negb (posf f)).
    by apply: (leqr_trans (fracr_posPx R' _ Hf)); apply ltrW; apply posr_inv.
  rewrite -posf_inv in Hf; move/negbEf: Hf => Hf.
  move: (fracr_pinv R' Hf) (fracr_pinv R Hf); rewrite !invf_inv.
  move=> [H _] [_ Hf'x]; apply: leqr_trans H _.
  move/(fracr_posPx R _): Hf (Hf) => Hf; move/(fracr_posPx R' _)=> Hf'. 
  rewrite (leqr_pinv2 Hf' Hx').
  case: (psi_frac (invf f)) => [H _]; apply: leqr_trans H.
  rewrite (psi_leq x (fracr R (invf f))) -(leqr_pinv2 Hf Hx).
  exact: leqr_trans (ltrW Hfx).
case: (reals_classic R (/ psi x <= psi (/ x))); first done.
move/fracr_dense=> [f Hxf []].
have Hf: posf (invf f).
  rewrite posf_inv; apply/(fracr_posPx R' _); apply: ltr_trans Hxf.
  by rewrite (psi_pos (/ x)); exact: posr_inv.
move: (fracr_pinv R' Hf) (fracr_pinv R Hf); rewrite !invf_inv.
move=> [_ H] [Hf'x _]; apply: leqr_trans H; apply ltrW.
move/(fracr_posPx R _): Hf (Hf) => Hf; move/(fracr_posPx R' _)=> Hf'. 
rewrite (leqr_pinv2 Hf' Hx'); apply psi_is_ub.
rewrite -(leqr_pinv2 Hf Hx); apply: ltr_leq_trans Hf'x.
rewrite -(psi_leq (fracr R f) (invr x)); apply: (ltr_leq_trans Hxf).
by case: (psi_frac f).
Qed.

Remark psi_inv : forall x, x != 0 -> psi (/ x) ==  / psi x.
Proof.
move=> x; case/ltr_total=> Hx; last exact: psi_pinv.
have Hx': psi x != 0.
  apply ltr_neq; case: psi_0 => [H _]; apply: ltr_leq_trans H.
  by rewrite (psi_leq 0 x).
have Hnx: - x > 0.
  case: (oppr0 R) => [_ H]; apply: leqr_lt_trans H _.
  by rewrite (leqr_opp2 x 0).
have Hnx': psi (- x) != 0 by apply gtr_neq; rewrite (psi_pos (- x)).
apply oppr_inj; apply: eqr_trans (invr_opp Hx').
apply: eqr_trans (invr_morphism Hnx' (psi_opp x));
apply: eqr_trans (psi_pinv Hnx).
apply eqr_sym; apply: (eqr_trans _ (psi_opp _)).
by rewrite (psi_eq (/ - x) (- / x)); apply: invr_opp; exact: ltr_neq.
Qed.

Remark psi_mul : forall x1 x2, psi (x1 * x2) == psi x1 * psi x2.
Proof.
move=> x1; suffice Hrec: forall x2, x2 > 0 -> psi (x1 * x2) == psi x1 * psi x2.
  move=> x2; case: (reals_classic R (x2 == 0)) => Hx2.
    apply: (eqr_trans (eqr_trans _ psi_0)).
      rewrite (psi_eq (x1 * x2) 0).
      by apply: eqr_trans (mulr0 x1); exact: mulr_morphism.
    apply: (eqr_sym (eqr_trans (mulr_morphism (eqr_refl _) _) (mulr0 _))).
    by apply: eqr_trans psi_0; rewrite (psi_eq x2 0).
  case/ltr_total: Hx2 => Hx2; auto; have Hnx2: - x2 > 0.
  case: (oppr0 R) => [_ H]; apply: leqr_lt_trans H _.
    by rewrite (leqr_opp2 x2 0).
  apply oppr_inj; apply: eqr_trans (mulr_oppr _ _).
  apply: (eqr_trans (eqr_sym (psi_opp _))).
  apply: (eqr_trans (eqr_trans _ (Hrec _ Hnx2))).
    rewrite (psi_eq (- (x1 * x2)) (x1 * - x2)); apply: eqr_sym; exact: mulr_oppr.
  by apply mulr_morphism; last exact: psi_opp.
move=> x2 Hx2; move: x1.
suffice Hrec: forall x1, x1 > 0 -> psi (x1 * x2) == psi x1 * psi x2.
  move=> x1; case: (reals_classic R (x1 == 0)) => Hx1.
    apply: (eqr_trans (eqr_trans _ psi_0)).
      rewrite (psi_eq (x1 * x2) 0).
      by apply: eqr_trans (mul0r x2); exact: mulr_morphism.
    apply: (eqr_sym (eqr_trans (mulr_morphism _ (eqr_refl _)) (mul0r _))).
    by apply: (eqr_trans _ psi_0); rewrite (psi_eq x1 0).
  case/ltr_total: Hx1 => Hx1; auto; have Hnx1: - x1 > 0.
  case: (oppr0 R) => [_ H]; apply: leqr_lt_trans H _.
    by rewrite (leqr_opp2 x1 0).
  apply oppr_inj; apply: eqr_trans (mulr_oppl _ _).
  apply: (eqr_trans (eqr_sym (psi_opp _))).
  apply: (eqr_trans (eqr_trans _ (Hrec _ Hnx1))).
    rewrite (psi_eq (- (x1 * x2)) (- x1 * x2)); apply: eqr_sym; exact: mulr_oppl.
  by apply mulr_morphism; first exact: psi_opp.
move: x2 Hx2.
suffice Hrec: forall x1 x2, x1 > 0 -> x2 > 0 -> psi (x1 * x2) <= psi x1 * psi x2.
  move=> x2 Hx2 x1 Hx1; split; auto.
  have Hx1': psi x1 > 0 by rewrite (psi_pos x1).
  rewrite -(leqr_pmul2l (psi x1 * psi x2) (psi (x1 * x2)) (posr_inv Hx1')).
  case: (pmulr_inv (psi x2) Hx1') => [H _]; apply: leqr_trans H _.
  move: Hx2; rewrite -(posr_pmull x2 Hx1) => Hx12.
  move: (pmulr_inv x2 Hx1); rewrite -(psi_eq (mulr (/ x1) (x1 * x2)) x2).
  move=> [_ H]; apply: leqr_trans H _.
  apply: (leqr_trans (Hrec _ _ (posr_inv Hx1) Hx12)); apply eqr_leq.
  by apply mulr_morphism; first exact: psi_pinv.
move=> x1 x2 Hx1 Hx2.
have Hx1': psi x1 > 0 by rewrite (psi_pos x1).
have Hx2': psi x2 > 0 by rewrite (psi_pos x2).
apply: psi_leq_ub => [_ [f Hfx]]; pose y2 := fracr R f / x1.
case Hf: (negb (posf f)).
  apply: (leqr_trans (fracr_posPx _ _ Hf)); apply ltrW.
  by rewrite (posr_pmull (psi x2) Hx1') (psi_pos x2).
have Hy2: y2 < x2.
  rewrite -(leqr_pmul2l x2 y2 Hx1); apply: leqr_lt_trans Hfx; apply eqr_leq.
  apply: (eqr_trans (mulrA _ _ _)); apply: (eqr_trans (mulrC _ _)).
  exact: pmulr_inv.
case: (fracr_dense Hy2) => [f2 Hy2f2 Hf2x2].
have Hf2: posf f2.
  move/(fracr_posPx R _): Hf => Hf; apply/(fracr_posPx R _).
  apply: ltr_trans Hy2f2; rewrite /y2 (posr_pmull (/ x1) Hf); exact: posr_inv.
pose f1 := mulf f (invf f2); have Hf1: fracr R f1 < x1.
  move/(fracr_posPx R _): (Hf2) => Hf2'.
  rewrite -(leqr_pmul2l x1 (fracr R f1) Hf2').
  case: (fracr_mul R f2 f1) => [_ H]; apply: leqr_lt_trans H _.
  apply leqr_lt_trans with (fracr R f).
    by apply: fracr_leqP; rewrite /f1 mulfA mulfC; case/andP: (pmulf_inv f Hf2).
  case: (mulrC (fracr R f2) x1) => _; apply: ltr_leq_trans; move: Hy2f2.
  rewrite -(leqr_pmul2l (fracr R f2) y2 Hx1); apply: leqr_lt_trans.
  apply eqr_leq; apply eqr_sym; apply: (eqr_trans (mulrA _ _ _)).
  by apply: (eqr_trans (mulrC _ _)); exact: pmulr_inv.
apply leqr_trans with (fracr R' f1 * fracr R' f2).
case: (fracr_mul R' f1 f2) => [H _]; apply: leqr_trans H; apply: fracr_leqP.
  by rewrite /f1 -mulfA mulfC -mulfA; case/andP: (pmulf_inv f Hf2).
apply leqr_trans with (psi x1 * fracr R' f2).
  move/(fracr_posPx R' _): (Hf2) => Hf2'.
  case: (mulrC (psi x1) (fracr R' f2)) => _; apply: leqr_trans.
  case: (mulrC (fracr R' f1) (fracr R' f2)) => [H _]; apply: leqr_trans H _.
  rewrite (leqr_pmul2l (fracr R' f1) (psi x1) Hf2'); apply: ltrW; exact: psi_is_ub.
rewrite (leqr_pmul2l (fracr R' f2) (psi x2) Hx1'); apply: ltrW; exact: psi_is_ub.
Qed.

Remark psi_sup : forall E, has_supr E -> psi (sup E) == sup (imager psi E).
Proof.
move=> E HE; have [HloE' HhiE']: has_supr (imager psi E).
  case: HE => [[x Hx] [z Hz]]; split; first by exists (psi x); exists x.
  exists (psi z) => _ [y <- Hy]; rewrite (psi_leq y z); exact: Hz.
split.
  apply: psi_leq_ub => [_ [f Hf]]; case: (supr_total (fracr R f) HE); last tauto.
  case: (psi_frac f) => [_ H] [x Hx Hfx]; apply: leqr_trans H _; move: Hfx.
  rewrite -(psi_leq (fracr R f) x) => H; apply: leqr_trans H _.
  by apply: (ubr_sup HhiE'); exists x.
apply: (leqr_sup_ub HloE') => [_ [x <- Hx]].
by rewrite (psi_leq x (sup E)); exact: (supr_upper_bound R).
Qed.

Definition canonical_real_morphism := psi.

Theorem canonical_real_morphism_morphism :
  real_structure_morphism canonical_real_morphism.
Proof.
exact (RealStructureMorphism
         psi_leq psi_sup psi_add psi_0 psi_opp psi_mul psi_1 psi_inv).
Qed.

End CanonicalRealMorphism.

Notation psi := (@canonical_real_morphism _).
Notation Hphi := (@real_structure_morphism _ _).

Theorem real_morphism_uniq : forall (R : real_structure) (R' : real_model),
    forall phi1 phi2 : R -> R', Hphi phi1 -> Hphi phi2 ->
  forall x, phi1 x == phi2 x.
Proof.
move=> R R'; suffice: forall (phi1 phi2 : R -> R') x,
    Hphi phi1 -> Hphi phi2 -> phi1 x <= phi2 x.
- by move=> *; split; auto.
move=> phi1 phi2 x Hphi1 Hphi2; case: (reals_classic R' (phi1 x <= phi2 x)); auto.
move/fracr_dense=> [f Hxf []].
case: (morphr_frac Hphi1 f) => [H _]; apply: leqr_trans H; apply ltrW.
rewrite (morphr_leq Hphi1 (fracr R f) x) -(morphr_leq Hphi2 (fracr R f) x).
by apply: (ltr_leq_trans Hxf); case: (morphr_frac Hphi2 f).
Qed.

Theorem inverse_canonical_real_morphism : forall R R' : real_model,
  forall x, psi R (psi R' x) == x.
Proof.
move=> R R'.
apply: real_morphism_uniq (fun x => psi R (psi R' x)) (fun x => x) _ _.
  apply: (@real_morphism_comp R R' R); exact: canonical_real_morphism_morphism.
exact: real_morphism_id.
Qed.

End RealsCategorical.

Set Strict Implicit.
Unset Implicit Arguments.

