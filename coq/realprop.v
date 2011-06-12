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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section RealOperations.

(**********************************************************)
(**  Derived real operations:                             *)
(*     definition by nondeterministic/deterministiccases, *)
(*     min, max                                           *)
(*     injections from Z, and Q into R                    *)
(*     floor, range1r (unit interval)                     *)
(**********************************************************)

Variable R : real_structure.

Open Scope real_scope.

Definition pickr_set P1 P2 (x1 x2 y : R) := P1 /\ y == x1 \/ P2 /\ y == x2.

Definition pickr P1 P2 x1 x2 := supr (pickr_set P1 P2 x1 x2).

Definition selr P := pickr P (~ P).

Definition minr x1 x2 := pickr (x1 <= x2) (x2 <= x1) x1 x2.

Definition maxr x1 x2 := pickr (x1 <= x2) (x2 <= x1) x2 x1.

Coercion Local natR := natr R.

Definition znatr m := match m with Zpos n => natr R n | Zneg n => - S n end.

Coercion Local znatr : znat >-> real_carrier.

Definition fracr f := let: Frac d m := f in m / S d.

Inductive floor_set (x : R) : R -> Prop :=
  FloorSet : forall m : znat, m <= x -> floor_set x m.

Definition floor x := supr (floor_set x).

Definition range1r (x y : R) := x <= y < x + 1.

End RealOperations.

Notation "'select' { x1 'if' P1 , x2 'if' P2 }" := (pickr P1 P2 x1 x2)
   (at level 10, x1, x2, P1, P2 at level 100,
    format "'select'  { x1  'if'  P1 ,  x2  'if'  P2 }") : real_scope.

Notation "'select' { x1 'if' P , 'else' x2 }" := (selr P x1 x2)
   (at level 10, x1, x2, P at level 100,
    format "'select'  { x1  'if'  P ,  'else'  x2 }") : real_scope.

Notation min := (@minr _).
Notation max := (@maxr _).

Section RealLemmas.

(* Basic arithmetic/order/setoid lemmas for real numbers.    *)
(* The local definitions below need to be included verbatim  *)
(* by clients of this module, along with all the setoid      *)
(* declaration, in order to make setoid rewriting usable.    *)
(* Note that the sup and inverse operators are not morphisms *)
(* because of the undefined cases.                           *)
(*   Most of the lemmas here do not depend explicitly on     *)
(* classical reasoning; to underscore this we only prove the *)
(* excluded middle at the very end of this section, when it  *)
(* is needed to prove, e.g., the archimedean property.       *)

Variable R : real_model.

Open Scope real_scope.

Let RR : Type := R.
Let isR (x : RR) := x.
Let eqR : RR -> RR -> Prop := @eqr _.
Let leqR : RR -> RR -> Prop := locked (@leqr _).
Let addR : RR -> RR -> RR := locked (@addr _).
Let oppR : RR -> RR := locked (@oppr _).
Let mulR : RR -> RR -> RR := locked (@mulr _).
Let selR : Prop -> RR -> RR -> RR := locked (@selr _).
Let minR : RR -> RR -> RR := locked (@minr _).
Let maxR : RR -> RR -> RR := locked (@maxr _).
Let floorR : RR -> RR := locked (@floor _).
Let range1R : RR -> RR -> Prop := @range1r _.
Coercion Local natR := natr R.
Coercion Local znatR := znatr R.
Coercion Local fracR := fracr R.

Remark rwR : forall x1 x2, x1 == x2 -> eqR (isR x1) (isR x2). Proof. done. Qed.

Remark leqRI : forall x1 x2, (x1 <= x2) = leqR (isR x1) (isR x2).
Proof. by unlock leqR. Qed.

Remark eqRI : forall x1 x2, (x1 == x2) = eqR (isR x1) (isR x2).
Proof. by unlock eqR. Qed.

Remark addRI : forall x1 x2, (x1 + x2)%R = addR (isR x1) (isR x2).
Proof. by unlock addR. Qed.

Remark oppRI : forall x, - x = oppR (isR x).
Proof. by unlock oppR. Qed.

Remark mulRI : forall x1 x2, x1 * x2 = mulR (isR x1) (isR x2).
Proof. by unlock mulR. Qed.

Remark selRI : forall P x1 x2,
  select {x1 if P, else x2} = selR P (isR x1) (isR x2).
Proof. by unlock selR. Qed.

Remark minRI : forall x1 x2, min x1 x2 = minR (isR x1) (isR x2).
Proof. by unlock minR. Qed.

Remark maxRI : forall x1 x2, max x1 x2 = maxR (isR x1) (isR x2).
Proof. by unlock maxR. Qed.

Remark floorRI : forall x, floor x = floorR (isR x).
Proof. by unlock floorR. Qed.

Remark range1RI : forall x, range1r x = range1R (isR x).
Proof. by unlock range1R. Qed.

(*********************************************************)
(**     Comparisons and the least upper bound axioms     *)
(*********************************************************)

Lemma eqr_leq2 : forall x1 x2 : R, x1 == x2 <-> x1 <= x2 <= x1.
Proof. by split. Qed.

Lemma eqr_leq : forall x1 x2 : R, x1 == x2 -> x1 <= x2.
Proof. by move=> x1 x2 [Hx12 _]. Qed.

Lemma ltr_neq : forall x1 x2 : R, x1 < x2 -> x1 != x2.
Proof. rewrite /eqr; tauto. Qed.

Lemma gtr_neq : forall x1 x2 : R, x2 < x1 -> x1 != x2.
Proof. rewrite /eqr; tauto. Qed.

Lemma leqrr : forall x : R, x <= x.
Proof. exact (leqr_reflexivity R). Qed.
Hint Resolve leqrr.

Lemma leqr_trans : forall x1 x2 x3 : R, x1 <= x2 -> x2 <= x3 -> x1 <= x3.
Proof. exact (leqr_transitivity R). Qed.

Lemma ubr_sup : forall E : R -> Prop, hasr (ubr E) -> ubr E (sup E).
Proof.
by move=> E HhiE x Hx; apply: (supr_upper_bound R) (Hx); split; first by exists x.
Qed.

Lemma ubr_geq_sup : forall E (x : R), hasr (ubr E) -> sup E <= x -> ubr E x.
Proof. move=> E x; move/ubr_sup=> HhiE Hx y Hy; apply: leqr_trans Hx; auto. Qed.

Lemma supr_total : forall (x : R) E, has_supr E -> boundedr x E \/ sup E <= x.
Proof. exact (supr_totality R). Qed.

Lemma leqr_total : forall x1 x2 : R, x1 <= x2 \/ x2 <= x1.
Proof.
move=> x1 x2; pose E y := x2 = y.
have HE: (has_supr E) by split; exists x2; last by move=> x <-.
 case: (supr_total x1 HE) => [[y <-]|HEx1]; first by left.
by right; apply: leqr_trans HEx1; apply: ubr_sup => //; exists x2; move=> x <-.
Qed.

Lemma ltr_total : forall x1 x2 : R, x1 != x2 -> x1 < x2 \/ x2 < x1.
Proof. move=> x1 x2; rewrite /eqr; move: (leqr_total x1 x2); tauto. Qed.

Lemma ltrW : forall x1 x2 : R, x1 < x2 -> x1 <= x2.
Proof. by move=> x1 x2 Hx12; case: (leqr_total x1 x2) => // *; case: Hx12. Qed.
Hint Resolve ltrW.

Lemma leqr_lt_trans : forall x1 x2 x3 : R, x1 <= x2 -> x2 < x3 -> x1 < x3.
Proof. move=> x1 x2 x3 Hx12 Hx23 Hx31; case: Hx23; exact: leqr_trans Hx12. Qed.

Lemma ltr_leq_trans : forall x1 x2 x3 : R, x1 < x2 -> x2 <= x3 -> x1 < x3.
Proof. move=> x1 x2 x3 Hx12 Hx23 Hx31; case: Hx12; exact: leqr_trans Hx31. Qed.

Lemma ltr_trans : forall x1 x2 x3 : R, x1 < x2 -> x2 < x3 -> x1 < x3.
Proof. move=> x1 x2 x3 Hx12; apply: leqr_lt_trans; exact: ltrW. Qed.

(**********************************************************)
(**      The setoid structure                             *)
(**********************************************************)

Lemma eqr_refl : forall x : R, x == x.
Proof. split; apply: leqrr. Qed.
Hint Resolve eqr_refl.
Hint Unfold eqR.

Remark eqR_refl : forall x : R, eqR x x. Proof. auto. Qed.
Hint Resolve eqR_refl.

Lemma eqr_sym : forall x1 x2 : R, x1 == x2 -> x2 == x1.
Proof. rewrite /eqr; tauto. Qed.
Hint Immediate eqr_sym.

Lemma eqr_trans : forall x1 x2 x3 : R, x1 == x2 -> x2 == x3 -> x1 == x3.
Proof.
move=> x1 x2 x3 [Hx12 Hx21] [Hx23 Hx32]; split; eapply leqr_trans; eauto.
Qed.

Lemma eqr_theory : Setoid_Theory RR eqR.
Proof. split; auto; exact eqr_trans. Qed.

Add Setoid RR eqR eqr_theory.

Add Morphism isR : isr_morphism. Proof. done. Qed.

Add Morphism (@leqr _ : RR -> RR -> Prop) : leqr_morphism.
Proof. move: leqr_trans => Htr x1 y1 x2 y2 [_ Hyx1] [Hxy2 _]; eauto. Qed.

Add Morphism leqR : leqR_morphism.
Proof. unlock leqR; exact leqr_morphism. Qed.

(**********************************************************)
(**       Addition                                        *)
(**********************************************************)

Lemma addrC : forall x1 x2 : R, x1 + x2 == x2 + x1.
Proof. exact (addr_commutativity R). Qed.

Add Morphism (@addr _ : RR -> RR -> RR) : addr_morphism.
Proof.
move=> x1 y1 x2 y2 Dx1 Dx2; apply eqr_trans with (x1 + y2).
  by case Dx2; split; apply: (addr_monotony R).
rewrite eqRI (rwR (addrC x1 y2)) (rwR (addrC y1 y2)).
by case Dx1; split; apply: (addr_monotony R).
Qed.

Add Morphism addR : addR_morphism.
Proof. unlock addR; exact addr_morphism. Qed.

Lemma addrA : forall x1 x2 x3 : R, x1 + (x2 + x3) == x1 + x2 + x3.
Proof. exact (addr_associativity R). Qed.

Lemma addrCA : forall x1 x2 x3 : R, x1 + (x2 + x3) ==  x2 + (x1 + x3).
Proof.
move=> x1 x2 x3; rewrite eqRI (rwR (addrA x1 x2 x3)) (rwR (addrA x2 x1 x3)).
by rewrite addRI (rwR (addrC x1 x2)) -addRI.
Qed.

Lemma add0r : forall x : R, 0 + x == x.
Proof. exact (addr_neutral_left R). Qed.

Lemma addr0 : forall x : R, x + 0 == x.
Proof. move=> x; rewrite eqRI (rwR (addrC x 0)); exact: add0r. Qed.

Lemma subrr : forall x : R, x - x == 0.
Proof. exact (addr_inverse_right R). Qed.

Lemma addr_inv : forall x1 x2 : R, - x1 + (x1 + x2) == x2.
Proof.
move=> x1 x2; rewrite eqRI (rwR (addrCA (- x1) x1 x2)).
rewrite (rwR (addrA x1 (- x1) x2)) addRI (rwR (subrr x1)) -addRI; exact: add0r.
Qed.

Lemma addr_injl : forall x x1 x2 : R, x + x1 == x + x2 -> x1 == x2.
Proof.
move=> x x1 x2 Ex12; rewrite eqRI -(rwR (addr_inv x x1)) addRI (rwR Ex12) -addRI.
exact: addr_inv.
Qed.

Lemma addr_injr : forall x x1 x2 : R, x1 + x == x2 + x -> x1 == x2.
Proof.
move=> x x1 x2; rewrite eqRI (rwR (addrC x1 x)) (rwR (addrC x2 x)).
exact: addr_injl.
Qed.

Lemma oppr_opp : forall x : R, - - x == x.
Proof.
move=> x; apply addr_injr with (- x); rewrite eqRI (rwR (subrr x)).
rewrite (rwR (addrC (- - x) (- x))); exact: subrr.
Qed.

Lemma oppr_add : forall x1 x2 : R, - (x1 + x2) == - x1 - x2.
Proof.
move=> x1 x2; apply addr_injl with (x1 + x2); rewrite eqRI.
rewrite (rwR (addrCA (x1 + x2) (-x1) (-x2))) (rwR (subrr (x1 + x2))).
rewrite addRI -(rwR (addrA x1 x2 (-x2))) -addRI.
by rewrite (rwR (addr_inv x1 (x2 - x2))) (rwR (subrr x2)).
Qed.

Lemma oppr_sub : forall x1 x2 : R, - (x1 - x2) == x2 - x1.
Proof.
move=> x1 x2; rewrite eqRI (rwR (oppr_add x1 (- x2))) addRI (rwR (oppr_opp x2)).
rewrite -addRI; apply: addrC.
Qed.

Lemma leqr_add2l : forall x x1 x2 : R, x + x1 <= x + x2 <-> x1 <= x2.
Proof.
move=> x x1 x2; split; last exact: (addr_monotony R).
move=> Hx12; rewrite leqRI -(rwR (addr_inv x x1)) -(rwR (addr_inv x x2)) -leqRI.
exact: (addr_monotony R).
Qed.

Lemma leqr_add2r : forall x x1 x2 : R, x1 + x <= x2 + x <-> x1 <= x2.
Proof.
move=> x x1 x2; rewrite leqRI (rwR (addrC x1 x)) (rwR (addrC x2 x)) -leqRI.
exact: leqr_add2l.
Qed.

Lemma leqr_0sub : forall x1 x2 : R, x1 <= x2 <-> 0 <= x2 - x1.
Proof.
move=> x1 x2; rewrite -(leqr_add2r (- x1) x1 x2) leqRI (rwR (subrr x1)) -leqRI.
by split.
Qed.

Lemma leqr_sub0 : forall x1 x2 : R, x1 <= x2 <-> x1 - x2 <= 0.
Proof.
move=> x1 x2; rewrite -(leqr_add2r (- x2) x1 x2) leqRI (rwR (subrr x2)) -leqRI.
by split.
Qed.

Lemma leqr_opp2 : forall x1 x2 : R, - x1 <= - x2 <-> x2 <= x1.
Proof.
move=> x1 x2; rewrite (leqr_0sub (- x1) (- x2)) (leqr_0sub x2 x1).
rewrite leqRI addRI (rwR (oppr_opp x1)) -addRI (rwR (addrC (oppr x2) x1)) -leqRI.
by split.
Qed.

Lemma oppr_inj : forall x1 x2 : R, - x1 == - x2 -> x1 == x2.
Proof.
move=> x y; rewrite /eqR /eqr (leqr_opp2 x y) (leqr_opp2 y x); tauto.
Qed.

Add Morphism (@oppr _ : RR -> RR) : oppr_morphism.
Proof.
move=> x y; rewrite /eqR /eqr (leqr_opp2 x y) (leqr_opp2 y x); tauto.
Qed.

Add Morphism oppR : oppR_morphism.
Proof. unlock oppR; exact oppr_morphism. Qed.

Lemma oppr0 : - (0 : R) == 0.
Proof. by rewrite eqRI -(rwR (subrr 0)) (rwR (add0r (- 0))). Qed.

(**********************************************************)
(**       Multiplication                                  *)
(**********************************************************)

Lemma mulrC : forall x1 x2 : R, x1 * x2 == x2 * x1.
Proof. exact (mulr_commutativity R). Qed.

Lemma mulr_addr : forall x x1 x2 : R, x * (x1 + x2) == x * x1 + x * x2.
Proof. exact (mulr_addr_distributivity_right R). Qed.

Lemma mulr_addl : forall x x1 x2 : R, (x1 + x2) * x == x1 * x + x2 * x.
Proof.
move=> x x1 x2;
 rewrite eqRI (rwR (mulrC (x1 + x2) x)) (rwR (mulr_addr x x1 x2)).
by rewrite addRI (rwR (mulrC x x1)) (rwR (mulrC x x2)) -addRI.
Qed.

Add Morphism (@mulr _ : RR -> RR -> RR) : mulr_morphism.
Proof.
have Hpos: forall x x1 x2 : R, 0 <= x -> x1 == x2 -> x * x1 == x * x2.
  by move=> x x1 x2 Hx [Hx12 Hx21]; split; apply (mulr_monotony R).
have Hmull: forall x x1 x2 : R, x1 == x2 -> x * x1 == x * x2.
move=> x x1 x2 Dx1; case: (leqr_total 0 x) => Hx; auto.
  have Hx': 0 <= - x by move: Hx; rewrite -(leqr_opp2 0 x) !leqRI (rwR oppr0).
  apply addr_injr with (- x * x1).
  rewrite eqRI -(rwR (mulr_addl x1 x (- x))) 2!addRI -addRI.
  rewrite (rwR (Hpos _ _ _ Hx' Dx1)) -addRI -(rwR (mulr_addl x2 x (- x))).
  apply: Hpos; last done; apply eqr_leq; apply eqr_sym; apply subrr.
rewrite /eqR; move=> x1 y1 x2 y2 Dx1 Dx2.
apply eqr_trans with (x1 * y2); auto.
rewrite eqRI (rwR (mulrC x1 y2)) (rwR (mulrC y1 y2)) -eqRI; auto.
Qed.

Add Morphism mulR : mulR_morphism. Proof. unlock mulR; exact mulr_morphism. Qed.

Lemma mulrA : forall x1 x2 x3 : R, x1 * (x2 * x3) == x1 * x2 * x3.
Proof. exact (mulr_associativity R). Qed.

Lemma mulrCA : forall x1 x2 x3 : R, x1 * (x2 * x3) == x2 * (x1 * x3).
Proof.
move=> x1 x2 x3; rewrite eqRI (rwR (mulrA x1 x2 x3)) (rwR (mulrA x2 x1 x3)).
by rewrite mulRI (rwR (mulrC x1 x2)) -mulRI.
Qed.

Lemma mul1r : forall x : R, 1 * x == x.
Proof. exact (mulr_neutral_left R). Qed.

Lemma mulr1 : forall x : R, x * 1 == x.
Proof. move=> x; rewrite eqRI (rwR (mulrC x 1)); exact: mul1r. Qed.

Lemma mul2r : forall x : R, 2 * x == x + x.
Proof.
by move=> x; rewrite eqRI (rwR (mulr_addl x 1 1)) !addRI (rwR (mul1r x)).
Qed.

Lemma mul0r : forall x : R, 0 * x == 0.
Proof.
move=> x; apply addr_injl with (1 * x); rewrite eqRI -(rwR (mulr_addl x 1 0)).
by rewrite (rwR (addr0 (1 * x))) !mulRI (rwR (addr0 1)).
Qed.

Lemma mulr0 : forall x : R, x * 0 == 0.
Proof. by move=> x; rewrite eqRI (rwR (mulrC x 0)); apply: mul0r. Qed.

Lemma mulr_oppr :
 forall x1 x2 : R, x1 * - x2 == - (x1 * x2).
Proof.
move=> x1 x2; apply addr_injl with (x1 * x2).
rewrite eqRI -(rwR (mulr_addr x1 x2 (- x2))) (rwR (subrr (x1 * x2))).
rewrite mulRI (rwR (subrr x2)) -mulRI; exact: mulr0.
Qed.

Lemma mulr_oppl : forall x1 x2 : R, - x1 * x2 == - (x1 * x2).
Proof.
move=> x1 x2; rewrite eqRI (rwR (mulrC (- x1) x2)) (rwR (mulr_oppr x2 x1)).
by rewrite !oppRI (rwR (mulrC x2 x1)).
Qed.

Lemma mulr_opp : forall x : R, - 1 * x == - x.
Proof.
by move=> x; rewrite eqRI (rwR (mulr_oppl 1 x)) !oppRI (rwR (mul1r x)).
Qed.

Lemma mulr_opp1 : forall x : R, x * - 1 == - x.
Proof. move=> x; rewrite eqRI (rwR (mulrC x (- 1))); exact: mulr_opp. Qed.

(* Properties of 1 (finally!) *)

Lemma neqr10 : (1 : R) != 0.
Proof. exact (mulr_neutral_nonzero R). Qed.

Lemma ltr01 : (0 : R) < 1.
Proof.
case/ltr_total: neqr10 => // H H10; case: H; move: (H10).
rewrite -(leqr_opp2 0 1) -(leqr_opp2 1 0) !leqRI (rwR oppr0) -leqRI.
move=> Hn1; rewrite -(rwR (mulr1 (- 1))) -(rwR (mulr0 (- 1))) -leqRI.
exact: (mulr_monotony R).
Qed.
Hint Resolve ltr01.

Lemma ltrSr : forall x : R, x < x + 1.
Proof.
by move=> x; rewrite leqRI -(rwR (addr0 x)) -leqRI (leqr_add2l x 1 0).
Qed.
Implicit Arguments ltrSr [].

Lemma ltPrr : forall x : R, x - 1 < x.
Proof.
move=> x /=; rewrite -(leqr_opp2 (x - 1) x) leqRI (rwR (oppr_add x (- 1))).
rewrite addRI (rwR (oppr_opp 1)) -addRI -leqRI; exact: ltrSr.
Qed.
Implicit Arguments ltPrr [].

Lemma ltr02 : (0 : R) < 2.
Proof. exact (ltr_trans ltr01 (ltrSr _)). Qed.
Hint Resolve ltr02.

(* Division (well, mostly inverse) *)

Lemma divrr : forall x : R, x != 0 -> x / x == 1.
Proof. exact (mulr_inverse_right R). Qed.

Lemma leqr_pmul2l : forall x x1 x2 : R, x > 0 -> (x * x1 <= x * x2 <-> x1 <= x2).
Proof.
move=> x x1 x2 Hx; split; last by apply (mulr_monotony R); exact: ltrW.
move=> Hx12; rewrite leqRI -(rwR (mul1r x1)) -(rwR (mul1r x2)).
rewrite !mulRI -(rwR (divrr (gtr_neq Hx))) (rwR (mulrC x (/ x))) -!mulRI.
rewrite -(rwR (mulrA (/ x) x x1)) -(rwR (mulrA (/ x) x x2)) -leqRI.
apply: (mulr_monotony R) Hx12; apply ltrW; move=> Hix.
case ltr01; rewrite leqRI -(rwR (divrr (gtr_neq Hx))) -(rwR (mulr0 x)) -leqRI.
apply: (mulr_monotony R) Hix; exact: ltrW.
Qed.

Lemma leqr_pmul2r : forall x x1 x2 : R, x > 0 -> (x1 * x <= x2 * x <-> x1 <= x2).
Proof.
move=> x x1 x2 Hx; rewrite leqRI (rwR (mulrC x1 x)) (rwR (mulrC x2 x)) -leqRI.
exact: leqr_pmul2l Hx.
Qed.

Lemma pmulr_inv : forall x x1 : R, x > 0 -> / x * (x * x1) == x1.
Proof.
move=> x x1 Hx; rewrite eqRI (rwR (mulrCA (/ x) x x1)) (rwR (mulrA x (/ x) x1)).
rewrite mulRI (rwR (divrr (gtr_neq Hx))) -mulRI; apply: mul1r.
Qed.

Lemma posr_pmull : forall x1 x2 : R, x1 > 0 -> (x1 * x2 <= 0 <-> x2 <= 0).
Proof.
move=> x1 x2 Hx1; rewrite -(leqr_pmul2l x2 0 Hx1) 2!leqRI (rwR (mulr0 x1)); tauto.
Qed.

Lemma pmulr_injl : forall x x1 x2 : R, x > 0 -> x * x1 == x * x2 -> x1 == x2.
Proof.
move=> x x1 x2 Hx Ex12; rewrite eqRI -(rwR (pmulr_inv x1 Hx)) mulRI (rwR Ex12).
rewrite -mulRI; exact (pmulr_inv x2 Hx).
Qed.

Lemma pmulr_injr : forall x x1 x2 : R, x > 0 -> x1 * x == x2 * x -> x1 == x2.
Proof.
move=> x x1 x2 Hx; rewrite eqRI (rwR (mulrC x1 x)) (rwR (mulrC x2 x)).
by apply: pmulr_injl.
Qed.

Lemma mulr_injl : forall x x1 x2 : R, x != 0 -> x * x1 == x * x2 -> x1 == x2.
Proof.
move=> x x1 x2 Hx; case: (leqr_total (real0 _) x) => Hx0.
  by apply: pmulr_injl => [H0x]; case Hx; split.
move/oppr_morphism; rewrite eqRI -(rwR (mulr_oppl x x1)) -(rwR (mulr_oppl x x2)).
apply: pmulr_injl; rewrite leqRI -(rwR oppr0) -leqRI (leqr_opp2 x 0).
by move=> H0x; case Hx; split.
Qed.

Lemma mulr_injr : forall x x1 x2 : R, x != 0 -> x1 * x == x2 * x -> x1 == x2.
Proof.
move=> x x1 x2 Hx; rewrite eqRI (rwR (mulrC x1 x)) (rwR (mulrC x2 x)).
exact: mulr_injl.
Qed.

(* The inverse is only a partial morphism. It might be worth fixing, say,  *)
(* 1/0 = 0 in order to make setoid rewriting work better.                  *)

Lemma invr_morphism : forall x y : R, x != 0 -> x == y -> / x == / y.
Proof.
move=> x y Hx Dx; have Hy: y != 0 by rewrite eqRI -(rwR Dx).
apply: (mulr_injl Hx); rewrite eqRI (rwR (divrr Hx)) -(rwR (divrr Hy)).
by rewrite !mulRI (rwR Dx).
Qed.

Lemma invr1 : / (1 : R) == 1.
Proof. by rewrite eqRI -(rwR (divrr neqr10)) (rwR (mul1r (invr 1))). Qed.

Lemma invr_pmul : forall x1 x2 : R, x1 > 0 -> x2 > 0 ->
  / (x1 * x2) == / x1 * / x2.
Proof.
move=> x1 x2 Hx1 Hx2; set y := / (x1 * x2); apply: (pmulr_injl Hx1).
rewrite eqRI (rwR (mulrCA x1 (/ x1) (/ x2))) (rwR (pmulr_inv (/ x2) Hx1)) /isR.
apply: (pmulr_injl Hx2); rewrite eqRI (rwR (divrr (gtr_neq Hx2))).
rewrite (rwR (mulrCA x2 x1 y)) (rwR (mulrA x1 x2 y)).
apply: divrr; apply: gtr_neq; rewrite leqRI -(rwR (mulr0 x1)) -leqRI.
by rewrite (leqr_pmul2l x2 0 Hx1).
Qed.

Lemma invr_opp : forall x : R, x != 0 -> / - x == - / x.
Proof.
move=> x Hx; apply: (mulr_injl Hx); apply oppr_inj.
rewrite eqRI -(rwR (mulr_oppl x (/ - x))) -(rwR (mulr_oppr x (- / x))).
rewrite !mulRI (rwR (oppr_opp (/ x))) -!mulRI (rwR (divrr Hx)); apply: divrr.
by rewrite eqRI -(rwR oppr0) -eqRI; move/oppr_inj.
Qed.

Lemma posr_inv : forall x : R, x > 0 -> / x > 0.
Proof.
move=> x Hx; rewrite -(leqr_pmul2l (/ x) 0 Hx).
by rewrite leqRI (rwR (mulr0 x)) (rwR (divrr (gtr_neq Hx))) -leqRI.
Qed.

Lemma leqr_pinv2 : forall x1 x2 : R, x1 > 0 -> x2 > 0 ->
  ( / x1 <= / x2 <-> x2 <= x1).
Proof.
move=> x1 x2 Hx1 Hx2; rewrite -(leqr_pmul2r (/ x1) (/ x2) Hx1).
rewrite -(leqr_pmul2l (/ x1 * x1) (/ x2 * x1) Hx2).
rewrite !leqRI (rwR (mulrC x2 (/ x1 * x1))) -(rwR (mulrA (/ x1) x1 x2)).
rewrite (rwR (mulrCA x2 (/ x2) x1)) (rwR (pmulr_inv x1 Hx2)).
rewrite (rwR (pmulr_inv x2 Hx1)); tauto.
Qed.

(**********************************************************)
(**      The least upper bound and derived operations.    *)
(**********************************************************)

Lemma leqr_sup_ub : forall E (x : R), hasr E -> ubr E x -> sup E <= x.
Proof.
move=> E x HloE Hx; set y := sup E; pose z := (x + y) / 2.
have Dz: 2 * z == x + y.
  apply: (eqr_trans (mulrA _ _ _)); apply: (eqr_trans (mulrC _ _)).
  apply: pmulr_inv; exact ltr02.
have HE: has_supr E by split; last by exists x.
case: (supr_total z HE) => [[t Ht Hzt]|Hyz].
  rewrite -(leqr_add2l x y x) leqRI -(rwR Dz) -(rwR (mul2r x)) -leqRI.
  rewrite (leqr_pmul2l z x ltr02); apply: (leqr_trans Hzt); auto.
rewrite -(leqr_add2r y y x) leqRI -(rwR Dz) -(rwR (mul2r y)) -leqRI.
by rewrite (leqr_pmul2l y z ltr02).
Qed.

Lemma supr_sup : forall E, has_supr E -> forall x : R, ubr E x <-> sup E <= x.
Proof.
by move=> E [HloE HhiE] x; split; [ apply leqr_sup_ub | apply ubr_geq_sup ].
Qed.

(* Partial morphism property of the sup function; similarly to 1/0,   *)
(* it might be helpful to define (supr [_]True) and (supr [_]False).  *)

Lemma supr_morphism : forall E, has_supr E -> forall E',
  (forall x : R, E x <-> E' x) -> sup E == sup E'.
Proof.
have Hleq: forall E E', hasr E -> hasr (ubr E') ->
    (forall x : R, E x -> E' x) -> sup E <= sup E'.
  by move=> *; apply: leqr_sup_ub => // x Hx; apply ubr_sup; auto.
move=> E [HloE HhiE] E' DE'.
split; (apply Hleq; auto; last by move=> x; case (DE' x); auto).
  by move: HhiE => [y Hy]; exists y; move=> x; case (DE' x); auto.
by move: HloE => [x Hx]; case (DE' x); exists x; auto.
Qed.

(* Definition by nondeterministic cases.                        *)

Section PickrCases.

Variables (P1 P2 : Prop) (x1 x2 : R).
Hypotheses (HP : P1 \/ P2) (HPx : P1 /\ P2 -> x1 == x2).

Inductive pickr_spec : R -> Prop :=
  PickrSpec : forall y, pickr_set P1 P2 x1 x2 y -> pickr_spec y.

Lemma pickr_cases : pickr_spec (select {x1 if P1, x2 if P2}).
Proof.
pose ps := pickr_set P1 P2 x1 x2; set x := select {x1 if P1, x2 if P2}.
have [x3 Hx3lo Ex3]:  exists2 x3, ps x3 & forall y, ps y <-> y == x3.
  case: HP => HPi; [ exists x1; try split; try by left; split
                   | exists x2; try split; try by right; split ];
   case; case=> Hpj Dy //; apply: (eqr_trans Dy); auto; apply eqr_sym; auto.
have Hx3hi: ubr ps x3.
  by move=> x4; rewrite (Ex3 x4); move=> Dx4; rewrite leqRI (rwR Dx4) -leqRI.
split; rewrite -/ps (Ex3 x); split; last by apply: ubr_sup; first by exists x3.
by apply: leqr_sup_ub; first by exists x3.
Qed.

End PickrCases.

Section PickrMorphism.

Variables (P1 P2 : Prop) (x1 x2 : R).
Hypotheses (HP : P1 \/ P2) (HPx : P1 /\ P2 -> x1 == x2).

Lemma pickr_morphism : forall Q1 Q2 y1 y2,
   (P1 <-> Q1) -> (P2 <-> Q2) -> x1 == y1 -> x2 == y2 ->
  select {x1 if P1, x2 if P2} == select {y1 if Q1, y2 if Q2}.
Proof.
move=> Q1 Q2 y1 y2 DP1 DP2 Dx1 Dx2; rewrite -/eqR.
have HQ: Q1 \/ Q2 by rewrite -DP1 -DP2.
have HQy: Q1 /\ Q2 -> y1 == y2 by rewrite -DP1 -DP2 eqRI -(rwR Dx1) -(rwR Dx2).
case: (pickr_cases HQ HQy) => y; case: (pickr_cases HP HPx) => x.
rewrite /pickr_set -DP1 -DP2 (eqRI y y1) -(rwR Dx1) (eqRI y y2) -(rwR Dx2) -!eqRI.
case; case=> HPi Dx; case; case=> HPj Dy;
 rewrite /eqR eqRI (rwR Dx) (rwR Dy) -eqRI; auto; apply eqr_sym; auto.
Qed.

End PickrMorphism.

(* min and max.                                                         *)

Section MinMaxReal.

Variable x1 x2 : R.

Let Hx12 := leqr_total x1 x2.
Let Ex12 (H : x1 <= x2 <= x1) := H : x1 == x2.
Let Ex21 (H : x1 <= x2 <=x1) := eqr_sym H.

Lemma leqr_minl : min x1 x2 <= x1.
Proof.
rewrite /minr; case: (pickr_cases Hx12 Ex12) => x3.
by case; case=> Hx Dx3; rewrite leqRI (rwR Dx3) -leqRI.
Qed.

Lemma leqr_minr : min x1 x2 <= x2.
Proof.
rewrite /minr; case: (pickr_cases Hx12 Ex12) => x3.
by case; case=> Hx Dx3; rewrite leqRI (rwR Dx3) -leqRI.
Qed.
Hint Resolve leqr_minl leqr_minr.

Lemma ltr_min : forall x : R, x < min x1 x2 <-> x < x1 /\ x < x2.
Proof.
rewrite /minr; case: (pickr_cases Hx12 Ex12) => x3.
case; case=> Hx Dx3 x; rewrite leqRI (rwR Dx3) -leqRI;
 by split; [ split; try exact: ltr_leq_trans Hx | case ].
Qed.

Lemma leqr_min : forall x : R, x <= min x1 x2 <-> x <= x1 /\ x <= x2.
Proof.
move=> x; split; first by split; eapply leqr_trans; eauto.
 move=> [Hxx1 Hxx2]; rewrite /minr; case: (pickr_cases Hx12 Ex12) => x3.
by case; case=> Hx Dx3; rewrite leqRI (rwR Dx3) -leqRI.
Qed.

Lemma leqr_maxl : x1 <= max x1 x2.
Proof.
rewrite /maxr; case: (pickr_cases Hx12 Ex21) => x3.
by case; case=> Hx Dx3; rewrite leqRI (rwR Dx3) -leqRI.
Qed.

Lemma leqr_maxr : x2 <= max x1 x2.
Proof.
rewrite /maxr; case: (pickr_cases Hx12 Ex21) => x3.
by case; case=> Hx Dx3; rewrite leqRI (rwR Dx3) -leqRI.
Qed.
Hint Resolve leqr_maxl leqr_maxr.

Lemma ltr_max : forall x : R, max x1 x2 < x <-> x1 < x /\ x2 < x.
Proof.
rewrite /maxr; case: (pickr_cases Hx12 Ex21) => x3.
case; case=> Hx Dx3 x; rewrite leqRI (rwR Dx3) -leqRI;
 by split; [ split; try exact: (leqr_lt_trans Hx) | case ].
Qed.

Lemma leqr_max : forall x : R, maxr x1 x2 <= x <-> x1 <= x /\ x2 <= x.
Proof.
move=> x; split; first by split; eapply leqr_trans; eauto.
move=> [Hxx1 Hxx2]; rewrite /maxr; case: (pickr_cases Hx12 Ex21) => x3.
by case; case=> Hx Dx3; rewrite leqRI (rwR Dx3) -leqRI.
Qed.

End MinMaxReal.

Add Morphism (minr (R := _) : RR -> RR -> RR) : minr_morphism.
Proof.
move=> x1 y1 x2 y2 Dx1 Dx2; apply: (pickr_morphism _ _ _) => //;
 try apply leqr_total; by rewrite !leqRI Dx1 Dx2; split.
Qed.

Add Morphism minR : minR_morphism. Proof. unlock minR; exact minr_morphism. Qed.

Add Morphism (maxr (R := _) : RR -> RR -> RR) : maxr_morphism.
Proof.
move=> x1 y1 x2 y2 Dx1 Dx2; apply: (pickr_morphism _ _ _) => //;
 try apply leqr_total; try by rewrite !leqRI Dx1 Dx2; split.
by move/eqr_sym.
Qed.

Add Morphism maxR : maxR_morphism. Proof. unlock maxR; exact maxr_morphism. Qed.

(**********************************************************)
(** Properties of the injections from N, Z, and Q into R  *)
(**********************************************************)

Lemma natr_S : forall n, S n == n + 1.
Proof.
case=> [|n] /=; first by rewrite eqRI (rwR (add0r 1)).
elim: n {2 3}(real1 R) => //= [] x; apply addrC.
Qed.

Lemma ltr0Sn : forall n, 0 < S n.
Proof.
elim=> // n Hrec; apply: ltr_trans Hrec _.
rewrite leqRI -(rwR (addr0 (S n))) (rwR (natr_S (S n))) -leqRI.
by rewrite (leqr_add2l (S n) 1 0).
Qed.
Implicit Arguments ltr0Sn [].

Lemma leqr0n : forall n : nat, 0 <= n.
Proof. by move=> [|n]; [ apply leqrr | apply ltrW; apply ltr0Sn ]. Qed.

Lemma znatr_inc : forall m, incz m == m + 1.
Proof.
move=> [n|n]; rewrite eqRI; first by rewrite /= -/natR -(rwR (natr_S n)).
case: n => [|n]; first by rewrite /= (rwR (addrC (- 1) 1)) (rwR (subrr 1)).
rewrite {2}/znatR /znatr -/natR addRI oppRI (rwR (natr_S (S n))) -oppRI.
rewrite (rwR (oppr_add (S n) 1)) -addRI.
rewrite -(rwR (addrA (- S n) (- 1) 1)) addRI (rwR (addrC (- 1) 1)).
by rewrite (rwR (subrr 1)) -addRI (rwR (addr0 (- (S n)))).
Qed.

Lemma znatr_dec : forall m, decz m == m - 1.
Proof.
move=> m; rewrite -{2}[m]incz_dec; move/decz: m => m.
rewrite eqRI addRI (rwR (znatr_inc m)) -addRI -(rwR (addrA m 1 (- 1))).
by rewrite addRI (rwR (subrr 1)) -addRI (rwR (addr0 m)).
Qed.

Lemma znatr_opp : forall m, (- m)%Z == - m.
Proof.
move=> [[|[|n]]|[|m]] //=; apply eqr_sym; first [ exact: oppr0 | exact: oppr_opp ].
Qed.

Lemma znatr_add : forall m1 m2, (m1 + m2)%Z == m1 + m2.
Proof.
have znatr_addpos: forall (n : nat) m, (n + m)%Z == n + m.
  move=> n m; elim: n => [|n Hrec]; first by rewrite add0z /= eqRI (rwR (add0r m)).
  rewrite eqRI addRI (rwR (natr_S n)) -addRI -add1n zpos_addn -addzA addzC.
  rewrite -incz_def (rwR (znatr_inc (n + m))) addRI (rwR Hrec) -addRI.
  rewrite -(rwR (addrA n m 1)) -(rwR (addrA n 1 m)).
  by rewrite addRI (rwR (addrC m 1)) -addRI.
move=> [n1|m1] m2; first by apply: znatr_addpos.
set m12 := (_ + _)%Z; rewrite -(oppz_opp m12) eqRI.
rewrite (rwR (znatr_opp (- m12))) {}/m12 oppz_add [addz]lock /= -lock.
rewrite oppRI (rwR (znatr_addpos (S m1) (- m2)%Z)) -oppRI.
rewrite (rwR (oppr_add (S m1) (- m2)%Z)) addRI.
by rewrite -(rwR (znatr_opp (- m2))) oppz_opp -addRI.
Qed.

Lemma znatr_subz : forall m1 m2, (m1 - m2)%Z == m1 - m2.
Proof.
move=> m1 m2; rewrite eqRI (rwR (znatr_add m1 (- m2))).
by rewrite !addRI (rwR (znatr_opp m2)).
Qed.

Lemma znatr_mul : forall m1 m2, (m1 * m2)%Z == m1 * m2.
Proof.
move=> m1 m2; elim/oppz_cases: m1 => [m1 Dm12|n1].
rewrite mulz_oppl eqRI (rwR (znatr_opp (m1 * m2))) oppRI {Dm12}(rwR Dm12).
  by rewrite -oppRI -(rwR (mulr_oppl m1 m2)) !mulRI (rwR (znatr_opp m1)).
elim: n1 => [|n1 Hrec]; first by rewrite mul0z eqRI /= (rwR (mul0r m2)).
rewrite -add1n zpos_addn mulzC mulz_addr !(mulzC m2) eqRI [(_ * _)%Z]/= mulRI.
rewrite (rwR (znatr_add (Zpos 1%nat) n1)) (rwR (znatr_add m2 (n1 * m2)%Z)) -mulRI.
rewrite addRI (rwR Hrec) /= -/natR (rwR (mulr_addl m2 1 n1)) addRI.
by rewrite (rwR (mul1r m2)).
Qed.

Lemma znatr_scale : forall d m, scalez d m == S d * m.
Proof. move=> d m; exact (znatr_mul (S d) m). Qed.

Lemma znatr_addbit : forall m : znat, m == oddz m + 2 * halfz m.
Proof.
move=> m; rewrite -{1}[m]odd_double_halfz; move/halfz: m (oddz m) => m b.
rewrite eqRI (rwR (znatr_add b (m + m))) 2!addRI (rwR (mul2r m)).
by rewrite (rwR (znatr_add m m)).
Qed.

Lemma znatr_leqPx : forall m1 m2 : znat, reflect (m1 <= m2) (m1 <= m2)%Z.
Proof.
move=> m1 m2; rewrite /leqz; apply: (iffP idP);
  rewrite (leqr_sub0 m1 m2) leqRI -(rwR (znatr_subz m1 m2)) -leqRI;
  case: (m1 - m2)%Z => [[|n]|m] //; last by case/ltr0Sn.
rewrite leqRI -(rwR oppr0) -leqRI /znatR /znatr -/natR (leqr_opp2 (S m) 0).
clear; exact: leqr0n.
Qed.

Notation znatr_leqP := (znatr_leqPx _ _).

Lemma znatr_ltPx : forall m1 m2 : znat, reflect (m1 < m2) (incz m1 <= m2)%Z.
Proof.
move=> m1 m2; rewrite -negb_leqz.
by apply: (iffP idP) => Hm12; [ move/znatr_leqP: Hm12 | apply/znatr_leqP ].
Qed.

Notation znatr_ltP := (znatr_ltPx _ _).

(* Embedding the rationals.                                                     *)

Lemma fracr_eq : forall d m f, f = Frac d m -> m == S d * f.
Proof.
move=> d m f Df; rewrite Df /fracR /fracr -/natR -/znatR eqRI.
rewrite (rwR (mulrA (S d) m (/ S d))) (rwR (mulrC (S d * m) (/ S d))).
by rewrite (rwR (pmulr_inv m (ltr0Sn d))).
Qed.

Lemma fracr_leqPx : forall f1 f2 : frac, reflect (f1 <= f2) (leqf f1 f2).
Proof.
move=> f1 f2; case Df1: {2}f1 => [d1 m1]; case Df2: {2}f2 => [d2 m2] /=.
suffice [Hzr Hrz]: scalez d2 m1 <= scalez d1 m2 <-> f1 <= f2.
  exact: (iffP (znatr_leqPx _ _)).
rewrite leqRI (rwR (znatr_scale d2 m1)) (rwR (znatr_scale d1 m2)).
rewrite !mulRI (rwR (fracr_eq Df1)) (rwR (fracr_eq Df2)) -!mulRI.
rewrite (rwR (mulrCA (S d2) (S d1) f1)) -leqRI.
rewrite (leqr_pmul2l (S d2 * f1) (S d2 * f2) (ltr0Sn d1)).
apply: leqr_pmul2l; exact: ltr0Sn.
Qed.

Notation fracr_leqP := (fracr_leqPx _ _).

Lemma fracr_ltPx : forall f1 f2 : frac, reflect (f1 < f2) (ltf f1 f2).
Proof.
move=> f1 f2; rewrite /ltf; case (fracr_leqPx f2 f1); constructor; tauto.
Qed.

Notation fracr_ltP := (fracr_ltPx _ _).

Lemma fracrz : forall m, let f := Frac 0%nat m in m == f.
Proof. move=> m f; rewrite eqRI -(rwR (mul1r f)); exact: (@fracr_eq 0%nat). Qed.

Lemma fracr0 : F0 == 0.
Proof. apply eqr_sym; exact (fracrz 0%nat). Qed.

Lemma fracr1 : F1 == 1.
Proof. apply eqr_sym; exact (fracrz 1%nat). Qed.

Lemma fracr2 : F2 == 2.
Proof. apply eqr_sym; exact (fracrz 2%nat). Qed.

Lemma fracr_posPx : forall f : frac, reflect (f <= 0) (negb (posf f)).
Proof.
move=> f; rewrite -nposfI.
by apply: (iffP (fracr_leqPx _ _)); rewrite !leqRI (rwR fracr0).
Qed.

Notation fracr_posP := (fracr_posPx _).

Lemma fracr_opp : forall f, oppf f == - f.
Proof.
move=> [d m]; rewrite /oppf /fracR /fracr -/znatR -/natR eqRI.
rewrite !mulRI (rwR (znatr_opp m)) -!mulRI; apply: mulr_oppl.
Qed.

Lemma natr_muld : forall d1 d2 : nat, S (muld d1 d2) == S d1 * S d2.
Proof.
move=> d1 d2; apply: eqr_trans (znatr_mul (S d1) (S d2)).
by rewrite muldE mulz_nat.
Qed.

Lemma fracr_add : forall f1 f2, addf f1 f2 == f1 + f2.
Proof.
move=> f1 f2; move Df: (addf f1 f2) => f.
case Df1: {1}f1 Df => [d1 m1]; case Df2: {1}f2 => [d2 m2] /=.
set d := muld d1 d2; move/esym=> Df; apply: (pmulr_injl (ltr0Sn d)).
rewrite eqRI (rwR (mulr_addr (S d) f1 f2)) -{Df}(rwR (fracr_eq Df)).
rewrite (rwR (znatr_add (scalez d2 m1) (scalez d1 m2))) !addRI.
rewrite (rwR (znatr_scale d2 m1)) (rwR (znatr_scale d1 m2)) !mulRI {}/d.
rewrite (rwR (fracr_eq Df1)) (rwR (fracr_eq Df2)) (rwR (natr_muld d1 d2)) -!mulRI.
rewrite (rwR (mulrCA (S d2) (S d1) f1)).
by rewrite (rwR (mulrA (S d1) (S d2) f1)) (rwR (mulrA (S d1) (S d2) f2)).
Qed.

Lemma fracr_mul : forall f1 f2, mulf f1 f2 == f1 * f2.
Proof.
move=> f1 f2; move Df: (mulf f1 f2) => f.
case Df1: {1}f1 Df => [d1 m1]; case Df2: {1}f2 => [d2 m2] /=.
set d := muld d1 d2; move/esym=> Df; apply: (pmulr_injl (ltr0Sn d)).
rewrite eqRI -(rwR (fracr_eq Df)) (rwR (znatr_mul m1 m2)).
rewrite mulRI (rwR (fracr_eq Df1)) (rwR (fracr_eq Df2)) -mulRI.
rewrite -(rwR (mulrA (S d1) f1 (S d2 * f2))).
rewrite mulRI (rwR (mulrCA f1 (S d2) f2)) -mulRI.
rewrite (rwR (mulrA (S d1) (S d2) (f1 * f2))).
by rewrite mulRI -(rwR (natr_muld d1 d2)) -/d -mulRI.
Qed.

Lemma fracr_pinv : forall f, posf f -> invf f == / f.
Proof.
move=> f Hff; have Hf: 0 < f.
  move: Hff; rewrite -posfI; move/fracr_leqP.
  by rewrite leqRI /F0 -(rwR (fracrz 0%nat)) -leqRI.
apply: (pmulr_injl Hf); rewrite eqRI (rwR (divrr (gtr_neq Hf))).
case Df: {1 3}f Hff => [d [[|m]|m]] // _; rewrite /invf {2}/fracR /fracr /znatr.
rewrite -/natR (rwR (mulrA f (S d) (/ S m))) mulRI (rwR (mulrC f (S d))).
rewrite -(rwR (fracr_eq Df)) -mulRI; apply: divrr; apply gtr_neq; exact: ltr0Sn.
Qed.

(* The floor function                                                   *)


Remark ubr_floor_set : forall x : R, ubr (floor_set x) x.
Proof. by move=> x y [m]. Qed.
Hint Resolve ubr_floor_set.

Remark hasr_ub_floor_set : forall x : R, hasr (ubr (floor_set x)).
Proof. by move=> x; exists x. Qed.
Hint Resolve hasr_ub_floor_set.

Remark hasr_floor_max : forall x : R, hasr (floor_set x) -> x < floor x + 1.
Proof.
move=> x Hxlo Hx; have Hinc: forall m : znat, m <= x -> incz m <= x.
  move=> m Hm; apply: leqr_trans Hx; rewrite leqRI (rwR (znatr_inc m)) -leqRI.
  rewrite (leqr_add2r 1 m (floor x)); apply: ubr_sup; auto.
  by rewrite /znatR; split.
have Hsup: has_supr (floor_set x) by split.
case: (supr_total (floor x - 1) Hsup); last exact: ltPrr.
move=> [_ [m]]; do 2 move/Hinc.
rewrite -/znatR -{2}[m]decz_inc; move/incz: m => m Hm.
rewrite leqRI (rwR (znatr_dec m)) -!leqRI (leqr_add2r (- 1) (floor x) m).
move=> H; case: {H}(leqr_lt_trans H (ltrSr _)).
by rewrite leqRI -(rwR (znatr_inc m)) -leqRI /znatR; apply: ubr_sup; auto; split.
Qed.

Remark hasr_lb_floor_set : forall x : R, hasr (floor_set x).
Proof.
move=> x; case: (leqr_total 0 x) => Hx; first by exists (znatr R 0%nat); split.
have Hnx: has_supr (floor_set (- x)).
  split; auto; exists (znatr R 0%nat); split.
  by rewrite leqRI /= -(rwR oppr0) -leqRI (leqr_opp2 0 x).
  case: (supr_total (floor (- x) - 1) Hnx); last by case/ltPrr.
case; auto; move=> _ [m _] Hm; set m1 := incz m; set m2 := incz m1.
exists (znatr R (- m2)); split; move: Hm.
rewrite -/znatR !leqRI -[m]decz_inc -/m1 (rwR (znatr_dec m1)).
rewrite (rwR (znatr_opp m2)) -(rwR (oppr_opp x)) -!leqRI.
rewrite (leqr_add2r (- 1) (floor (- x)) m1) (leqr_opp2 m2 (- x)).
rewrite -(leqr_add2r 1 (floor (- x)) m1) leqRI -(rwR (znatr_inc m1)) -leqRI.
by apply: leqr_trans; apply ltrW; apply hasr_floor_max; case Hnx.
Qed.
Hint Resolve hasr_lb_floor_set.

Lemma has_supr_floor_set : forall x : R, has_supr (floor_set x).
Proof. by split. Qed.
Hint Resolve has_supr_floor_set.

Add Morphism (@floor _ : RR -> RR) : floor_morphism.
Proof.
move=> x x' Dx; apply: supr_morphism; first by split.
by move=> y; split; case=> m Hm {y}; split; apply: (leqr_trans Hm); case Dx.
Qed.

Add Morphism floorR : floorR_morphism.
Proof. unlock floorR; exact floor_morphism. Qed.

Add Morphism range1R : range1r_morphism.
Proof.
move=> x1 y1 x2 y2 Dx1 Dx2.
by rewrite /range1R /range1r !leqRI !addRI (rwR Dx1) (rwR Dx2).
Qed.

Lemma range1r_floor : forall x : R, range1r (floor x) x.
Proof. by move=> x; split; [ apply: leqr_sup_ub | apply hasr_floor_max ]. Qed.

Lemma znat_floor : forall x : R, exists m : znat, floor x == m.
Proof.
move=> x; case: (range1r_floor x); set y := floor x => Hyx Hxy; pose h2 : R := / 2.
have Hh2: 0 < h2 by exact: posr_inv.
have Hyh2: y - h2 < y.
  rewrite (leqr_0sub y (y - h2)) leqRI (rwR (addrC (y - h2) (- y))).
  by rewrite (rwR (addr_inv y (- h2))) -(rwR oppr0) -leqRI (leqr_opp2 0 h2).
case: (supr_total (y - h2) (has_supr_floor_set x)) => Hy2; last by case: Hyh2.
case: Hy2 => [_ [m Hmx] Hym]; rewrite -/znatR in Hmx Hym; exists m.
split; last by apply: ubr_sup; auto; rewrite /znatR; split.
apply: leqr_sup_ub; auto => _ [m' Hm'].
apply: znatr_leqP; rewrite -leqz_inc2; apply/znatr_ltP; set m1 := m + h2.
have Hym1: y <= m1.
  rewrite -(leqr_add2r (- h2) y m1); apply: (leqr_trans Hym); apply eqr_leq.
  rewrite eqRI /m1 addRI (rwR (addrC m h2)) -addRI.
  by rewrite (rwR (addrC (h2 + m) (- h2))) (rwR (addr_inv h2 m)).
move: (Hh2); rewrite -(leqr_add2l m1 h2 0) leqRI (rwR (addr0 m1)).
rewrite {1}/m1 -(rwR (addrA m h2 h2)) addRI -(rwR (mul2r h2)) /h2.
rewrite (rwR (divrr (gtr_neq ltr02))) -addRI -(rwR (znatr_inc m)) -leqRI.
by apply: leqr_lt_trans; apply: (ubr_geq_sup _ Hym1) => //; rewrite /znatR; split.
Qed.

Lemma range1z_inj : forall (x : R) (m1 m2 : znat),
  range1r m1 x -> range1r m2 x -> m1 = m2.
Proof.
move=> x.
suffice: forall m1 m2 : znat, range1r m1 x -> range1r m2 x -> (m1 <= m2)%Z.
  by move=> Hle m1 m2 Hm1 Hm2; apply: eqP; rewrite eqz_leq !Hle.
move=> m1 m2 [Hm1 _] [_ Hm2]; rewrite -leqz_inc2; apply/znatr_ltP.
rewrite leqRI (rwR (znatr_inc m2)) -leqRI; eapply leqr_lt_trans; eauto.
Qed.

Lemma range1zz : forall m : znat, range1r m m.
Proof.
move=> m; split; auto; rewrite leqRI -(rwR (znatr_inc m)) -leqRI.
apply: znatr_ltP; exact: leqzz.
Qed.

Lemma range1z_floor : forall (m : znat) (x : R), range1r m x <-> floor x == m.
Proof.
have Hlr: forall (m : znat) (x : R), floor x == m -> range1r m x.
  move=> m x Dm; rewrite range1RI -(rwR Dm); exact: range1r_floor.
move=> m x; split; auto; case: (znat_floor x) => [m' Dm'] Hm.
by rewrite -(range1z_inj (Hlr _ _ Dm') Hm).
Qed.

Lemma floor_znat : forall m : znat, floor m == m.
Proof. move=> m; rewrite -(range1z_floor m m); exact: range1zz. Qed.

Lemma find_range1z : forall x : R, exists m : znat, range1r m x.
Proof.
move=> x; case: (znat_floor x) => [m Hm]; exists m; case (range1z_floor m x); auto.
Qed.

Lemma fracr_dense : forall x y : R, x < y -> exists2 f : frac, x < f & f < y.
Proof.
move=> x y Hxy; pose z := y - x.
have Hz: z > 0 by rewrite leqRI -(rwR (subrr x)) -leqRI /z (leqr_add2r (- x) y x).
case: (find_range1z (invr z)) => [[d|m] [Hdz Hzd]].
set dd : R := S d; have Hdd: dd > 0 by exact: ltr0Sn.
case: (find_range1z (dd * x)) => [m [Hmx Hxm]].
move Df': (Frac d (incz m)) => f'; move/esym: Df' => Df'; exists f'.
- rewrite -(leqr_pmul2l f' x Hdd) {1}/dd leqRI -(rwR (fracr_eq Df')).
  by rewrite (rwR (znatr_inc m)) -leqRI.
- rewrite -(leqr_pmul2l y f' Hdd) {2}/dd leqRI -(rwR (fracr_eq Df')).
  rewrite mulRI -(rwR (addr_inv x y)) (rwR (addrC (- x) (x + y))).
  rewrite -(rwR (addrA x y (- x))) -/z -mulRI (rwR (znatr_inc m)).
  rewrite (rwR (mulr_addr dd x z)) -leqRI; move: Hmx.
  rewrite -(leqr_add2r (dd * z) m (dd * x)); apply: ltr_leq_trans.
  rewrite (leqr_add2l m (dd * z) 1).
  rewrite leqRI -(rwR (divrr (gtr_neq Hz))) (rwR (mulrC dd z)) -leqRI.
  by rewrite (leqr_pmul2l (dd : RR) (invr z) Hz) leqRI /dd (rwR (natr_S d)) -leqRI.
case Hzd; apply ltrW; apply: leqr_lt_trans (posr_inv Hz).
rewrite leqRI -(rwR (znatr_inc (Zneg m))) -leqRI.
by apply: (znatr_leqPx _ 0%nat); case m.
Qed.

(**********************************************************)
(*   The excluded middle, and lemmas that depend on       *)
(* explicit classical reasoning.                          *)
(**********************************************************)

Lemma reals_classic : excluded_middle.
Proof.
move=> P; pose E (x : R) := 0 = x \/ P /\ 2 = x.
have HhiE: (hasr (ubr E)) by exists (2 : R); move=> x [<-|[_ <-]] //; apply ltrW.
have HE: has_supr E by split; first by exists (0 : R); left.
case: (supr_total 1 HE) => HE1.
  by left; case: HE1 => [x [<-|[HP _]]] // *; case ltr01.
right; move=> HP; case: (ltrSr 1); apply: leqr_trans HE1.
by apply ubr_sup; last by right; split.
Qed.

(* Deciding comparisons. *)

Lemma leqr_eqVlt : forall x1 x2 : R, x1 <= x2 <-> x1 == x2 \/ x1 < x2.
Proof.
move=> x1 x2; rewrite /eqr.
case: (reals_classic (x2 <= x1)) (leqr_total x1 x2); tauto.
Qed.

Lemma ltr_neqAle : forall x1 x2 : R, x1 < x2 <-> x1 != x2 /\ x1 <= x2.
Proof. move=> x1 x2; rewrite (leqr_eqVlt x1 x2) /eqr; tauto. Qed.

(* Deciding definition by cases. *)

Lemma selr_cases : forall P (x1 x2 : R),
  pickr_spec P (~ P) x1 x2 (select {x1 if P, else x2}).
Proof. move=> P x1 x2; apply: pickr_cases; try tauto; exact: reals_classic. Qed.

Add Morphism (@selr _ : Prop -> RR -> RR -> RR) : selr_morphism.
Proof.
move=> P Q x1 y1 x2 y2 DP Dx1 Dx2; apply: pickr_morphism; try tauto.
exact: reals_classic.
Qed.

Add Morphism selR : selR_morphism. Proof. unlock selR; exact selr_morphism. Qed.

End RealLemmas.

Implicit Arguments neqr10 [].
Implicit Arguments ltr01 [].
Implicit Arguments ltr02 [].
Implicit Arguments ltrSr [R].
Implicit Arguments ltPrr [R].
Implicit Arguments ltr0Sn [].

Set Strict Implicit.
Unset Implicit Arguments.

