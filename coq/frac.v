(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import znat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The rationals, used only for constructing the reals and    *)
(* proving that the real axioms are categorical. We don't use *)
(* setoid rewriting here, because most identities are strict. *)

(* Scale factor product.                                      *)

Definition muld n1 n2 := n1 + iter n1 (addn n2) n2.

Lemma muldE : forall n1 n2, S (muld n1 n2) = S n1 * S n2.
Proof. by move=> n1 n2; rewrite /muld -{2}[n2]addn0 iter_f mulnC /= mulnC. Qed.

Lemma mul0d : forall n, muld 0 n = n. Proof. done. Qed.
Lemma muld0 : forall n, muld n 0 = n. Proof. by elim=> //= *; congr S. Qed.

Lemma muldC : forall n1 n2, muld n1 n2 = muld n2 n1.
Proof. by move=> *; apply eq_add_S; rewrite !muldE mulnC. Qed.

Lemma muldA : forall n1 n2 n3, muld n1 (muld n2 n3) = muld (muld n1 n2) n3.
Proof. by move=> *; apply eq_add_S; rewrite !muldE mulnA. Qed.

(* integer scaling *)

Definition scalez d m := iter d (addz m) m.

Lemma scalezE : forall d m, scalez d m = (S d * m)%Z. Proof. done. Qed.

Lemma scalez_pos : forall d n : nat, scalez d n = (S d) * n.
Proof. by move=> *; rewrite scalezE mulz_nat. Qed.

Lemma scalez0 : forall d, scalez d 0 = 0.
Proof. by move=> *; rewrite scalezE mulz0. Qed.

Lemma scalez_opp : forall d m, scalez d (- m) = (-scalez d m)%Z.
Proof. by move=> *; rewrite scalezE mulz_oppr. Qed.

Lemma scalez_add : forall d m1 m2,
  scalez d (m1 + m2) = (scalez d m1 + scalez d m2)%Z.
Proof. by move=> *; rewrite scalezE mulz_addr. Qed.

Lemma leqz_scale : forall d m1 m2, (scalez d m1 <= scalez d m2)%Z = (m1 <= m2)%Z.
Proof. by move=> *; rewrite !scalezE leqz_pmul2l. Qed.

Lemma scalez_scale : forall d1 d2 m,
  scalez d1 (scalez d2 m) = scalez (muld d1 d2) m.
Proof. by move=> *; rewrite !scalezE muldE mulzA mulz_nat. Qed.

(* Fractions                                                             *)

Inductive frac : Set := Frac : nat -> znat -> frac.

Definition leqf f1 f2 :=
  let: Frac d1 m1 := f1 in let: Frac d2 m2 := f2 in
  (scalez d2 m1 <= scalez d1 m2)%Z.

Definition ltf f1 f2 := negb (leqf f2 f1).

Lemma ltfNge : forall f1 f2, ltf f1 f2 = negb (leqf f2 f1). Proof. done. Qed.
Lemma leqfNgt : forall f1 f2, leqf f1 f2 = negb (ltf f2 f1).
Proof. by move=> *; rewrite /ltf negb_elim. Qed.

Definition eqf f1 f2 := leqf f1 f2 && leqf f2 f1.

Lemma leqff : forall f, leqf f f. Proof. case=> *; exact: leqzz. Qed.

Lemma ltff : forall f, ltf f f = false.
Proof. by move=> *; rewrite /ltf leqff. Qed.

Lemma leqf_trans : forall f1 f2 f3, leqf f1 f2 -> leqf f2 f3 -> leqf f1 f3.
Proof.
move=> [d1 m1] [d2 m2] [d3 m3] /=.
rewrite -(leqz_scale d3) !scalez_scale muldC => H12.
rewrite -(leqz_scale d1) !scalez_scale muldC => H23.
rewrite -(leqz_scale d2) !scalez_scale (muldC d2 d1); eapply leqz_trans; eauto.
Qed.

Lemma leqf_lt_trans : forall f1 f2 f3, leqf f1 f2 -> ltf f2 f3 -> ltf f1 f3.
Proof.
move=> f1 f2 f3 Hf12 Hf23; apply/idP => [Hf13]; case/idP: Hf23.
by apply: leqf_trans Hf12.
Qed.

Lemma ltf_leq_trans : forall f1 f2 f3, ltf f1 f2 -> leqf f2 f3 -> ltf f1 f3.
Proof.
move=> f1 f2 f3 Hf12 Hf23; apply/idP => [Hf13]; case/idP: Hf12.
by apply: leqf_trans Hf13.
Qed.

Lemma leqf_eqVlt : forall f1 f2, leqf f1 f2 = eqf f1 f2 || ltf f1 f2.
Proof.
by move=> [d1 m1] [d2 m2]; rewrite /eqf /ltf /= -eqz_leq negb_leqz -leqz_inc.
Qed.

Lemma ltfW : forall f1 f2, ltf f1 f2 -> leqf f1 f2.
Proof. move=> *; rewrite leqf_eqVlt; apply/orP; auto. Qed.

Lemma leqf_cases : forall f1 f2, leqf f1 f2 \/ ltf f2 f1.
Proof. move=> f1 f2; apply: orP; apply: orb_neg_b. Qed.

Lemma leqf_eql : forall f1 f2, eqf f1 f2 -> leqf f1 =1 leqf f2.
Proof.
move=> f1 f2; move/andP=> [Hf12 Hf21] f3.
apply/idP/idP => *; eapply leqf_trans; eauto.
Qed.

Lemma leqf_eqr : forall f1 f2, eqf f1 f2 -> forall f3, leqf f3 f1 = leqf f3 f2.
Proof.
move=> f1 f2; move/andP=> [Hf12 Hf21] f3.
apply/idP/idP => *; eapply leqf_trans; eauto.
Qed.

Lemma eqff : forall f, eqf f f.
Proof. by move=> *; rewrite /eqf leqff. Qed.

Lemma eqf_sym : forall f1 f2, eqf f1 f2 = eqf f2 f1.
Proof. by move=> *; rewrite /eqf andbC. Qed.

Lemma eqf_eql : forall f1 f2, eqf f1 f2 -> eqf f1 =1 eqf f2.
Proof.
by move=> f1 f2 Ef12 f3; rewrite /eqf (leqf_eql Ef12) (leqf_eqr Ef12).
Qed.

Lemma eqf_eqr : forall f1 f2, eqf f1 f2 -> forall f3, eqf f3 f1 = eqf f3 f2.
Proof.
by move=> f1 f2 Ef12 f3; rewrite /eqf (leqf_eql Ef12) (leqf_eqr Ef12).
Qed.

Lemma eqf_trans : forall f1 f2 f3, eqf f1 f2 -> eqf f2 f3 -> eqf f1 f3.
Proof. by move=> f1 f2 f3 Ef12; rewrite (eqf_eql Ef12). Qed.

Definition addf f1 f2 :=
  let: Frac d1 m1 := f1 in let: Frac d2 m2 := f2 in
  Frac (muld d1 d2) (scalez d2 m1 + scalez d1 m2).

Definition F0 := Frac 0 0.
Definition F1 := Frac 0 1.

Definition eqf0 f := if f is Frac _ (Zpos 0) then true else false.

Lemma eqf0I : forall f, eqf f F0 = eqf0 f.
Proof. by move=> [d m]; rewrite /eqf /= -eqz_leq scalez0; case: m => [[|n]|n]. Qed.

Lemma addF0 : forall f, addf f F0 = f.
Proof. by move=> [d m]; rewrite /= scalez0 muld0 addz0. Qed.

Lemma addf0 : forall f f0, eqf0 f0 -> eqf (addf f f0) f.
Proof.
by move=> [d m] [d' [[|n]|n]]; rewrite /eqf //= scalez0 addz0 scalez_scale leqzz.
Qed.

Lemma addfC : forall f1 f2, addf f1 f2 = addf f2 f1.
Proof. by move=> [d1 m1] [d2 m2] /=; rewrite muldC addzC. Qed.

Lemma addfA : forall f1 f2 f3, addf f1 (addf f2 f3) = addf (addf f1 f2) f3.
Proof.
move=> [d1 m1] [d2 m2] [d3 m3]; rewrite /= muldA; congr Frac.
by rewrite !scalez_add !scalez_scale addzA !(muldC d3).
Qed.

Lemma addfCA : forall f1 f2 f3, addf f1 (addf f2 f3) = addf f2 (addf f1 f3).
Proof. by move=> f1 f2 f3; rewrite !addfA (addfC f1). Qed.

Lemma leqf_add2l : forall f f1 f2, leqf (addf f f1) (addf f f2) = leqf f1 f2.
Proof.
move=> [d m] [d1 m1] [d2 m2] /=; rewrite -!scalez_scale leqz_scale !scalez_add.
by rewrite !scalez_scale muldC leqz_add2l -!(muldC d) -!scalez_scale leqz_scale.
Qed.

Lemma leqf_add2r : forall f f1 f2, leqf (addf f1 f) (addf f2 f) = leqf f1 f2.
Proof. by move=> f f1 f2; rewrite -!(addfC f) leqf_add2l. Qed.

Lemma leqf_add2 : forall f1 f2 f3 f4,
  leqf f1 f2 -> leqf f3 f4 -> leqf (addf f1 f3) (addf f2 f4).
Proof.
move=> f1 f2 f3 f4 Hf12 Hf34.
by apply leqf_trans with (addf f1 f4); rewrite ?leqf_add2l ?leqf_add2r.
Qed.

Lemma eqf_add2l : forall f f1 f2, eqf (addf f f1) (addf f f2) = eqf f1 f2.
Proof. by move=> *; rewrite /eqf !leqf_add2l. Qed.

Lemma eqf_add2r : forall f f1 f2, eqf (addf f1 f) (addf f2 f) = eqf f1 f2.
Proof. by move=> *; rewrite /eqf !leqf_add2r. Qed.

Definition oppf f := let: Frac d m := f in Frac d (- m).

Lemma oppF0 : oppf F0 = F0. Proof. done. Qed.

Lemma addfI : forall f, eqf0 (addf f (oppf f)).
Proof. by move=> [e m]; rewrite /= scalez_opp subzz. Qed.

Lemma addf_inv : forall f1 f2, eqf (addf (oppf f1) (addf f1 f2)) f2.
Proof. move=> *; rewrite addfCA addfA addfC; apply addf0; apply addfI. Qed.

Lemma oppf_opp : forall f, oppf (oppf f) = f.
Proof. by move=> [d m]; rewrite /= oppz_opp. Qed.

Lemma oppf_add : forall f1 f2, oppf (addf f1 f2) = addf (oppf f1) (oppf f2).
Proof. by move=> [d1 m1] [d2 m2]; rewrite /= !scalez_opp -oppz_add. Qed.

Lemma leqf_opp2 : forall f1 f2, leqf (oppf f1) (oppf f2) = leqf f2 f1.
Proof. by move=> [d1 m1] [d2 m2]; rewrite /= !scalez_opp leqz_opp2. Qed.

Lemma eqf_opp2 : forall f1 f2, eqf (oppf f1) (oppf f2) = eqf f1 f2.
Proof. by move=> *; rewrite /eqf !leqf_opp2 andbC. Qed.

(* Frac multiplication. *)

Definition mulf f1 f2 :=
  let: Frac d1 m1 := f1 in let: Frac d2 m2 := f2 in Frac (muld d1 d2) (m1 * m2).

Lemma mul0f : forall f0 f, eqf0 f0 -> eqf0 (mulf f0 f).
Proof. by move=> [d0 [[|n]|n]] [d m]. Qed.

Lemma mul1f : forall f, mulf F1 f = f. Proof. by case. Qed.

Lemma mulfC : forall f1 f2, mulf f1 f2 = mulf f2 f1.
Proof. by move=> [d1 m1] [d2 m2] /=; rewrite muldC mulzC. Qed.

Lemma mulfA : forall f1 f2 f3, mulf f1 (mulf f2 f3) = mulf (mulf f1 f2) f3.
Proof. by move=> [d1 m1] [d2 m2] [d3 m3] /=; rewrite muldA mulzA. Qed.

Lemma mulF0 : forall f, eqf (mulf f F0) F0.
Proof. by move=> *; rewrite mulfC eqf0I mul0f. Qed.

Lemma mulf1 : forall f, mulf f F1 = f.
Proof. by move=> *; rewrite mulfC mul1f. Qed.

Lemma mulfCA : forall f1 f2 f3, mulf f1 (mulf f2 f3) = mulf f2 (mulf f1 f3).
Proof. by move=> f1 f2 f3; rewrite !mulfA (mulfC f1). Qed.

Lemma mulf_oppl : forall f1 f2, mulf (oppf f1) f2 = oppf (mulf f1 f2).
Proof. by move=> [d1 m1] [d2 m2]; rewrite /= mulz_oppl. Qed.

Lemma mulf_oppr : forall f1 f2, mulf f1 (oppf f2) = oppf (mulf f1 f2).
Proof. by move=> [d1 m1] [d2 m2]; rewrite /= mulz_oppr. Qed.

Lemma scalez_1mul : forall d m, scalez d m = (scalez d 1 * m)%Z.
Proof.
move=> d m; rewrite mulzC; elim: d => [|d Hrec]; first by rewrite mulzC.
by rewrite [Zpos]lock /= -lock mulz_addr mulzC -Hrec.
Qed.

Lemma mulf_addr : forall f f1 f2,
  eqf (mulf f (addf f1 f2)) (addf (mulf f f1) (mulf f f2)).
Proof.
move=> [d m] [d1 m1] [d2 m2]; rewrite /eqf /= muldA -(muldC d) -!muldA muldC.
rewrite -!scalez_scale -scalez_add !leqz_scale -eqz_leq !scalezE.
by rewrite mulz_addr -!(mulzCA m) set11.
Qed.

Lemma mulf_addl : forall f f1 f2,
  eqf (mulf (addf f1 f2) f) (addf (mulf f1 f) (mulf f2 f)).
Proof. by move=> f *; rewrite -!(mulfC f) mulf_addr. Qed.

Definition F2 := addf F1 F1.

Lemma mulF2 : forall f, eqf (mulf F2 f) (addf f f).
Proof. by move=> f; rewrite -{2 3}[f]mul1f; apply: mulf_addl. Qed.

Definition nnegf f := if f is Frac _ (Zpos _) then true else false.

Lemma nnegfI : forall f, leqf F0 f = nnegf f.
Proof. by move=> [d [[|n]|n]] /=; rewrite scalez0. Qed.

Lemma oppf_cases : forall P : frac -> Prop,
 (forall f, nnegf f -> (P f -> P (oppf f)) /\ P f) -> forall f, P f.
Proof.
move=> P Hrec [d [n|n]]; first by case (Hrec (Frac d n)).
by case (Hrec (Frac d (S n))); simpl; auto.
Qed.

Definition posf f := negb (nnegf (oppf f)).

Lemma posfI : forall f, ltf F0 f = posf f.
Proof. by move=> *; rewrite /ltf -leqf_opp2 oppF0 nnegfI. Qed.

Lemma nposfI : forall f, leqf f F0 = negb (posf f).
Proof. by move=> *; rewrite leqfNgt posfI. Qed.

Lemma nnegf_0Vpos : forall f, nnegf f = eqf0 f || posf f.
Proof. by case=> [d [[|n]|n]]. Qed.

Lemma posf_n0Anneg : forall f, posf f = negb (eqf0 f) && nnegf f.
Proof. by case=> [d [[|n]|n]]. Qed.

Lemma posf_opp : forall f, posf (oppf f) = negb (nnegf f).
Proof. by case=> [e [[|n]|n]]. Qed.

Lemma nnegf_opp : forall f, nnegf (oppf f) = negb (posf f).
Proof. by case=> [d [[|n]|n]]. Qed.

Lemma leqf_pmul2l : forall f, posf f ->
  forall f1 f2, leqf (mulf f f1) (mulf f f2) = leqf f1 f2.
Proof.
move=> [d m] /= Hm [d1 m1] [d2 m2] /=; rewrite -!scalez_scale leqz_scale.
by rewrite !scalezE -!(mulzCA m) leqz_pmul2l; last by case: m Hm; case.
Qed.

Lemma eqf_mul2l : forall f f1 f2, eqf f1 f2 -> eqf (mulf f f1) (mulf f f2).
Proof.
move=> f f1 f2 Ef12; elim/oppf_cases: f => [f Hf]; split.
  by rewrite !mulf_oppl eqf_opp2.
rewrite nnegf_0Vpos in Hf; case/orP: Hf => Hf.
  by apply eqf_trans with F0; rewrite ?eqf0I 1?eqf_sym ?eqf0I mul0f.
by rewrite /eqf !leqf_pmul2l.
Qed.

Lemma eqf_mul2r : forall f f1 f2, eqf f1 f2 -> eqf (mulf f1 f) (mulf f2 f).
Proof. by move=> f *; rewrite -!(mulfC f) eqf_mul2l. Qed.

Lemma posf_pmull : forall f1 f2, posf f1 -> posf (mulf f1 f2) = posf f2.
Proof.
by move=> f1 f2 Hf1; rewrite -!posfI /ltf -(leqf_eqr (mulF0 f1)) leqf_pmul2l.
Qed.

(* Inverse.                                                                *)

Definition invf f :=
  match f with
  | Frac _ (Zpos 0) => f
  | Frac d (Zpos (S n)) => Frac n (S d)
  | Frac d (Zneg n) => Frac n (Zneg d)
  end.

Lemma invf_inv : forall f, invf (invf f) = f.
Proof. by move=> [d [[|n]|n]]. Qed.

Lemma invf_opp : forall f, invf (oppf f) = oppf (invf f).
Proof. by move=> [d [[|n]|n]]. Qed.

Lemma mulfI : forall f, negb (eqf0 f) -> eqf (mulf f (invf f)) F1.
Proof.
elim/oppf_cases=> [[d [[|n]|n]]] // _; split; try done.
  by rewrite mulf_oppl invf_opp mulf_oppr oppf_opp.
clear; rewrite /eqf /= -eqz_leq muldC; apply/eqP.
by rewrite scalezE mulz1 muldE -mulz_nat.
Qed.

Lemma pmulf_inv : forall f1 f2, posf f1 -> eqf (mulf (invf f1) (mulf f1 f2)) f2.
Proof.
move=> f1 f2; rewrite posf_n0Anneg; case/andP; move/mulfI=> Ef1 _.
by move: (eqf_mul2r f2 Ef1); rewrite mul1f (mulfC f1) mulfA.
Qed.

Lemma posf_inv : forall f, posf (invf f) = posf f.
Proof. by move=> [d [[|n]|n]]. Qed.

Lemma nnegf_inv : forall f, nnegf (invf f) = nnegf f.
Proof. by move=> [d [[|n]|n]]. Qed.

Lemma frac_dense : forall f1 f3, ltf f1 f3 -> {f2 : frac | ltf f1 f2 & ltf f2 f3}.
Proof.
have Ef2: (forall f : frac, eqf f (mulf (invf F2) (addf f f))).
  by move=> f; rewrite -(eqf_eql (@pmulf_inv F2 f _)) // eqf_mul2l // mulF2.
move=> f1 f3 Hf13; exists (mulf (invf F2) (addf f1 f3)).
  by rewrite /ltf (leqf_eqr (Ef2 f1)) leqf_pmul2l // leqf_add2l.
by rewrite /ltf (leqf_eql (Ef2 f3)) leqf_pmul2l // leqf_add2r.
Qed.

Set Strict Implicit.
Unset Implicit Arguments.


