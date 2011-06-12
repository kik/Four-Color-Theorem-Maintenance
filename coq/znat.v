(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import finset.
Require Import paths.
Require Import connect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Minimal handling of signed integers:                                 *)
(*    - the additive group.                                             *)
(*    - comparison                                                      *)
(*    - increment/decrement                                             *)
(*    - halving/parity                                                  *)
(*    - multiplication (mostly for the construction of the reals)       *)
(*    - summations over finite domains, and over quotients in such      *)
(*      domains                                                         *)

Inductive znat : Set :=
  | Zpos (n : nat)
  | Zneg (m : nat).

Delimit Scope znat_scope with Z.
Bind Scope znat_scope with znat.
Open Local Scope znat_scope.

Coercion Zpos: nat >-> znat.

Fixpoint subnz (m n : nat) {struct m} : znat :=
  match m, n with
  | O, _ => Zneg n
  | S m', O => m'
  | S m', S n' => subnz m' n'
  end.

Definition addz z1 z2 :=
  match z1, z2 with
  | Zpos n1, Zpos n2 => Zpos (n1 + n2)
  | Zpos n1, Zneg n2 => subnz n1 n2
  | Zneg n1, Zneg n2 => Zneg (S (n1 + n2))
  | Zneg n1, Zpos n2 => subnz n2 n1
  end.

Notation "z1 + z2" := (addz z1 z2) : znat_scope.

Lemma zpos_addn : forall n1 n2, Zpos (n1 + n2) = n1 + n2.
Proof. done. Qed.

Lemma add0z : forall z, 0 + z = z. Proof. by case. Qed.

Lemma addzC : forall z1 z2, z1 + z2 = z2 + z1.
Proof. by move=> [n|n] [m|m]; rewrite /= 1?addnC. Qed.

Lemma addz0 : forall z, z + (Zpos 0) = z.
Proof. by move=> *; rewrite addzC add0z. Qed.

Lemma addzA : forall z1 z2 z3, z1 + (z2 + z3) = z1 + z2 + z3.
Proof.
have Hsub: forall m n p, subnz (m + n) p = (subnz m p) + n.
  by move=> m n; elim: m => [|m Hrec] [|p] /=.
have Hsub': forall m n p, subnz m (S (n + p)) = (subnz m n) + Zneg p.
  by move=> m n p; elim: m n => [|m Hrec] [|n]; try exact (Hrec n).
move=> [n|n] [m|m] [p|p]; rewrite /= ?addnI ?addnS ?addnA //.
- by rewrite addnC Hsub addzC.
- by rewrite -Hsub addnC Hsub addzC.
- by rewrite -Hsub' addnC Hsub' addzC.
by rewrite addnC Hsub' addzC.
Qed.

Lemma addzCA : forall z1 z2 z3, z1 + (z2 + z3) = z2 + (z1 + z3).
Proof. by move=> z1 *; rewrite !addzA (addzC z1). Qed.

Definition oppz z := match z with
 | Zpos (S n') => Zneg n'
 | Zneg n => Zpos (S n)
 | _ => z
end.
Notation "- z" := (oppz z) : znat_scope.
Notation "z1 - z2" := (addz z1 (oppz z2)) : znat_scope.

Lemma oppzS : forall n, - S n = Zneg n. Proof. done. Qed.

Lemma oppz_opp : forall z, - - z = z.
Proof. by move=> [[|n]|n]. Qed.

Lemma subzz : forall z, z - z = Zpos 0.
Proof. by move=> [[|n]|n]; try elim: n => /=. Qed.

Lemma addz_opp_inv : forall z, monic (addz (- z)) (addz z).
Proof. by move=> z1 z2; rewrite addzA subzz add0z. Qed.

Lemma addz_inv : forall z, monic (addz z) (addz (- z)).
Proof. move=> z; rewrite -{1}[z]oppz_opp; apply: addz_opp_inv. Qed.

Lemma addz_inj : forall z, injective (addz z).
Proof. move=> z; exact: (monic_inj (addz_inv z)). Qed.

Lemma oppz_add : forall z1 z2, - (z1 + z2) = - z1 - z2.
Proof.
move=> z1 z2; apply (@addz_inj (z1 + z2)).
by rewrite subzz -addzA (addzCA z2) addzA !subzz.
Qed.

Lemma subz0 : forall z, z - 0 = z. Proof. exact: addz0. Qed.

Lemma sub0z : forall z, 0 - z = - z. Proof. move=> z; exact: add0z. Qed.

Lemma zpos_subn : forall n1 n2,
   Zpos (n1 - n2)%dnat = if (n2 <= n1)%dnat then (n1 - n2)%Z else 0.
Proof.
elim=> [|n1 Hrec] [|n2] //=; first by rewrite addn0.
by rewrite subSS Hrec ltnS; case: n2 => //; rewrite subz0.
Qed.

Lemma addz_subA : forall z1 z2 z3, z1 + (z2 - z3) = z1 + z2 - z3.
Proof. move=> *; exact: addzA. Qed.

Lemma addz_subCA : forall z1 z2 z3, z1 + (z2 - z3) = z2 + (z1 - z3).
Proof. by move=> *; exact: addzCA. Qed.

Lemma addz_sub : forall z1 z2, z1 + (z2 - z1) = z2.
Proof. by move=> *; rewrite addz_subCA subzz addz0. Qed.

Lemma addz_sub2CA : forall z1 z2 z3 z4, z1 - z2 + (z3 - z4) = z1 - z4 + (z3 - z2).
Proof. by move=> z1 z2 z3 z4; rewrite -!addzA -!(addzCA z3) (addzC (-z2)). Qed.

Lemma addz_sub2 : forall z2 z1 z3, z1 - z2 + (z2 - z3) = z1 - z3.
Proof. by move=> *; rewrite addz_sub2CA subzz addz0. Qed.

Lemma subz_add : forall z1 z2, z1 + z2 - z1 = z2.
Proof. by move=> *; rewrite -addz_subA addz_sub. Qed.

Lemma subz_sub : forall z2 z1 z3, z1 - z2 - z3 = z1 - (z2 + z3).
Proof. by move=> *; rewrite oppz_add addzA. Qed.

Lemma subz_add2l : forall z1 z2 z3, z1 + z2 - (z1 + z3) = z2 - z3.
Proof.  by move=> *; rewrite -subz_sub subz_add. Qed.

Lemma subz_add2r : forall z1 z2 z3, (z1 + z2) - (z3 + z2) = z1 - z3.
Proof. by move=> z1 z2 z3; rewrite -!(addzC z2) subz_add2l. Qed.

Lemma oppz_sub : forall z1 z2, - (z1 - z2) = z2 - z1.
Proof. by move=> *; rewrite oppz_add oppz_opp addzC. Qed.

Definition incz z := match z with
 | Zpos n => Zpos (S n)
 | Zneg O => Zpos 0
 | Zneg (S n) => Zneg n
 end.

Definition decz z := match z with
 | Zneg n => Zneg (S n)
 | Zpos O => Zneg 0
 | Zpos (S n) => Zpos n
 end.

Lemma incz_def : forall z, incz z = z + 1.
Proof. by move=> z; rewrite addzC; case: z => [n|[|n]]. Qed.

Lemma decz_def : forall z, decz z = z - 1.
Proof. by move=> z; rewrite addzC; case: z => [[|n]|n]. Qed.

Lemma incz_dec : forall x, incz (decz x) = x.
Proof. by case=> [[|n]|m]. Qed.

Lemma decz_inc : forall x, decz (incz x) = x.
Proof. by case=> [n|[|m]]. Qed.

Definition posz z := if z is Zpos (S _) then true else false.

Lemma posz_add : forall z1 z2, posz (z1 + z2) -> posz z1 \/ posz z2.
Proof. by move=> [[|n]|n] [[|m]|m]; auto. Qed.

Lemma posz_cover : forall z, or3 (posz z) (z = 0) (posz (- z)).
Proof. by move=> [[|n]|n]; [ constructor 2 | constructor 1 | constructor 3 ]. Qed.

Definition leqz z1 z2 := negb (posz (z1 - z2)).

Notation "z1 '<=' z2" := (leqz z1 z2) : znat_scope.

Lemma leqzI : forall z1 z2, negb (posz (z1 - z2)) = (z1 <= z2).
Proof. done. Qed.

Lemma leqzz : forall z, z <= z.
Proof. by move=> *; rewrite /leqz subzz. Qed.

Lemma leqz_trans : forall z2 z1 z3, z1 <= z2 -> z2 <= z3 -> z1 <= z3.
Proof.
move=> z2 z1 z3 Hz12 Hz23; rewrite /leqz -(addz_sub2 z2).
by apply/idP; case/posz_add; apply: negP.
Qed.

Lemma leqz_add2l : forall z1 z2 z3, (z1 + z2 <= z1 + z3) = (z2 <= z3).
Proof. by move=> *; rewrite /leqz subz_add2l. Qed.

Lemma leqz_add2r : forall z1 z2 z3, (z2 + z1 <= z3 + z1) = (z2 <= z3).
Proof. by move=> *; rewrite /leqz subz_add2r. Qed.

Lemma leqz_add2 : forall z1 z2 z3 z4,
   z1 <= z2 -> z3 <= z4 -> z1 + z3 <= z2 + z4.
Proof.
move=> z1 z2 z3 z4 Hz12 Hz34.
by apply (@leqz_trans (z1 + z4)); [rewrite leqz_add2l | rewrite leqz_add2r].
Qed.

Lemma leqz_opp2 : forall z1 z2, (- z1 <= - z2) = (z2 <= z1).
Proof. by move=> *; rewrite {1}/leqz oppz_opp addzC. Qed.

Lemma leqz_nat : forall m n : nat, (m <= n) = (m <= n)%dnat.
Proof.
elim=> [|m Hrec] [|n] //; rewrite ltnS -Hrec.
by case n; rewrite /leqz //= addn0.
Qed.

Lemma leq0z : forall z, (0 <= z) = negb (posz (- z)).
Proof. by move=> [[|n]|n]. Qed.

Lemma leq1z : forall z, (1 <= z) = posz z.
Proof. by move=> [[|[|n]]|n]. Qed.

Definition eqz z1 z2 := if z1 - z2 is Zpos 0 then true else false.

Lemma eqzP : reflect_eq eqz.
Proof.
move=> z1 z2; apply: introP => [Hz12|Hz12 Dz1].
  rewrite -{1}[z2]addz0; apply (monic_move (addz_opp_inv z2)).
  by move: Hz12; rewrite addzC /eqz; case: (z1 - z2) => [[|n]|n].
by rewrite Dz1 /eqz subzz in Hz12.
Qed.

Canonical Structure znatData := DataSet eqzP.

Lemma eqz_leq : forall z1 z2 : znat, (z1 =d z2) = (z1 <= z2) && (z2 <= z1).
Proof.
move=> z1 z2; apply/idP/idP;
 first by move/eqP=> Dz1; rewrite Dz1 leqzz.
move/andP=> [Hz12 Hz21]; rewrite /leqz -oppz_sub /eqd /= /eqz in Hz21 Hz12 |- *.
by case: (posz_cover (z1 - z2)) Hz21 Hz12 => ->.
Qed.

Lemma leqz_inc : forall z1 z2, (z1 <= z2) = (z1 =d z2) || (incz z1 <= z2).
Proof.
move=> z1 z2; rewrite /leqz incz_def -addzA addzCA /eqd /= /eqz.
by case: (z1 - z2); case.
Qed.

Lemma leqz_dec : forall z1 z2, (z1 <= z2) = (z1 =d z2) || (z1 <= decz z2).
Proof.
move=> z1 z2; rewrite /leqz decz_def oppz_sub addzCA /eqd /= /eqz.
by case: (z1 - z2); case.
Qed.

Lemma leqz_inc2 : forall x y, (incz x <= incz y) = (x <= y).
Proof. by move=> *; rewrite !incz_def leqz_add2r. Qed.

Lemma leqz_dec2 : forall x y, (decz x <= decz y) = (x <= y).
Proof. by move=> *; rewrite !decz_def leqz_add2r. Qed.

Lemma leqz_dec_inc : forall x y, (decz x <= y) = (x <= incz y).
Proof. by move=> *; rewrite -leqz_inc2 incz_dec. Qed.

Lemma leqz_inc_dec : forall x y, (incz x <= y) = (x <= decz y).
Proof. by move=> *; rewrite -leqz_dec2 decz_inc. Qed.

Lemma leq_z_incz : forall x, x <= incz x.
Proof. by move=> *; rewrite leqz_inc leqzz orbT. Qed.

Lemma leq_decz_z : forall x, decz x <= x.
Proof. by move=> *; rewrite leqz_dec leqzz orbT. Qed.

Lemma leq_decz_incz : forall x, decz x <= incz x.
Proof. by move=> *; rewrite leqz_dec decz_inc leq_decz_z orbT. Qed.

Lemma negb_leqz : forall x y, negb (x <= y) = (incz y <= x).
Proof.
move=> x y; rewrite {2}/leqz -oppz_sub incz_def -subz_sub /leqz.
by case: (x - y) => [[|[|n]]|m].
Qed.

(* Parity & halving.                                 *)

Definition oddz z := match z with Zpos n => odd n | Zneg m => negb (odd m) end.

Lemma oddz_add : forall z1 z2, oddz (z1 + z2) = oddz z1 +b oddz z2.
Proof.
have Hsnz: forall m n, oddz (subnz m n) = negb (odd m +b odd n).
  elim=> //= [m Hrec] [|n] /=; first by rewrite addbF negb_elim.
  rewrite Hrec -!addbT; congr addb; rewrite -!addbA; congr addb.
  by rewrite addbC -addbA addbC.
move=> [m1|n1] [m2|n2] //=; rewrite ?odd_addn ?Hsnz //= -!addbT -!addbA //.
  by rewrite addbC -addbA.
by congr addb; rewrite addbA addbC.
Qed.

Lemma oddz_double : forall z, oddz (z + z) = false.
Proof. by move=> *; rewrite oddz_add addbb. Qed.

Definition halfz z := match z with
  | Zpos n => Zpos (half n)
  | Zneg m => Zneg (half m)
  end.

Lemma oddz_bit : forall b : bool, oddz b = b.
Proof. by case. Qed.

Lemma halfz_double : forall z, halfz (z + z) = z.
Proof. by case=> *; rewrite /= -double_addnn ?half_double ?uphalf_double. Qed.

Lemma halfz_bit : forall b : bool, halfz b = 0.
Proof. by case. Qed.

Lemma odd_double_halfz : forall z, oddz z + (halfz z + halfz z) = z.
Proof.
case=> [n|m]; first by rewrite /= -double_addnn odd_double_half.
rewrite {1}[addz]lock /= -lock -double_addnn -add1n.
by rewrite -(addn_negb (odd m)) -addnA odd_double_half; case (odd m).
Qed.

Lemma halfz_add_double : forall z1 z2, halfz (z1 + (z2 + z2)) = halfz z1 + z2.
Proof.
move=> z1 z2; rewrite -{1}[z1]odd_double_halfz -!addzA -(addzCA z2).
rewrite (addzA _ z2); case: (oddz z1) (halfz z1 + z2) => [|] [m|n] //=;
 by rewrite ?add0n -double_addnn ?half_double ?uphalf_double.
Qed.

Lemma leqz_halfr : forall x y, (x <= halfz y) = (x + x <= y).
Proof.
move=> x y; rewrite -{2}[y]odd_double_halfz; move: {y}(oddz y) (halfz y) => b y.
rewrite /leqz !oppz_add addzCA -addzA (addzCA _ (-y)) (addzA x).
by case: (x - y) b => [[|n]|[|m]] [|] //=; rewrite addnS.
Qed.

Lemma leqz_halfl : forall x y, (halfz x <= y) = (x <= incz (y + y)).
Proof.
move=> x y; rewrite -(leqz_inc2 x) -negb_leqz !incz_def addzC -!addzA addzCA.
by rewrite addzA -incz_def -leqz_halfr negb_leqz leqz_inc2.
Qed.

(* Multiplication.                                           *)

Definition mulz z1 z2 :=
  match z1 with
  | Zpos O => z1
  | Zpos (S n) => iter n (addz z2) z2
  | Zneg n => - (iter n (addz z2) z2)
  end.

Notation "z1 * z2" := (mulz z1 z2) : znat_scope.

Lemma mulz0 : forall z, z * 0 = 0.
Proof. by move=> [[|n]|n] //=; elim: n => // [n Hrec]; rewrite -iter_f. Qed.

Lemma mul0z : forall z, 0 * z = 0. Proof. done. Qed.

Lemma mulz_oppl : forall z1 z2, - z1 * z2 = - (z1 * z2).
Proof. by move=> [[|n]|n] //= z2; rewrite oppz_opp. Qed.

Lemma oppz_cases : forall P : znat -> Type,
 (forall z, P z -> P (- z)) -> (forall n : nat, P n) -> forall z, P z.
Proof.
move=> P Hopp Hpos z; rewrite -(oppz_opp z).
case: z => [n|n] //; auto; apply Hopp; apply: Hpos.
Qed.

Lemma mulz_oppr : forall z1 z2, z1 * (- z2) = - (z1 * z2).
Proof.
elim/oppz_cases; first by move=> m1 Hrec m2; rewrite !mulz_oppl Hrec.
by move=> [[|n]|n] //= z2; elim: n => [|n Hrec] //=; rewrite Hrec oppz_add.
Qed.

Lemma mulz_nat : forall n1 n2 : nat, n1 * n2 = (n1 * n2)%dnat.
Proof.
by move=> [|n1] n2 //=; elim: n1 => [|n1 Hrec] /=; rewrite ?addn0 ?Hrec.
Qed.

Lemma mulzC : forall z1 z2, z1 * z2 = z2 * z1.
Proof.
elim/oppz_cases=> [z1 Hz1|n1] z2; first by rewrite mulz_oppl mulz_oppr Hz1.
elim/oppz_cases: z2 => [z2 Hz2|n2]; first by rewrite mulz_oppl mulz_oppr Hz2.
by rewrite !mulz_nat mulnC.
Qed.

Lemma mulzA : forall z1 z2 z3, z1 * (z2 * z3) = z1 * z2 * z3.
Proof.
move=> z1 z2 z3; elim/oppz_cases: z1 => [z1 Hz1|n1].
  by rewrite !mulz_oppl Hz1.
elim/oppz_cases: z2 => [z2 Hz2|n2].
  by rewrite mulz_oppr !mulz_oppl mulz_oppr Hz2.
elim/oppz_cases: z3 => [z3 Hz3|n3]; first by rewrite !mulz_oppr Hz3.
by rewrite !mulz_nat mulnA.
Qed.

Lemma mulzCA : forall z1 z2 z3, z1 * (z2 * z3) = z2 * (z1 * z3).
Proof. by move=> z1 z2 z3; rewrite !mulzA (mulzC z1). Qed.

Lemma mul1z : forall z, 1 * z = z. Proof. done. Qed.
Lemma mulz1 : forall z, z * 1 = z. Proof. by move=> *; rewrite mulzC. Qed.

Lemma mulz_addr : forall z z1 z2, z * (z1 + z2) = (z * z1) + (z * z2).
Proof.
move=> z z1 z2; elim/oppz_cases: z => [z Hz|n].
  by rewrite !mulz_oppl -oppz_add Hz.
case: n => //=; elim=> [|n Hrec] //=.
by rewrite Hrec -!addzA; congr addz; rewrite addzCA.
Qed.

Lemma posz_mull : forall z z1, posz z -> posz (z * z1) = posz z1.
Proof.
case=> [[|n]|m] // [n1|m1] _; first by rewrite mulzC mulz_nat; case n1.
by rewrite -oppzS mulz_oppr mulz_nat.
Qed.

Lemma leqz_pmul2l : forall z z1 z2, posz z -> (z * z1 <= z * z2) = (z1 <= z2).
Proof.
move=> z z1 z2 Hz; congr negb; rewrite -mulz_oppr -mulz_addr; exact: posz_mull.
Qed.

(* A small theory of summations over finite subsets. *)

Section ZnatSums.

Variable d : finSet.

Definition sumz f a := foldr (fun x => addz (f x)) (0) (filter a (enum d)).

Lemma sumz0 : forall f, sumz f set0 = 0.
Proof. by move=> *; rewrite /sumz filter_set0. Qed.

Lemma eq_sumz_r : forall a b : set d, a =1 b -> forall f, sumz f a = sumz f b.
Proof. by move=> a b Eab f; rewrite /sumz (eq_filter Eab). Qed.

Lemma eq_sumz_l : forall f g (a : set d),
  (forall x, a x -> f x = g x) -> sumz f a = sumz g a.
Proof.
move=> f g a Efg; rewrite /sumz; elim: (enum d) => //= [x s Hrec].
by case Hx: (a x) => //=; rewrite Hrec Efg.
Qed.

Lemma eq_sumz : forall f g, f =1 g -> sumz f =1 sumz g.
Proof. move=> f g Efg a; apply: eq_sumz_l => x _; exact: Efg. Qed.

Lemma sumz_sub : forall f g a, sumz (fun x => f x - g x) a = sumz f a - sumz g a.
Proof.
move=> f g a; rewrite /sumz; elim: (filter a (enum d)) => //= x p ->.
by rewrite -subz_sub -!addzA (addzCA (- g x)).
Qed.

Definition zconst n (_ : d) := Zpos n.

Lemma zconstI : forall n, (fun _ => Zpos n) = zconst n.
Proof. done. Qed.

Lemma sumz_const : forall n a, sumz (zconst n) a = (n * card a)%dnat.
Proof.
move=> n a; rewrite /sumz /card count_filter mulnC.
by elim: {a}(filter a (enum d)) => [|x p Hrec] //=; rewrite Hrec.
Qed.

Lemma sumz_opp : forall f a, sumz (fun x => oppz (f x)) a = oppz (sumz f a).
Proof.
move=> f a; apply: etrans (etrans (sumz_sub (zconst 0) f a) _).
  by apply: eq_sumz => x; rewrite sub0z.
by rewrite sumz_const sub0z.
Qed.

Lemma sumz_add : forall f g a, sumz (fun x => f x + g x) a = sumz f a + sumz g a.
Proof.
move=> f g a; apply: etrans (etrans (sumz_sub f (fun x => - g x) a) _).
  by apply: eq_sumz => x; rewrite oppz_opp.
by rewrite sumz_opp oppz_opp.
Qed.

Lemma sumz_setID : forall b f a, sumz f a = sumz f (setI a b) + sumz f (setD a b).
Proof.
move=> b f a; rewrite /sumz; elim: (enum d) => [|x p Hrec] //=.
rewrite {1}/setD andbC {1}/setI /id; case (a x); rewrite //= Hrec.
by case (b x); rewrite /= -?addzA -?(addzCA (f x)).
Qed.

Lemma sumz_set1 : forall f x, sumz f (set1 x) = f x.
Proof.
move=> f x; move: (count_set1_enum x) (filter_enum (eqd x) x).
rewrite /sumz count_filter; case: (filter _ _) => [|y [|z p]] // _.
by rewrite /= set11 /setU1 orbF addz0; move/eqP=> ->.
Qed.

Lemma sumz_roots : forall e, connect_sym e -> forall f,
  sumz (fun x => sumz f (connect e x)) (roots e) = sumz f d.
Proof.
move=> e He f; set a := @setA d; rewrite (sumz_setID a) addzC.
rewrite -(@eq_sumz_r set0) // sumz0 add0z.
have: closed e a by done.
elim: {a}(S (card a)) {-2}a (ltnSn (card a)) => [|n Hrec] a //.
case: (pickP a) => [x Hx|Ha0] Hn Ha.
  rewrite (sumz_setID (set1 (root e x))) (sumz_setID (connect e x) f a).
  congr addz.
    apply: etrans (etrans (eq_sumz_r _ _) (sumz_set1 _ (root e x))) _.
    move=> y; rewrite /setI andbC; case: (root e x =P y) => // <-.
      by rewrite (roots_root He) /= -(closed_connect Ha (connect_root e x)).
    apply: eq_sumz_r => y; rewrite -(same_connect He (connect_root e x)).
    rewrite /setI andbC; case Hxy: (connect e x y); last done.
    by rewrite -(closed_connect Ha Hxy).
  apply: etrans (eq_sumz_r _ _) (Hrec _ _ _) => [y||y z Hyz].
  - rewrite /setD /setI; case Hy: (roots e y); rewrite /= ?andbF //.
    by rewrite -{1}(eqP Hy) (sameP eqP (rootPx He x y)).
  - rewrite ltnS -(cardIC (connect e x)) in Hn.
    apply: (leq_trans _ Hn); rewrite -add1n; apply leq_add2.
      by rewrite ltnNge leqn0; apply/set0Pn; exists x; rewrite /setI Hx connect0.
    by apply: subset_leq_card; apply/subsetP => y; rewrite /setD andbC.
  by rewrite /setD (Ha _ _ Hyz) !(He x) (same_connect He (connect1 Hyz)).
rewrite (eq_sumz_r Ha0) -(@eq_sumz_r set0) ?sumz0 //.
by move=> y; rewrite /setI Ha0 andbF.
Qed.

Lemma posz_sum : forall f a, posz (sumz f a) -> exists2 x, a x & posz (f x).
Proof.
move=> f a; rewrite /sumz; elim: (enum d) => [|x p Hrec] //=.
by case Hx: (a x) => [] //=; case/posz_add; first by exists x.
Qed.

Lemma sumz_perm : forall h, injective h -> forall a, fclosed h a ->
  forall f, sumz (fun x => f (h x)) a = sumz f a.
Proof.
move=> h Hh a Ha f; set ea := filter a (enum d).
have Ea: a =1 maps h ea.
  move=> x; apply/idP/mapsP => [Hx|[y Hy <-]].
    exists (finv h x); last by apply f_finv.
    by rewrite /ea filter_enum (fclosed1 Ha) f_finv.
  by move: Hy; rewrite /ea filter_enum (fclosed1 Ha).
  rewrite {Ha Ea}(eq_sumz_r Ea f) {1}/sumz -/ea.
have Uea: (uniq ea) by exact (uniq_filter _ (uniq_enum d)).
elim: {a}ea Uea => [|x p Hrec]; rewrite /= ?sumz0 //.
move/andP=> [Hx Up]; rewrite {Hrec Up}(Hrec Up).
apply: (etrans _ (esym (sumz_setID (eqd (h x)) _ _))); congr addz.
  rewrite -(eq_sumz_r (a := eqd (h x))) ?sumz_set1 // /setU1 /setI.
  by move=> y /=; case (h x =d y); rewrite ?andbF.
apply: eq_sumz_r => [y]; rewrite /setD /setU1.
by case: (h x =P y) => // <-; rewrite (mem_maps Hh) (negbE Hx).
Qed.

End ZnatSums.

Unset Implicit Arguments.