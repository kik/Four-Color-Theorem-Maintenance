(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import paths.
Require Import znat.
Require Import real.
Require Import realmap.
Require Import realsyntax.
Require Import realprop.
Require Import grid.
Require Import approx.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FinitizeMap.

(* We use a special case of the compactness theorem for predicate logic to *)
(* extend the four color theorem from finite to arbitrary maps. We can     *)
(* dispense with the axiom of choice because of the local compactness of   *)
(* the plane. This is the only part of the development that is             *)
(* intrinsically classical.                                                *)

Variable R : real_model.

Notation point := (point R).
Notation region := (region R).
Notation map := (map R).
Notation rect := (rect R).
Notation interval := (interval R).

Let Hclassical : excluded_middle := reals_classic R.

Variable nc : nat.
Hypothesis Hfin : forall m : map, finite_simple_map m -> map_colorable nc m.

Variable m0 : map.
Hypothesis Hm0 : simple_map m0.

(* We will deduce an enumeration of regions from a canonical enumeration of *)
(* of grid points.                                                          *)

Definition pairn sn := let: (s, n) := sn in pred (iter s double (S (double n))).

Fixpoint unpairn_rec (s r n : nat) {struct n} : nat * nat :=
  match r, n with
  | S (S r'), S n' => unpairn_rec s r' n'
  | S O, S n' => unpairn_rec (S s) n' n'
  | _, _ => (s, n)
  end.

Definition unpairn m := unpairn_rec 0 m m.

Lemma pairn_unpair : monic unpairn pairn.
Proof.
move=> m; symmetry; transitivity (pred (iter 0 double (S (double m - m)))).
  by rewrite double_addnn subn_addl.
rewrite /unpairn; elim: m {1 4 5}m 0 (leqnn m) => [|n Hrec] [|[|r]] s //= Hr.
case: (unpairn_rec (S s) n n) {Hrec Hr}(Hrec _ (S s) (leqnn _)) => [s' n'] <-.
  by rewrite (double_addnn n) subn_addl -iter_f.
by case: (unpairn_rec s r n) {Hrec Hr}(Hrec r s (leqW Hr)) => [s' n'] <-.
Qed.

Lemma unpairn_pair : monic pairn unpairn.
Proof.
move=> sn; move: (pairn_unpair (pairn sn)).
case: sn (unpairn (pairn sn)) => [s n] [s' n'] /= Ess'.
have Dss': iter s' double (S (double n')) = iter s double (S (double n)).
  have Em: forall s1 m1, let m := iter s1 double (S m1) in S (pred m) = m.
    move=> s1 m1 /=; apply: ltnSpred 0 _; elim: s1 => //= [s1 Hrec].
    by rewrite -double0 ltn_double.
  by rewrite -Em Ess' Em.
elim: s s' Dss' {Ess'} => [|s Hrec] [|s'] H;
 move: {H}(congr1 odd H) (congr1 half H);
 rewrite /= ?odd_double ?half_double ?uphalf_double //; clear; auto.
by case/(Hrec s') => <- <-.
Qed.

Definition injzn m := match m with Zpos n => double n | Zneg n => S (double n) end.

Definition uninjzn n := (if odd n then Zneg else Zpos) (half n).

Lemma uninjzn_inj : monic injzn uninjzn.
Proof.
by case=> *; rewrite /uninjzn /= odd_double ?half_double ?uphalf_double.
Qed.

Lemma injzn_uninj : monic uninjzn injzn.
Proof. by move=> n; rewrite -{2}[n]odd_double_half /uninjzn; case (odd n). Qed.

Definition std_point i : point :=
  let: (s, mxy) := unpairn i in let: (mx, my) := unpairn mxy in
  scale_point R s (Gpoint (uninjzn mx) (uninjzn my)).

Lemma has_std_point : forall z, inmap m0 z -> exists i, m0 z (std_point i).
Proof.
move=> z Hz; case: (map_open Hm0 Hz) => [rr Hrrz Hrrm].
case: (approx_rect Hrrz) => [s [b [p Hp Hbp] Hbr]]; move Dp: p => [mx my].
exists (pairn (s, pairn (injzn mx, injzn my))); apply: Hrrm; apply: Hbr.
rewrite /std_point !unpairn_pair !uninjzn_inj -Dp.
apply: (mem_approx_scale R s b p); apply: (mem_sub_grect Hbp); exact: gtouch_refl.
Qed.

Definition in_partial n : region := fun z => exists2 i, i < n & m0 z (std_point i).

Lemma leq_partial : forall n1 n2, n1 <= n2 ->
  subregion (in_partial n1) (in_partial n2).
Proof.
by move=> n1 n2 Hn12 z [i Hi Hz]; exists i; first exact: leq_trans Hn12.
Qed.

Lemma partial_trans : forall n z, in_partial n z ->
  subregion (m0 z) (in_partial n).
Proof.
move=> n z1 [i Hi Hz1] z2 Hz12; exists i; auto.
apply: (map_trans Hm0) Hz1; exact: (map_sym Hm0).
Qed.

Lemma proper_inmap_r : forall m : map, proper_map m ->
  forall z, subregion (m z) (inmap m).
Proof. move=> m [Sm Tm] z1 z2 Hz12; apply: Tm (Hz12); exact: Sm. Qed.

Lemma proper_inmap_l : forall m : map, proper_map m ->
 forall z, subregion (fun t => m t z) (inmap m).
Proof. move=> m Hm z1 z2; move/(map_sym Hm); exact: proper_inmap_r. Qed.

Definition partial_map n (m : map) : map :=
  fun z1 z2 => and3 (m z1 z2) (in_partial n z1) (in_partial n z2).

Lemma leq_partial_map : forall n1 n2, n1 <= n2 ->
  forall m, covers (partial_map n1 m) (partial_map n2 m).
Proof.
move=> n1 n2; move/leq_partial=> Hn12 m z1 z2 [Hz12 Hz1 Hz2]; split; auto.
Qed.

Lemma covers_partial_map : forall n m, covers (partial_map n m) m.
Proof. by move=> n m z1 z2; case. Qed.

Lemma proper_partial_map : forall n m, proper_map m ->
  proper_map (partial_map n m).
Proof.
move=> n m [Sm Tm]; split; first by move=> z1 z2 [Hz12 Hz1 Hz2]; split; auto.
by move=> z1 z2 [Hz12 Hz1 _] z3 [Hz23 _ Hz3]; split; auto; apply: Tm Hz23.
Qed.

Lemma finite_partial_map : forall n, finite_simple_map (partial_map n m0).
Proof.
move=> n; split.
  split; try exact (proper_partial_map n Hm0).
  move=> z1 z2 [Hz12 Hz1 Hz2]; case: (map_open Hm0 Hz12) => [rr Hrr2 Hrr].
    exists rr; auto; move=> t Ht; split; auto; apply: (partial_trans Hz1); auto.
  move=> z r1 r2 Hrz [z1 [Hr1z1 [Hzz1 Hz _]]] [z2 [Hr2z2 [Hzz2 _ _]]].
  apply: ((map_connected Hm0) z); [ idtac | exists z1 | exists z2 ]; try by split.
  by move=> t Ht; apply Hrz; split; auto; exact: partial_trans Ht.
exists n; exists std_point; move=> z [_ [i Hi Hzi] Hz].
exists i; first exact: ltP.
by split; auto; [ exact: (map_sym Hm0) | exact: (partial_trans Hz) ].
Qed.

Lemma size_partial_map : forall n k, proper_map k -> size_at_most nc k ->
  size_at_most nc (partial_map n k).
Proof.
move=> n m Hk [f Hf].
suffice [f' Hf']: exists f', forall j, j < nc ->
    forall z, in_partial n z -> m (f j) z -> partial_map n m (f' j) z.
- exists f'; move=> z [Hkz Hz _]; case: (Hf _ Hkz) => i; exists i; auto.
  by apply: Hf'; first apply/ltP.
elim: nc => [|i [f' Hf']]; first by exists f.
case: (Hclassical (nonempty (intersect (m (f i)) (in_partial n)))).
  move=> [zi [Hkzi Hzi]]; exists (fun j => if j =d i then zi else f' j).
  move=> j; rewrite ltnS leq_eqVlt; case: (j =P i) => //=; auto.
  move=> -> _ z Hz Hiz; split; auto.
  by apply: (map_trans Hk) Hiz; exact: (map_sym Hk).
move=> Hi; exists f' => j; rewrite ltnS leq_eqVlt; case: (j =P i) => //=; auto.
by move=> -> _ z Hz Hiz; case Hi; exists z; split; auto.
Qed.

Record quasi_coloring (k : map) : Prop := QuasiColoring {
  qc_proper :> proper_map k;
   qc_inmap : subregion (inmap k) (inmap m0);
   qc_size : size_at_most nc k;
   qc_adj : forall z1 z2, k z1 z2 -> adjacent m0 z1 z2 -> m0 z1 z2
}.

Lemma quasi_coloring_partial : forall n k, quasi_coloring k ->
   quasi_coloring (partial_map n k).
Proof.
move=> n m [Hk Hkm0 Hnck Hka]; split.
- exact: proper_partial_map.
- by move=> z [Hz _ _]; auto.
- exact: size_partial_map.
move=> z1 z2 [Hkz12 _ _]; exact: Hka.
Qed.

Definition partial_coloring n k := quasi_coloring k /\ covers (partial_map n m0) k.

Lemma exist_partial_coloring : forall n,
 exists2 k, partial_coloring n k & subregion (inmap k) (in_partial n).
Proof.
move=> n; case: (Hfin (finite_partial_map n)) => [k [Hk Hkn Hnk Hka] Hknc].
exists k; last by move=> z Hz; case (Hkn _ Hz).
do 2 (split; auto); first by move=> z Hz; case (Hkn _ Hz).
have Hb: forall z t, in_partial n z -> closure (m0 z) t ->
    closure (partial_map n m0 z) t.
  move=> z t Hz Hzt r Hr Hrt; case: (Hzt r) => // [] u [Hzu Hru].
  by exists u; repeat split; auto; exact: partial_trans Hzu.
move=> z1 z2 Hk12 [z [[f Hf] [Hzz1 Hzz2]]]; case: (Hka _ _ Hk12) => //.
case: (Hkn _ (proper_inmap_l Hk Hk12)) => [_ Hz1 _].
case: (Hkn _ (proper_inmap_r Hk Hk12)) => [_ Hz2 _].
exists z; split; last by split; auto.
exists f; move=> t [[Ht Htn _] Htz]; case (Hf t).
split; auto; move=> r Hr Hrz; case: (Htz r) => // u [[Htu _ _] Hru].
  by exists u; split.
move=> i Hi [Hit Hiz]; have Hfi: in_partial n (f i).
  by apply (partial_trans Htn); exact: (map_sym Hm0).
exists i; auto; do 2 (split; auto).
Qed.

Lemma leq_partial_coloring : forall n1 n2, n1 <= n2 ->
 forall k, partial_coloring n2 k -> partial_coloring n1 k.
Proof.
move=> n1 n2 Hn12 k [Hk Hkn]; split; auto.
by move=> z1 z2 Hz12; apply: Hkn; exact: (leq_partial_map Hn12).
Qed.

Definition partial_eq n k k' :=
  covers (partial_map n k) k' /\ covers (partial_map n k') k.

Lemma partial_eq_sym : forall n k k', partial_eq n k k' -> partial_eq n k' k.
Proof. by move=> n k k'; case; split. Qed.

Lemma partial_eq_trans : forall n k k' k'',
 partial_eq n k k' -> partial_eq n k' k'' -> partial_eq n k k''.
Proof.
move=> n k1 k2 k3 [Hk12 Hk21] [Hk23 Hk32].
by split; move=> z1 z2 [Hz12 Hz1 Hz2]; [ apply Hk23 | apply Hk21 ]; split; auto;
  [ apply Hk12 | apply Hk32 ]; split.
Qed.

Lemma partial_eq_partial : forall n k, partial_eq n k (partial_map n k).
Proof. by move=> n k; split; move=> z1 z2; last by do 2 case. Qed.

Lemma leq_partial_eq : forall n1 n2, n1 <= n2 ->
 forall k k', partial_eq n2 k k' -> partial_eq n1 k k'.
Proof.
move=> n1 n2; move/leq_partial_map=> Hn12 k k' [Hkk' Hk'k].
by split; move=> z1 z2 Hz12; [ apply: Hkk' | apply: Hk'k ]; exact: Hn12.
Qed.

Definition extensible n k :=
  and3 (quasi_coloring k) (subregion (inmap k) (in_partial n))
       (forall n', exists2 k', partial_coloring n' k' & partial_eq n k k').

Lemma extensible_partial : forall n k, extensible n k -> partial_coloring n k.
Proof.
move=> n k [Hk Ek Xk]; case: {Xk}(Xk n) => [k' [Hk' Hk'n] [Hkk' Hk'k]].
by split; auto; move=> z1 z2 Hz12; apply Hk'k; case Hz12; split; auto; apply Hk'n.
Qed.

Lemma leq_extensible : forall n1 n2, n1 <= n2 ->
  forall k, extensible n2 k -> extensible n1 (partial_map n1 k).
Proof.
move=> n1 n2; move/leq_partial_eq=> Hn12 k [Hk Ek Xk].
split; try by first [ exact: quasi_coloring_partial | move=> z [_ Hz _] ].
move=> n; case: (Xk n) => [k' Hk' Ek']; exists k'; auto.
apply: (partial_eq_trans (partial_eq_sym (partial_eq_partial n1 k))); auto.
Qed.

Definition min_partial1 i k :=
  forall j' k',
    let zi := std_point i in let zj' := std_point j' in
    partial_eq i k k' -> extensible (S i) k' -> k' zj' zi ->
  exists2 j, j <= j' & k (std_point j) zi.

Fixpoint min_partial (n : nat) (k : map) {struct n} : Prop :=
  if n is S i then min_partial1 i k /\ min_partial i k else True.

Definition exact_partial n k := min_partial n k /\ extensible n k.

Lemma exists_exact_partial : forall n, exists k, exact_partial n k.
Proof.
pose ak (k : map) i j := k (std_point i) (std_point j).
pose inm0 j := inmap m0 (std_point j).
have Hinm0: forall i j, j < i -> inm0 j -> in_partial i (std_point j).
  by move=> i j; exists j.
pose akn i i' k k' := partial_eq i k k' /\ partial_coloring i' k'.
pose akm i i' j j' k k' := akn i i' k k' -> ak k' i j' -> j <= j'.
pose akx i j k := exists2 i', i < i' & (forall j' k', akm i i' j j' k k').
elim=> /= [|i [k [Hkm [Hk Hkn Xk]]]].
  exists (fun z1 z2 : point => False); do 2 split; try by move.
    by split; [ split | move | exists std_point | done ].
  move=> n; case: (exist_partial_coloring n) => [k [Hk Hnk] Hkn].
  by exists k; split=> // z1 z2 [] _ [].
case: (Hclassical (akx i (S i) k)).
  case: (Hclassical (inm0 i)) => Hm0i.
    move=> [n' Hin' Hn']; case: (Xk n') => [k' Hk' Ekk']; case/idP: (ltnn i).
    by apply: (Hn' _ k'); [ split | case: Hk' => _; apply; split=> //; exists i ].
  have Ei: subregion (in_partial (S i)) (in_partial i).
    move=> z [j Hj Hz]; rewrite ltnS leq_eqVlt in Hj.
    case/setU1P: Hj => [Dj|Hj]; last by exists j.
    by case: Hm0i; apply: ((proper_inmap_r Hm0) z); rewrite -Dj.
  clear; exists k; split.
    split; last done; move=> j' k' /= _ [[Hk' Hm0k' _ _] _ _] Hj'i.
    case Hm0i; apply: Hm0k'; exact (proper_inmap_r Hk' Hj'i).
  split; auto; first by move=> z Hz; apply (leq_partial (leqnSn i)); auto.
  move=> n'; case: (Xk n') => [k' Hk' [Ekk' Ek'k]]; exists k'; auto.
  split; move=> z1 z2 [Hz12 Hz1 Hz2]; [ apply: Ekk' | apply: Ek'k ]; split; auto.
  elim: {1 3}(S i) (ltnSn i) {Xk} => [|j Hrec] Hj HSj.
  by case HSj; exists (S i); first exact: leqnn.
case: (Hclassical (akx i j k)) => [[n1 Hin1 Hn1]|]; last by apply Hrec; apply ltnW.
clear Hrec; pose extij n2 := exists2 k2, akn i n2 k k2 & ak k2 i j.
have Hxn1: forall n2, n1 <= n2 -> extij n2.
  move=> n2 Hn12; case: (Hclassical (extij n2)) => // Nk2; case: HSj.
  exists n2; [ exact: leq_trans Hn12 | move=> j' k' [Ekk' Hk'] Hk'j' ].
  rewrite ltn_neqAle andbC (Hn1 j' k') //;
    last by split; last exact: (leq_partial_coloring Hn12).
  apply/eqP => Dj'; rewrite -Dj' in Hk'j'.
  by case Nk2; exists k'; first by split.
case: (Hxn1 _ (leqnn n1)) {HSj} => [k1 Hk1 Ek1i].
case: Hk1 (Hn1 _ _ Hk1) => [Ekk1 Hk1] Hk1i.
have [Hm0i Hm0j]: inm0 i /\ inm0 j.
  case: Hk1 => [[Hk1 Hm0k1 _ _] _].
  move: (proper_inmap_l Hk1 Ek1i) (proper_inmap_r Hk1 Ek1i); split; exact: Hm0k1.
pose k2 := partial_map (S i) k1; have HSi := ltnSn i; have HSi' := leqnSn i.
have Ek2i: ak k2 i j by split; auto.
have Ekk2: partial_eq i k k2.
  exact (partial_eq_trans Ekk1 (leq_partial_eq HSi' (partial_eq_partial _ _))).
have Hk2: quasi_coloring k2 by apply: quasi_coloring_partial; case Hk1.
exists k2; do 2 split; auto; try by move=> z; case.
- move=> j' k' /= Ek2k' Hk' Ek'i; exists j; last exact: (map_sym Hk2).
  case: Hk' => [Hk' Hk'i Xk']; case: (Xk' n1) => [k'' Hk'' Ek''].
  apply: (Hn1 _ k'').
    split; auto; apply: (partial_eq_trans Ekk2); apply: (partial_eq_trans Ek2k').
    exact: (leq_partial_eq HSi').
  case: Ek'' => [H _]; apply: H; split; auto; first exact: (map_sym Hk').
  apply Hk'i; exact (proper_inmap_l Hk' Ek'i).
- elim: {-2}i (leqnn i) Hkm => //= [i1 Hrec] Hi1 [Hki1 Hkm].
  split; last by apply: Hrec Hkm; exact: ltnW.
  move=> j' k' /= Ek' Hk' Hk'j'.
  have Ekk': partial_eq i1 k k'.
    by apply: partial_eq_trans Ek'; exact: (leq_partial_eq (ltnW Hi1)).
  case: {Hki1}(Hki1 j' k' Ekk' Hk' Hk'j') => [j1 Hj1j' Ekj1].
  exists j1; first done; move: Ekk2 => [H _]; apply: H.
  suffice: in_partial i (std_point j1) /\ in_partial i (std_point i1).
    by case; split.
  by move: (proper_inmap_l Hk Ekj1) (proper_inmap_r Hk Ekj1); split; exact: Hkn.
move=> n; have [n' Hn1n' Hnn']: exists2 n', n1 <= n' & n <= n'.
  by case (leqP n1 n); [ exists n | exists n1 ]; rewrite ?leqnn // ltnW.
case: (Hxn1 _ Hn1n') => [k' [Ekk' Hk'] Ek'i]; exists k'.
  exact: (leq_partial_coloring Hnn').
apply: (partial_eq_trans (partial_eq_sym (partial_eq_partial _ _))).
case: (partial_eq_trans (partial_eq_sym Ekk1) Ekk') => [Hk1k' Hk'k1].
move/(leq_partial_coloring Hn1n'): Hk' => Hk'.
pose kij k :=
   and3 (partial_coloring (S i) k) (ak k i j) (forall j', ak k i j' -> j <= j').
move/leq_partial_coloring: Hin1 => Hin1.
have Hk1ij: kij k1 by split; auto.
have Hk'ij: kij k' by split; auto; move=> j'; apply Hn1; split.
clear Hkm Hk Hkn Hn1 Hxn1 Ekk1 k2 Ek2i Ekk2 Hk2 n n' Hn1n' Hnn' Ekk'.
clear k akn akm akx extij n1 Hin1 Hk1 Hk' Ek'i Ek1i Hk1i.
suffice: forall k1 k2, kij k1 -> kij k2 -> covers (partial_map i k1) k2 ->
    covers (partial_map (S i) k1) k2.
  by split; auto.
clear k1 k' Hk1k' Hk'k1 Hk1ij Hk'ij.
move=> k k' [[Hk Hik] Eki Hki] [[Hk' Hik'] Ek'i _] Ekk'.
pose zi := std_point i; pose zj := std_point j.
pose a0i z := partial_map (S i) m0 zi z.
have Vm0': forall z, in_partial (S i) z -> in_partial i z \/ a0i z.
  move=> z Hz; case: (Hz) => j'; rewrite ltnS leq_eqVlt.
  case/setU1P=> [Dj'|Hj']; last by left; exists j'.
  by rewrite Dj'; right; split; auto; [ exact: (map_sym Hm0) | exact: Hinm0 ].
have Hm0'i: in_partial (S i) zi by exists i.
have Hizi: forall z, in_partial i z -> k zi z -> k' zi z.
  move=> z Hz Hziz; apply: (map_trans Hk' Ek'i); apply Ekk'; split; auto.
    exact: (map_trans Hk (map_sym Hk Eki)).
  apply: Hinm0; auto; case: (Hz) => [j' Hj' Hzj']; apply: leq_trans (Hj').
  apply: Hki; apply: (map_trans Hk Hziz); apply Hik.
  split=> //; apply: (leq_partial HSi'); exists j' => //.
  exact: (proper_inmap_r Hm0 Hzj').
have Ha0i: forall z z', a0i z -> (k zi z' -> k' zi z') -> k z z' -> k' z z'.
  move=> z z' Hz Hziz' Hzz'; apply (map_trans Hk') with zi.
    by apply (map_sym Hk'); exact: Hik'.
  by apply Hziz'; apply: (map_trans Hk) Hzz'; exact: Hik.
move=> z1 z2 [Hz12 Hz1 Hz2]; case: (Vm0' _ Hz1) => Hz1'.
  apply (map_sym Hk'); move/(map_sym Hk): Hz12 => Hz12.
  by case: (Vm0' _ Hz2) => Hz2'; eauto; apply Ekk'; split.
by apply: Ha0i Hz12 => // Hz12; case: (Vm0' _ Hz2) => Hz2'; auto; exact: Hik'.
Qed.

Lemma leq_exact_partial : forall n1 n2, n1 <= n2 -> forall k1 k2,
  exact_partial n1 k1 -> exact_partial n2 k2 -> covers k1 k2.
Proof.
move=> n1 n2 Hn12 k1 k2 [Mk1 Xk1] [Mk2 Xk2]; suffice: partial_eq n1 k1 k2.
  move: Xk1 {Mk1 Xk2 Mk2} => [Hk1 Hk1n1 _] [Hk12 _] z1 z2 Hz12; apply Hk12.
  by move: (proper_inmap_l Hk1 Hz12) (proper_inmap_r Hk1 Hz12); split; auto.
have Mk21: min_partial n1 k2.
  by elim: (leP Hn12) Mk2 => //= n _ Hrec [_ Hn]; auto.
elim: {-2}n1 (leqnn n1) Mk1 Mk21 {Mk2} => /= [|i Hrec] Hin1.
  by split; move=> z1 z2 [_ [j Hj _] _].
move=> [Hk1i Mk1] [Hk2i Mk2]; move/(leq_trans Hin1): Hn12 => Hin2.
move: {Hrec Mk1 Mk2}(Hrec (ltnW Hin1) Mk1 Mk2) => Ek12.
have Ek21 := partial_eq_sym Ek12.
move: (partial_eq_partial (S i) k1) (partial_eq_partial (S i) k2).
move: {Hin1}(leq_extensible Hin1 Xk1) {Hin2}(leq_extensible Hin2 Xk2).
pose zi := std_point i; set aSi := partial_map (S i).
case: Xk1 Xk2 => [Hk1 _ _] [Hk2 _ _] Xk1 Xk2 Ek1 Ek2.
apply: (partial_eq_trans Ek1 (partial_eq_trans _ (partial_eq_sym Ek2))).
have Ek12' := (partial_eq_trans Ek12 (leq_partial_eq (leqnSn i) Ek2)).
have Ek21' := (partial_eq_trans Ek21 (leq_partial_eq (leqnSn i) Ek1)).
pose ak (k : map) j1 j2 := k (std_point j1) (std_point j2).
pose minki k k' := forall j', ak k' j' i -> exists2 j, j <= j' & ak k j i.
have Hminki: forall k k', partial_eq i k k' -> extensible (S i) k' ->
    quasi_coloring k -> min_partial1 i k -> minki (aSi k) k'.
  move=> k k' Ekk' Hk' Hk Hki j' Hj'i.
  have [Hj' Hi]: in_partial (S i) (std_point j') /\ in_partial (S i) zi.
    move: Hk' => [Hk' Ek' _].
    by move: (proper_inmap_l Hk' Hj'i) (proper_inmap_r Hk' Hj'i); split; apply Ek'.
  have [j1 [Hj1 Hj1j' Hj1i]]: exists j1, and3 (j1 <= i) (j1 <= j') (ak k' j1 i).
    case: (leqP j' i) => Hij'; first by exists j'; split; try apply leqnn.
    move/extensible_partial: Hk' => [Hk' Hik'].
    case: (Hj') => [j1 Hj1 Hj1j']; exists j1; split; auto.
      by apply ltnW; eapply leq_trans; eauto.
    apply: (map_trans Hk') Hj'i; apply (map_sym Hk'); apply Hik'; split; auto.
    by exists j1; last exact: (proper_inmap_r Hm0 Hj1j').
  case: {Hki Ekk' Hk' Hj' Hj'i Hj1i}(Hki _ _ Ekk' Hk' Hj1i) => [j Hj Hji].
  exists j; first by eapply leq_trans; eauto.
  split; auto; exists j; first by apply leq_trans with (S j1).
  by apply (qc_inmap Hk); exact (proper_inmap_l Hk Hji).
have Hk1i': minki (aSi k1) (aSi k2) by auto.
have Hk2i': minki (aSi k2) (aSi k1) by auto.
move/extensible_partial: Xk2 Hk2i' {Hminki}; move/extensible_partial: Xk1 Hk1i'.
move: (partial_eq_trans (partial_eq_sym Ek12') (partial_eq_trans Ek12 Ek21')).
move/aSi: k2 {n1 n2 Hk1i Hk2i Hk1 Hk2 Ek1 Ek2 Ek12' Ek21' Ek12 Ek21}; move/aSi: k1.
suffice: forall k1 k2, partial_coloring (S i) k1 -> minki k1 k2 ->
                   partial_coloring (S i) k2 -> minki k2 k1 ->
      covers (partial_map i k1) k2 -> covers (aSi k1) k2.
- by move=> Xi k1 k2; case; split; apply Xi.
move=> k1 k2 [Hk1 Hik1] Hk21i [Hk2 Hik2] Hk12i Hk12.
have Hk1zi: forall z, in_partial i z -> k1 z zi -> k2 z zi.
  move=> z Hz Hzzi; case: (Hz) => [j Hj]; set zj := std_point j; move=> Hzzj.
  have Hzj: in_partial i zj by exists j; last exact: (proper_inmap_r Hm0 Hzzj).
  have Hzj': aSi m0 z zj by split; auto; exact: (leq_partial (leqnSn i)).
  move: {Hz Hzzj Hzzi}(map_trans Hk1 (map_sym Hk1 (Hik1 _ _ Hzj')) Hzzi) => Hzji.
  apply: (map_trans Hk2 (Hik2 _ _ Hzj')) => {Hzj'}.
  have [j' [Hj' Hj'1 Hj'2]]: exists j', and3 (j' < i) (ak k1 j' i) (ak k2 j' i).
    move: {Hzj}Hzji; rewrite {}/zj; elim: {1 2}i j Hj => //= [i' Hrec] j0 Hi' Hj0.
    case: (Hk12i _ Hj0) => [j1 Hj10 Hj1]; case: (Hk21i _ Hj1) => [j2 Hj21 Hj2].
    rewrite leq_eqVlt in Hj21; case/setU1P: Hj21 => [Dj2|Hj21].
      by rewrite Dj2 in Hj2; exists j1; split; auto; apply: leq_trans Hi'.
    have Hj2': j2 < i'.
      by rewrite ltnS in Hi'; exact: leq_trans (leq_trans Hj10 Hi').
    case: (Hrec _ Hj2' Hj2) => [j' [Hj' Hj'1 Hj'2]].
    by move: (ltnW Hj'); exists j'; split.
  apply: (map_trans Hk2) Hj'2; apply: Hk12; split; auto.
    exact: (map_trans Hk1) (map_sym Hk1 Hj'1).
  exists j'; auto; move: Hk1 => [Hk1 Hm0k1 _ _]; apply: Hm0k1.
  exact (proper_inmap_l Hk1 Hj'1).
have Vm0: forall z, in_partial (S i) z -> in_partial i z \/ aSi m0 zi z.
  move=> z Hz; case: (Hz) => j'; rewrite ltnS leq_eqVlt.
  case/setU1P=> [Dj'|Hj']; last by left; exists j'.
  rewrite Dj'; move=> Hiz; right; split; auto; first exact: (map_sym Hm0).
  exists i; [ exact: leqnn | exact: (proper_inmap_r Hm0 Hiz) ].
move=> z1 z2 [Hz12 Hz1 Hz2]; case/Vm0: Hz1 => Hz1.
  case/Vm0: Hz2 => Hz2; first by apply Hk12; split.
  apply: (map_trans Hk2) (Hik2 _ _ Hz2); apply: Hk1zi => //.
  exact: (map_trans Hk1) (map_sym Hk1 (Hik1 _ _ Hz2)).
apply (map_sym Hk2); apply: (map_trans Hk2) (Hik2 _ _ Hz1).
move: {z1 Hz12 Hz1}(map_sym Hk1 (map_trans Hk1 (Hik1 _ _ Hz1) Hz12)) => Hz2i.
by case/Vm0: Hz2 => Hz2; auto; apply (map_sym Hk2); exact: Hik2.
Qed.

Definition limit_coloring : map :=
  fun z1 z2 => exists2 k : map, k z1 z2 & (exists n, exact_partial n k).

Lemma limit_coloring_coloring : coloring m0 limit_coloring.
Proof.
split.
- split; move=> z1 z2 [k Hz12 [n Hk]].
    by exists k; [ case: Hk => [_ [Hk _ _]]; exact: (map_sym Hk) | exists n ].
  move=> z3 [k3 Hz23 [n3 Hk3]].
  have [k' [Hz12' Hz23' [n' Hk']]]: exists k' : map,
      and3 (k' z1 z2) (k' z2 z3) (exists n', exact_partial n' k').
    case: (leqP n n3) => Hnn3.
      exists k3; split; auto; last by exists n3.
      exact: ((leq_exact_partial Hnn3) k k3).
    exists k; split; auto; last by exists n.
    exact: ((leq_exact_partial (ltnW Hnn3)) k3 k).
  exists k'; last by exists n'.
  case: Hk' => [_ [Hk' _ _]]; exact: (map_trans Hk' Hz12').
- by move=> z [k Hz [n [_ [[_ Hk _ _] _ _]]]]; auto.
- move=> z1 z2 Hz12; move: (has_std_point (proper_inmap_l Hm0 Hz12)) => [i1 Hiz1].
  move: (has_std_point (proper_inmap_r Hm0 Hz12)) => [i2 Hiz2].
  have [n Hni1 Hni2]: exists2 n, i1 < n & i2 < n.
    by case (leqP i1 i2); [exists (S i2) | exists (S i1)]; rewrite ?leqnn // ltnW.
  case: (exists_exact_partial n) => [k Hk]; exists k; last by exists n.
  case: Hk => _; case/extensible_partial=> [Hk Hnk].
  by apply: Hnk; split; [ done | exists i1 | exists i2 ].
by move=> z1 z2 [k Hz12 [n [_ [[_ _ _ Hka] _ _]]]]; auto.
Qed.

Lemma size_limit_coloring : size_at_most nc limit_coloring.
Proof.
pose inmf n k f := forall i, i < n -> inmap k (f i : point).
pose injf n (k : map) f :=  forall i j, i < j -> j < n -> ~ k (f i) (f j).
pose minsize n k := exists2 f, inmf n k f & injf n k f.
case: (Hclassical (minsize (S nc) limit_coloring)).
  move=> [f Hf If].
  have [k Hfk Hk]: exists2 k, inmf (S nc) k f & (exists n, exact_partial n k).
    elim: {-2}(S nc) (ltnSn nc) => [|n Hrec] Hn.
      by case: (exists_exact_partial 0) => [k Hk]; exists k; [ move | exists 0 ].
    case: (Hrec (ltnW Hn)) => [k1 Hk1f [n1 Hk1]].
    case: (Hf _ Hn) => [k2 Hk2f [n2 Hk2]]; case: (ltnP n2 n1) => Hn12.
      exists k1; last by exists n1.
      move=> i; rewrite ltnS leq_eqVlt; case/setU1P=> [Di|Hi]; auto.
      by rewrite Di; exact: ((leq_exact_partial (ltnW Hn12)) k2 k1).
    exists k2; last by exists n2.
    move=> i; rewrite ltnS leq_eqVlt; case/setU1P; first by move ->.
    by move/Hk1f; exact: ((leq_exact_partial Hn12) k1 k2).
  case: (Hk) {Hf} => [nk [_ [[Hk' _ [f' Hf'] _] _ _]]].
  have [s Ls Ds]: exists2 s, size s = S nc
     & forall i, i < S nc -> let j := sub 0 s i in j < nc /\ k (f' j) (f i).
    elim: (S nc) f Hfk {If} => [|n Hrec] f Hf; first by exists (seq0 : natseq).
    case: {Hrec}(Hrec (fun i => f (S i))); first by move=> i Hi; exact: Hf.
    move=> s Ls Hs; case: (Hf' (f 0)); first by apply Hf.
    move=> j Hjnc Hjf'; exists (Adds j s); first by rewrite /= Ls.
    by move=> [|i]; [ split; first by apply/ltP | exact: Hs ].
  clear Hfk Hf'; have Us: uniq s.
    rewrite -[s]take_size; move: (leqnn (size s)).
    elim: {-2}(size s) => [|n Hrec] Hn; first by rewrite take0.
    rewrite (take_sub 0 Hn) uniq_add_last {}Hrec 1?ltnW // andbT.
    apply/(subPx 0 _ _); rewrite size_take Hn; move=> [i Hi Ei].
    rewrite Ls in Hn; case: (If _ _ Hi Hn); exists k; auto.
    case: (Ds _ Hn) => [_]; rewrite -Ei sub_take //; apply: (map_trans Hk').
    by apply (map_sym Hk'); case: (Ds _ (ltn_trans Hi Hn)).
  have [s' Ls' Ds']: exists2 s', size s' = nc & s' =1 (fun i => i < nc).
    exists (traject S 0 nc); first by rewrite size_traject.
    have EitS: forall i, iter i S 0 = i by elim=> //= *; congr S.
    by move=> i; apply/trajectP/idP => [[i' Hi' <-]|]; [ rewrite EitS | exists i ].
  case/idP: (ltnn nc); rewrite -Ls -Ls'; apply: uniq_leq_size => // i.
  by rewrite Ds'; move/(subPx 0)=> [j Hj <-]; rewrite Ls in Hj; case: (Ds _ Hj).
move: limit_coloring => k; elim: nc => [|n Hrec] Hn.
  exists (fun _ : nat => std_point 0); move=> z Hz; case Hn.
  by exists (fun _ : nat => z); move=> i; case.
case: (Hclassical (minsize (S n) k)).
  move{Hrec} => [f Hf Ij]; exists f; move=> z Hz.
  case (Hclassical (exists2 i, (i < S n)%nat & k (f i) z)); auto.
  move=> Hfz; case Hn; exists (fun i => if i < S n then f i else z).
    by move=> i /= _; case Hi: (i < S n); auto.
  move=> j i /= Hj Hi; rewrite ltnS in Hi; rewrite (leq_trans Hj Hi).
  case: (ltnP i (S n)); auto; rewrite leq_eqVlt ltnNge Hi orbF; move/eqP=> Di Hjz.
  by case: Hfz; exists j; first by apply: ltP; rewrite Di.
case/Hrec {Hrec Hn} => [f Hf]; exists f; move=> z; move/(Hf z)=> [i Hi Hz].
by exists i; first by right.
Qed.

Lemma compactness_extension : map_colorable nc m0.
Proof.
by move: limit_coloring_coloring size_limit_coloring; exists limit_coloring.
Qed.

End FinitizeMap.

Set Strict Implicit.
Unset Implicit Arguments.

