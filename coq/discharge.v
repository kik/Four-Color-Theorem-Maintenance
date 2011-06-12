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
Require Import znat.
Require Import hypermap.
Require Import geometry.
Require Import part.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Discharging arities to neighboring faces. This file contains the data for *)
(* the 32 (37 after disambiguation) rules, functions for constructing a      *)
(* symmetrical rule database, and for computing its converse.                *)
(* It contains the proof that after discharging, some dart has a positive    *)
(* score.                                                                    *)

Definition drules := seq partData.

Section DischargeRules.

Import PartSyntax.

Definition drule1 := Part [] * [] * [] 6+ [] * [] * [].

Definition drule2  := Part [] * [] 5 [] 7+ [] * [] * [].
Definition drule2' := Part [] * [] 5 [] 7+ [] * [] * [] * [].

Definition drule3  := Part [] 5 [] 6- [] 6+ [] * [] * [].
Definition drule3' := Part [] 5 [] 6- [] 6+ [] * [] * [] * [].

Definition drule4  := Part [] 6- [5] 5 [] 6+ [] * [] * [] * [].
Definition drule4' := Part [] 6- [5] 6 [] 6+ [] * [] * [] * [].

Definition drule5 := Part [] 6 [6- 5] 6 [] 6+ [] * [] * [] * [].

Definition drule6 := Part [] 6 [6-] 5 [5] 7+ [] * [] * [] * [].

Definition drule7 := Part [] 6 [6 6-] 6 [5] 7+ [] * [] * [] * [].

Definition drule8 := Part [] 5 [] 6- [] 7+ [] * [] * [] * [] * [].

Definition drule9 := Part [] 6- [] 6- [] 7+ [] * [] * [] * [] 5 [].

Definition drule10  := Part [] 5 [] 5 [] 7+ [] 5 [] 6+ [] * [] * [].
Definition drule10' := Part [] 5 [] 5 [] 7+ [] 5 [] 5 [] * [] * [].

Definition drule11 := Part [] 6 [5] 5 [] 7+ [] 5 [] 6+ [] * [] * [].

Definition drule12 := Part [] 5 [5] 5 [] 7+ [] 5 [5] 5 [] * [] * [].

Definition drule13 := Part [] 6 [5] 5 [5] 8+ [] 5 [] 5 [] * [] * [].

Definition drule14 := Part [] 5 [5] 6 [] 7+ [] 5 [] * [] * [] * [].

Definition drule15 := Part [] 5 [] 6 [] 7+ [] 5 [] 7+ [] 5 [] 6 [].

Definition drule16 := Part [] 6 [] 6 [] 7+ [] 5 [] 5 [] 5 [] 6 [].

Definition drule17 := Part [] 5 [6] 6 [] 7+ [] 5 [] 5 [] 7+ [] 5 [].

Definition drule18 := Part [] 6 [5] 5 [5] 7 [] 6+ [] * [] * [] 5 [].

Definition drule19 := Part [] 6 [] 6+ [] 8+ [5] 5 [5] 6 [] 5 [] 6 [].

Definition drule20 := Part [] 5 [] 6 [] 7+ [] 6 [] 6 [] 5 [] 5 [].

Definition drule21 := Part [] 6- [] 6 [5] 7 [] 6+ [] * [] 5 [] 5 [].

Definition drule22 := Part [] 5 [] 6 [5] 7 [] 6+ [] * [] 5 [] 6 [].

Definition drule23 := Part [] 5 [5] 7 [] 7+ [] 5 [] * [] * [] * [].

Definition drule24 := Part [] 5 [] 5 [5] 7 [] 7+ [] 6 [] 6 [] 5 [].

Definition drule25 := Part [] 5 [] 5 [] 7+ [* * 5] 7 [6] 5 [] 5 [] * [].

Definition drule26 := Part [] 6 [] 6 [5] 7 [] 7+ [] 5 [] 5 [] 6 [].

Definition drule27 := Part [] 7+ [] 6 [6 5 6+] 7 [] 7 [5] 6- [] * [] * [].

Definition drule28 := Part [] 5 [] 5 [] 7+ [] 5 [] 5 [] * [] * [] 5 [].

Definition drule29 := Part [] 5 [5] 5 [] 7+ [] 5 [] * [] * [] 5 [] 5 [].

Definition drule30 := Part [] 5 [] 5 [] 7+ [] 5 [5] 6 [] 5 [] * [] * [].

Definition drule31  := Part [] 5 [5] 5 [] 7+ [] 5 [6+] 5 [] 6+ [] * [] 6+ [].
Definition drule31' := Part [] 5 [5] 5 [] 7+ [] 5 [5] 5 [] 6+ [] * [] 6+ [].

Definition drule32 := Part [] 5 [] 6 [5] 7 [] 7+ [] 6 [] 5 [] 5 [] 5 [].

End DischargeRules.

Definition base_drules : drules :=
  Seq drule1  drule1   drule2  drule2' drule3  drule3'  drule4  drule4' drule5
      drule6  drule7   drule8  drule9  drule10 drule10' drule11 drule12 drule13
      drule14 drule15  drule16 drule17 drule18 drule19  drule20 drule21 drule22
      drule23 drule24  drule25 drule26 drule27 drule28  drule29 drule30
      drule31 drule31' drule32.

Fixpoint symmetrize_drules (r : drules) : drules :=
  if r is Adds p r' then
    let p' := iter 5 (rot_part (pred (size_part p))) (mirror_part p) in
    let psr := Adds p (symmetrize_drules r') in
    if cmp_part p p' is Psubset then psr else Adds p' psr
  else r.

Definition the_drules := symmetrize_drules base_drules.

Section Discharge.

Variable g : hypermap.

Definition dscore1 (x : g) := count (exact_fitp (inv_face2 x)) the_drules : znat.

Definition dscore2 x := (dscore1 (edge x) - dscore1 x)%Z.

Definition dscore x := (60 - (10 * arity x)%dnat + sumz dscore2 (cface x))%Z.

Lemma dscore_cface : forall x y, cface x y -> dscore x = dscore y.
Proof.
by move=> x y Hxy; rewrite /dscore (arity_cface Hxy) (eq_sumz_r (same_cface Hxy)).
Qed.

End Discharge.

Prenex Implicits dscore dscore1 dscore2.

Section DischargePlanar.

Variable g : hypermap.

Hypothesis Hg : planar_plain_cubic_connected g.
Let De2 := plain_eq Hg.
Let Dn3 := cubic_eq Hg.

Lemma dscore_roots : @sumz g dscore (froots face) = 120.
Proof.
pose ds3 (x : g) := sumz (fun y => (dscore2 y - zconst 10 y)%Z) (cface x).
transitivity (sumz (fun x => (zconst 60 x + ds3 x)%Z) (froots face)).
  by apply: eq_sumz => x; rewrite /ds3 sumz_sub sumz_const addz_subCA addzC.
rewrite sumz_add {}/ds3 (sumz_roots (Sface g)) sumz_sub !sumz_const.
have: planar g := Hg; rewrite (cubic_Euler Hg) /n_comp.
rewrite -(@eq_card g (froots face)); last by move=> y; rewrite /setI andbT.
move/eqP=> Eg; rewrite -{1}[60]/(10 * 6) -mulnA {}Eg muln_addr zpos_addn.
rewrite addz_subCA subz_add /dscore2 (sumz_sub (fun x => dscore1 (edge x))).
by rewrite  (sumz_perm (Iedge g)) // subzz.
Qed.

Lemma posz_dscore : exists x : g, posz (dscore x).
Proof.
case: (@posz_sum g dscore (froots face)); first by rewrite dscore_roots.
by move=> x; exists x.
Qed.

Lemma dscore_mirror : forall x : g, @dscore (mirror g) x = @dscore g x.
Proof.
move=> x; rewrite /dscore arity_mirror (eq_sumz_r (cface_mirror x)); congr addz.
suffice Es1x: forall y : g, @dscore1 (mirror g) (face y) = dscore1 y.
  rewrite -(sumz_perm (Iface g)).
    apply: eq_sumz => y; rewrite /dscore2.
    by rewrite [dscore1]lock /= -lock /comp !Es1x (plain_eq' Hg).
  by move=> y z Dz; rewrite cface1r (eqP Dz).
move{x} => x; rewrite /dscore1 /the_drules; congr Zpos.
elim: base_drules => [|p r Hrec] //; pose n := size_part p.
pose rp i := iter i (rot_part (pred n)) (mirror_part p).
have Erp: forall i, size_part (rp i) = n.
  by elim=> /= *; rewrite ?size_rot_part ?size_mirror_part.
have Hrp: forall i g' x',
    @exact_fitp g' x' (rp i) = exact_fitp (iter i face x') (mirror_part p).
  elim{Hrec} => //= [i Hrec] g' x'; case Hx': (arity x' =d n).
    rewrite -arity_face in Hx'; rewrite /= -{1}(finv_f (Iface g') x') /finv.
    by rewrite (eqP Hx') -fitp_rot ?Hrec ?iter_f // Erp -subn1 leq_subr.
  rewrite /exact_fitp size_rot_part Erp arity_face arity_iter_face.
  by rewrite size_mirror_part -/n Hx'.
move Dp': (rp 5) => p'; move: Dp' {Hrp}(Hrp 5) {Erp}(Erp 5) => /=.
rewrite -/n => -> Hp' Ep'.
set x2' := inv_face2 x; pose x3 := face (face (face x)).
have Ex3: x3 = iter 5 face x2' by rewrite /x2' /inv_face2 /= !Enode.
rewrite /= in Hrec Ex3; case Hpp': (cmp_part p p') => //=;
 rewrite {}Hrec /comp ?(f_finv (Inode g)) -/x2' -/x3;
 try by rewrite !Hp' // -Ex3 {1}Ex3 /= ?(finv_f (Iface g));
     rewrite -?(fitp_mirror Hg) mirror_mirror_part addnCA.
congr ((_ : bool) + _); apply/idP/idP; move/andP=> [Exp Hxp].
  have Hxp': @exact_fitp (mirror g) x3 p'.
    by rewrite /exact_fitp (fitp_cmp Hxp) Hpp' /= andbT Ep'.
  move: Hxp'; rewrite Hp' Ex3 /= !(finv_f (Iface g)) -(fitp_mirror Hg).
  by rewrite mirror_mirror_part.
by rewrite -(fitp_mirror Hg) Ex3 -Hp' /exact_fitp (fitp_cmp Hxp) Hpp' andbT Ep'.
Qed.

End DischargePlanar.

Section ScoreBound.

Variable nhub : nat. (* hub size *)

(* Rule selectors, by source or target arity, or by matching a part. The *)
(* "target arity" returns a list of converse rules. The "matching"       *)
(* selector returns a pair of the number of rules that are forced by the *)
(* part, plus the list of rules that straddle the part, discarding the   *)
(* rules that are disjoint from or forced by the part. The matching      *)
(* selector is part of the inner loop of the unavoidability computation. *)

Definition pick_source_drules : drules -> drules :=
  filter (fun p => size_part p =d nhub).

Fixpoint pick_target_drules (r : drules) : drules :=
  if r is Adds p r' then
    let (u, p') := converse_part p in
    let tr := pick_target_drules r' in
    if u nhub then Adds p' tr else tr
  else r.

Section SortDrules.

Record sort_drules_result : Set := SortDrules {
  nb_forced_drules :> nat;
  straddling_drules :> drules
}.

Variable p : part.

Fixpoint sort_drules_rec (n : nat) (rs r : drules) {struct r}
                       : sort_drules_result :=
  if r is Adds p' r' then
    match cmp_part p p' with
    | Psubset => sort_drules_rec (S n) rs r'
    | Pstraddle => sort_drules_rec n (Adds p' rs) r'
    | Pdisjoint => sort_drules_rec n rs r'
    end
  else SortDrules n rs.

Definition sort_drules r := sort_drules_rec 0 seq0 r.

End SortDrules.

(* A rule fork specializes the full set of discharge rules for a specific *)
(* hub size, so that the source/target arity selection is only performed  *)
(* once. We use a dependent predicate to specify the computation.         *)

Inductive drule_fork_values : drules -> drules -> Prop :=
    DruleForkValues :
      drule_fork_values (pick_source_drules the_drules)
                        (pick_target_drules the_drules).

Record drule_fork : Set := DruleFork {
   source_drules : drules;
   target_drules : drules;
   drule_fork_values_def : drule_fork_values source_drules target_drules
}.

Variable rf : drule_fork.
Let rs : drules := source_drules rf.
Let rt : drules := target_drules rf.

Variable g : hypermap.
Hypothesis Hg : plain_cubic_pentagonal g.
Let HgF : pentagonal g := Hg.
Let De2 := plain_eq Hg.
Let Dn3 := cubic_eq Hg.

Section BoundDart.

Definition dbound1 (r : drules) (x : g) := count (fitp x) r.

Definition dbound2 r r' x := (dbound1 r x - dbound1 r' x)%Z.

Definition dboundK := if nhub - 5 is S n then (- (n * 10))%Z else (10 : znat).

Variables (x : g) ( (* hub *) p : part (* for sort_drules *)).
Hypotheses (Hxn : arity x = nhub) (Hpn : size_part p = nhub) (Hxp : fitp x p).

Lemma dbound1_eq : dscore1 (face (face x)) = dbound1 rs x.
Proof.
congr Zpos; rewrite /rs /source_drules; case: rf => [_ _ []].
elim: the_drules => //= [r dr ->].
by rewrite /exact_fitp /inv_face2 !Eface Hxn eqd_sym; case (size_part r =d nhub).
Qed.

Lemma sort_dbound1_eq : forall ru, let rup := sort_drules p ru in
  dbound1 ru x = rup + dbound1 rup x.
Proof.
move=> ru; apply: (etrans (esym (addn0 _))); rewrite /sort_drules.
rewrite -{1}[0]/(0 + count (fitp x) seq0).
elim: ru 0 (seq0 : drules) => //= [r ru Hrec] m ru'.
rewrite (fitp_cmp Hxp); case Hpr: (cmp_part p r) => //=.
  by rewrite -Hrec /= -!addnA; repeat NatCongr.
by rewrite -Hrec /= !addSn addnS.
Qed.

Inductive sort_drules_spec (r : drules) : sort_drules_result -> nat -> Set :=
  SortDrulesSpec : forall n r',
    sort_drules_spec r (SortDrules n r') (n + dbound1 r' x).

Lemma sort_drulesP : forall r, sort_drules_spec r (sort_drules p r) (dbound1 r x).
Proof. by move=> r; rewrite sort_dbound1_eq; case (sort_drules p r). Qed.

Lemma dbound2_leq : (dscore2 (face (face x)) <= dbound2 rt rs x)%Z.
Proof.
rewrite /dbound2 -dbound1_eq /dscore2 leqz_add2r /dscore1 /dbound1 leqz_nat.
set y := inv_face2 _; rewrite /rt /target_drules; case: rf => _ _ [].
elim: the_drules => //= [r dr Hrec].
case Dr': (converse_part r) => [u r'].
case Hyr: (exact_fitp y r).
  move: (fitp_converse Hg Hyr); rewrite Dr'; case/andP.
  by rewrite {1 2}/y /inv_face2 !Enode De2 !Eface Hxn => -> /= ->.
by case: (u nhub) => //=; case: (fitp x r') => //; apply ltnW.
Qed.

Lemma dboundK_eq : dboundK = (60 - (10 * arity x)%dnat)%Z.
Proof.
rewrite -(leq_add_sub (HgF x)) Hxn /dboundK; case: (subn nhub 5) => // m.
by rewrite -addSnnS muln_addr zpos_addn -oppz_sub subz_add mulnC mulz_nat.
Qed.

End BoundDart.

Lemma dscore_cap1 : forall m : nat, (forall y : g, (dscore1 y <= m)%Z) ->
  forall x : g, posz (dscore x) ->  forall d, 59 < (10 - m) * d -> arity x < d.
Proof.
move=> m Hm x Hx d Hdm; rewrite ltnNge; apply/idP => Hdx; case/idPn: Hx.
have H60: (60 <= ((10 - m) * arity x)%dnat)%Z.
  rewrite leqz_nat; apply: (leq_trans Hdm).
  by rewrite -(leq_add_sub Hdx) muln_addr leq_addr.
rewrite /dscore addzC addz_subCA -oppz_sub; apply: (leqz_trans H60); apply/idP.
rewrite /order -!sumz_const -!sumz_sub; case/posz_sum=> [y _]; apply: negP.
have Hm10: m < 10 by rewrite ltn_lt0sub; case: (10 - m) Hdm.
rewrite /zconst -{2}(leq_add_sub (ltnW Hm10)) zpos_addn -oppz_sub subz_sub.
rewrite subz_add2r /dscore2 oppz_sub subz_sub {2}/dscore1 - zpos_addn [Zpos]lock.
by apply: (leqz_trans (Hm _)); rewrite -lock leqz_nat leq_addl.
Qed.

Lemma source_drules_range : negb (Pr58 nhub) -> rs = seq0.
Proof.
move=> Hu; rewrite /rs /source_drules; case: rf => _ _ [].
have Eu: (fun p => size_part p =d nhub)
            =1 comp (fun n => negb (Pr58 n) && (n =d nhub)) size_part.
  by move=> p; rewrite /comp andbC; case: (size_part p =P nhub) => // ->.
by rewrite /pick_source_drules (eq_filter Eu).
Qed.

Lemma dscore_cap2 : forall x : g, arity x = nhub ->
  posz (dscore x) -> posz (dboundK + (sumz (dbound2 rt rs) (cface x))).
Proof.
move=> x Hxn; rewrite -!leq1z; apply: (fun H => leqz_trans H _).
rewrite /dscore -dboundK_eq // leqz_add2l.
rewrite -2!(sumz_perm (Iface g) (connect_closed (Sface g) x)).
rewrite /leqz -sumz_sub; apply/idP; case/posz_sum=> [y Hxy]; apply: negP.
rewrite [dscore2]lock [dbound2]lock.
rewrite (arity_cface Hxy) in Hxn; move: (dbound2_leq Hxn).
by rewrite /leqz {1}[dscore2]lock {1}[dbound2]lock.
Qed.

End ScoreBound.

Unset Implicit Arguments.