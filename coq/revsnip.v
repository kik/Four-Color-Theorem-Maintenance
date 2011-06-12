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
Require Import patch.
Require Import sew.
Require Import snip.
Require Import color.
Require Import chromogram.
Require Import coloring.
Require Import kempe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Dissecting a connected plain map along a proper ring, and its reverse  *)
(* edge-conjugate. This gives a symmetric cover (compare with snip.v,     *)
(* where the construction is asymmetric). The properties established here *)
(* feed directly into birkhoff; the chord constructions are also used in  *)
(* embed when using induction over the disk size of a ring.               *)

Section ProperRing.

(* A proper ring is a non-empty ring that is NOT an edge orbit.           *)
(* A nontrivial ring of order m must have more that m face orbits in both *)
(* its inner and outer face disks.                                        *)

Variables (n0 : nat) (g : hypermap).
Hypothesis Hg : plain g.

Definition proper_ring (r : seq g) : bool :=
  match r with
  | Adds _ (Adds _ (Adds _ _)) => true
  | Adds x (Adds y Seq0) => negb (edge x =d y)
  | _ => false
  end.

Lemma size_proper_ring : forall r, 2 < size r -> proper_ring r.
Proof. by move=> [|x [|y [|z r]]]. Qed.

Lemma proper_ring_rot : forall r, proper_ring (rot n0 r) = proper_ring r.
Proof.
move=> r; case Hr: (2 < size r); first by rewrite !size_proper_ring ?size_rot.
case: n0 r Hr => [|[|i]] [|x [|y [|z r]]] //= _.
by rewrite -{1}[x]plain_eq // eqd_sym (inj_eqd (Iedge g)).
Qed.

Definition nontrivial_ring m (r : seq g) :=
  (m < fcard face (diskF r)) && (m < fcard face (diskFC r)).

Lemma fcard0P : forall a : set g, fclosed face a ->
  reflect (exists x, a x) (0 < fcard face a).
Proof.
move=> a Ha; rewrite ltnNge leqn0.
apply: (iffP (set0Pnx (setI _ _))); first by case; move=> x; case/andP; exists x.
move=> [x Hx]; exists (froot face x); rewrite /setI (roots_root (Sface g)).
by rewrite -(closed_connect Ha (connect_root _ x)).
Qed.

Lemma fcard1P : forall a : set g, fclosed face a ->
  reflect (exists2 x, a x & exists2 y, a y & negb (cface x y)) (1 < fcard face a).
Proof.
move=> a Ha; rewrite ltn_neqAle andbC eqd_sym; apply introP.
  case/andP; case/(fcard0P Ha)=> [x Hx] Ha1.
  rewrite /n_comp (cardD1 (froot face x)) {1}/setI (roots_root (Sface g)) in Ha1.
  rewrite -(closed_connect Ha (connect_root _ x)) Hx in Ha1.
  case/set0Pn: Ha1; move=> y; case/and3P=> [Hxy Dy Hy].
  exists x; auto; exists y; auto.
  by rewrite (sameP (rootP (Sface g)) eqP) (eqP Dy).
move=> H [x Hx [y Hy Hxy]]; case/andP: H; split.
  by apply/(fcard0P Ha); exists x.
rewrite /n_comp (cardD1 (froot face x)) (cardD1 (froot face y)) {1 2}/setI.
rewrite {1}/setD1 !(roots_root (Sface g)).
rewrite -!(closed_connect Ha (connect_root _ _)).
by rewrite Hx Hy (sameP eqP (rootPx (Sface g) x y)) Hxy.
Qed.

Lemma nontrivial0P : forall r,
  reflect ((exists x, diskF r x) /\ (exists x, diskFC r x)) (nontrivial_ring 0 r).
Proof.
move=> r; rewrite /nontrivial_ring.
case: (fcard0P (diskF_face r)); move=> HrF.
case: (fcard0P (diskFC_face r)); move=> HrFC; constructor; first by split.
  by move=> [_ H]; case HrFC.
by right; move=> [H _]; case HrF.
Qed.

Lemma nontrivial1P : forall r : seq g,
 reflect ((exists2 x, diskF r x & exists2 y, diskF r y & negb (cface x y))
       /\ (exists2 x, diskFC r x & exists2 y, diskFC r y & negb (cface x y)))
   (nontrivial_ring 1 r).
Proof.
move=> r; rewrite /nontrivial_ring.
case: (fcard1P (diskF_face r)); move=> HrF.
case: (fcard1P (diskFC_face r)); move=> HrFC; constructor; first by split.
  by move=> [_ H]; case HrFC.
by right; move=> [H _]; case HrF.
Qed.

End ProperRing.

Section RevSnip.

Variable g : hypermap.
Hypothesis Hg : planar_bridgeless_plain_connected g.
Let Hpg : planar g := Hg.
Let Hbg : bridgeless g := Hg.
Let HgE : plain g := Hg.
Let Hcg : connected g := Hg.
Let De2 := plain_eq Hg.
Let He1 := plain_neq Hg.

Definition rev_ring (r : seq g) := rev (maps edge r).

Lemma rev_rev_ring : forall r, rev_ring (rev_ring r) = r.
Proof.
by move=> r; rewrite /rev_ring maps_rev rev_rev (@monic_maps _ g _ _ De2).
Qed.

Lemma proper_rev_ring : forall r, proper_ring (rev_ring r) = proper_ring r.
Proof.
move=> r; case Hr: (2 < size r).
  by rewrite !size_proper_ring /rev_ring ?size_rev ?size_maps.
by case: r Hr => [|x [|y [|z r]]]; rewrite //= De2 eqd_sym.
Qed.

(* We use a redundant assumption to facilitate matching in lemmas *)
(* with dependently typed terms.                                  *)
Hypothesis Hpg' : planar g.

Variable r : seq g.
Hypothesis HUr : scycle rlink r.
Let Hr := scycle_cycle HUr.
Let UrF := scycle_simple HUr.
Let Ur := scycle_uniq HUr.

Lemma mem_rev_ring : forall x, rev_ring r x = r (edge x).
Proof.
by move=> x; rewrite -{1}[x]De2 /rev_ring mem_rev (mem_maps (Iedge g)).
Qed.

Lemma cycle_rev_ring : cycle rlink (rev_ring r).
Proof.
rewrite /rev_ring /=; case Dr: r => [|x p] //; rewrite (cycle_path x).
rewrite -Dr {1}Dr /= rev_adds last_add_last; apply/(pathP x) => i Hi.
rewrite size_rev in Hi; rewrite -rev_add_last -maps_add_last.
rewrite (sub_rev x Hi); rewrite size_maps in Hi.
rewrite sub_rev !size_maps size_add_last; last by apply ltnW.
rewrite (leq_subS Hi); set (j := subn (size r) (S i)).
have Hj: j < size r by rewrite /j -(leq_subS Hi) subSS leq_subr.
rewrite !(sub_maps x x) ?size_add_last // /rlink De2 Sface Dr /=.
have Hrr := Hr; rewrite -(cycle_rot 1) (cycle_path x) in Hrr.
move: (pathP x Hrr j); rewrite size_rot Hj Dr rot1_adds last_add_last.
rewrite -add_last_adds -Dr -cats1 sub_cat /= Hj /=; auto.
Qed.

Lemma froot_face_rev_ring :
  maps (froot face) (rev_ring r) = rev (rot 1 (maps (froot face) r)).
Proof.
rewrite /rev_ring maps_rev -maps_rot; congr rev.
case: r Hr => [|x0 p] //; rewrite rot1_adds /=.
by elim: p {1 3}x0 => [|y p Hrec] x /=; move/andP=> [Hx Hp];
  try rewrite -(Hrec _ Hp); rewrite (rootP (Sface g) Hx).
Qed.

Lemma simple_rev_ring : simple (rev_ring r).
Proof.
by rewrite /simple froot_face_rev_ring uniq_rev uniq_rot; case (andP HUr).
Qed.

Lemma scycle_rev_ring : scycle rlink (rev_ring r).
Proof. by rewrite /scycle cycle_rev_ring simple_rev_ring. Qed.

Notation HUrr := scycle_rev_ring (only parsing).

Lemma fband_rev_ring : fband (rev_ring r) =1 fband r.
Proof.
move=> x; apply/hasP/hasP => [] [y Hy Hxy].
  rewrite mem_rev_ring in Hy.
  exists (next r (edge y)); first by rewrite mem_next.
  apply: (connect_trans Hxy); rewrite -{1}[y]De2; exact (next_cycle Hr Hy).
exists (edge (prev r y)); first by rewrite mem_rev_ring De2 mem_prev.
apply: (connect_trans Hxy); rewrite Sface; exact (prev_cycle Hr Hy).
Qed.

Section RingPartitions.

Hypothesis HrE : proper_ring r.

Lemma pick_in_ring : exists x, r x.
Proof. by case: r HrE => [|x p]; last by exists x; rewrite /= setU11. Qed.

Lemma diskN_edge_ring : forall x : g, r x -> diskN r (edge x) = false.
Proof.
move=> x Hx; rewrite diskN_E /setU -(fclosed1 (diskE_edge Hpg HUr)).
rewrite /diskE /setD Hx /= orbF; apply/idP => [Hex].
have Dex: edge x = next r x.
  by apply: (scycle_cface HUr (next_cycle Hr Hx) Hex); rewrite mem_next.
have Dx: x = next r (edge x).
  apply: (scycle_cface HUr _ Hx); last by rewrite mem_next.
  by rewrite -{1}[x]De2; exact (next_cycle Hr Hex).
case: (rot_to Hx) Dex Dx Ur HrE => [i p Dr].
rewrite -!(next_rot i Ur) -(proper_ring_rot i) // -(uniq_rot i) {i}Dr.
case: p => [|y [|z p]] Dex; rewrite /= ?set11 /eqdf Dex /= ?set11 // /=.
by move=> Dx; rewrite Dx /setU1; case (y =d x); rewrite set11 /= ?orbT.
Qed.

Lemma diskN_rev_ring : diskN (rev_ring r) =1 setC (diskN r).
Proof.
case: pick_in_ring => [y Hy] x; rewrite -(De2 y) in Hy; rewrite /setC.
case: (connected_clink Hcg x (edge y)) Hy => [p Hp <-] {y}.
elim: p x Hp => [|x' p Hrec] x /=.
  move=> _ Hex; rewrite diskN_E /setU mem_rev_ring Hex /= -(De2 x).
  by rewrite (diskN_edge_ring Hex).
case/andP; move/clinkP=> [Dx|Dx'] Hp.
  rewrite Dx -!(fun r' => fclosed1 (diskN_node r') x'); auto.
  rewrite diskN_E /setU mem_rev_ring; case Hrex: (r (edge x)).
  by clear; rewrite -{2}[x]De2 (diskN_edge_ring Hrex).
rewrite /= diskN_E /setU (fclosed1 (diskE_edge Hpg scycle_rev_ring)).
rewrite (fclosed1 (diskE_edge Hpg HUr)) /diskE /setD Hrex mem_rev_ring De2.
case: (r x) => //=.
by rewrite -(Eface _ x) Dx' De2 -!(fclosed1 (diskN_node _) x'); auto.
Qed.

Lemma diskF_rev_ring : diskF (rev_ring r) =1 setD (setC (diskN r)) (fband r).
Proof. by move=> y; rewrite /setD -diskN_rev_ring -fband_rev_ring. Qed.

Definition chord_ring (x : g) := Adds x (arc r (fproj r (edge x)) (fproj r x)).

Lemma scycle_chord_ring : forall x, fband r x -> fband r (edge x) ->
   scycle rlink (chord_ring x).
Proof.
move=> x Hx Hex; case: {Hx}(fprojP Hx) {Hex}(fprojP Hex).
rewrite /chord_ring; set y1 := fproj r x; set y2 := fproj r (edge x).
move=> Hy1 Hxy1 [Hy2 Hxy2]; have Hy21: (negb (eqd y2 y1)).
  apply/eqP => [Dy1]; case/set0Pn: Hbg; exists x.
  by rewrite (same_cface Hxy1) -Dy1 Sface.
case (andP HUr); case: (rot_to_arc Ur Hy2 Hy1 Hy21) => [i p1 p2 <- _ Dr].
rewrite -(cycle_rot i) -(simple_rot i) {}Dr.
rewrite /= add_last_cat path_cat /= -cat_adds {2}/rlink; move/and3P=> [Hp1 Ep1 _].
rewrite -cat_add_last simple_cat -rot1_adds simple_rot; move/andP=> [Up1 _].
rewrite /scycle (cycle_path x) /= Hp1 /rlink Hxy2 Sface (same_cface Hxy1) Sface.
by rewrite Ep1 andTb simple_adds (closed_connect (fbandF _) Hxy1) -simple_adds.
Qed.

Variable x : g.

Hypotheses (HxE : diskE r x) (Hx : fband r x) (Hex : fband r (edge x)).

Remark RingPartHdEr : forall y, diskE r y = diskE r (edge y).
Proof. exact (fclosed1 (diskE_edge Hpg HUr)). Qed.
Notation HdEr := RingPartHdEr.

Remark RingPartHeex : fband r (edge (edge x)). Proof. by rewrite De2 Hx. Qed.
Notation Heex := RingPartHeex.
Remark RingPartHexE : diskE r (edge x). Proof. by rewrite -HdEr HxE. Qed.
Notation HexE := RingPartHexE.

Let x1 := fproj r x.
Let x2 := fproj r (edge x).
Remark RingPartHx1 : r x1. Proof. by case (fprojP Hx). Qed.
Let Hx1 := RingPartHx1.
Remark RingPartHx2 : r x2. Proof. by case (fprojP Hex). Qed.
Let Hx2 := RingPartHx2.
Remark RingPartHxx1 : cface x x1. Proof. by case (fprojP Hx). Qed.
Let Hxx1 := RingPartHxx1.
Remark RingPartHxx2 : cface (edge x) x2. Proof. by case (fprojP Hex). Qed.
Let Hxx2 := RingPartHxx2.
Remark RingPartHx12 : negb (x1 =d x2).
Proof.
apply/eqP => Dx1; case/set0Pn: Hbg; exists x.
by rewrite (same_cface Hxx1) Dx1 Sface Hxx2.
Qed.
Let Hx12 := RingPartHx12.

Let r1 := arc r x1 x2.
Let r2 := arc r x2 x1.
Let ix := let (i, _, _, _, _, _) := rot_to_arc Ur Hx1 Hx2 Hx12 in i.
Remark RingPartDr : rot ix r = cat r1 r2.
Proof.
by rewrite /ix /r1 /r2; case: rot_to_arc => [i p1 p2 <- <- Dr].
Qed.
Let Dr := RingPartDr.
Remark RingPartEr : r =1 setU r1 r2.
Proof. by move=> y; rewrite -mem_cat -Dr mem_rot. Qed.
Let Er := RingPartEr.
Remark RingPartDr1 : {p1 : seq g | Adds x1 p1 = r1}.
Proof. by case: (rot_to_arc Ur Hx1 Hx2 Hx12) => [i p1 p2 Dp1 _ _]; exists p1. Qed.
Let Dr1 := RingPartDr1.
Remark RingPartDr2 : {p2 : seq g | Adds x2 p2 = r2}.
Proof. by case: (rot_to_arc Ur Hx1 Hx2 Hx12) => [i p1 p2 _ Dp2 _]; exists p2. Qed.
Let Dr2 := RingPartDr2.

Let cr1 := chord_ring x.
Let cr2 := chord_ring (edge x).
Remark RingPartDcr1 : cr1 = Adds x r2. Proof. done. Qed.
Let Dcr1 := RingPartDcr1.
Remark RingPartDcr2 : cr2 = Adds (edge x) r1.
Proof. by rewrite /cr2 /chord_ring De2. Qed.
Let Dcr2 := RingPartDcr2.

Remark RingPartHdEr1 : forall y, diskE cr1 y = diskE cr1 (edge y).
Proof. exact (fclosed1 (diskE_edge Hpg (scycle_chord_ring Hx Hex))). Qed.
Let HdEr1 := RingPartHdEr1.
Remark RingPartHdEr2 : forall y, diskE cr2 y = diskE cr2 (edge y).
Proof. exact (fclosed1 (diskE_edge Hpg (scycle_chord_ring Hex Heex))). Qed.
Let HdEr2 := RingPartHdEr2.

Lemma proper_chord_ring : proper_ring cr1.
Proof.
rewrite Dcr1; case: Dr2 => [[|z p] <-] //=.
by apply/eqP => Dx2; case/andP: HexE; rewrite Dx2 Hx2.
Qed.

Lemma diskN_chord_ring : diskN cr1 =1 setD (diskN r) (diskN cr2).
Proof.
move=> y; suffice: diskN cr1 y + diskN cr2 y = diskN r y.
  by rewrite /setD; case (diskN cr1 y); case (diskN cr2 y); case (diskN r y).
  case: (connected_clink Hcg x y) => [p Hp <-] {y}.
elim/last_ind: p Hp => [|p y Hrec] /=.
  clear; rewrite !diskN_E /setU HxE orbT HdEr2 {1}Dcr2 /diskE /setD.
  by case (andP HxE); rewrite /= !setU11 /= /setU1 He1 Er /setU; case (r1 x).
rewrite last_add_last -cats1 path_cat !(fclosed1 (diskN_node _) y).
move/and3P=> [Hp Dy _]; case/clinkP: Dy {Hrec Hp}(Hrec Hp) => [<-|Dy]; auto.
rewrite -[last x p]Eface {p}Dy; move/node: y => y.
rewrite !diskN_E {1 2 4 5 6}/setU {1 3}Dcr1 {1 3}Dcr2 /= /setU1.
rewrite -{1}[x]De2 !(inj_eqd (Iedge g)).
case: (x =P y) => [<-|_].
  clear; rewrite HdEr2 HxE He1 /= /diskE /setD /= setU11 orbT /=.
  by case/andP: HxE; rewrite Er /setU; case (r1 x).
case: (edge x =P y) => [<-|_].
  clear; rewrite HexE HdEr1 /diskE /setD /= De2 setU11 orbT /=.
  by case (andP HexE); rewrite Er /setU orbC; case (r2 (edge x)).
case Hry: (r y).
  rewrite -diskN_E (diskN_edge_ring Hry) -HdEr1 -HdEr2 /= orbC.
  case: (diskE cr1 y) => //=; rewrite orbC addnC; case: (diskE cr2 y) => //= _.
  move: Ur Hry; rewrite -(uniq_rot ix) Er Dr uniq_cat /setU !orbF.
  case/and3P=> [_ Hr12 _].
  by case Hr2: (r2 y); [ rewrite (negbE (hasPn Hr12 y Hr2)) | rewrite orbF => -> ].
rewrite Er /setU in Hry; case: (r1 y) Hry => [|] // -> /=.
rewrite (HdEr y) (HdEr1 y) (HdEr2 y) {3 6}/diskE /setD /setU.
case Hrey: (r (edge y)); rewrite Er /setU in Hrey.
  case/orP: Hrey; move=> Hrey; rewrite Hrey /= orbC.
  case: (diskE cr1 (edge y)) => //=.
    by rewrite /diskE /setD Dcr2 /= /setU1 Hrey orbT.
  case: (diskE cr2 (edge y)); first by rewrite addnC.
  by rewrite /diskE /setD Dcr1 /= /setU1 Hrey orbT.
by case/norP: Hrey => [H H']; rewrite (negbE H) (negbE H').
Qed.

Lemma fband_chord_ring : setU (fband cr1) (fband cr2) =1 fband r.
Proof.
move=> y; apply/orP/hasP.
  rewrite /fband; case; move/hasP=> [z Hz Hyz];
   (rewrite ?Dcr1 ?Dcr2 /= in Hz; case/setU1P: Hz => [Dz|Hz];
     last by exists z; first by rewrite Er /setU Hz ?orbT);
   [ exists x1 | exists x2 ]; rewrite ?(same_cface Hyz) -?Dz;
   [ exact Hx1 | exact Hxx1 | exact Hx2 | exact Hxx2 ].
move=> [z Hz Hyz]; rewrite Er in Hz.
case/orP: Hz => [Hz|Hz]; [ right | left ]; apply/hasP;
 by exists z; rewrite //= /setU1 ?De2 -/x1 -/x2 -/r1 -/r2 Hz orbT.
Qed.

Lemma diskF_chord_ring : diskF cr1 =1 setD (diskF r) (diskF cr2).
Proof.
move=> y; rewrite {2 3}/diskF /setD -fband_chord_ring /setU.
case HyF: (fband cr2 y).
  rewrite /fband in HyF; case/hasP: HyF => [z Hz Hyz].
  rewrite (closed_connect (diskF_face _) Hyz) /diskF /setD.
  by rewrite diskN_chord_ring /setD diskN_E /setU Hz orbT /= andbF.
rewrite /diskF /setD diskN_chord_ring.
by case (fband cr1 y); rewrite // /= ?andbF.
Qed.

Lemma nontrivial_chord_ring : negb (x2 =d next r x1) ->
 (exists y, diskF cr1 y) -> nontrivial_ring 0 cr1 /\ size cr1 < size r.
Proof.
rewrite -(next_rot ix Ur) -(size_rot ix r) Dr.
case: (Dr1) => [[|x3 p1] Dp1]; rewrite -Dp1.
  by case: (Dr2) => [p2 <-]; rewrite /= !set11.
move=> _ Hcr1F; split; last by rewrite size_cat Dcr1 /= !addSnnS leq_addl.
apply/(nontrivial0P _); split; auto.
exists x3; apply/andP; split.
  have Hx3: r x3 by rewrite Er -Dp1 /setU /= /setU1 set11 /= orbT.
  have Ux3 := Ur; rewrite -(uniq_rot ix) Dr -Dp1 /= mem_cat in Ux3.
  case/and3P: Ux3; move/norP=> [Ux31 _]; move/norP=> [_ Ux3] _.
  apply/hasP => [[y Hy Hyx3]]; rewrite Dcr1 /= in Hy.
  case/setU1P: Hy => [Dy|Hy].
    case/eqP: Ux31; apply: (scycle_cface HUr _ Hx3 Hx1).
    by rewrite (same_cface Hyx3) -Dy Hxx1.
  case: (negP Ux3); rewrite (scycle_cface HUr Hyx3 Hx3) //.
  by rewrite Er /setU Hy orbT.
rewrite /setC diskN_chord_ring /setD diskN_E /setU {1}Dcr2 -Dp1 /=.
by rewrite /setU1 set11 /= !orbT.
Qed.

End RingPartitions.

Section NonTrivialRing.

Variable m : nat.
Hypothesis Hm : nontrivial_ring m r.

Lemma nontrivial_ring_proper : proper_ring r.
Proof.
case Dr: {1 3}r (andP Hm) => [|x r'] [Hm1 Hm2].
  by rewrite /n_comp -(@eq_card g set0) ?card0 // in Hm1 => y; rewrite /setI andbC.
case: r' Dr {Hm1} => [|ex [|z r']] Dr //.
  by move: Hr; rewrite Dr /= /rlink Sface (set0P Hbg).
apply/eqP=> Dex; rewrite /n_comp -(@eq_card g set0) ?card0 // in Hm2 => {Hm2} y.
suffice Hy: diskN r y by rewrite /setI /diskFC /setC /setD Hy /= !andbF.
case: (connected_clink Hcg x y) => [p Hp <-] {y}.
have Hrx: r x by rewrite Dr /= setU11.
elim/last_ind: p Hp => [|p y Hrec]; first by rewrite /= diskN_E /setU Hrx.
rewrite last_add_last -cats1 path_cat (fclosed1 (diskN_node r)).
move/and3P=> [Hp Dy _]; apply: etrans {Hrec Hp}(Hrec Hp).
case/clinkP: Dy => [<-|Dy] //; rewrite -[last x p]Eface Dy !diskN_E /setU.
rewrite -(fclosed1 (diskE_edge Hpg HUr)); congr orb.
by rewrite Dr -Dex /= /setU1 !orbF -{3}[x]De2 !(inj_eqd (Iedge g)) orbC.
Qed.

Lemma nontrivial_rev_ring : nontrivial_ring m (rev_ring r).
Proof.
case: (andP Hm) (diskN_rev_ring nontrivial_ring_proper) => [Hm1 Hm2] HrN.
have HrF := fband_rev_ring; apply/andP; split; [ move: Hm2 | move: Hm1 ];
 apply: etrans; congr leq; apply: eq_n_comp_r => x.
  by rewrite /diskFC /setD -HrN -HrF.
by rewrite /diskFC /setD /setC HrN HrF /setC negb_elim.
Qed.

Notation gd := (snip_disk Hpg' HUr) (only parsing).
Notation bgd := (snipd_ring Hpg' HUr) (only parsing).
Let pfd x := preimage (fun y : snip_disk Hpg' HUr => snipd y) (cface x).

Remark RingPartpfdP : forall x y, cface x (snipd y) ->
   exists2 z, Some z = pick (pfd x) & cface y z.
Proof.
move=> x y Hy; case: (pickP (pfd x)) => [z Hz|Ha]; last by case/idP: (Ha y).
exists z; rewrite //= Sface in Hy |- *.
by apply: (etrans (esym (cface_snipd _ _)) (connect_trans _ Hz)).
Qed.
Let pfdP := RingPartpfdP.

Definition rev_snipd_disk := snip_disk Hpg' scycle_rev_ring.

Definition rev_snipr_disk := snip_rem Hpg' scycle_rev_ring.

Definition rev_snipd_ring : seq rev_snipd_disk := snipd_ring Hpg' scycle_rev_ring.

Definition rev_snipr_ring : seq rev_snipr_disk := snipr_ring Hpg' scycle_rev_ring.

Lemma rev_snipr_ring_eq : maps (@snipr _ _ _ _) rev_snipr_ring = maps edge r.
Proof. by rewrite /rev_snipr_ring maps_snipr_ring /rev_ring rev_rev. Qed.

Notation grd := rev_snipd_disk (only parsing).
Notation bgrd := rev_snipd_ring (only parsing).
Notation grr := rev_snipr_disk (only parsing).
Notation bgrr := rev_snipr_ring (only parsing).
Let pfrr x := preimage (fun y : rev_snipr_disk => snipr y) (cface x).

Remark RingPartpfrrP : forall x y, cface x (snipr y) ->
  exists2 z, Some z = pick (pfrr x) & cface y z.
Proof.
move=> x y Hy; case: (pickP (pfrr x)) => [z Hz|Ha]; last by case/idP: (Ha y).
exists z; rewrite //= Sface in Hy.
by apply: (etrans (patch_face_r (snip_patch _ _) _ _) (connect_trans _ Hz)).
Qed.
Let pfrrP := RingPartpfrrP.

Lemma rev_ring_cotrace : forall et,
  ring_trace (snipd_ring Hpg' HUr) et <-> ring_trace (rotr 1 rev_snipr_ring) et.
Proof.
set pd := snipd_ring Hpg' HUr; set pr := rotr 1 rev_snipr_ring.
have Efp: maps (froot face) (maps (@snipr _ _ _ _) pr) =
          maps (froot face) (maps (@snipd _ _ _ _) pd).
  rewrite /pd maps_snipd_ring // /pr !maps_rotr /rev_snipr_ring.
  rewrite /rev_snipr_disk maps_snipr_ring maps_rev.
  by rewrite froot_face_rev_ring rev_rev rotr_rot.
move=> et; split.
  move=> [k [HkE HkF] Det]; rewrite {et}Det.
  pose k' :=
    if pick (pfd (snipr (_ : rev_snipr_disk))) is Some y then k y else Color0.
  have Hppgr := snip_patch Hpg' scycle_rev_ring.
  have HgrrE: plain rev_snipr_disk.
    by move: HgE; rewrite (plain_patch Hppgr); case/andP.
  have Hk'F: invariant face k' =1 rev_snipr_disk.
    move=> x; apply/eqcP; rewrite /setA /k' -(@eq_pick _ (pfd (snipr x))) //.
    by move=> y; apply: {y}same_cface; rewrite -(patch_face_r Hppgr) fconnect1.
  have Hk'E: forall x, rev_ring r (snipr x) = false ->
     (k' (edge x) =d k' x) = false.
    move=> [x Hx]; rewrite /k' /=; move=> Hxr.
    rewrite /setC /diskE /setD Hxr /= in Hx.
    rewrite (diskN_rev_ring nontrivial_ring_proper) /= /setC negb_elim in Hx.
    rewrite -(codom_snipd Hpg' HUr) in Hx.
    move/set0Pn: Hx => [xd Dx]; rewrite /preimage in Dx.
    case: (@pfdP x xd); first by rewrite -(eqP Dx) connect0.
    move=> yd /= <- Hyd; rewrite -{yd Hyd}(fconnect_invariant HkF Hyd).
    pose fexd := face (edge xd); case: (@pfdP (edge x) fexd).
      rewrite (eqP Dx) -{1}[xd]Eedge -/fexd cface1.
      by case: fexd => [y Hy]; rewrite /= Enode connect0.
    move=> yd /= <- Hyd; rewrite /fexd -(@cface1 (snip_disk Hpg' HUr)) in Hyd.
    by rewrite -{yd Hyd}(fconnect_invariant HkF Hyd); exact: HkE.
  exists k'; [ split; auto | idtac ].
    move=> xr; case Hxr: (rev_ring r (snipr xr)); last exact: Hk'E.
    rewrite /invariant eqd_sym -{1}[xr](plain_eq HgrrE); apply: Hk'E.
    case: xr Hxr => [x _] /=; rewrite !mem_rev_ring => Hex.
    move: (diskN_edge_ring nontrivial_ring_proper Hex).
    by rewrite diskN_E; case/norP; move/negbE.
  congr trace; elim: pd pr Efp => [|xd pd Hrec] [|xr pr] //=.
  case; move/(introT (rootP (Sface g)))=> Hxrd Hp; congr Adds; auto.
  case: (pfdP Hxrd); rewrite /k' /=; move=> yd <- Hyd.
  exact (fconnect_invariant HkF Hyd).
move=> [k' [Hk'E Hk'F] -> {et}].
pose k := if pick (pfrr (@snipd _ Hpg' _ HUr _)) is Some y then k' y else Color0.
have HkF: invariant face k =1 snip_disk Hpg' HUr.
  move=> x; apply/eqcP; rewrite /setA /k -(@eq_pick _ (pfrr (snipd x))) //.
  by move=> y; apply: {y}same_cface; rewrite cface_snipd fconnect1.
exists k; first (split; auto => x).
  rewrite /invariant -(eqcP (HkF (edge x))) -{2}[x]Eedge.
  move: {x}(face (edge x)) => [x Hx]; rewrite /k /=.
  have Hxr := codom_snipr Hpg' scycle_rev_ring (node x).
  rewrite /setC /diskE /setD in Hxr.
  rewrite (diskN_rev_ring nontrivial_ring_proper) /setC in Hxr.
  rewrite -(fclosed1 (diskN_node r)) {}Hx andbF /= in Hxr.
  case/(@set0Pnx rev_snipr_disk _): Hxr; move=> nxr; move/eqP=> Dnx.
  case: (@pfrrP (node x) nxr); first by rewrite Dnx connect0.
  move=> yr /= <- Hyr; rewrite -{yr Hyr}(fconnect_invariant Hk'F Hyr).
  pose enxr := edge nxr; case: (@pfrrP x enxr) => [|yr /= <- Hyr].
    rewrite -{1}[x]Enode Dnx /enxr -cface1.
    by case: (nxr) => /= *; rewrite connect0.
  rewrite -{yr Hyr}(fconnect_invariant Hk'F Hyr); exact: Hk'E.
congr trace; elim: pd pr Efp => [|xd pd Hrec] [|xr pr] //=.
case; move/(introT (rootP (Sface g)))=> Hxr Hp; congr Adds; auto.
rewrite Sface in Hxr; case: (pfrrP Hxr); rewrite /k /=; move=> yr <- Hyr.
exact (fconnect_invariant Hk'F Hyr).
Qed.

Lemma ring_disk_closed : cubic g ->
  kempe_closed (ring_trace (snipd_ring Hpg' HUr)).
Proof.
move=> HgN; have Hppgr := snip_patch Hpg' scycle_rev_ring.
have Hbgrr: (ucycle_planar_plain_quasicubic (rotr 1 rev_snipr_ring)).
  split; last exact (planar_snipr Hpg' scycle_rev_ring).
  split; last by rewrite /ucycle cycle_rotr uniq_rotr; case Hppgr.
  split; first by move: HgE; rewrite (plain_patch Hppgr); case/andP.
  move: HgN; rewrite (cubic_patch Hppgr); case/andP; clear; apply: etrans.
  by apply: eq_subset => [x]; rewrite /setC mem_rotr.
move=> et; case: (rev_ring_cotrace et) => [H _]; move/H {H} => Hetr.
case: (kempe_map Hbgrr Hetr) => [Hget [w Hw Hwet]]; split.
  move=> ge; case: (rev_ring_cotrace (permt ge et)); auto.
exists w; auto; move=> et' Hwet'; case (rev_ring_cotrace et'); auto.
Qed.

Lemma colorable_from_ring : forall et,
   ring_trace (snipd_ring Hpg' HUr) et -> ring_trace rev_snipd_ring (rev et) ->
  four_colorable g.
Proof.
move=> et Hetr Hetd; have Hppgr := snip_patch Hpg' scycle_rev_ring.
case (colorable_patch Hppgr); clear; apply.
case: (rev_ring_cotrace et) => [H _]; case/H: {H}Hetr => [k Hk Det].
exists (rev et); first done; rewrite rev_rev; exists k; auto.
by rewrite Det -!urtrace_trace -urtrace_rot -maps_rot rot_rotr.
Qed.

Lemma ring_disk_chord : negb (chordless (snipd_ring Hpg' HUr)) ->
 exists2 r', @scycle g rlink r' & nontrivial_ring 0 r' /\ size r' < size r.
Proof.
have Ird := @inj_snipd _ Hpg' _ HUr; have Drd := maps_snipd_ring Hpg' HUr.
move/andP: (ucycle_snipd_ring Hpg' HUr) => [_ Urd].
have Erd: forall xd yd, (xd =d yd) = (@snipd _ Hpg' _ HUr xd =d snipd yd) by done.
have EdN: forall xd, @snipd _ Hpg' _ HUr (node xd) = node (snipd xd) by done.
case/set0Pn; move=> xd; case/andP; move=> Hrx.
rewrite -(mem_maps Ird) maps_snipd_ring in Hrx.
case/set0Pn; move=> yd; case/andP; rewrite /adj; case/hasP; move=> zd.
rewrite {1}/rlink cface1 -fconnect_orbit -{1}[zd]Eedge -!cface_snipd {}EdN.
case: {zd}(face (edge zd)) => z /=.
rewrite (fclosed1 (diskN_node r)) -{3}[z]Enode -cface1.
move/node: z => z HzN Hxz Hzy; case/and3P.
rewrite !{}Erd -(next_maps Ird Urd) -(prev_maps Ird Urd) -(mem_maps Ird) {}Drd.
move/snipd: yd Hzy {Ird Urd} => y Hzy.
move/snipd: xd Hrx Hxz => x Hrx Hxz Hrxy Hryx Hry.
rewrite eqd_sym -(monic2F_eqd (prev_next Ur)) in Hryx.
have HzF: fband r z by apply/hasP; exists x; rewrite // Sface.
have HezF: fband r (edge z) by apply/hasP; exists y.
have HzE: diskE r z.
  apply/andP; split; last done; apply/idP => [Hrz]; case/idP: Hrxy.
  rewrite (scycle_cface HUr Hxz Hrx Hrz); apply/eqP.
  apply (scycle_cface HUr); auto; last by rewrite mem_next.
  rewrite Sface -(same_cface Hzy); exact (next_cycle Hr Hrz).
have HezE: diskE r (edge z) by rewrite -(fclosed1 (diskE_edge Hpg' HUr)).
have HrF := scycle_fproj HUr.
have EzF: fproj r z = x by rewrite -(fproj_cface r Hxz) HrF.
have EezF: fproj r (edge z) = y by rewrite (fproj_cface r Hzy) HrF.
have HrE := nontrivial_ring_proper.
case: (elimT (fcard0P (diskF_face r))). 
  by case/andP: Hm => [Hm1 _]; apply: leq_trans Hm1.
move=> t Ht; case Htz: (diskF (chord_ring z) t).
  exists (chord_ring z); first by apply scycle_chord_ring.
  apply nontrivial_chord_ring; auto; last by exists t.
  by rewrite EzF EezF eqd_sym.
exists (chord_ring (edge z)); first by apply scycle_chord_ring; rewrite ?De2.
apply nontrivial_chord_ring; rewrite ?De2; auto.
  by rewrite EzF EezF eqd_sym.
by exists t; rewrite (diskF_chord_ring HrE) ?De2 // /setD Htz.
Qed.

End NonTrivialRing.

End RevSnip.

Unset Implicit Arguments.
