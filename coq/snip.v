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
Require Import hypermap.
Require Import jordan.
Require Import color.
Require Import geometry.
Require Import patch.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Snip.

Variable g : hypermap.
Hypothesis Hpg : planar g.

(* Cutting a planar graph along a ring (i.e., a simple rlink cycle r).   *)

Variable r : seq g.

Hypothesis HUr : scycle rlink r.
Let Hr := scycle_cycle HUr.
Let UrF := scycle_simple HUr.
Let Ur := scycle_uniq HUr.

(* The disk defined by the ring is defined by the darts that can be      *)
(* reached from the ring by a clink path that starts with a inverse node *)
(* step and that does not cross the contour. That disk is node-closed.   *)
(* Because a planar g has the Jordan property, the edge-interior of that *)
(* disk is simply g with r removed (assuming we're not in the trivial    *)
(* case where r is an edge 2-cycle). For the face interior there we need *)
(* to remove all of (fband r).                                           *)

Definition dlink x y := negb (r x) && clink x y.

Definition dconnect x y := connect dlink (finv node y) x.

Definition diskN x := has (dconnect x) r.

Definition diskE := setD diskN r.

Definition diskF := setD diskN (fband r).

Definition diskFC := setD (setC diskN) (fband r).

Lemma diskN_node : fclosed node diskN.
Proof.
suffice Hn: fclosed (finv node) diskN.
  apply: (intro_closed (Snode g)) => x y Dy Hx.
  by rewrite (fclosed1 Hn y) -(eqP Dy) (finv_f (Inode g)).
have Inode' := (finv_inj (Inode g)).
apply: (intro_closed (fconnect_sym Inode')) => [x y Dy Hx]; apply/hasP.
case Hrx: (r x); first by exists x; last by rewrite /dconnect (eqP Dy) connect0.
case/hasP: Hx => [z Hrz Hzx].
exists z; first done; apply: (connect_trans Hzx); apply connect1.
by rewrite /dlink Hrx /clink /relU /setU Dy.
Qed.

Lemma diskN_E : diskN =1 setU r diskE.
Proof.
move=> x; rewrite /setU /diskE /setD; case Hx: (r x); last done.
rewrite -(diskN_node (introT eqP (f_finv (Inode g) x))).
by apply/hasP; exists x; last exact: connect0.
Qed.

Lemma diskF_face : fclosed face diskF.
Proof.
apply: (intro_closed (Sface g)) => [x y]; move/eqP=> <- {y}; move/andP=> [HxF HxN].
rewrite /diskF /setD -(fclosed1 (fbandF r)) HxF.
case: (hasP HxN) => y Hy Hyx; apply: (introT (hasPx (dconnect _) r)).
exists y; auto.
apply: {y Hy Hyx}(connect_trans Hyx); apply connect1; apply/andP.
split; last exact: clinkF.
by apply/idP => Hx; case/idP: HxF; apply: (subsetP (ring_fband _)).
Qed.

Lemma diskFC_face : fclosed face diskFC.
Proof.
move=> /= x y Dy; move: (diskF_face Dy).
rewrite /diskFC /diskF /setD /setC (fbandF r Dy).
by case Hy: (fband r y); last by move=> /= <-.
Qed.

Lemma diskE_edge : fclosed edge diskE.
Proof.
apply: (intro_closed (Sedge g)) => [x y]; move/eqP=> <- {y} Hx.
suffice: exists2 x', diskN x'
   & exists2 p, fpath face x' p /\ last x' p = edge x & negb (has r (Adds x' p)).
  move=> /= [x' Hx' [p [Hp <-] H]]; move/norP: H => [Hrx' Hrp].
  elim/last_ind: p Hp Hrp => [|p y Hrec] /=.
    by move=> _; rewrite /diskE /setD Hx' Hrx'.
  rewrite last_add_last -cats1 path_cat has_cat /= andbT orbF.
  move/andP=> [Hp Dy]; move/norP=> [Hrp Hry].
  rewrite /diskE /setD {}Hry /=; apply/hasP.
  move/andP: {Hrec Hp Hrp}(Hrec Hp Hrp) => [Hry' Hy'].
  move/hasP: Hy' => [z Hz Hzy']; exists z; auto.
  apply: (connect_trans Hzy'); apply connect1.
  by rewrite /dlink (negbE Hry') -(eqP Dy) clinkF.
move/andP: Hx => [Hrx HxN]; set x' := face (edge x).
have Hx': cface x' (edge x) by rewrite Sface /x' fconnect1.
case/connectP: Hx'; move=> q0; case/shortenP=> q Hq Uq _ {q0} Eq.
case Hqr: (negb (has r (Adds x' q))).
  by exists x'; [ rewrite (fclosed1 diskN_node) /x' Eedge | exists q; auto ].
case/hasP: Hqr => [y Hqy Hry]; case/rot_to: (Hry) Hr => [i r' Dr].
rewrite -(cycle_rot i rlink r) (cycle_path y) Dr /=.
set z := last y r'; set z' := face (edge z); move/andP=> [Hzy Hr'].
have Hrz: r z by rewrite -(mem_rot i) Dr /z mem_last.
have Hyz': cface y z' by rewrite Sface /z' -cface1.
have Hqz': Adds x' q z'.
  have HqF: cface x' =1 Adds x' q.
    apply: fconnect_cycle; last by apply: setU11.
    by rewrite (cycle_path x) /= Eq {1}/eqdf set11.
  by rewrite -HqF; apply: (connect_trans _ Hyz'); rewrite HqF.
simpl in Hqz'; case/orP: Hqz' => [Dz'|Hqz'].
  by rewrite (Iedge g (Iface g (eqP Dz'))) Hrz in Hrx.
case: Eq; case/splitPr: {q}Hqz' Uq Hq Hqy => [q1 q2].
rewrite -cat_adds uniq_cat mem_cat path_cat last_cat.
move/and3P=> [Uq1 Uq12 Uq2]; rewrite /= {2}/eqdf; move/and3P=> [Hq1 Eq1 Hq2].
case/orP=> [Hq1y|Hq2y].
  exists z'; first by rewrite (fclosed1 diskN_node) /z' Eedge diskN_E /setU Hrz.
  exists q2; first by auto.
  apply/(hasPx _ (Adds z' q2)) => [[t Hq2t Hrt]]; case/hasP: Uq12; exists y; auto.
  have Hyt: cface y t by apply: (connect_trans Hyz' (path_connect Hq2 _)).
  by rewrite (scycle_cface HUr Hyt Hry Hrt).
pose rclink t := face (if r t then edge t else t).
have [c [Hc Uc Ec] [Hr'c Hcq1]]: exists2 c,
       and3 (fpath rclink z' c) (uniq (Adds z' c)) (last z' c = z)
    &  sub_set (Adds y r') (Adds z' c) /\ negb (has (Adds x' q1) (Adds z' c)).
  have Hr'r: sub_set r' r.
    by move=> t Ht; rewrite -(mem_rot i r) Dr; apply: setU1r.
  have HcF: forall (t : g) c, fpath face t c ->
      sub_set (Adds t c) (cface (last t c)).
    move=> t c Hc t' Ht'; apply: (connect_trans _ (path_connect Hc Ht')).
    by rewrite Sface; apply/connectP; exists c.
  have HcrF: forall t c, uniq (Adds t c) -> r (last t c) -> fpath face t c ->
      fpath rclink t c.
    have Hbase: fun_base (fun t => t) rclink face r.
      by move=> t t' Ht; rewrite /eqdf /rclink (negbE Ht).
    move=> t c Uc Hrc Hc; rewrite -(maps_id c) (path_maps (d := g) Hbase) //.
    rewrite -(@eq_has _ r) //.
    rewrite lastI uniq_add_last in Uc; case/andP: Uc => [Uc _].
    apply/hasPn=> [t' Ht']; apply/idP => [Hrt']; case/idP: Uc.
    rewrite (scycle_cface HUr _ Hrc Hrt') //.
    by apply: (HcF _ _ Hc); apply mem_belast.
  have Ur' := Ur; rewrite -(uniq_rot i) Dr /= in Ur'.
  move/andP: Ur' => [Hr'y Ur'].
  suffice [c2 [Hc2 Uc2 Ec2] [Hr'c2 Hc2r']]: exists2 c2,
        and3 (fpath rclink y c2) (uniq c2) (last y c2 = z)
     &  sub_set r' c2 /\ sub_set (fband c2) (fband r').
    have Hc2y: forall t, c2 t -> negb (cface y t).
      move=> t Hc2t; apply/idP => Hyt.
      have Hr't: has (cface t) r'.
        by apply: Hc2r'; apply/hasP; exists t; last exact: connect0.
      move: {Hr't}(hasP Hr't) => [t' Hr't' Htt']; case (negP Hr'y).
      by rewrite (scycle_cface HUr (connect_trans Hyt Htt') Hry) ?Hr'r.
    case/splitPl: {q2 Eq2}Hq2y Hq2 Uq12 Uq2 => [c1 q2' Ec1].
    rewrite path_cat -cat_adds has_cat uniq_cat.
    move/andP=> [Hc1 _]; move/norP=> [Hc1q1 _]; move/andP=> [Uc1 _].
    exists (cat c1 c2).
      rewrite path_cat last_cat Ec1 -cat_adds uniq_cat Uc1 Uc2 andbT.
      rewrite (HcrF _ _ Uc1) ?Ec1 //; repeat split; auto.
      apply/hasP => [[t Hc2t Hc1t]]; case/idP: (Hc2y _ Hc2t); rewrite -Ec1.
      apply: HcF; auto.
    rewrite -cat_adds has_cat (negbE Hc1q1); split.
      move=> t; move/setU1P=> [<-|Ht].
        by rewrite -Ec1 mem_cat /setU mem_last.
      by rewrite mem_cat /setU (Hr'c2 _ Ht) orbT.
      apply/hasP => [[t Hc2t Hq1t]]; case/idP: (Hc2y _ Hc2t).
    apply: (connect_trans Hyz'); rewrite -(eqP Eq1) -cface1; apply: HcF; auto.
  rewrite {i Dr z' Hzy Hrz Hyz' Uq12 Uq2 Eq2 Eq1 Hq2 Hq2y Hr'y}/z.
  elim: r' y Hry Hr'r Hr' Ur' => [|y' r' Hrec] y Hry /=.
    by do 3 clear; exists (Seq0 g); [ auto | split; move=> z ].
  move=> H; move: {H}(H _ (setU11 _ _)) (H _ (setU1r _ _)) => Hry' Hr'r.
  move/andP=> [Hyy' Hr']; move/andP=> [Hr'y' Ur'].
  case: {Hrec Hr' Ur'}(Hrec _ Hry' Hr'r Hr' Ur').
  move=> c2 [Hc2 Uc2 Ec2] [Hr'c2 Hc2r'].
  rewrite /rlink cface1 in Hyy'; case/connectP: Hyy'.
  move=> c0; case/shortenP=> c1 Hc1 Uc1 _ {c0} Ec1.
  have Hc1F := HcF _ _ Hc1; rewrite Ec1 in Hc1F.
  exists (cat (Adds (face (edge y)) c1) c2).
    split; last by rewrite last_cat /= Ec1.
      rewrite path_cat /= Ec1 Hc2 andbT {1}/rclink {1}/eqdf Hry set11.
      by apply: HcrF; rewrite ?Ec1.
    rewrite uniq_cat Uc1 Uc2 andbT.
    apply/hasP => [[t Hc1t Hc2t]]; case/idP: Hr'y'.
    have Hr't: fband r' t.
      by apply: Hc2r'; apply/hasP; exists t; last exact: connect0.
    case/hasP: Hr't => [t' Hr't' Htt'].
    have Hy't': cface y' t' by apply: (connect_trans (Hc1F _ _) Htt').
    by rewrite (scycle_cface HUr Hy't' Hry' (Hr'r _ Hr't')).
  split; move=> t Ht.
    case/setU1P: Ht => [<-|Ht].
      by rewrite -Ec1 mem_cat /setU mem_last.
    by rewrite mem_cat /setU (Hr'c2 _ Ht) orbT.
  rewrite /fband has_cat in Ht; case/orP: Ht => [Hc1t|Hc2t].
    case/hasP: Hc1t => [t' Hc1t' Htt'].
    apply/hasP; exists y'; first by apply: setU11.
    by rewrite (same_connect (Sface g) Htt') Sface Hc1F.
  move: {Hc2t}(hasP (Hc2r' _ Hc2t)) => [t' Hr't' Htt'].
  by apply/hasP; exists t'; first by apply: setU1r.
have [x1 Hnx1 [p [Hp Ep] Upc]]: exists2 x1, Adds z' c (node x1)
          & exists2 p, path clink x1 p /\ last x1 p = x'
                    &  negb (has (Adds z' c) (Adds x1 p)).
  case/hasP: HxN; move=> x0 Hrx0; case/connectP.
  set x0' := finv node x0; move=> p Hp.
  have Hcc: fcycle rclink (Adds z' c).
    by rewrite (cycle_path x) /= Hc /eqdf /rclink Ec Hrz -/z' set11.
  have Hpc: has (Adds z' c) (Adds x0' p).
    have Hcx0: Adds z' c x0 by apply: Hr'c; rewrite -Dr mem_rot.
    have <-: rclink x0 = x0'.
      by rewrite /x0' -{2}[x0]Eedge (finv_f (Inode g)) /rclink Hrx0.
    by apply/orP; left; rewrite (eqP (next_cycle Hcc Hcx0)) mem_next.
  elim: p {x0 Hrx0}x0' Hp Hpc => [|x1 p Hrec] x0.
    rewrite /= orbF; move=> _ Hcx Dx0.
    exists x'; first by rewrite /x' Eedge -Dx0.
    exists (Seq0 g); first by split.
    rewrite /= orbF; apply/idP => [Hcx']; case/hasP: Hcq1.
    by exists x'; last by apply: setU11.
  rewrite {-1 3 5}[Adds]lock /= -lock; move/andP=> [Hx01 Hp].
  case Hcp: (has (Adds z' c) (Adds x1 p)); eauto.
  rewrite orbF; move=> Hcx0 Ep; move: (Hcx0) Hx01 {Hrec}.
  rewrite /dlink -mem_next -(eqP (next_cycle Hcc Hcx0)) /rclink.
  case (r x0); first done.
  move=> Hcfx0; case/clinkP=> [Dx0|Dx1];
   last by rewrite /= -Dx1 -mem_adds Hcfx0 in Hcp.
  exists x1; first by rewrite -Dx0.
  exists (add_last p x').
    split; last by rewrite last_add_last.
    rewrite -cats1 path_cat /= Ep -{1}[x]Eedge -/x' clinkN /= andbT.
    by apply: (sub_path _ Hp) => [t t']; case/andP.
  rewrite -cats1 -cat_adds has_cat Hcp /= orbF.
  by apply/idP => [Hcx']; case/hasP: Hcq1; exists x'; last exact: setU11.
have Hcc: path clink z' c.
  apply: (sub_path _ Hc) => [t t']; move/eqP=> <- {t'}; rewrite /rclink.
  by case (r t); [ rewrite -{1}[t]Eedge clinkN | rewrite clinkF ].
have [c0 [Hc0 Ec0] Hc0c]: exists2 c0, path clink x1 c0 /\ clink (last x1 c0) z'
                                    & negb (has (Adds z' c) (Adds x1 c0)).
  exists (cat p q1).
    split; last by rewrite last_cat Ep -(eqP Eq1) clinkF.
    rewrite path_cat Hp Ep; exact (sub_path (@sub_relUr _ _ _) Hq1).
  rewrite -cat_adds has_cat (negbE Upc).
  by rewrite has_sym in Hcq1; case (norP Hcq1).
case/shortenP: Hc0 Ec0 => [c1 Hc1 Uc1 Hc01] Ec1.
case/and3P: (planarP g Hpg (Adds x1 (cat c1 (Adds z' c)))); split.
- rewrite last_cat /= Ec mem2_cat mem2_adds (finv_eq_monic (Enode g)) -/z'.
  by rewrite set11 -mem_adds Hnx1 orbT.
- rewrite -cat_adds uniq_cat Uc1 Uc andbT andTb; apply/hasP => [[t Hct Hc1t]].
  case/hasP: Hc0c; exists t; rewrite //= /setU1.
  by case: (orP Hc1t) => [Dt|Ht]; [ rewrite Dt | rewrite (Hc01 _ Ht) orbT ].
by rewrite path_cat /= Hc1 Ec1.
Qed.

Let ddart := subFin diskN.

Definition snipd_edge x := if r x then next r x else edge x.

Remark Hdedge : forall u : ddart, diskN (snipd_edge (subdE u)).
Proof.
move=> [x HxN]; rewrite /= /snipd_edge diskN_E /setU.
case Hrx: (r x); first by rewrite mem_next Hrx.
by rewrite orbC -(fclosed1 diskE_edge) /diskE /setD HxN Hrx.
Qed.

Definition snipd_face x := if r x then face (edge (prev r x)) else face x.

Remark Hdface : forall u : ddart, diskN (snipd_face (subdE u)).
Proof.
move=> [x HxN]; rewrite /= /snipd_face (fclosed1 diskN_node) diskN_E /setU.
case Hrx: (r x); first by rewrite Eedge mem_prev Hrx.
by rewrite orbC (fclosed1 diskE_edge) Eface /diskE /setD Hrx HxN.
Qed.

Remark Hdnode : forall u : ddart, diskN (node (subdE u)).
Proof. by move=> [x HxN]; rewrite /= -(diskN_node (x := x) (set11 _)). Qed.

Let dedge u : ddart := subdI (Hdedge u).
Let dnode u : ddart := subdI (Hdnode u).
Let dface u : ddart := subdI (Hdface u).

Remark snipd_monic : monic3 dedge dnode dface.
Proof.
move=> [x Hx]; apply: (subdE_inj _); rewrite /= /snipd_edge.
case Hrx: (r x); rewrite /snipd_face.
  by rewrite mem_next Hrx Eedge (prev_next Ur).
have HxE: (diskE (edge x)) by rewrite -(fclosed1 diskE_edge) /diskE /setD Hrx.
by case/andP: HxE => [Hrex _]; rewrite (negbE Hrex) Eedge.
Qed.

Definition snip_disk := Hypermap snipd_monic.
Definition snipd (u : snip_disk) := subdE u.

Lemma inj_snipd : injective snipd. Proof. apply: subdE_inj. Qed.

Lemma codom_snipd : codom snipd =1 diskN.
Proof.
move=> z; apply/set0Pn/idP => [[[y Hy] Dy]|Hz]; first by rewrite (eqP Dy).
exists (subdI Hz : snip_disk); apply: set11.
Qed.

Definition snipd_ring := preimage_seq snipd r.

Lemma maps_snipd_ring : maps snipd snipd_ring = r.
Proof.
by apply: maps_preimage => [x Hx]; rewrite codom_snipd diskN_E /setU Hx.
Qed.

Lemma ucycle_snipd_ring : ufcycle edge snipd_ring.
Proof.
have Ubgd: uniq snipd_ring by rewrite -(uniq_maps inj_snipd) maps_snipd_ring Ur.
rewrite /ucycle Ubgd andbT.
apply: (cycle_from_next Ubgd) => x Hx; apply/eqP; apply: inj_snipd.
rewrite /= /snipd_edge -/(snipd x) -maps_snipd_ring (mem_maps inj_snipd) Hx.
apply (next_maps inj_snipd Ubgd).
Qed.

Lemma cface_snipd : forall u v, cface (snipd u) (snipd v) = cface u v.
Proof.
have HdgF: forall u v, cface u v -> cface (snipd u) (snipd v).
  move=> u v; move/connectP=> [p Hp <-] {v}.
  elim: p u Hp => [|u p Hrec] [x Hx] /=; first by rewrite connect0.
  move/andP=> [Hux Hp]; apply: (connect_trans _ (Hrec _ Hp)) => {Hrec Hp}.
  rewrite -{u Hux}((_ =P u) Hux) /= /snipd_face.
  case Hrx: (r x); last by rewrite fconnect1.
  rewrite Sface -cface1; exact (prev_cycle Hr Hrx).
have HgdFr: forall u v, fband snipd_ring u = false ->
                        cface (snipd u) (snipd v) -> cface u v.
  move=> [x Hx] /= v Hxr; move/connectP=> [p Hp Ep].
  elim: p x Hx Hxr Hp Ep => [|y p Hrec] x Hx Hxr /=.
    by move=> _ Dx; apply: eq_connect0; apply: inj_snipd.
  move/andP=> [Dy Hp] Ep.
  case Hrx: (r x).
    case/hasP: Hxr; exists (@subdI g _ _ Hx); last exact: connect0.
    by rewrite -(mem_maps inj_snipd) maps_snipd_ring /=.
  have Hy: diskN y.
    rewrite (fclosed1 diskN_node) diskN_E /setU (fclosed1 diskE_edge).
    by rewrite -(eqP Dy) Eface orbC /diskE /setD Hrx Hx.
  apply: connect_trans {Hrec Hp Ep}(Hrec _ Hy _ Hp Ep).
    by apply connect1; rewrite /eqdf /eqd /= /snipd_face Hrx.
  apply/hasP => [[u Hu Hyu]]; case/hasP: Hxr; exists u; first done.
  apply: (connect_trans _ Hyu).
  by apply connect1; rewrite /eqdf /eqd /= /snipd_face Hrx.
move=> u v; apply/idP/idP; auto; case Hur: (fband snipd_ring u); auto.
rewrite (Sface snip_disk) Sface; case Hvr: (fband snipd_ring v); auto.
case: (hasP Hur) (hasP Hvr) => [u' Hu' Huu'] [v' Hv' Hvv'] Hvu.
have Hv'u': cface (snipd v') (snipd u').
  apply: (connect_trans (connect_trans _ Hvu) (HdgF _ _ Huu')).
  by rewrite Sface; auto.
rewrite Sface in Huu'; apply: (connect_trans Hvv' (connect_trans _ Huu')).
apply: (eq_connect0 _ (inj_snipd (scycle_cface HUr Hv'u' _ _)));
  by rewrite -maps_snipd_ring (mem_maps inj_snipd).
Qed.

Lemma simple_snipd_ring : simple snipd_ring.
Proof.
have Hdr: forall u, snipd_ring u -> r (snipd u).
  by move=> u Hu; rewrite -maps_snipd_ring (mem_maps inj_snipd).
move: Ur; rewrite -maps_snipd_ring (uniq_maps inj_snipd) /simple.
elim: snipd_ring Hdr => [|u p Hrec] //=.
move=> H; move: {H}(H _ (setU11 _ _)) (H _ (setU1r _ _)) => Hru Hpr.
move/andP=> [Hpu Up]; apply/andP; split; last by auto.
apply/mapsP => [[v Hv Hvu]]; case/idP: Hpu.
rewrite -(fun H => inj_snipd (scycle_cface HUr H (Hpr _ Hv) Hru)) // cface_snipd.
by apply/(rootP (Sface _)).
Qed.

Lemma scycle_snipd_ring : sfcycle edge snipd_ring.
Proof.
by rewrite /scycle simple_snipd_ring andbT; case (andP ucycle_snipd_ring).
Qed.

Let rdart := subFin (setC diskE).

Remark redgeP : forall u : rdart, setC diskE (edge (subdE u)).
Proof. move=> [z Hz]; by rewrite /setC /= -(diskE_edge (x := z) (set11 _)). Qed.

Definition snipr_node z := if r z then prev r z else node z.

Remark rnodeP : forall u : rdart, setC diskE (snipr_node (subdE u)).
Proof.
move=> [z Hz]; rewrite /snipr_node /setC /=.
case Hrz: (r z); first by rewrite /diskE /setD mem_prev Hrz.
apply/idP => [Hnz]; case/idP: Hz; rewrite /diskE /setD Hrz /=.
by rewrite (fclosed1 diskN_node) diskN_E /setU Hnz orbT.
Qed.

Definition snipr_face z :=
  if r (node (face z)) then next r (node (face z)) else face z.

Remark rfaceP : forall u : rdart, setC diskE (snipr_face (subdE u)).
Proof.
move=> [z Hz]; rewrite /snipr_face /setC /=.
case Hrnfz: (r (node (face z))); first by rewrite /diskE /setD mem_next Hrnfz.
rewrite /diskE /setD andbC (fclosed1 diskN_node) diskN_E /setU Hrnfz /=.
by rewrite (fclosed1 diskE_edge) Eface (negbE Hz).
Qed.

Let redge u : rdart := subdI (redgeP u).
Let rnode u : rdart := subdI (rnodeP u).
Let rface u : rdart := subdI (rfaceP u).

Remark snipr_monic : monic3 redge rnode rface.
Proof.
move=> [z Hz]; apply: subdE_inj; rewrite /= /snipr_node /snipr_face Eedge.
case Hrz: (r z); first by rewrite mem_next Hrz (prev_next Ur).
rewrite /setC /diskE /setD Hrz /= -{1}[z]Eedge -(fclosed1 diskN_node) in Hz.
by rewrite diskN_E in Hz; case/norP: Hz => [Hz _]; rewrite (negbE Hz) Eedge.
Qed.

Definition snip_rem := Hypermap snipr_monic.
Definition snipr (u : snip_rem) : g := subdE u.
Lemma inj_snipr : injective snipr. Proof. apply: subdE_inj. Qed.
Lemma codom_snipr : codom snipr =1 setC diskE.
Proof.
move=> z; apply/set0Pn/idP => [[[y Hy] Dy]|Hz]; first by rewrite (eqP Dy).
exists (subdI Hz : snip_rem); apply: set11.
Qed.

Definition snipr_ring : seq snip_rem := preimage_seq snipr (rev r).

Lemma maps_snipr_ring : maps snipr snipr_ring = rev r.
Proof.
apply: maps_preimage => [x Hx]; rewrite mem_rev in Hx.
by rewrite codom_snipr /diskE /setC /setD Hx.
Qed.

Lemma ucycle_snipr_ring : ufcycle node snipr_ring.
Proof.
have Ubgr: uniq snipr_ring.
  by rewrite -(uniq_maps inj_snipr) maps_snipr_ring uniq_rev Ur.
rewrite /ucycle Ubgr andbT.
apply: (cycle_from_next Ubgr) => [x Hx]; apply/eqP; apply: inj_snipr.
rewrite -(mem_maps inj_snipr) maps_snipr_ring mem_rev in Hx.
rewrite /= /snipr_node -/(snipr x) Hx -(next_maps inj_snipr Ubgr).
by rewrite maps_snipr_ring (next_rev Ur).
Qed.

Lemma snip_patch : patch snipd snipr snipd_ring snipr_ring.
Proof.
split.
- exact inj_snipd.
- exact inj_snipr.
- exact scycle_snipd_ring.
- exact ucycle_snipr_ring.
- rewrite maps_snipd_ring; exact maps_snipr_ring.
- move=> x; rewrite /setU /setC maps_snipd_ring codom_snipd codom_snipr.
  by rewrite /setC /diskE /setD negb_andb negb_elim orbC.
- move=> [x Hx]; rewrite /setC -(mem_maps inj_snipd) maps_snipd_ring /=.
  by move/negPf=> Hxb; rewrite /snipd_edge Hxb.
- by case.
- by case.
move=> [x Hx]; rewrite /setC -(mem_maps inj_snipr) maps_snipr_ring mem_rev /=.
by move/negPf=> Hxb; rewrite /snipr_node Hxb.
Qed.

Lemma planar_snipd : planar snip_disk.
Proof. by move: Hpg; rewrite (planar_patch snip_patch); case/andP. Qed.

Lemma planar_snipr : planar snip_rem.
Proof. by move: Hpg; rewrite (planar_patch snip_patch); case/andP. Qed.

End Snip.

Section SnipRot.

(* Disks only depend on the extent of their ring; hence, they are invariant *)
(* under rotation.                                                          *)

Variables (n0 : nat) (g : hypermap) (r : seq g).

Lemma diskN_rot : diskN (rot n0 r) =1 diskN r.
Proof.
move=> x; apply: (etrans (has_rot _ _ _) (eq_has _ _)) => y.
by apply: {x y}eq_connect => x y; rewrite /dlink mem_rot.
Qed.

Lemma diskE_rot : diskE (rot n0 r) =1 diskE r.
Proof. by move=> x; rewrite /diskE /setD mem_rot diskN_rot. Qed.

Lemma diskF_rot : diskF (rot n0 r) =1 diskF r.
Proof. by move=> x; rewrite /diskF /setD fband_rot diskN_rot. Qed.

Lemma diskFC_rot : diskFC (rot n0 r) =1 diskFC r.
Proof. by move=> x; rewrite /diskFC /setD /setC fband_rot diskN_rot. Qed.

End SnipRot.

Unset Implicit Arguments.
