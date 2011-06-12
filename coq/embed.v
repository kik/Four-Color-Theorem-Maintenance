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
Require Import color.
Require Import chromogram.
Require Import coloring.
Require Import patch.
Require Import snip.
Require Import revsnip.
Require Import kempe.
Require Import birkhoff.
Require Import contract.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* This is the heart of the proof: we build an injective embedding of a *)
(* configuration map from the partial embedding constructed by the part *)
(* quiz, and derive a contradiction from the reducibility property.     *)

Section Embeddings.

Variables (gm gc : hypermap) (rc cc : seq gc) (h : gc -> gm).

Let rrc := rev rc.
Notation ac := (kernel rc).
Notation bc := (setC rc).
Let Hacbc := subsetP (kernel_off_ring rc).
Let HacF := kernelF rc.

Hypothesis Hgm : minimal_counter_example gm.
Hypothesis Hgc : embeddable rc.
Hypothesis Hh : preembedding ac h.
Hypothesis Hcc : c_reducible rc cc.

Let Hpgm : planar gm := Hgm.
Let Hbgm := bridgeless_cface Hgm.
Let HgmE : plain gm := Hgm.
Let De2m := plain_eq Hgm.
Let Dn3m := cubic_eq Hgm.
Let HgmF : pentagonal gm := Hgm.
Let Hgm' : planar_bridgeless_plain_connected gm := Hgm.

Let Hpgc : planar gc := Hgc.
Let Hbgc := bridgeless_cface Hgc.
Let HgcE : plain gc := Hgc.
Let HgcN : quasicubic rc := Hgc.
Let De2c := plain_eq Hgc.
Let Dn3c := quasicubic_eq HgcN.
Let Hgc' : planar_bridgeless_plain_connected gc := Hgc.
Let HUrc : sfcycle node rc := Hgc.
Let Hrc := scycle_cycle HUrc.
Let Urc := scycle_uniq HUrc.
Let UrcF := scycle_simple HUrc.

Notation hc := (edge_central h).
Let HhcE := edge_central_edge h Hgc Hgm.
Let HhF := preembedding_face Hh.
Notation Hhac := ((preembedding_simple_path Hh HacF) _ _).

Lemma embed_functor : forall x, ac x -> ac (edge x) -> h (edge x) = edge (h x).
Proof.
suffice: ~ exists2 x, setD ac hc x &
    exists2 p, scycle rlink (Adds x p) & sub_set p (setI ac hc).
- move=> H x Hx Hex; apply: eqP; apply/idPn => [Hhex]; case: H.
  exists x; first by rewrite /setD /hc Hhex.
  case: {Hx Hex Hhex}(Hhac Hex Hx) => [p]; case; case/lastP: p => // [p y].
  rewrite last_add_last; move=> Hp Hyx _ [Up Hpac]; exists p.
    apply/andP; split.
      by move: Hp; rewrite /= -!cats1 !path_cat /= (rlinkFr Hyx).
    by rewrite simple_adds -(closed_connect (fbandF p) Hyx) -simple_add_last.
  by move=> z Hz; apply: (allP Hpac); rewrite mem_add_last; apply: setU1r.
suffice: ~ exists2 x, negb (hc x) &
       exists2 p, scycle rlink (Adds x p) &
                  sub_set p hc /\ sub_set (diskN (Adds x p)) ac.
- move=> H [x Hx [p HUp Hpac]]; case: H; case/andP: Hx => [HxE Hx].
  have Hxpac: sub_set (Adds x p) ac.
    by move=> y; case/setU1P=> [<-|Hy] //; case (andP (Hpac _ Hy)).
    case HpN: (negb (has (diskF (Adds x p)) rc)).
      exists x; first done; exists p; auto; split.
        by move=> y Hy; case (andP (Hpac _ Hy)).
      move=> y Hy; case HyF: (fband (Adds x p) y).
      rewrite /fband in HyF; case/hasP: HyF => [z Hz Hyz].
      by rewrite (closed_connect HacF Hyz); auto.
    apply/hasP => [[z Hz Hyz]]; case/hasP: HpN; exists z; first done.
    by rewrite -(closed_connect (diskF_face (Adds x p)) Hyz) /diskF /setD HyF.
  have Erp1: rev_ring (rot 1 (Adds x p)) = Adds (edge x) (rev_ring p).
    by rewrite {1}/rev_ring maps_rot /= rot1_adds rev_add_last.
  have HUp1: scycle rlink (rot 1 (Adds x p)) by rewrite scycle_rot.
  exists (edge x); [ by rewrite HhcE | exists (rev_ring p) ].
    by rewrite -Erp1; apply scycle_rev_ring.
  split=> y Hy.
    rewrite mem_rev_ring // in Hy.
    by case: (andP (Hpac _ Hy)); rewrite HhcE.
  rewrite -Erp1 (diskN_rev_ring Hgc' HUp1) in Hy.
  apply/hasP => [] [z Hz Hyz]; case HzF: (diskF (Adds x p) z).
  + rewrite -(closed_connect (diskF_face (Adds x p)) Hyz) in HzF.
    case/andP: HzF => [_ HyN]; rewrite /diskN in HyN.
    case/hasP: HyN => [y' Hy' Hyy'].
    case/hasP: Hy; exists y'; first by rewrite mem_rot.
    apply: etrans Hyy'; apply: {y' Hy'}eq_connect => y1 y2.
    by rewrite /dlink mem_rot.
  + case/andP: HzF {y Hy Hyz}; split.
      apply/hasP => [] [y Hy Hyz].
      by case/hasP: (Hxpac _ Hy); exists z; rewrite 1?Sface.
    case/hasP: HpN => [z' Hz' Hz'N]; rewrite -(fconnect_cycle Hrc Hz) in Hz'.
    by rewrite (closed_connect (diskN_node (Adds x p)) Hz'); case/andP: Hz'N.
  rewrite proper_ring_rot //.
  case: (p) HUp Hpac => [|x' [|x'' p']] //.
    by rewrite /scycle /= /rlink Sface Hbgc.
  move=> _ H; apply/eqP => Dx'; move: {H}(H _ (setU11 _ _)).
  by rewrite /setI -Dx' HhcE (negbE HxE) andbF.
move=> [x HxE [p HUp [HpE Hpac]]]; pose n := S (card (diskN (Adds x p))).
move: (leqnn n) HUp HpE Hpac; rewrite {1}/n.
elim: {x p}n (x) HxE (p) => [|n Hrec] // x HxE p Hn HUp HpE.
set xp := Adds x p => Hpac.
have HxN: diskN xp x by rewrite diskN_E /setU /xp /= setU11.
have HnxN: diskN xp (node x) by rewrite -(fclosed1 (diskN_node xp)).
have HnnxN: diskN xp (node (node x)) by rewrite -(fclosed1 (diskN_node xp)).
 case: (andP HUp) => [Hp]; move/simple_uniq=> Up.
case Dp': p (Hp) => [|x' p']; first by rewrite /= /rlink Sface Hbgc.
clear; pose enx := edge (node x); pose p1 := add_last p enx.
have Hp1: path rlink x p1.
  rewrite /p1 -cats1 path_cat /= {2}/rlink cface1r /enx Enode.
  by rewrite /= -cats1 path_cat in Hp.
have Up1: simple p1.
  have Henxx: cface enx x by rewrite cface1 /enx Enode connect0.
  rewrite /p1 simple_add_last (closed_connect (fbandF p) Henxx) -simple_adds.
  by case (andP HUp).
case HnxE: (hc (node x)).
  move: (cubicP HgcN _ (Hacbc (Hpac _ HxN))) => [Dn3x Hnxx].
  case HnnxE: (hc (node (node x))).
    case/eqP: HxE; apply Iface; apply: etrans (Dn3m _).
    do 2 (apply Iedge; apply Iface); rewrite !Enode Eedge -{1}Dn3x -HhF.
      rewrite Enode -(eqP HnnxE) -HhF.
        rewrite Enode -(eqP HnxE) -HhF ?Enode //.
        rewrite /kernel /setC (fclosed1 (fbandF rc)) Enode; exact (Hpac _ HxN).
      rewrite /kernel /setC (fclosed1 (fbandF rc)) Enode; exact (Hpac _ HnxN).
    rewrite /kernel /setC (fclosed1 (fbandF rc)) Enode; exact (Hpac _ HnnxN).
  pose ennx := edge (node (node x)).
  pose i := find (cface ennx) p1; pose q := Adds ennx (take i p1).
  have Hi: i <= size p1 by apply: find_size.
  have HUq: scycle rlink q.
    have Hp1': path rlink ennx p1.
      move: Hp1; rewrite -(drop0 p1) (drop_sub x) ?sub0 /=.
        by rewrite /= {1 3}/rlink -{1}Dn3x cface1 /ennx Enode De2c.
      by rewrite /p1 size_add_last.
    apply/andP; rewrite leq_eqVlt orbC in Hi; move: Hi Hp1' {Hp1}Up1.
    case Hi: (i < size p1).
      rewrite -(cat_take_drop (S i) p1) (take_sub x Hi); move=> _ Hp1 Up1.
      rewrite /i -has_find in Hi; move/(sub_find x): Hi => Hi.
      rewrite -cats1 !path_cat /= {2}/rlink Sface -(same_cface Hi) in Hp1.
      rewrite simple_cat simple_add_last in Up1; case/andP: Up1 => [Up1 _].
      split; last by rewrite /q simple_adds (closed_connect (fbandF _) Hi).
      by rewrite /= -cats1 path_cat /= {2}/rlink Sface; case/andP: Hp1.
    move=> Di Hp1 Up1; rewrite /q (eqnP Di) take_size (cycle_path x) /=.
    rewrite Hp1 {1}/p1 last_add_last /rlink /enx {1}/ennx cface1r Enode De2c.
    split; first by rewrite connect0.
    apply/andP; split; [ apply/mapsP => [] [y Hy Hyennx] | done ].
    rewrite /i -has_find in Hi; case/hasP: Hi.
    by exists y; last by apply/(rootP (Sface _)).
  have Hp1E: sub_set (take i p1) hc.
    move=> y Hy'; have Hy: p1 y by rewrite -(cat_take_drop i p1) mem_cat /setU Hy'.
    rewrite /p1 mem_add_last in Hy; case/setU1P: Hy; last by auto.
    by move <-; rewrite /enx HhcE.
  have Hqx: diskN q x = false.
  rewrite 2!(fclosed1 (diskN_node q)) -[node (node x)]De2c.
    apply: (diskN_edge_ring Hgc' HUq _ (setU11 _ _)).
    rewrite /q; case Dp1: (take i p1) => [|x1 [|x2 p1']] //.
      by rewrite /scycle /q Dp1 /= /rlink Sface Hbgc in HUq.
    rewrite /ennx /= De2c; apply/eqP => [Dx1]; case/idP: HnnxE.
    by rewrite Dx1; apply Hp1E; rewrite Dp1 /= setU11.
  have HqN: sub_set (diskN q) (diskN xp).
    move=> y Hy; rewrite /diskN in Hy; case/hasP: Hy => [z Hz].
    case/connectP=> [r Hr <-] {y}; move: Hr; set y := finv node z.
    have Hy: diskN xp y && diskN q y.
      rewrite !(fclosed1 (diskN_node _) y) /y (f_finv (Inode gc)).
      rewrite !diskN_E /setU Hz /= andbT /q /= /setU1 (orbC (x =d z)).
      apply/orP; case Hpz: (p z); [ by left | right ].
      move: Hz; rewrite /q /= /setU1; case: (ennx =P z) => [<-|_].
        clear; rewrite /ennx -(fclosed1 (diskE_edge Hpgc HUp)).
        rewrite /diskE /setD -/xp HnnxN andbT; apply/orP.
        move=> [Dnnx|Hpnnx]; last by rewrite (HpE _ Hpnnx) in HnnxE.
          move: (Hbgc (node x)).
        by rewrite {1}(eqP Dnnx) Dn3x cface1r Enode connect0.
      pose p2 := take i p; rewrite /= /p1 -cats1 take_cat -/p2.
      rewrite /i /p1 -cats1 find_cat.
      case HpF: (has (cface ennx) p).
        rewrite -has_find HpF /p2 /=; move=> Hp2z.
        by rewrite -(cat_take_drop i p) mem_cat /setU Hp2z in Hpz.
      rewrite ltnNge leq_addr subn_addr /= cface1 /ennx Enode /enx.
      rewrite Hbgc /= mem_cat /setU Hpz /= /setU1 orbF.
      move=> Dz; rewrite -(eqP Dz) -(fclosed1 (diskE_edge Hpgc HUp)).
      rewrite /diskE /setD -/xp HnxN andbT /= /setU1 eqd_sym Hnxx /=.
      apply/idP => [Hnx]; case/hasP: HpF.
      by exists (node x); last by rewrite /ennx cface1 Enode connect0.
    elim: {z Hz Hrec}r y Hy => [|z r Hrec] y Hy; [ by case (andP Hy) | simpl ].
      rewrite {1}/dlink; case Hqy: (q y); first done.
    case/andP=> Dz; apply: {r}Hrec; rewrite !(fclosed1 (diskN_node _) z).
    case/clinkP: Dz => <- {z}//; rewrite -(De2c y) Eedge.
    move/andP: Hy => [Hxpy HqyN].
    rewrite !diskN_E /setU -(fclosed1 (diskE_edge Hpgc HUp)).
    rewrite -(fclosed1 (diskE_edge Hpgc HUq)) /diskE /setD Hqy -/xp Hxpy HqyN.
    rewrite /= orbT !andbT orbC /setU1; apply/orP; left.
    case: (x =P y) => [Dx|_]; first by rewrite Dx HqyN in Hqx.
    rewrite /q /= in Hqy; case/norP: Hqy => _.
    rewrite /p1 -cats1 take_cat {Hi}.
    case Hi: (i < size p); last by rewrite mem_cat /setU; case (p y).
    move=> Hy; rewrite -(cat_take_drop i p) mem_cat /setU {Hy}(negbE Hy) /=.
    rewrite (drop_sub x Hi); apply/idP => [Hy]; case/idP: Hqx.
    move: (mem_rot 1 xp) Hp Up; rewrite {1}/xp -(uniq_rot 1) rot1_adds.
    rewrite {1}[xp]lock /= -lock -(cat_take_drop (S i) p) -cats1 -catA.
    case/splitPl: Hy => [r' r Er']; rewrite -catA cats1 uniq_cat catA.
    rewrite -{6}(last_add_last y r x); move: {r}(add_last r x) => r.
    rewrite has_cat path_cat last_cat.
    move=> Erp; move/andP=> [_ Hr]; move/and3P=> [_ Ur _].
    have HrF: negb (has (fband (locked q)) r).
      apply/hasP => [] [z Hrz Hqz]; case/orP: Ur; right.
      apply/hasP; exists z; first done.
      have Hpz: fband (take (S i) p) z.
        rewrite (take_sub x Hi) -cats1 /fband has_cat /= orbF orbC Sface.
        have Hi1: i < size p1 by rewrite /p1 size_add_last leqW.
        rewrite /i -has_find in Hi1.
        rewrite /fband -lock /= Sface (same_cface (sub_find x Hi1)) in Hqz.
        by rewrite -/i /p1 sub_add_last -cats1 take_cat Hi in Hqz |- *.
      case/hasP: Hpz => [z' Hz' Hzz']; rewrite (scycle_cface HUp Hzz') //.
        by rewrite -/xp -Erp mem_cat /setU Hrz orbT.
      by rewrite /= /setU1 -(cat_take_drop (S i) p) mem_cat /setU Hz' /= orbT.
    rewrite (take_sub x Hi) last_add_last {r' Erp Ur}Er' in Hr.
    elim: r {Hxpy Hqy}y HqyN Hr HrF => [|z r Hrec] y Hy //=.
    move/andP=> [Hyz Hr]; move/norP=> [HzF HrF].
    have Hz: diskF q z; last by case/andP: Hz; auto.
    rewrite /rlink cface1 in Hyz; rewrite -lock in HzF.
    rewrite -(closed_connect (diskF_face q) Hyz) /diskF /setD.
    rewrite (closed_connect (fbandF q) Hyz) HzF.
    by rewrite (fclosed1 (diskN_node q)) Eedge.
  rewrite -HhcE in HnnxE.
  case: {Hrec}(Hrec _ (negbI HnnxE) (take i p1)); rewrite -/q; auto.
    rewrite ltnS in Hn; apply: leq_trans Hn.
    rewrite {1}[card]lock (cardD1 x) -lock.
    rewrite {1}[diskN]lock diskN_E /setU -lock /= setU11 /= add1n ltnS.
    apply: subset_leq_card; apply/subsetP => [y Hy].
    rewrite /setD1 -/xp (HqN _ Hy) andbT; apply/eqP => [Dx].
    by case/idP: Hqx; rewrite Dx.
  by move=> y Hy; apply Hpac; apply HqN.
have HenxN: diskN xp enx.
  rewrite diskN_E; apply/orP; right.
  rewrite /enx -(fclosed1 (diskE_edge Hpgc HUp)) /diskE /setD -/xp HnxN /= /setU1.
  case Hpnx: (p (node x)); first by case/idP: HnxE; auto.
  rewrite orbF andbT; apply/eqP => Dnx.
  by move: (Hbgc (node x)); rewrite cface1r Enode -Dnx connect0.
rewrite -[node x]De2c -/enx in HnxN.
case: (Hhac (Hpac _ HnxN) (Hpac _ HxN)) => [q1 [Hq1 Eq1 Eq10] [Uq1 Hq1ac]].
pose i := find (fband p1) q1; pose q2 := take i q1.
have Upq2: negb (has (fband q2) p1).
  apply/hasP => [[y Hy]]; case/hasP=> [z Hz Hyz].
  case (elimF (hasPx (cface z) p1)); last by exists y; rewrite 1?Sface.
  have Hq1z: q1 z by rewrite -(cat_take_drop i q1) -/q2 mem_cat /setU Hz.
  rewrite -/(fband p1 z) -(sub_index x Hq1z); apply before_find.
  rewrite -(size_takel (find_size (fband p1) q1)) -/i -/q2.
  by rewrite -(cat_take_drop i q1) -/q2 index_cat Hz index_mem.
have Hih: has (fband p1) q1.
  apply/hasP; exists (last enx q1).
    by case: (q1) Eq10 => // [nx' q1'] _; apply: mem_last.
  apply/hasP; exists enx; first by rewrite /p1 mem_add_last /= setU11.
  by rewrite cface1r /enx Enode.
have Hi: i < size q1 by rewrite /i -has_find.
pose y' := sub x q1 i; have Hy': fband p1 y' by apply: sub_find.
rewrite /fband in Hy'; case/hasP: Hy' => [y Hy Hyy'].
move: (simple_uniq Up1) Upq2 (last_add_last y p enx) {Up}; rewrite -/p1.
case/splitPr Dp: p1 / Hy {Up} => [p2 p3] Up.
rewrite last_cat /= has_cat; move/norP=> [Up2q Up3q] Ep3.
pose q3 := cat q2 (belast y p3); pose q := Adds enx q3.
have HUq: scycle rlink q.
  apply/andP; split.
    rewrite /= /q3 -cats1 -catA cats1 path_cat -{3}Ep3 -lastI /=.
    rewrite -(cat_take_drop i q1) -/q2 (drop_sub x Hi) -/y' path_cat in Hq1.
    rewrite /= andbA {2}/rlink Sface (same_cface Hyy') Sface in Hq1.
    case/andP: Hq1 => [H _]; rewrite {2}/rlink andbA {}H /=.
    by rewrite Dp path_cat in Hp1; case/and3P: Hp1.
  rewrite -(simple_rot 1) /q rot1_adds -cats1 /q3 -catA.
  rewrite -Ep3 cats1 -lastI simple_cat; apply/and3P; split; auto.
    by rewrite -(cat_take_drop i q1) simple_cat in Uq1; case/andP: Uq1.
  by rewrite Dp simple_cat in Up1; case/and3P: Up1.
have Hp3p: sub_set (belast y p3) p.
  move=> z Hz; rewrite -{1}[p]/(behead (Adds x p)).
  rewrite -(belast_add_last x p enx) -/p1 Dp belast_cat /= -cat_add_last.
  by rewrite -lastI /= mem_cat /setU Hz orbT.
have Hq3E: sub_set q3 hc.
  move=> z; rewrite /q3 mem_cat; case/orP=> Hz; auto.
  by case: (andP (allP Hq1ac z (mem_take Hz))).
have Hqx: diskN q x = false.
  rewrite (fclosed1 (diskN_node q)) -[node x]De2c.
  apply: (diskN_edge_ring Hgc' HUq _ (setU11 _ _)).
  case/andP: HUq (Hq3E (node x)); rewrite /q.
  case: (q3) => [|y1 [|y2 q4]] //; first by rewrite /= /rlink Sface Hbgc.
  do 2 clear; rewrite /= /setU1 orbF /enx De2c eqd_sym.
  move=> *; apply/idP => Dy1; case/idP: HnxE; auto.
have HqN: sub_set (diskN q) (diskN xp).
  move{Hrec} => z0; rewrite {1}/diskN; case/hasP=> [z2 Hz2].
  case/connectP=> [r Hr <-] {z0}; move: Hr; set z1 := finv node z2.
  have Hz1: diskN xp z1 && diskN q z1.
    rewrite !(fclosed1 (diskN_node _) z1) /z1 (f_finv (Inode gc)).
    rewrite andbC diskN_E /setU Hz2; rewrite /q /q3 -cat_adds mem_cat in Hz2.
    case/orP: Hz2 => Hz2;
      last by rewrite diskN_E {1}/xp /setU /= /setU1 (Hp3p _ Hz2) orbT.
    have Uq2p: negb (has (fband xp) q2).
      apply/hasP => [[t Ht]]; rewrite /fband; move/hasP=> [t' Ht' Htt'].
      case: (elimN (hasPx (fband q2) p1)).
        by rewrite Dp has_cat; apply/norP; split.
      rewrite /xp /= in Ht'; case/setU1P: Ht' => [Dt'|Ht'].
        exists enx; first by rewrite /p1 mem_add_last /= setU11.
        apply/hasP; exists t; first done.
        by rewrite cface1 /enx Enode Dt' Sface.
      exists t'; first by rewrite /p1 mem_add_last /= setU1r.
      by apply/hasP; exists t; last by rewrite Sface.
    case/andP: HUq Uq2p; rewrite /= -cats1 /q3 -catA.
    case/splitPl: Hz2 => [q' q'' <-]; rewrite -catA path_cat has_cat.
    move/andP=> [Hq' _] _; move/norP=> [Uq'p _] {q''}.
    elim: q' (enx) Hq' HenxN Uq'p => [|t2 q' Hrec] t1 //=.
    move/andP=> [Dt2 Hq'] Ht1; move/norP=> [Ut2p Uq'p].
    have Ht2: diskF xp t2; last by case/andP: Ht2; auto.
    rewrite /rlink cface1 in Dt2.
    rewrite -(closed_connect (diskF_face xp) Dt2) /diskF /setD.
    rewrite (closed_connect (fbandF xp) Dt2).
    by rewrite (fclosed1 (diskN_node xp)) Eedge Ht1 andbT.
  elim: r {z2 Hz2 Hrec}z1 Hz1 => [|z2 r Hrec] z1 Hz1; first by case/andP: Hz1.
  rewrite /= {1}/dlink; case Hqz1: (q z1); first done.
  case/andP=> Dz1; apply: {r Hrec}Hrec; rewrite !(fclosed1 (diskN_node _) z2).
  case/clinkP: Dz1 => <- //; rewrite -{z2}(De2c z1) Eedge.
  case/andP: Hz1 => [Hxpz1 Hqz1N].
  rewrite !diskN_E /setU -(fclosed1 (diskE_edge Hpgc HUp)).
  rewrite -(fclosed1 (diskE_edge Hpgc HUq)) /diskE /setD Hqz1 -/xp Hxpz1 Hqz1N.
  rewrite /xp -(belast_add_last x p enx) -/p1 Dp belast_cat /= orbT !andbT.
  apply/orP; right; rewrite -cat_add_last -lastI mem_cat /setU; apply/norP.
  split; last by rewrite /q /q3 -cat_adds mem_cat in Hqz1; case/norP: Hqz1.
  have Uqp2: negb (has (fband q) p2).
    apply/hasP => [] [t Ht]; rewrite /fband; move/hasP=> [t' Ht' Htt'].
    rewrite -(mem_rot 1) /q rot1_adds in Ht'.
    rewrite -cats1 /q3 -catA cats1 -Ep3 -lastI mem_cat in Ht'.
    case/orP: Ht' => Ht'.
      by case/hasP: Up2q; exists t; last by apply/hasP; exists t'.
    rewrite Dp simple_cat in Up1; case/and3P: Up1; clear; case/hasP.
    by exists t'; last by apply/hasP; exists t; rewrite 1?Sface.
  apply/idP => Hz1; case/idP: Hqx {Hqz1}.
  have Hp2 := Hp1; rewrite Dp path_cat in Hp2; move/andP: Hp2 => [Hp2 _].
  case/splitPl: Hz1 Hp2 Uqp2 Hqz1N => [p2' p2'' <-] {z1 Hxpz1}.
  rewrite path_cat has_cat; move/andP=> [Hp2' _]; move/norP=> [Up2' _] {p2''}.
  elim/last_ind: p2' Hp2' Up2' => [|r z Hrec] //.
  rewrite last_add_last -cats1 has_cat path_cat {2}/rlink /= orbF cface1.
  move/and3P=> [Hr Dz _]; move/norP=> [Ur Uz] Hz.
  have HzF: diskF q z by apply/andP; split.
  rewrite -(closed_connect (diskF_face q) Dz) in HzF; case/andP: HzF => _.
  by rewrite (fclosed1 (diskN_node q)) Eedge; auto.
rewrite -HhcE in HnxE.
case: {Hrec}(Hrec _ (negbI HnxE) q3); rewrite -/enx -/q; auto.
  rewrite ltnS in Hn; apply: leq_trans Hn.
  rewrite {1}[card]lock (cardD1 x) -lock.
  rewrite {1}[diskN]lock diskN_E /setU -lock /= setU11 /= add1n ltnS.
  apply subset_leq_card; apply/subsetP => [z Hz].
  rewrite /setD1 -/xp (HqN _ Hz) andbT.
  by apply/eqP => [Dx]; rewrite Dx Hz in Hqx.
by move=> z Hz; apply Hpac; apply HqN.
Qed.

Remark Embed_cface_ac_h : forall x y, ac x -> cface x y -> cface (h x) (h y).
Proof.
move=> x y Hx; case/connectP=> [p Hp <-] {y}.
elim: p x Hx Hp => [|y p Hrec] x Hx; first by rewrite /= connect0.
rewrite cface1 -(HhF Hx) /=; move/andP=> [Dy Hp].
move: Hx Hp; rewrite (fclosed1 HacF) (eqP Dy); exact (Hrec y).
Qed.
Notation cface_ac_h := Embed_cface_ac_h.

Remark Embed_cface_h_ac : forall x u, ac x -> cface (h x) u ->
  exists2 y, cface x y & h y = u.
Proof.
move=> x u Hx; case/connectP=> [p Hp <-] {u}.
elim: p x Hx Hp => [|u p Hrec] x Hx; first by exists x; first by apply connect0.
simpl; case/andP; rewrite {1}/eqdf -(HhF Hx); move/eqP=> <- {u} Hp.
rewrite (fclosed1 HacF) in Hx; case: (Hrec _ Hx Hp) => [y Hxy <-].
by exists y; first by rewrite cface1.
Qed.
Notation cface_h_ac := Embed_cface_h_ac.

Let HhFn := preembedding_arity Hh.

Remark cface_inj_embed : forall x y, ac x -> cface x y -> h x = h y -> x = y.
Proof.
move=> x y Hx Hxy Ehxy.
have Ehn: forall n, h (iter n face x) = iter n face (h x).
  elim=> [|n Hrec] //=; rewrite HhF ?Hrec // /kernel /setC.
  by rewrite -(closed_connect (fbandF rc) (fconnect_iter face n x)).
have Efxy: findex face (h x) (h y) = findex face x y.
  by rewrite -{1}(iter_findex Hxy) Ehn findex_iter // HhFn // findex_max.
by rewrite -(iter_findex Hxy) -Efxy Ehxy findex0.
Qed.

Definition pre_hom_ring x p :=
  and3 (path rlink x p) (sub_set (Adds x p) ac) (scycle rlink (maps h (Adds x p))).

Lemma intro_pre_hom_ring : forall x p, path rlink x p ->
   rlink (h (last x p)) (h x) ->
   sub_set (Adds x p) ac ->
   simple (maps h (Adds x p)) -> 
 pre_hom_ring x p.
Proof.
move=> x p Hp Ehp Hpac Uhp; split; auto.
rewrite /scycle {}Uhp andbT (cycle_path (h x)) last_maps /= {}Ehp /=.
move/(introT subsetP): Hpac; rewrite /subset {1}/setC disjoint_has.
elim: p x Hp => [|y p Hrec] x //; rewrite /= negb_orb negb_elim.
move/andP=> [Hxy Hp]; move/andP=> [Hx Hpac]; move/norP: (Hpac) => [Hex _].
rewrite negb_elim -(closed_connect HacF Hxy) in Hex.
rewrite {1}/rlink -(embed_functor Hx Hex) (cface_ac_h Hex Hxy) /=; auto.
Qed.

Lemma trivial_hom_ring : forall x p, pre_hom_ring x p ->
  fcard face (diskF (maps h (Adds x p))) <= 0 -> rlink (last x p) x.
Proof.
move=> x p Hxp; case: (pickP (diskF (maps h (Adds x p)))) => [y Hy|HpF].
  rewrite /n_comp (cardD1 (froot face y)) /setI.
  rewrite -(closed_connect (diskF_face _) (connect_root _ y)).
  by rewrite (roots_root (Sface gm)) Hy.
clear; elim: {p}(S (size p)) x {-2}p (ltnSn (size p)) HpF Hxp => // [n Hrec].
move=> x p Hn HpF []; set xp := Adds x p => Hp Hpac HUhp.
rewrite ltnS in Hn; set y := last x p; have Hxpy: xp y by apply: mem_last.
have Hhxpy: maps h xp (h y) by apply maps_f.
have Hy: ac y by apply Hpac.
have Hnhy: fband (maps h xp) (node (h y)).
apply negbEf; move: (HpF (node (h y))).
  rewrite /diskF /setD -(fclosed1 (diskN_node (maps h xp))) diskN_E /setU.
  by rewrite Hhxpy /= andbT.
rewrite /fband in Hnhy; case/hasP: (Hnhy) => u; case/mapsP=> z Hz <- {u}.
rewrite Sface => Hhzny.
case/splitPl Dp: p / (Hz) => [p1 p2 Ep1].
case/lastP: p2 Dp => [|p2 y'] Dp.
  rewrite cats0 in Dp; rewrite -Dp -/y in Ep1.
  by rewrite Ep1 -{1}[h z]Enode -cface1 Sface Hbgm in Hhzny.
have Dy': y' = y by rewrite /y Dp last_cat last_add_last.
case/lastP: p1 Ep1 Dp => [|p1 z'] Ep1 Dp.
  simpl in Ep1; case/andP: HUhp; rewrite (cycle_path (h x)) /=.
  rewrite last_maps -/y Ep1 (rlinkFr Hhzny) -{1}[node (h y)]Enode.
  by rewrite /rlink -cface1r cface1 -{1}[h y]Dn3m Enode Hbgm.
rewrite last_add_last in Ep1; rewrite {z'}Ep1 {y'}Dy' in Dp.
pose eny := edge (node y).
have Heny: ac eny by rewrite (fclosed1 HacF) /eny Enode.
have Dheny: h eny = edge (node (h y)).
  by rewrite -{1}[y]Enode -/eny (HhF Heny) Eface.
have Henyz: rlink eny z.
  case Hhpny: (maps h xp (node (h y))).
    case/mapsP: Hhpny => [t Ht Dht].
    case/splitPl Dp': p / (Ht) => [p1' p2' Ep1'].
    have Dp2': p2' = seq1 y.
      case: p2' Dp' => [|t1 [|t2 p2']] Dp'.
      - rewrite cats0 in Dp'; rewrite -Dp' -/y in Ep1'.
        move: (Hbgm (node (h y))); rewrite cface1r Enode.
        by rewrite -Dht Ep1' connect0.
      - by rewrite /y Dp' last_cat /=.
      case/andP: HUhp; rewrite /xp Dp' (cycle_path (h x)) -cat_adds.
      rewrite !maps_cat path_cat simple_cat.
      move/and3P=> [_ Htt1 _]; move/and3P=> [_ _ Ut1].
      rewrite maps_adds simple_adds in Ut1; move/andP: Ut1 => [Ut1 _].
      rewrite /fband in Ut1; case/hasP: Ut1; exists (h y).
        by apply maps_f; rewrite /y Dp' last_cat /= mem_lastU.
      by rewrite /= last_maps Ep1' /rlink Dht cface1 Enode Sface in Htt1 |- *.
    have Dt: t = node y.
      rewrite Dp' path_cat Ep1' Dp2' in Hp; case/and3P: Hp => [_ Hty _].
      have Het := Hy; rewrite -(closed_connect HacF Hty) in Het.
      rewrite /rlink -{1}[y]Enode -cface1r -/eny in Hty.
      apply: (Iedge _ (cface_inj_embed Het Hty _)).
      by rewrite (embed_functor (Hpac _ Ht) Het) Dht Dheny.
    case: p2 Dp (congr1 (fun q => last x (belast x q)) Dp) => [|z1 p2] Dp.
      rewrite Dp' Dp2' !belast_cat !last_cat /= last_add_last Ep1'.
      by move <-; rewrite /rlink /eny De2c Dt connect0.
    rewrite Dp' Dp2' -cats1 !belast_cat !last_cat /= belast_add_last Ep1' /=.
    move=> Ep2; rewrite lastI -Ep2 cat_add_last in Dp; case/andP: HUhp => _.
    rewrite /xp Dp -cat_adds maps_cat !maps_adds simple_cat !simple_adds /fband.
    case/and4P => _ _; case/hasP; exists (h t); last by rewrite Dht.
    by apply maps_f; do 2 rewrite mem_add_last /= /setU1; rewrite set11 orbT.
  pose q := add_last p2 eny.
  have HhenyF: cface (h eny) (h y) by rewrite cface1 Dheny Enode connect0.
  have Hzq: (pre_hom_ring z q).
    apply intro_pre_hom_ring.
    - rewrite Dp path_cat last_add_last in Hp; case/andP: Hp; clear.
      by rewrite /q -!cats1 !path_cat /= {4}/rlink cface1r /eny Enode.
    - rewrite /rlink /q last_add_last Sface (same_cface Hhzny).
      by rewrite -(fun u => Eedge gm (edge u)) De2m Dheny Enode connect0.
    - move=> t Ht; rewrite /q -cats1 -cat_adds cats1 mem_add_last in Ht.
      rewrite mem_adds in Ht; case/setU1P: Ht => [<-|Ht] //.
      apply Hpac; rewrite /xp /= setU1r // Dp cat_add_last mem_cat /setU.
      by rewrite -cats1 -cat_adds mem_cat /setU Ht /= orbT.
    rewrite {}/q -add_last_adds maps_add_last simple_add_last.
    rewrite (fun q => closed_connect (fbandF q) HhenyF) -simple_add_last.
    case/andP: HUhp => _; rewrite /xp Dp cat_add_last -cat_adds -add_last_adds.
    by rewrite maps_cat -maps_add_last simple_cat; case/and3P.
  rewrite -(last_add_last z p2 eny) -/q; apply Hrec; auto.
    apply: leq_trans Hn; rewrite /q Dp size_cat !size_add_last.
    by rewrite addSnnS leq_addl.
  have Hxpeny: fband (maps h xp) (h eny) by apply/hasP; exists (h y).
  have Eqr: chord_ring (maps h xp) (h eny) = maps h (rotr 1 (Adds z q)).
    rewrite /q -add_last_adds rotr1_add_last maps_adds; congr Adds.
    have <-: h y = fproj (maps h xp) (h eny).
    case: (fprojP Hxpeny) => [Hpr Hypr]; rewrite (same_cface HhenyF) in Hypr.
      by apply (scycle_cface HUhp).
    rewrite Dheny De2m.
    have <-: h z = fproj (maps h xp) (node (h y)).
    case: (fprojP Hnhy) => [Hpr Hzpr]; rewrite -(same_cface Hhzny) in Hzpr.
      by apply (scycle_cface HUhp); try by apply maps_f.
    case/andP: HUhp; clear; move/simple_uniq.
    rewrite -(rot_rotr 1 xp) maps_rot uniq_rot => Up.
    rewrite arc_rot //; last by apply maps_f; rewrite mem_rotr.
    move: Up; rewrite /xp Dp -cat_adds -add_last_cat rotr1_add_last.
    rewrite -add_last_adds cat_add_last maps_adds maps_cat !maps_adds.
    exact: right_arc.
  move=> u; rewrite -[Adds z q](rot_rotr 1) maps_rot diskF_rot -Eqr.
  rewrite diskF_chord_ring // /setD ?HpF ?andbF //; last by rewrite Dheny De2m.
    by rewrite /xp Dp; case: (p1) => [|x1 [|x2 p1']]; case p2.
  rewrite Dheny -(fclosed1 (diskE_edge Hpgm HUhp)) /diskE /setD Hhpny.
  by rewrite -(fclosed1 (diskN_node (maps h xp))) diskN_E /setU Hhxpy.
have Hny: ac (node y).
  by rewrite -[node y]De2c -/eny (closed_connect HacF Henyz) Hpac.
have Dhny: h (node y) = node (h y).
  by apply Iedge; rewrite -Dheny -embed_functor.
pose enny := edge (node (node y)).
have Henny: ac enny by rewrite (fclosed1 HacF) /enny Enode.
have Dhenny: h enny = edge (node (node (h y))).
  by rewrite -Dhny -[node y]Enode -/enny (HhF Henny) Eface.
have Hhyx: rlink (h y) (h x).
case: (andP HUhp); rewrite /xp (cycle_path (h x)) /= last_maps -/y.
  by case/andP.
have Hennyx: rlink enny x.
  case Hhpnny: (maps h xp (node (node (h y)))).
    case/mapsP: Hhpnny => [t Ht Dht].
    case/splitPl Dp': p / Ht => [p1' p2' Ep1'].
    have Dp1': p1' = seq0.
      case: p1' Dp' Ep1' => [|t1 p1'] Dp' Ep1' //.
      simpl in Ep1'; case/andP: HUhp => _.
      rewrite /rlink -[h y]Dn3m cface1 Enode -Dht in Hhyx.
      rewrite /xp maps_adds simple_adds {1}Dp' lastI Ep1' cat_add_last.
      by rewrite maps_cat fband_cat /= Sface Hhyx !orbT.
    rewrite -Ep1' Dp1' {t Ht p1' p2' Ep1' Dp' Dp1'}/= in Dht.
    have Dp1: p1 = seq0.
      case: p1 Dp => [|x1 p1] Dp //.
      case/andP: HUhp; rewrite /xp Dp /=; move/andP=> [Hxx1 _].
      rewrite /rlink Dht cface1 Enode -(same_cface Hhzny) Sface in Hxx1.
      rewrite cat_add_last !simple_adds maps_cat /= !fband_cat /= Hxx1 orbT.
      by rewrite andbF.
    rewrite {p1}Dp1 /= in Dp.
    have Dx: x = node (node y).
      rewrite Dp /= in Hp; move/andP: Hp => [Hxz _].
      have Hex: ac (edge x).
         by rewrite (closed_connect HacF Hxz); apply Hpac.
      rewrite /rlink /eny De2c -[node y]Enode -/enny -cface1 in Henyz.
      rewrite Sface -(same_cface Hxz) in Henyz.
      apply: (Iedge _ (cface_inj_embed Hex Henyz _)).
      by rewrite (embed_functor (Hpac _ (setU11 _ _)) Hex) Dht Dhenny.
    by rewrite /rlink /enny -Dx De2c connect0.
  pose q := add_last p1 enny.
  have HhennyF: cface (h enny) (h z) by rewrite cface1 Dhenny Enode Sface.
  have Hxq: pre_hom_ring x q.
    apply intro_pre_hom_ring.
    - rewrite Dp path_cat in Hp; case/andP: Hp => [H _]; move: H.
      rewrite /q -!cats1 !path_cat /= {2 4}/rlink Sface -(same_cface Henyz).
      by rewrite /eny De2c -[node y]Enode -cface1 Sface.
    - rewrite /rlink /q last_add_last Dhenny De2m.
      by rewrite -[h y]Eedge Dn3m -cface1.
    - move=> t Ht; rewrite /q -cats1 -cat_adds cats1 mem_add_last in Ht.
      rewrite mem_adds in Ht; case/setU1P: Ht => [<-|Ht] //.
      by apply Hpac; rewrite /xp Dp cat_add_last -cat_adds mem_cat /setU Ht.
    rewrite {}/q -add_last_adds maps_add_last simple_add_last.
    rewrite (closed_connect (fbandF _) HhennyF) -simple_add_last.
    case/andP: HUhp => _; rewrite -maps_add_last /xp Dp -cat_adds maps_cat.
    by rewrite simple_cat; case/and3P.
  rewrite -(last_add_last x p1 enny) -/q; apply Hrec; auto.
    apply: leq_trans Hn; rewrite /q Dp size_cat !size_add_last.
    by rewrite -addSnnS leq_addr.
  have Hphz: maps h xp (h z) by apply maps_f.
  have Hxpenny: fband (maps h xp) (h enny) by apply/hasP; exists (h z).
  rewrite /rlink -[h y]Dn3m cface1 Enode in Hhyx.
  have Hnny: fband (maps h xp) (node (node (h y))).
    by apply/hasP; exists (h x); first exact: setU11.
  have Eqr: chord_ring (maps h xp) (h enny) = maps h (rotr 1 (Adds x q)).
    rewrite /q -add_last_adds rotr1_add_last maps_adds; congr Adds.
    have <-: h z = fproj (maps h xp) (h enny).
    case: (fprojP Hxpenny) => [Hpr Hypr].
      by rewrite (same_cface HhennyF) in Hypr; apply (scycle_cface HUhp).
    have <-: h x = fproj (maps h xp) (edge (h enny)).
    case: (fprojP Hnny) => [Hpr Hzpr]; rewrite (same_cface Hhyx) in Hzpr.
      by rewrite Dhenny De2m; apply (scycle_cface HUhp); rewrite //= setU11.
    case/andP: HUhp; clear; move/simple_uniq.
    rewrite /xp Dp cat_add_last maps_adds maps_cat !maps_adds.
    exact: left_arc.
  move=> u; rewrite -[Adds x q](rot_rotr 1) maps_rot diskF_rot -Eqr.
  rewrite diskF_chord_ring // /setD ?HpF ?andbF //; last by rewrite Dhenny De2m.
    by rewrite /xp Dp; case: (p1) => [|x1 [|x2 p1']]; case p2.
  rewrite Dhenny -(fclosed1 (diskE_edge Hpgm HUhp)) /diskE /setD Hhpnny.
  by rewrite -!(fclosed1 (diskN_node (maps h xp))) diskN_E /setU Hhxpy.  
rewrite /rlink -[edge enny]Enode -cface1 /enny De2c Dn3c // in Hennyx.
exact (Hacbc Hy).
Qed.

Remark Embed_HrcN : fclosed node rc.
Proof.
apply: (intro_closed (Snode _)) => [x nx Dnx Hx].
by rewrite -(fconnect_cycle Hrc Hx) connect1.
Qed.
Notation HrcN := Embed_HrcN.

Lemma edge_perimeter : forall x, bc x || bc (edge x).
Proof.
move=> x; rewrite /setC -negb_andb; apply/andP => [] [Hx Hex].
have Dfx: face x = x.
  apply (scycle_cface HUrc); auto; first by rewrite Sface fconnect1.
  by rewrite (fclosed1 HrcN) -{1}[x]De2c Eedge.
have HxF1: fcycle face (seq1 x) by rewrite /= /eqdf Dfx set11.
move: (allP (embeddable_ring Hgc) _ Hx) => HxF3; rewrite /good_ring_arity in HxF3.
by rewrite (order_cycle HxF1) // in HxF3; rewrite /= setU11.
Qed.

Notation erc := (maps edge rc).

Remark Embed_Drrrc : rev_ring rrc = erc.
Proof. by rewrite /rev_ring /rrc maps_rev rev_rev. Qed.
Notation Drrrc := Embed_Drrrc.

Remark Embed_HUrrc : scycle rlink rrc.
Proof.
rewrite /rrc /scycle simple_rev UrcF andbT.
case: rc Hrc => [|x p] //=; rewrite (cycle_path x) rev_adds.
rewrite last_add_last; elim: p {1 4}x => [|z p Hrec] y; rewrite /= ?andbT.
  by move/eqP=> <-; rewrite /rlink cface1 Enode connect0.
move/andP=> [Dz Hp]; rewrite -cats1 rev_adds path_cat last_add_last /=.
by rewrite (Hrec _ Hp) -(eqP Dz) /rlink cface1 Enode connect0.
Qed.
Let HUrrc := Embed_HUrrc.

Remark Embed_HUerc : scycle rlink erc.
Proof. rewrite -Drrrc; exact (scycle_rev_ring Hgc' HUrrc). Qed.
Let HUerc := Embed_HUerc.

Lemma chordless_perimeter : forall x, bc x -> bc (edge x) -> ac x || ac (edge x).
Proof.
have EercF: fband erc =1 fband rc.
  move=> x; rewrite -Drrrc (fband_rev_ring Hgc' HUrrc).
  by apply: eq_has_r => [y]; rewrite /rrc mem_rev.
case: (andP HUerc) => Herc; move/simple_uniq=> Uerc x Hix Hiex.
rewrite /kernel /setC -negb_andb; apply/andP => [] [Hx Hex].
have Perc: proper_ring erc.
  move: Hx Herc (edge_perimeter (head x rc)).
  case: (rc) => [|x1 [|x2 [|x3 p]]] //= _; first by rewrite /rlink Sface Hbgc.
  clear; rewrite /setC /= /setU1 set11 /= orbF (inj_eqd (Iedge gc)).
  by rewrite (eqd_sym x2); case/norP.
move: x Hix Hiex Hx Hex; have Prrc: (proper_ring rrc).
  by rewrite -(proper_rev_ring Hgc') Drrrc.
have HeiF0: forall x, fband erc x -> fband erc (edge x) -> diskE erc x ->
    exists y, diskF (chord_ring erc x) y.
- move=> x Hx Hex HxE; set rx := chord_ring _ x.
  have HUrx: scycle rlink rx by apply: scycle_chord_ring.
  have Prx: proper_ring rx by rewrite /rx proper_chord_ring.
  have Hirx: sub_set (behead rx) erc.
    move: (fprojP Hx) (fprojP Hex) => [Hx' Hxx'] [Hex' Hexex'].
    case: (rot_to_arc Uerc Hex' Hx').
      by apply/eqP => Dex'; rewrite Sface Dex' -(same_cface Hxx') Hbgc in Hexex'.
    move=> i p1 _ Dp1 ->; rewrite -cat_adds {p1}Dp1 => Derc y Hy.
    by rewrite -(mem_rot i) Derc mem_cat /setU; apply/orP; left.
  have HirxN: sub_set (diskN rx) bc.
    move=> y Hy; rewrite /rx diskN_chord_ring // in Hy.
    case/andP: Hy => _; rewrite -Drrrc diskN_rev_ring //.
    by rewrite {1}/setC diskN_E /setU /rrc mem_rev; case/norP.
  move: (leqnn (size rx)) HUrx Prx Hirx HirxN {Hx Hex HxE}.
  elim: {x rx}(size rx) {-2}rx => [|n Hrec] p; first by case p.
  move=> Hn HUp Pp Hip HipN; apply: set0Pn; apply/set0P => [HpF0].
  case/andP: (HUp) => Hp; move/simple_uniq=> Up.
  case Dp: p (Pp) => [|x p'] // _.
  have Hpx: p x by rewrite Dp /= setU11.
  have HpxN: diskN p x by rewrite diskN_E /setU Hpx.
  have Hix: bc x by apply HipN.
  have HpF := fbandF p; have HpN := diskN_node p.
  pose efex := edge (face (edge x)); have HpE := diskE_edge Hpgc HUp.
  have Eefex: face efex = node x by rewrite /efex -{1}(Dn3c Hix) !Enode.
  case HefexE: (diskE p efex).
    have Hefex: fband p efex.
    apply negbEf; rewrite (fclosed1 HpF) Eefex; move: (HpF0 (node x)).
      by rewrite /diskF /setD andbC -(fclosed1 HpN) HpxN.
    have Heefex: fband p (edge efex).
      apply/hasP; exists (next p x); first by rewrite mem_next.
      rewrite /efex De2c -cface1; exact (next_cycle Hp Hpx).
    pose y := fproj p efex; have Hp'y: p' y.
      case: (fprojP Hefex); rewrite -/y Dp /=; case/setU1P=> // [<-].
      by rewrite -{1}[x]Enode -cface1r cface1 Eefex Hbgc.
    case/splitPr Dp': p' / Hp'y => [p1 p2].
    have Dp1: Adds efex p1 = chord_ring p efex.
      congr Adds; rewrite -/y /efex De2c /arc.
      set z := fproj p (face (edge x)).
      have <-: 1 = index z p.
        case: (fprojP Heefex); rewrite /efex De2c -/z; move=> Hpz Hzex.
        rewrite -cface1 Sface in Hzex; rewrite Dp /=.
        case: (z =P x) => [Dz|_]; first by rewrite Dz Hbgc in Hzex.
        move: Hp; rewrite Dp; case: (p') Dp => [|z' p''] //= Dp.
        case/andP=> [Hzz' _].
        case: (z =P z') => [_|[]] //; apply: (scycle_cface HUp _ Hpz).
          by rewrite (same_cface Hzex).
        by rewrite Dp /= setU1r ?setU11.
      rewrite Dp rot1_adds -cats1 Dp' -catA index_cat.
      rewrite Dp /= Dp' uniq_cat andbA /= in Up.
      case/and3P: Up; clear; case/norP=> [Hp1y _] _.
      by rewrite (negbE Hp1y) /= set11 addn0 take_cat ltnn subnn take0 cats0.
    case: {Hrec}(Hrec (Adds efex p1)).
    + rewrite -ltnS /=; apply: leq_trans Hn.
      by rewrite Dp Dp' /= size_cat /= addnS !ltnS leq_addr.
    + by rewrite Dp1; apply scycle_chord_ring.
    + by rewrite Dp1; apply proper_chord_ring.
    + by move=> /= z Hz; apply Hip; rewrite Dp Dp' /= mem_cat /setU Hz.
    + move=> z; rewrite Dp1 diskN_chord_ring //.
      by move=> H; apply HipN; case/andP: H.
    by move=> z; rewrite Dp1 diskF_chord_ring // /setD HpF0 andbF.
  rewrite /efex -(fclosed1 HpE) /diskE /setD (fclosed1 HpN) Eedge in HefexE.
  rewrite HpxN andbT in HefexE; move/idP: HefexE => Hpfex.
  case: p' Dp => [|fex p'] Dp; first by rewrite Dp in Pp.
  have Hpfex': p fex by rewrite Dp /= setU1r ?setU11.
  have Dfex: fex = face (edge x).
    apply: (scycle_cface HUp _ Hpfex' Hpfex).
    by rewrite Dp /scycle /= /rlink cface1 Sface -andbA in HUp; case/andP: HUp.
  pose enx := edge (node x); have Henx: fband p enx.
    rewrite (fclosed1 HpF) /enx Enode; exact (subsetP (ring_fband _) _ Hpx).
  have Heenx: fband p (edge enx).
    apply/hasP; exists (next p fex); first by rewrite mem_next.
    rewrite /enx De2c -Eefex /efex -cface1 Dfex; exact (next_cycle Hp Hpfex).
  have HenxE: diskE p enx.
    rewrite /enx -(fclosed1 HpE) /diskE /setD -(fclosed1 HpN) HpxN andbT.
    rewrite Dp /=; apply/setU1P => [] [Dnx|Hnx].
      by move: (Hbgc (node x)); rewrite cface1r Enode -Dnx connect0.
    rewrite Dp in Hip; move: {Hnx Hip}(Hip _ Hnx) (Hip _ (setU11 _ _)).
    rewrite -[node x]Eface -[fex]De2c Dfex -/efex !(mem_maps (Iedge gc)).
    rewrite -(fclosed1 HrcN) => Hfnx Hefex; pose q := seq2 efex (node x).
    have Hq: fcycle face q.
      rewrite /q /= /eqdf andbT Eefex set11 /=.
      apply: (introT eqP (scycle_cface HUrc _ Hfnx Hefex)).
      by rewrite -Eefex -!cface1 connect0.
    move: (allP (embeddable_ring Hgc) _ Hefex) (card_size q).
    rewrite /good_ring_arity /order (eq_card (fconnect_cycle Hq (setU11 _ _))).
    by case/or4P; move/eqP=> <-.
  have Dp': Adds enx p' = chord_ring p enx.
    congr Adds; have <-: x = fproj p enx.
    case: (fprojP Henx) => [Hpy Hxy]; apply: (scycle_cface HUp _ Hpx Hpy).
      by rewrite -{1}[x]Enode -cface1.
    case: p' Dp => [|z p'] Dp; rewrite Dp in Hp; case/and3P: Hp => [_ Hz _];
      rewrite /rlink Dfex -/efex cface1 Eefex in Hz.
      by rewrite (adj_no_cface Hgc (adjN x)) in Hz.
    have <-: z = fproj p (edge enx).
    move: (fprojP Heenx) => [Hpz' Hzz'].
    rewrite {1}[edge enx](De2c (node x)) (same_cface Hz) in Hzz'.
      by apply: (scycle_cface HUp); rewrite // Dp /= /setU1 set11 !orbT.
    by symmetry; move: Up; rewrite Dp -(cat1s fex); apply: right_arc.
  case: {Hrec}(Hrec (Adds enx p')).
  - by rewrite -ltnS /=; apply: leq_trans Hn; rewrite Dp /= leqnn.
  - by rewrite Dp'; apply scycle_chord_ring.
  - by rewrite Dp'; apply proper_chord_ring.
  - by move=> /= z Hz; apply Hip; rewrite Dp /= /setU1 Hz orbT.
  - by move=> z; rewrite Dp' diskN_chord_ring //; case/andP=> *; apply HipN.
  by move=> z; rewrite Dp' diskF_chord_ring // /setD HpF0 andbF.
have HeiFac: forall x, fband erc x -> fband erc (edge x) -> diskE erc x ->
    diskF (chord_ring erc x) =1 ac.
- move=> x Hx Hex HxE; set rx := chord_ring _ _.
  have Hrxac: sub_set (diskF rx) ac.
    by move=> y; rewrite /rx diskF_chord_ring // /kernel /setC -EercF; case/and3P.
  have HUrx: scycle rlink rx by apply: scycle_chord_ring.
  have HrxF: forall y, ac y -> diskN rx y -> diskF rx y.
    move=> y Hy HyN; rewrite /diskF /setD HyN andbT.
    rewrite /kernel /setC -EercF -(fband_chord_ring Hgc' HUerc Hx Hex) in Hy.
    by case/norP: Hy.
  move=> z; apply/idP/idP; [ exact: Hrxac | move=> Hz ].
  case: (HeiF0 _ Hx Hex HxE) => [y HyF].
  have Heey := Hrxac _ HyF; rewrite -{1}[y]De2c in Heey.
  case: (Hhac Heey Hz) => [p [Hp Ep Ep0] [_ Hphac]].
  have Hpac: subset p ac.
    by rewrite all_setI -subset_all in Hphac; case/andP: Hphac.
  rewrite /kernel subset_all /= in Hpac.
  case: p Ep0 Ep Hp Hpac {Hphac} => //= [y1 p] _ Ep; move/andP=> [Hyy1 Hp].
  have Hy1: diskF rx y1.
    by rewrite -(closed_connect (diskF_face rx) Hyy1) De2c; auto.
  rewrite -(closed_connect (diskF_face rx) Ep); case/andP {Ep Hyy1} => _.
  elim: p y1 Hy1 Hp => [|y2 p Hrec] y1 Hy1 //=.
  move/andP=> [Hy12 Hp]; move/andP=> [Hy2ac Hpac].
  apply: {p Hrec Hp Hpac}(Hrec _ _ Hp Hpac).
  rewrite /rlink cface1 in Hy12; rewrite -(closed_connect (diskF_face rx) Hy12).
  apply HrxF; first by rewrite /kernel /setC (closed_connect (fbandF rc) Hy12).
  by rewrite (fclosed1 (diskN_node rx)) Eedge; case (andP Hy1).
move=> x Hix Hiex; rewrite -!EercF => Hx Hex.
have HexE: diskE erc (edge x).
  rewrite /diskE /setD (mem_maps (Iedge gc)) (negbE Hix) -Drrrc.
  rewrite (diskN_rev_ring Hgc' HUrrc Prrc).
  apply/hasP => [[y Hy]]; case/connectP.
  rewrite /rrc mem_rev -{1}(f_finv (Inode gc) y) -(fclosed1 HrcN) in Hy.
  move=> [|z p]; first by move=> _ Dx; rewrite /setC -Dx /= Hy in Hiex.
  by rewrite /= {1}/dlink /rrc mem_rev Hy.
case: (HeiF0 _ Hex); rewrite ?De2c //; move=> y Hy; move: (Hy).
rewrite HeiFac in Hy; rewrite ?De2c // diskF_chord_ring ?De2c //.
rewrite -(fclosed1 (diskE_edge Hpgc HUerc)) in HexE.
by rewrite /setD HeiFac ?Hy.
Qed.

Lemma fcard_adj_perimeter : forall x, negb (ac x) ->
  card (setI (cface x) (fun y => fband rc (edge y))) = 2.
Proof.
move=> x; move/negbE2; case/hasP=> [y Hiy Hxy].
rewrite (cardD1 y) (cardD1 (edge (node y))) /setD1 /setI Hxy.
rewrite cface1r Enode Hxy.
have Hiny: rc (node y) by rewrite -(fclosed1 HrcN).
case: (y =P edge (node y)) => [Dy|_].
  by move: (edge_perimeter (node y)); rewrite /setC De2c -Dy Hiy Hiny.
have Hfey: fband rc (edge y).
  apply/hasP; exists (face (edge y)); last by apply fconnect1.
  by rewrite (fclosed1 HrcN) Eedge.
rewrite De2c /setC (subsetP (ring_fband _) _ Hiny) Hfey /=; apply: eqP.
apply/set0P => [z]; apply/and4P => [[Hzeny Hzy Hyz Hz]].
rewrite (same_cface Hxy) in Hyz.
case Hiz: (rc z); first by case/eqP: Hzy; apply: (scycle_cface HUrc).
case Hiez: (rc (edge z)).
  case/eqP: Hzeny; apply: (scycle_cface HUerc).
  - by rewrite cface1 Enode.
  - by apply maps_f.
  by rewrite -{1}[z]De2c; apply maps_f.
case/orP: (chordless_perimeter (negbI Hiz) (negbI Hiez)).
  by case/hasP; exists y; rewrite 1?Sface.
by rewrite /kernel /setC Hz.
Qed.

Lemma adj_kernel_min : forall x, negb (ac x) -> exists2 y, ac y & cface x (edge y).
Proof.
move=> x; move/negbE2; case/hasP=> [y Hiy Hxy].
move: (allP (embeddable_ring Hgc) _ Hiy); rewrite /good_ring_arity /order.
rewrite -(cardIC (fun z => fband rc (edge z))) fcard_adj_perimeter.
  case: (pickP (setI (cface y) (setC (fun z => fband rc (edge z))))) => [z Hz|Hy].
    case/andP: Hz => [Hxez Hez] _; exists (edge z); first done.
    by rewrite De2c (same_cface Hxy).
  by rewrite (eq_card Hy) card0.
by apply/idP => Hy; case/idP: (Hacbc Hy).
Qed.

Lemma adj_kernel_max : forall x, negb (ac x) ->
  card (setI (cface x) (fun y => ac (edge y))) <= 4.
Proof.
move=> x; move/negbE2; case/hasP=> [y Hiy Hxy].
move: (allP (embeddable_ring Hgc) _ Hiy).
rewrite /good_ring_arity -(arity_cface Hxy).
rewrite /order -(cardIC (fun z => fband rc (edge z))) fcard_adj_perimeter.
  rewrite /kernel /setC.
  move: (card (setI (cface x) (fun z => negb (fband rc (edge z))))).
  repeat case=> //.
by rewrite (closed_connect HacF Hxy); apply/idP => Hy; case/idP: (Hacbc Hy).
Qed.

Lemma embed_full : forall x1 x2, ac x1 -> ac x2 ->
  edge (h x1) = h x2 -> edge x1 = x2.
Proof.
suffice Hgc5: ~exists x1, exists2 p,
        and3 (path rlink x1 p) (negb (last x1 p =d x1)) (sub_set p ac)
      & edge (h (last x1 p)) = h (edge x1) /\ size p <= 5.
- move=> x1 x2 Hx1 Hx2 Dhx; apply: eqP; apply/idPn => [Hex12]; case: Hgc5.
  case: (radius2P _ (embeddable_kernel Hgc)) => [x0 Hx0 Hx0ac].
  case: (at_radius2P HacF _ _ (Hx0ac _ Hx1)) => [x01 [x10 [Hx001 Hx110]]].
  case: (at_radius2P HacF _ _ (Hx0ac _ Hx2)) => [x02 [x20 [Hx002 Hx220]]].
  move=> [Hx02F Hex02] [Hx01F Hex01].
  exists (edge x1); exists (Seq x10 (edge x01) x02 (edge x20) x2).
    rewrite eqd_sym; split; auto.
      rewrite /path /rlink !De2c Hx110 Sface Hex01 Hex02 -(same_cface Hx001).
      by rewrite Hx002 Sface Hx220.
    apply: subsetP; rewrite subset_all /= Hx01F Hx2.
    rewrite -(closed_connect HacF Hx110) Hx1.
    rewrite -(closed_connect HacF Hx002) Hx0.
    by rewrite -(closed_connect HacF Hex02) Hx02F.
  by split; rewrite //= De2c -Dhx De2m.
suffice Hgc5: ~exists x, exists2 p,
    pre_hom_ring x p /\ negb (rlink (last x p) x) & size p <= 4.
- move=> [x0 [p [Hp Ep Hpac] [Hhp Hp5]]].
  suffice: exists2 q, and3 (path rlink x0 q) (last x0 q = last x0 p) (sub_set q ac)
                & simple (maps h q) /\ size q <= size p.
  + case=> [[|x q] [Hq Eq Hqac] [Uq Hqp]]; first by rewrite -Eq /= set11 in Ep.
    case: Hgc5; exists x; exists q; last by exact (leq_trans Hqp Hp5).
    have Hx: ac x by exact (Hqac _ (setU11 _ _)).
    rewrite /= in Hq Eq; case/andP: Hq => [Hx0x Hq]; split.
      apply intro_pre_hom_ring; rewrite // Eq /rlink Hhp Sface.
      by rewrite /rlink Sface in Hx0x; apply cface_ac_h.
    apply/idP => Eqx; case/eqP: Ep; apply Iedge.
    have Hx0p: ac (edge (last x0 p)).
      by rewrite -Eq (closed_connect HacF Eqx).
    apply cface_inj_embed; auto.
      by rewrite -Eq (same_cface Eqx) Sface.
    rewrite embed_functor // -Eq; exact (Hqac _ (mem_last _ _)).
  elim: p x0 Hp Hpac Hp5 {Ep Hhp} => [|x1 p Hrec] x0.
    by do 2 clear; exists (Seq0 gc); split.
  simpl; move/andP=> [Dx1 Hp1] Hpac Hp5.
  case: {Hrec Hp1}(Hrec _ Hp1 (fun z Hz => Hpac _ (setU1r _ Hz)) (ltnW Hp5)).
  move=> q [Hq Eq Hqac] [Uq Hqp].
  case Hhqx1: (negb (fband (maps h q) (h x1))).
    exists (Adds x1 q); split; auto; try by rewrite /= Dx1.
      move=> y; case/setU1P=> [Dy|Hy]; last by auto.
      by apply Hpac; rewrite Dy setU11.
    by rewrite maps_adds simple_adds Hhqx1.
  case/hasP: Hhqx1 => [u]; rewrite Sface; case/mapsP=> [x2 Hqx2 <-] {u} Hhx12.
  have Hx2: ac x2 by apply Hqac.
  case: (cface_h_ac Hx2 Hhx12) => [x3 Hx23 Hhx13].
  have Hx3: ac x3 by rewrite -(closed_connect HacF Hx23).
  case/splitP: {q}Hqx2 Hq Eq Hqp Uq Hqac => [q1 q2].
  rewrite path_cat last_cat last_add_last cat_add_last size_cat /=.
  move/andP=> [Hq1 Hq2] Eq2 Hqp Uq Hqac.
  case Hx13: (x1 =d x3).
    exists (Adds x2 q2); split; auto.
    + by rewrite /= {1}/rlink (same_cface Dx1) (eqP Hx13) Sface Hx23.
    + by move=> z Hz; apply Hqac; rewrite mem_cat /setU Hz orbT.
    + by rewrite maps_cat simple_cat in Uq; case/and3P: Uq.
    apply: (leqW (leq_trans _ Hqp)); exact: leq_addl.
  have Hx1: ac x1 by exact (Hpac _ (setU11 _ _)).
  case: {q}Hgc5; case: q1 Hqp Uq Hqac Hq1 => [|x q].
    move=> _ _ _ Hx12; rewrite /= andbT in Hx12.
    rewrite -(closed_connect HacF Hx12) in Hx2.
    move/(cface_ac_h Hx2): Hx12.
    by rewrite Sface (embed_functor Hx1 Hx2) (same_cface Hhx12) Hbgm.
  move=> Hqp Uq Hqac Hq; exists x; exists (add_last q x3);
    last by rewrite size_add_last; apply: leq_trans (leq_trans Hqp Hp5);
            exact: leq_addr.
  have Hx: ac x by exact (Hqac _ (setU11 _ _)).
  rewrite /= -cats1 path_cat in Hq; case/andP: Hq => [Hx1x Hq].
  have Hex1: ac (edge x1) by rewrite (closed_connect HacF Hx1x).
  rewrite last_add_last; split.
    apply intro_pre_hom_ring; auto.
    + by rewrite -cats1 path_cat /= {2}/rlink Sface -(same_cface Hx23) Sface.
    + by rewrite last_add_last Hhx13 /rlink -embed_functor // cface_ac_h.
    + move=> y Hy; rewrite -cats1 -cat_adds cats1 mem_add_last /= in Hy.
      case/setU1P: Hy => [<-|Hy] //.
    + by apply Hqac; rewrite mem_cat /setU /= Hy.
    move: Uq; rewrite -cats1 -cat_adds cats1 -cat_add_last !maps_cat simple_cat.
    rewrite !maps_add_last !simple_add_last; move/and3P=> [Uq _ _].
    by rewrite -(closed_connect (fbandF _) (cface_ac_h Hx2 Hx23)).
  apply/idP => Hx3x; case/eqP: Hx13; apply Iedge.
  rewrite /rlink Sface -(same_cface Hx1x) in Hx3x.
  apply (cface_inj_embed Hex1 Hx3x).
  rewrite (embed_functor Hx1 Hex1) -Hhx13 (embed_functor Hx3) //.
  by rewrite -(closed_connect HacF Hx3x).
suffice Hgc5: ~exists x, exists2 p,
         pre_hom_ring x p /\ negb (rlink (last x p) x)
       & fcard face (diskF (maps h (Adds x p))) <= (size (Adds x p) =d 5).
- move=> [x [p Hp Hp5]]; set xp := Adds x p.
  have Hphp: proper_ring (maps h xp).
    rewrite {}/xp; case: p Hp {Hp5} => [|y [|y' p']] //.
      by move=> [[_ _ H] _]; move: H; rewrite /scycle /= /rlink Sface Hbgm.
    move=> [[Hxy Hac _] H]; apply/eqP => Hhxy; case/idP: H.
    move: {Hac}(Hac _ (setU11 _ _)) (Hac _ (setU1r _ (setU11 _ _))) => Hx Hy.
    rewrite /= andbT in Hxy; simpl.
    have Hex := Hy; rewrite -(closed_connect HacF Hxy) in Hex.
    rewrite -(embed_functor Hx Hex) in Hhxy.
    by rewrite -(cface_inj_embed Hex Hxy Hhxy) /rlink De2c connect0.
  case Hgc5; exists x; exists p; first done.
  rewrite /= -(size_maps h) leqNgt; apply/idP => HhpF.
  move: Hp => [[Hp Hpac HUhp] Ep].
  have Hhxy: cface (h x) (edge (h (last x p))).
  case: (andP HUhp); rewrite (cycle_path (h x)) /= last_maps.
    by rewrite Sface; case/andP.
  have Hx: ac x by exact (Hpac _ (setU11 _ _)).
  case/lastP Dp: p => [|p' y]; first by rewrite Dp /= Hbgm in Hhxy.
  have Dy: y = last x p by rewrite Dp last_add_last.
  have Hy: ac y by rewrite Dy; exact (Hpac _ (mem_last _ _)).
  case: (cface_h_ac Hx Hhxy) => [ry Hxry Dhry].
  pose rp := add_last (rev (maps edge (belast x p'))) ry.
  pose rx := edge (last x p'); pose rxp := Adds rx rp.
  have Ehrp: maps h rxp = rot 1 (rev_ring (maps h xp)).
    rewrite /xp lastI /rev_ring !maps_add_last rev_add_last rot1_adds -Dhry.
    rewrite Dp belast_add_last {}/rxp {}/rx {}/rp.
    rewrite -cats1 -cat_adds cats1 -rev_add_last -maps_add_last -lastI.
    rewrite maps_add_last; congr add_last.
    apply: (monic_move (rev_rev (d := _))); move: Hp (introT subsetP Hpac).
    rewrite {}Dp /subset {1}/setC disjoint_has /=.
    elim: p' (x) => [|x2 p1 Hrec] x1; rewrite /= negb_orb negb_elim ?andbT.
      move=> Hx1y; move/andP=> [Hx1 _].
      rewrite -(closed_connect HacF Hx1y) in Hy.
      by rewrite (embed_functor Hx1 Hy).
    move/andP=> [Hx12 Hp1]; move/andP=> [Hx1 Hp1ac]; move/norP: (Hp1ac) => [Hx2 _].
    rewrite -(closed_connect HacF Hx12) negb_elim in Hx2.
    by rewrite rev_adds maps_add_last rev_add_last embed_functor ?Hrec.
  case: Hgc5; exists rx; exists rp.
    split.
      split.
      + move: Hxry Hp; rewrite Sface /rx /rp {Dhry}Dp.
        elim: (p') (ry) (x) => [|x3 p1 Hrec] x1 x2 /= Hx12.
          by clear; rewrite /rlink De2c Sface Hx12.
        move/andP=> [Hx23 Hp1]; rewrite -cats1 rev_adds path_cat last_add_last.
        by rewrite Hrec //= andbT /rlink De2c Sface.
      + move=> z; rewrite /rx /rp -cats1 -cat_adds cats1 mem_add_last.
        rewrite -rev_add_last /= /setU1 mem_rev -maps_add_last -lastI.
        rewrite -{2}[z]De2c (mem_maps (Iedge gc)).
        case/orP=> [Dz|Hz]; first by rewrite -(eqP Dz) -(closed_connect HacF Hxry).
        move: Hp Hpac; rewrite {}Dp; case/splitPl: Hz => [p1' p2' Dez].
        rewrite -cats1 -catA cats1 -[add_last p2' y]drop0.
        rewrite (drop_sub x) ?size_add_last // sub0 path_cat /= Dez.
        rewrite /rlink De2c; move/and3P=> [_ Hez _] Hp'ac.
        rewrite (closed_connect HacF Hez); apply Hp'ac.
        by rewrite /setU1 mem_cat /setU /= setU11 !orbT.
      rewrite -/rxp Ehrp /scycle cycle_rot /simple maps_rot uniq_rot.
      exact (scycle_rev_ring Hgm' HUhp).
    rewrite Dp -cats1 path_cat in Hp; case/and3P: Hp => [_ Hp'y _].
    rewrite /rp /rx last_add_last /rlink Sface {Hp'y}(same_cface Hp'y).
    apply/idP => Hyry; case/idP: Ep; move: (monic_move De2m (esym Dhry)).
    rewrite (closed_connect HacF Hxry) in Hx.
    have Hery := Hy; rewrite (closed_connect HacF Hyry) in Hery.
    rewrite -Dy -(embed_functor Hx Hery); move=> Dhy.
    by rewrite (cface_inj_embed Hy Hyry Dhy) /rlink De2c Sface.
  have EhrpF: diskF (maps h rxp) =1 diskF (rev_ring (maps h xp)).
    by move=> z; rewrite Ehrp diskF_rot.
  rewrite -/rxp [rxp]lock /= -!lock.
  have <-: size (maps h xp) = size rxp.
    rewrite /rxp /xp /rp /= size_maps Dp !size_add_last size_rev size_maps.
    by rewrite size_belast.
  rewrite (eq_n_comp_r EhrpF) leqNgt.
  rewrite (eq_n_comp_r (diskF_rev_ring Hgm HUhp Hphp)).
  rewrite -(size_maps h) in Hp5; apply/idP => HrpF.
  by case (fun H => elimF andP (birkhoff Hgm H HUhp)); auto.
move=> [x [p [Hp Ep] Hp5]].
case Hp0: (fcard face (diskF (maps h (Adds x p))) <=  0).
  by case (negP Ep); apply trivial_hom_ring.
case: (size (Adds x p) =P 5) Hp5 => [Dp5|_]; last exact (elimF idP Hp0).
rewrite leqn0 in Hp0; case/set0Pn: Hp0 => [u Hu].
rewrite /n_comp (cardD1 u) Hu; case/andP: Hu; case: Hp Dp5.
move Dxp: (Adds x p) => xp; rewrite -(size_maps h) /= add1n ltnS.
set hxp := maps h xp => Hp Hpac HUhxp Dp5 Hu HuF HxpF.
have HxpFf := closed_connect (diskF_face hxp).
have DxpF: diskF hxp =1 cface u.
  move=> y; symmetry; apply/idP/idP => [Huy|HyF].
    by rewrite -(HxpFf _ _ Huy) HuF.
  apply/(rootP (Sface _)); apply: eqP; apply/idPn => [Huy].
  rewrite leqn0 /setI /setD1 in HxpF; move: (set0P HxpF (froot face y)).
  rewrite (eqP Hu) in Huy; rewrite Huy.
  by rewrite (roots_root (Sface gm)) -(HxpFf _ _ (connect_root _ y)) HyF.
clear HxpF Hu; pose ru := spoke_ring u; pose frf := froots (@face gm).
have ExpF: fband hxp =1 fband ru.
  have HpFr: subset (setI frf (fband ru)) (setI frf (fband hxp)).
  apply/subsetP => v'; case Hv': (frf v'); rewrite /setI {}Hv' //=.
    move/hasP=> [v Hv Hvv'].
    rewrite {v' Hvv'}(closed_connect (fbandF hxp) Hvv').
    rewrite /ru mem_spoke_ring in Hv.
    have HvF: diskF hxp v = false.
      by rewrite DxpF (same_cface Hv) -{2}[v]Enode -cface1r Hbgm.
    have HvN: diskN hxp v.
      rewrite (fclosed1 (diskN_node hxp)).
      by rewrite -DxpF in Hv; case/andP: Hv.
    by rewrite /diskF /setD HvN andbT in HvF; apply negbEf.
  have EpFr: fcard face (fband ru) = fcard face (fband hxp).
    apply: eqP; rewrite eqn_leq {1 2}/n_comp -/frf (subset_leq_card HpFr).
    rewrite (scycle_fcard_fband HUhxp) Dp5.
    rewrite (@scycle_fcard_fband gm rlink); last by apply: scycle_spoke_ring.
    by rewrite /ru size_spoke_ring HgmF.
  move=> v; move: (subset_cardP EpFr HpFr (froot face v)).
  rewrite /setI (roots_root (Sface gm)) /=.
  by rewrite -!(closed_connect (fbandF _) (connect_root _ v)).
have Hhpu: sub_set hxp ru.
  case: (andP HUhxp) => [Hhp _] v Hv.
  have Huv: adj u v.
    rewrite -fband_spoke_ring -/ru -ExpF; exact (subsetP (ring_fband _) _ Hv).
  have Huev: adj u (edge v).
    rewrite (adjFr (next_cycle Hhp Hv)) -fband_spoke_ring -/ru -ExpF.
    by apply: (subsetP (ring_fband _)); rewrite mem_next.
  case/orP: (adj11_edge Hgm Huv Huev); auto.
  rewrite /ru mem_spoke_ring -DxpF; case/andP; clear.
  rewrite -(fclosed1 (diskN_node hxp)) diskN_edge_ring //.
  by move: Dp5; rewrite /hxp -Dxp; case: (p) => [|y1 [|y2 p']].
have Hhp1: cycle (fun v => set1 (face (face (edge v)))) hxp.
case: (andP HUhxp) => [Hhp UUhp].
  apply cycle_from_next; first by apply simple_uniq.
  have HUu := scycle_spoke_ring Hgm u.
  move=> v Hv; have Huv := Hhpu _ Hv.
  apply/eqP; apply: (scycle_cface HUu).
  - rewrite -!cface1; exact (next_cycle Hhp Hv).
  - by move: (Huv); rewrite -mem_next /ru (next_spoke_ring Hgm Huv).
  by apply Hhpu; rewrite mem_next.
rewrite (cycle_path (h x)) /hxp -Dxp /= last_maps in Hhp1.
case/andP: Hhp1 => [Dhx Hhpr].
have Hxpnx: subset (maps node xp) (cface (node x)).
move: (introT subsetP Hpac); rewrite -Dxp /subset {1}/setC !disjoint_has.
  rewrite /= {1}/setC connect0 /=.
  elim: (p) (x) Hp Hhpr => [|x2 p1 Hrec] x1 //=.
  move/andP=> [Hx12 Hp1]; move/andP=> [Dhx2 Hp1r].
  rewrite /= negb_orb negb_elim; move/andP=> [Hx1 Hp1ac].
  have Hnx12: cface (node x1) (node x2).
  case: (norP Hp1ac) => [Hx2 _]; rewrite negb_elim in Hx2.
    have Hex1 := Hx2; rewrite -(closed_connect HacF Hx12) in Hex1.
    have Hfex1 := Hex1; rewrite (fclosed1 HacF) in Hfex1.
    rewrite -(embed_functor Hx1 Hex1) eqd_sym in Dhx2.
    rewrite -(HhF Hex1) -(HhF Hfex1) in Dhx2.
    rewrite /rlink 2!cface1 Sface in Hx12.
    rewrite -[node x2]De2c (cface_inj_embed Hx2 Hx12 (eqP Dhx2)) Eface.
    rewrite cface1r -{2}[x1]Dn3c ?Enode ?connect0 //; exact (Hacbc Hx1).
  rewrite {1}/setC Hnx12 /= -(eq_has (a1 := setC (cface (node x2)))); auto.
  by move=> z; rewrite /setC (same_cface Hnx12).
case Hnx: (ac (node x)).
  case/idP: Ep; set y := last x p; rewrite -Dxp in Hpac.
  have Hx: ac x by exact (Hpac _ (setU11 _ _)).
  have Henx: ac (edge (node x)) by rewrite (fclosed1 HacF) Enode.
  have Hy: ac y by exact (Hpac _ (mem_last _ _)).
  have Heny: ac (edge (node y)) by rewrite (fclosed1 HacF) Enode.
  have Hnxny: cface (node x) (node y).
    apply (subsetP Hxpnx); rewrite (mem_maps (Inode gc)) -Dxp; exact: mem_last.
  have Hny: ac (node y) by rewrite -(closed_connect HacF Hnxny).
  have Dhny: h (node y) = h (face (node x)).
    rewrite (HhF Hnx) -[h (node x)]Eedge -(embed_functor Hnx Henx).
    rewrite -(HhF Henx) Enode -(eqP Dhx) -/y.
    rewrite -[h y]Dn3m Enode -[node (node (h y))]De2m Eedge Enode.
    by rewrite -{2}[y]Enode (HhF Heny) (embed_functor Hny Heny) Eedge.
  rewrite cface1 Sface in Hnxny.
  have Hrcy: bc y by exact (Hacbc Hy).
  rewrite /rlink -(Dn3c Hrcy) 2!cface1 Enode -[node (node y)]De2c.
  by rewrite (cface_inj_embed Hny Hnxny Dhny) Eface Enode connect0.
have Hxpnxac:
    subset (maps node xp) (setI (cface (node x)) (fun y => ac (edge y))).
  apply/subsetP => [y Hy]; rewrite /setI (subsetP Hxpnx _ Hy).
  case/mapsP: Hy => [z Hz <-]; rewrite (fclosed1 HacF) Enode /=; auto.
  move: (leq_trans (subset_leq_card Hxpnxac) (adj_kernel_max (negbI Hnx))).
have Unxp: uniq (maps node xp).
  case: (andP HUhxp) => _; move/simple_uniq=> Uhxp.
  rewrite (uniq_maps (Inode gc)); exact (maps_uniq Uhxp).
by rewrite /hxp size_maps in Dp5; rewrite (card_uniqP Unxp) size_maps Dp5.
Qed.

Lemma pre_embed_inj : forall x y, ac x -> ac y -> h x = h y -> x = y.
Proof.
move=> x y Hx Hy Dhx; have Heex := Hx; rewrite -[x]De2c in Heex.
case: (Hhac Heex Hy) => [[|z [|z' p]] [Hp Ep _] [_ Hpac]] //.
  move/andP: Hp => [Hxz _]; rewrite /= -(same_cface Hxz) De2c in Ep.
  by apply cface_inj_embed.
move/and3P: Hp => [Hxz Hzz' _]; rewrite /rlink De2c in Hxz.
have Hz: ac z by rewrite -(closed_connect HacF Hxz).
have Hez: ac (edge z).
  by rewrite (closed_connect HacF Hzz'); case/and3P: Hpac => [_]; case/andP.
  move: (cface_ac_h Hx Hxz); rewrite Dhx; move=> Hhyz.
  case: (cface_h_ac Hy Hhyz) (embed_functor Hz Hez) => [t Hyt <-] Hezt.
have Ht: ac t by rewrite -(closed_connect HacF Hyt).
rewrite (Iedge _ (embed_full Ht Hez (esym Hezt))) in Hyt.
by rewrite Sface -(same_cface Hxz) in Hyt; apply cface_inj_embed.
Qed.

Definition embed x :=
  if ac x then h x else
  if ac (edge x) then edge (h (edge x)) else
  if ac (node x) then face (edge (h (node x))) else
  edge (node (node (h (node (edge x))))).

Notation h1 := embed.

Lemma embed_cases : forall x,
  (ac x \/ ac (edge x))  \/ ac (node x) \/ ac (node (edge x)).
Proof.
suffice Hkic: forall x, bc x ->
     (ac x \/ ac (edge x)) \/ ac (node x).
  move=> x; move: (orP (edge_perimeter x)).
  case=> H; move: (Hkic _ H); rewrite ?De2c; tauto.
move=> x Hix; case Hiex: (bc (edge x)).
  by case: (orP (chordless_perimeter Hix Hiex)); tauto.
case Hienx: (bc (edge (node x))).
  rewrite /setC (fclosed1 HrcN) in Hix.
  case: (orP (chordless_perimeter Hix Hienx)); first tauto.
  by rewrite (fclosed1 HacF) Enode; tauto.
rewrite -{1}[x]Eface De2c /setC -(fclosed1 HrcN) in Hiex.
have Dfx: face x = edge (node x).
  apply: (scycle_cface HUrc _ (negbEf Hiex) (negbEf Hienx)).
  by rewrite -cface1 cface1r Enode connect0.
have EfxF: cface (face x) =1 seq2 x (face x).
  apply fconnect_cycle; first by rewrite /= /eqdf Dfx Enode !set11.
  by rewrite /= setU1r ?setU11.
move: (allP (embeddable_ring Hgc) _ (negbEf Hiex)).
rewrite /good_ring_arity /order (eq_card EfxF).
by move=> H; move: H (card_size (seq2 x (face x))); case/or4P; move/eqP => <-.
Qed.

Lemma embedE : forall x, h1 (edge x) = edge (h1 x).
Proof.
suffice HbcE: forall x, bc x -> h1 (edge x) = edge (h1 x).
  move=> x; case: (orP (edge_perimeter x)) => [Hx|Hex]; auto.
  by rewrite -{2}[x]De2c (HbcE _ Hex) De2m.
move=> x Hix; rewrite /h1; rewrite De2c.
case Hx: (ac x); case Hex: (ac (edge x)); rewrite ?De2m //.
  by rewrite embed_functor.
case: (embed_cases x); move/(introT orP); first by rewrite Hx Hex.
case Hnex: (ac (node (edge x))).
  have Hiex := Hacbc Hnex; rewrite /setC -(fclosed1 HrcN) in Hiex.
  by move: (chordless_perimeter Hix Hiex); rewrite Hx Hex.
by rewrite orbF => ->; rewrite -{2}[h (node x)]Dn3m Enode.
Qed.

Lemma embedN : forall x, bc x -> h1 (node x) = node (h1 x).
Proof.
move=> x Hix; rewrite /h1.
rewrite (fclosed1 HacF (edge (node x))) Enode.
rewrite -[node (node x)]Enode (Dn3c Hix) -(fclosed1 HacF).
case Hx: (ac x).
  rewrite -{1}[x]Enode -(fclosed1 HacF) in Hx.
  apply Iedge; rewrite -{4}[x]Enode (HhF Hx) Eface.
  by case Hnx: (ac (node x)); [ rewrite embed_functor | rewrite De2m ].
case Hex: (ac (edge x)).
  case Hnx: (ac (node x)).
  rewrite -[h (edge x)]Eface De2m -(HhF Hex) -{2}(Dn3c Hix) Enode.
    rewrite (fclosed1 HacF) -(Dn3c Hix) Enode in Hex.
    rewrite -[node x]Enode -(fclosed1 HacF) in Hnx.
    rewrite -{1}[node x]Enode (HhF Hnx) (embed_functor Hex Hnx).
    by apply Inode; rewrite Dn3m Eedge.
  rewrite -[h (face (edge x))]Dn3m Enode (HhF Hex).
  by rewrite -{1}[h (edge x)]De2m Eedge.
case: (embed_cases x); move/(introT orP); first by rewrite Hx Hex.
case Hnex: (ac (node (edge x))).
  have Hiex := Hacbc Hnex; rewrite /setC -(fclosed1 HrcN) in Hiex.
  by move: (chordless_perimeter Hix Hiex); rewrite Hx Hex.
by rewrite orbF => ->; rewrite Eedge.
Qed.

Lemma embed_inj : forall x y, bc x -> bc y -> h1 x = h1 y -> x = y.
Proof.
have HbcN: forall x, bc x ->
    ac x = false -> ac (edge x) = false -> ac (node x).
  move=> x Hix Hx Hex.
  case: (embed_cases x); move/(introT orP); first by rewrite Hx Hex.
  case Hnex: (ac (node (edge x))); last by rewrite orbF.
  have Hiex := Hacbc Hnex; rewrite /setC -(fclosed1 HrcN) in Hiex.
  by move: (chordless_perimeter Hix Hiex); rewrite Hx Hex.
move=> x y Hix Hiy; rewrite /h1.
case Hx: (ac x).
  case Hy: (ac y); first by exact (pre_embed_inj Hx Hy).
  case Hey: (ac (edge y)).
    by move=> Dh; rewrite -{1}[y]De2c (embed_full Hey Hx (esym Dh)) Hx in Hy.
  move: (HbcN _ Hiy Hy Hey) => Hny; rewrite Hny.
  rewrite -{1}[x]Enode -(fclosed1 HacF) in Hx; rewrite -{1}[x]Enode (HhF Hx) => Dh.
  have Hx' := Hx; rewrite -(embed_full Hny Hx (Iface _ (esym Dh))) in Hx'.
  by rewrite (fclosed1 HacF) Enode Hy in Hx'.
case Hex: (ac (edge x)).
  case Hy: (ac y).
    by move=> Dh; have Hy' := Hy; rewrite -(embed_full Hex Hy Dh) De2c Hx in Hy'.
  case Hey: (ac (edge y)).
    move=> Dh; exact (Iedge _ (pre_embed_inj Hex Hey (Iedge _ Dh))).
  move: (HbcN _ Hiy Hy Hey) => Hny; rewrite Hny.
  rewrite -[node y]Enode -(fclosed1 HacF) in Hny.
  rewrite -[edge (h (edge x))]Eedge De2m -(HhF Hex).
  rewrite (fclosed1 HacF) in Hex.
  rewrite -[node y]Enode (HhF Hny) -[h (edge (node (node y)))]De2m.
  rewrite -[edge (h (edge (node (node y))))]Dn3m !Enode.
  move=> Dh; have Hex' := Hex.
  rewrite -(embed_full Hny Hex' (Inode _ (esym Dh))) in Hex.
  rewrite De2c -[node (node y)]Enode (Dn3c Hiy) in Hex.
  by rewrite -(fclosed1 HacF) Hey in Hex.
move: (HbcN _ Hix Hx Hex) => Hnx; rewrite Hnx.
case Hy: (ac y).
  rewrite -{1}[y]Enode -(fclosed1 HacF) in Hy; rewrite -{1}[y]Enode (HhF Hy) => Dh.
  have Hy' := Hy; rewrite -(embed_full Hnx Hy' (Iface _ Dh)) in Hy.
  by rewrite (fclosed1 HacF) Enode Hx in Hy.
case Hey: (ac (edge y)).
  rewrite -[node x]Enode -(fclosed1 HacF) in Hnx.
  rewrite -[edge (h (edge y))]Eedge De2m -(HhF Hey).
  rewrite (fclosed1 HacF) in Hey.
  rewrite -[node x]Enode (HhF Hnx) -[h (edge (node (node x)))]De2m.
  rewrite -[edge (h (edge (node (node x))))]Dn3m !Enode => Dh.
  have Hey' := Hey; rewrite -(embed_full Hnx Hey' (Inode _ Dh)) in Hey.
  rewrite De2c -[node (node x)]Enode (Dn3c Hix) in Hey.
  by rewrite -(fclosed1 HacF) Hex in Hey.
move: (HbcN _ Hiy Hy Hey) => Hny; rewrite Hny => Dh.
exact (Inode _ (pre_embed_inj Hnx Hny (Iedge _ (Iface _ Dh)))).
Qed.

Let ddart : finSet := subFin bc.

Definition embd_edge x :=
  if bc (edge x) then edge x else edge (node (edge x)).

Remark Embed_Hdedge : forall u : ddart, bc (embd_edge (subdE u)).
Proof.
move=> [x Hx]; rewrite /= /embd_edge; case Hiex: (bc (edge x)); auto.
move: (edge_perimeter (node (edge x))).
by rewrite /setC -(fclosed1 HrcN) (negbEf Hiex).
Qed.
Notation Hdedge := Embed_Hdedge.

Remark Embed_Hdnode : forall u : ddart, bc (node (subdE u)).
Proof. by move=> [x Hx]; rewrite /= /setC -(fclosed1 HrcN). Qed.
Notation Hdnode := Embed_Hdnode.

Definition embd_face x := if bc (face x) then face x else face (face x).

Remark Embed_Hdface : forall u : ddart, bc (embd_face (subdE u)).
Proof.
move=> [x Hx]; rewrite /= /embd_face.
case Hfx: (bc (face x)) (edge_perimeter (face x)); auto.
by rewrite /= -{1}[face x]Eface De2c /setC -(fclosed1 HrcN).
Qed.
Notation Hdface := Embed_Hdface.

Let dedge u : ddart := subdI (Hdedge u).
Let dnode u : ddart := subdI (Hdnode u).
Let dface u : ddart := subdI (Hdface u).

Remark Embed_Hemb_disk : monic3 dedge dnode dface.
Proof.
hnf; move=> [x Hx]; apply: (subdE_inj _); rewrite /= /embd_edge.
case Hex: (bc (edge x)); last by rewrite /embd_face Enode Hex Eedge.
by rewrite /embd_face /setC (fclosed1 HrcN) Eedge (negbE Hx) /= Eedge.
Qed.
Notation Hemb_disk := Embed_Hemb_disk.

Definition emb_disk := Hypermap Hemb_disk.
Definition embd (u : emb_disk) := subdE u.

Lemma inj_embd : injective embd. Proof. exact: (@subdE_inj). Qed.

Lemma codom_embd : codom embd =1 bc.
Proof.
move=> z; apply/set0Pn/idP => [[[y Hy] Dy]|Hz]; first by rewrite (eqP Dy).
exists (subdI Hz : emb_disk); exact: set11.
Qed.

Definition embd_ring := preimage_seq embd erc.

Lemma maps_embd_ring : maps embd embd_ring = erc.
Proof.
apply: maps_preimage => [x Hex]; rewrite codom_embd.
rewrite -{1}[x]De2c (mem_maps (Iedge gc)) in Hex.
by move: (edge_perimeter x); rewrite /setC orbC Hex.
Qed.

Lemma cface_embd : forall u v, cface u v = cface (embd u) (embd v).
Proof.
move=> u v; apply/idP/idP.
  case/connectP=> [p Hp <-] {v}.
  elim: p u Hp => [|v p Hrec] [x Hx];  [ clear; exact: connect0 | simpl ].
  rewrite {1}/eqdf -(inj_eqd inj_embd); move/andP=> [Dv Hp].
  apply: (connect_trans _ (Hrec _ Hp)); rewrite -(eqP Dv) /= /embd_face.
  by case (bc (face x)); rewrite -!cface1r connect0.
move/connectP=> [p Hp Ep].
elim: {p}(S (size p)) u {-2}p (ltnSn (size p)) Hp Ep => [|n Hrec] // u.
case=> [|y p] Hn; first by move=> _ Dv; apply eq_connect0; apply inj_embd.
rewrite cface1 /=; case/andP; case: u {Hrec}(Hrec (face u)) => [x Hx].
rewrite /= /embd_face; move=> Hrec Dy Hp; move: Hrec; rewrite (eqP Dy).
case Hy: (bc y); first by move=> Hrec Ep; apply (Hrec p).
case: p Hn Hp => [|z p] /=.
  by case: v => [z Hz] _ _ _ Dy'; rewrite Dy' /= Hz in Hy.
move=> Hn; move/andP=> [Dz Hp]; rewrite (eqP Dz).
by move=> Hrec Ep; apply (Hrec p (ltnW Hn)).
Qed.

Lemma scycle_embd_ring : sfcycle edge embd_ring.
Proof.
have UrF: simple embd_ring.
  move: (scycle_simple HUerc); rewrite -maps_embd_ring.
  elim: embd_ring => [|u q Hrec] //; rewrite simple_adds /= simple_adds.
  move/andP=> [Hu Hq]; apply/andP; split; auto; clear Hrec Hq.
  apply/hasP => [[v Hv Huv]]; case/hasP: Hu.
  by exists (embd v); [ apply maps_f | rewrite -cface_embd ].
rewrite /scycle UrF andbT; have Ur := simple_uniq UrF.
apply: (cycle_from_next Ur) => [u Hu]; apply/eqP; apply inj_embd.
rewrite -(mem_maps inj_embd) maps_embd_ring -[embd u]De2c in Hu.
rewrite (mem_maps (Iedge gc)) in Hu.
rewrite -(next_maps inj_embd Ur) maps_embd_ring -[embd u]De2c.
rewrite (next_maps (Iedge gc) (simple_uniq UrcF)).
by rewrite -(eqP (next_cycle Hrc Hu)) /= -/(embd u) /embd_edge /setC Hu.
Qed.

Remark Embed_HidE : fclosed edge embd_ring.
Proof.
apply: (intro_closed (Sedge _)).
case: (andP scycle_embd_ring) => [Hr _] x y Dy Hx.
by rewrite -(fconnect_cycle Hr Hx) connect1.
Qed.
Notation HidE := Embed_HidE.

Definition embdd u := h1 (embd u).

Lemma embdd_inj : injective embdd.
Proof.
move=> [x Hx] [y Hy] Dh; apply: (inj_embd _); exact (embed_inj Hx Hy Dh).
Qed.

Lemma embddE : forall u, setC embd_ring u -> embdd (edge u) = edge (embdd u).
Proof.
move=> [x Hx]; rewrite /setC -(mem_maps inj_embd) maps_embd_ring /=.
rewrite /embdd /= -embedE -{1}[x]De2c (mem_maps (Iedge gc)) /embd_edge.
by move=> H; rewrite /setC H.
Qed.

Lemma embddN : forall u, embdd (node u) = node (embdd u).
Proof. by move=> [x Hx]; rewrite /embdd /= (embedN Hx). Qed.

Let rdom := setC (image embdd (setC embd_ring)).
Let rdart := subFin rdom.

Remark Embed_Hredge : forall w : rdart, rdom (edge (subdE w)).
Proof.
move=> [u Hu]; apply/set0Pn => [[x]]; move/andP=> [Du Hx].
rewrite /preimage /= (monic2F_eqd De2m) -(embddE Hx) in Du.
case/set0Pn: Hu; exists (edge x); rewrite /setI /preimage Du /=.
by apply/idP => Hex; rewrite /setC (fclosed1 HidE) /= Hex in Hx.
Qed.
Notation Hredge := Embed_Hredge.

Let erc1 u x := embd_ring x && (u =d embdd x).

Definition embr_node u :=
  if pick (erc1 u) is Some x then embdd (node (face x)) else node u.

Remark Embed_Hrnode : forall w : rdart, rdom (embr_node (subdE w)).
Proof.
move=> [u Hu]; apply/set0Pn => [[x]]; move/andP=> [Du Hx]; move: Du.
rewrite /preimage /= /embr_node.
case: pickP => [y Hy|Hu'].
  case/andP: Hy => [Hy _] Dx; case/idP: Hx.
  by rewrite -(embdd_inj (eqP Dx)) (fclosed1 HidE) Eface.
rewrite -{1}[x]Eedge embddN (inj_eqd (Inode gm)); move=> Du.
case/set0Pn: Hu; exists (face (edge x)); rewrite /setI /preimage Du.
by apply/idP => Hfex; move: (Hu' (face (edge x))); rewrite /erc1 Du Hfex.
Qed.
Notation Hrnode := Embed_Hrnode.

Definition embr_face u :=
  if pick (erc1 (edge u))is Some x then embdd (edge x) else face u.

Remark Embed_Hrface : forall w : rdart, rdom (embr_face (subdE w)).
Proof.
move=> [u Hu]; apply/set0Pn => [] [x]; move/andP=> [Du Hx]; move: Du.
rewrite /preimage /= /embr_face.
case: pickP => [y Hy|Hu'].
  case/andP: Hy => [Hy _] Dx.
  by rewrite /setC -(embdd_inj (eqP Dx)) -(fclosed1 HidE) Hy in Hx.
rewrite (monic2F_eqd (Eface gm)) -embddN => Du.
have Hnx: setC embd_ring (node x).
  apply/idP => [Hnx]; move: (Hu' (node x)).
  by rewrite /erc1 Hnx (eqP Du) De2m set11.
rewrite -(embddE Hnx) in Du.
case: (elimN set0Pn Hu); exists (edge (node x)); rewrite /setI /preimage Du.
by rewrite /setC -(fclosed1 HidE) (negbE Hnx).
Qed.
Notation Hrface := Embed_Hrface.

Let redge u : rdart := subdI (Hredge u).
Let rnode u : rdart := subdI (Hrnode u).
Let rface u : rdart := subdI (Hrface u).

Remark Embed_Hemb_rem : monic3 redge rnode rface.
Proof.
move=> [u Hu]; apply: subdE_inj; rewrite /= /embr_face De2m.
case: pickP => [y Hy|Hu']; rewrite /embr_node.
  case/andP: Hy => [Hy Du].
  case: pickP => [z Hz|Hy'].
    by move/andP: Hz => [Hz Dey]; rewrite -(embdd_inj (eqP Dey)) Eedge -(eqP Du).
  by move: (Hy' (edge y)); rewrite /erc1 set11 -(fclosed1 HidE) Hy.
case: pickP => [y Hy|_]; last by apply Eedge.
case/andP: Hy => [Hy Du]; move: (negbI (Hu' (node y))).
rewrite /erc1 embddN -(eqP Du) Eedge set11 andbT => Hny.
case/set0Pn: Hu; exists (node y).
by rewrite /setI /preimage embddN -(eqP Du) Eedge set11.
Qed.
Notation Hemb_rem := Embed_Hemb_rem.

Definition emb_rem := Hypermap Hemb_rem.
Definition embr (u : emb_rem) := subdE u.

Lemma inj_embr : injective embr. Proof. exact: (@subdE_inj). Qed.

Lemma codom_embr : codom embr =1 rdom.
Proof.
move=> z; apply/set0Pn/idP => [[[y Hy] Dy]|Hz]; first by rewrite (eqP Dy).
exists (subdI Hz : emb_rem); exact (set11 _).
Qed.

Definition embr_ring := preimage_seq embr (rev (maps embdd embd_ring)).

Lemma maps_embr_ring : maps embr embr_ring = rev (maps embdd embd_ring).
Proof.
apply: maps_preimage => [u Hu]; rewrite codom_embr; rewrite mem_rev in Hu.
case/mapsP: Hu => [x Hx Du]; apply/set0Pn => [[y]]; move/andP=> [Dy Hy].
by rewrite (eqP Dy) in Du; rewrite /setC -(embdd_inj Du) Hx in Hy.
Qed.

Lemma ucycle_embr_ring : ufcycle node embr_ring.
Proof.
case: (andP scycle_embd_ring) => Hrd; move/simple_uniq=> Urd.
have Urdd: uniq (maps embdd embd_ring) by rewrite (uniq_maps embdd_inj).
have Ur: uniq embr_ring.
  by rewrite -(uniq_maps inj_embr) maps_embr_ring uniq_rev.
rewrite /ucycle Ur andbT.
apply: (cycle_from_next Ur) => [u Hu]; apply/eqP; apply inj_embr.
rewrite -(next_maps inj_embr Ur) maps_embr_ring (next_rev Urdd).
rewrite -(mem_maps inj_embr) maps_embr_ring mem_rev in Hu.
rewrite /= /embr_node -/(embr u); case: (mapsP Hu) => [x Hx <-] {u Hu}.
case: (pickP (erc1 (embdd x))) => [y Hy|Hx'].
  case/andP: Hy => [_ Dy]; rewrite (prev_maps embdd_inj Urd).
  apply: (congr1 embdd (Iedge _ _)); rewrite Eface -(embdd_inj (eqP Dy)).
  apply: (esym (eqP _)); exact (prev_cycle Hrd Hx).
by move: (Hx' x); rewrite /erc1 set11 Hx.
Qed.

Lemma emb_patch : patch embdd embr embd_ring embr_ring.
Proof.
split.
- exact embdd_inj.
- exact inj_embr.
- exact scycle_embd_ring.
- exact ucycle_embr_ring.
- exact maps_embr_ring.
- move=> u; rewrite /setU /setC codom_embr /rdom /setC.
  case Hu: (codom embdd u).
    rewrite -(f_iinv Hu) (image_f embdd_inj) (mem_maps embdd_inj) /=.
    by rewrite negb_elim.
  apply: (introN set0Pn _); case=> x; move/andP=> [Du _].
  by case: (elimF set0Pn Hu); exists x.
- exact embddE.
- exact embddN.
- done.
move=> [u Hu]; rewrite /setC -(mem_maps inj_embr) maps_embr_ring /= mem_rev => Hu'.
rewrite /embr_node; case: pickP => [x Hx|_]; last done.
by case/andP: Hx => [Hx Du]; rewrite (eqP Du) (mem_maps embdd_inj) Hx in Hu'.
Qed.

Lemma planar_embr : planar emb_rem.
Proof.
by move: Hpgm; rewrite /planar (genus_patch emb_patch) addnC; case (genus emb_rem).
Qed.

Lemma plain_embr : plain emb_rem.
Proof. by move: HgmE; rewrite (plain_patch emb_patch); case/andP. Qed.

Lemma cubic_embr : quasicubic embr_ring.
Proof. by have: cubic gm := Hgm; rewrite (cubic_patch emb_patch); case/andP. Qed.

Notation ccr := (maps h1 cc).

Remark Embed_Ezh1 : forall p, insertE (maps h1 p) = maps h1 (insertE p).
Proof. by elim=> [|x p Hrec]; last by rewrite /= Hrec embedE. Qed.
Notation Ezh1 := Embed_Ezh1.

Remark Embed_HccE : forall x, insertE cc x -> insertE cc (edge x).
Proof.
move=> x; elim: cc => [|y p Hrec] //=; rewrite /setU1.
rewrite -{3}[y]De2c !(inj_eqd (Iedge gc)) !orbA (orbC (y =d x)).
by case: (_ || (y =d x)) => /=; auto.
Qed.
Notation HccE := Embed_HccE.

Lemma embed_sparse : sparse (insertE ccr).
Proof.
move: Hcc => [[H1 H2 _ _] _]; move: H1 H2; rewrite disjoint_has has_sym.
rewrite /sparse !simple_recI Ezh1 /=; elim: (insertE cc) => [|x p Hrec] //=.
move/norP=> [Hix Hip]; move/andP=> [Hx Hp].
rewrite {Hrec Hp}(Hrec Hip Hp) andbT /=.
apply/hasP => [[u]]; case/mapsP=> [y Hy <-] /= Hxy {u}; case/hasP: Hx.
exists y; auto; case/connectP: Hxy; move=> q.
elim: q x Hix => [|u q Hrec] x Hx /=.
  by move=> _ Dy; rewrite (embed_inj Hx (hasPn Hip _ Hy) Dy) connect0.
case/andP; move/eqP=> <-; rewrite -(embedN Hx).
by rewrite /setC (fclosed1 HrcN) in Hx; rewrite cnode1; auto.
Qed.

Remark Embed_cface_ac_h1 : forall x, ac x -> forall y,
  cface (h1 x) (h1 y) = cface x y.
Proof.
move=> x Hx; suffice: forall y, bc y -> cface (h1 x) (h1 y) = cface x y.
  move=> Hxbc y; case Hy: (bc y) (edge_perimeter y); auto.
  rewrite /= -{1 2}[y]Eface De2c /setC -(fclosed1 HrcN) => Hfy.
  by rewrite embedE (embedN Hfy) cface1r Enode (Hxbc _ Hfy) -cface1r.
move=> y Hy; rewrite -codom_embd in Hy; rewrite -(f_iinv Hy).
have Hxd: bc x by exact (Hacbc Hx).
rewrite -codom_embd in Hxd; rewrite -(f_iinv Hxd) -cface_embd.
symmetry; apply: {y Hy}(patch_face_d emb_patch).
apply/set0Pn => [] [u]; case/andP; rewrite codom_embr => Hxu; case/set0Pn.
rewrite /embdd f_iinv /h1 Hx in Hxu.
case: {Hxu}(cface_h_ac Hx Hxu) => [y Hxy <-] {u}.
rewrite (closed_connect HacF Hxy) in Hx.
have Hy: bc y by exact (Hacbc Hx).
rewrite -codom_embd in Hy; exists (iinv Hy).
rewrite /setI /preimage /embdd f_iinv /h1 Hx set11 /= /setC.
rewrite -(mem_maps inj_embd) f_iinv maps_embd_ring -{1}[y]Eface.
rewrite (mem_maps (Iedge gc)) -(fclosed1 HrcN).
apply: (introN idP (fun Hfy => elimN hasP Hx _)); exists (face y); auto.
exact: fconnect1.
Qed.
Notation cface_ac_h1 := Embed_cface_ac_h1.

Remark Embed_cface_h1 : forall x y, cface x y -> cface (h1 x) (h1 y).
Proof.
suffice: forall x y, bc x -> cface x y -> cface (h1 x) (h1 y).
  move=> Hbc x y Hxy; case Hx: (bc x); auto; case Hy: (bc y).
    by rewrite Sface; apply (Hbc y x Hy); rewrite Sface.
  by rewrite (scycle_cface HUrc Hxy (negbEf Hx) (negbEf Hy)) connect0.
suffice: forall x y, bc x -> bc y -> cface x y -> cface (h1 x) (h1 y).
  move=> Hbc x y Hx Hxy; case Hy: (bc y) (edge_perimeter y); auto.
  rewrite /= -{1 2}[y]Eface De2c /setC -(fclosed1 HrcN) => Hfy.
  rewrite embedE (embedN Hfy) cface1r Enode.
  by apply Hbc; rewrite -?cface1r.
move=> x y; rewrite -!codom_embd; move=> Hx Hy.
rewrite -(f_iinv Hx) -(f_iinv Hy) -cface_embd.
exact: (patch_face_d' emb_patch).
Qed.
Notation cface_h1 := Embed_cface_h1.

Remark Embed_adj_ac_h1 : forall x y, ac x -> ac y -> adj (h1 x) (h1 y) = adj x y.
Proof.
move=> x y Hx Hy; rewrite /h1 Hx Hy; apply/adjP/adjP.
  move=> [u Hxu Huy].
  case/(cface_h_ac Hx): Hxu Huy => [z Hxz <-] {u} Hzy; exists z; auto.
  have Hz: ac z by rewrite -(closed_connect HacF Hxz).
  rewrite /rlink Sface in Hzy.
  case/(cface_h_ac Hy): Hzy => [t Hyt Hzt].
  have Ht: ac t by rewrite -(closed_connect HacF Hyt).
  by move: Hyt; rewrite -(embed_full Hz Ht (esym Hzt)) Sface.
move=> [z Hxz Hzy]; have Hz: ac z by rewrite -(closed_connect HacF Hxz).
rewrite /rlink Sface in Hzy.
have Hez: ac (edge z) by rewrite -(closed_connect HacF Hzy).
exists (h z); first by exact (cface_ac_h Hx Hxz).
by rewrite /rlink Sface -(embed_functor Hz Hez) (cface_ac_h Hy Hzy).
Qed.
Notation adj_ac_h1 := Embed_adj_ac_h1.

Remark Embed_orbitF_h1 : forall x : gc, ac x ->
  orbit face (h1 x) = maps h1 (orbit face x).
Proof.
move=> x Hx; rewrite /orbit -/(arity (h1 x)) {2}/h1 Hx (HhFn Hx) -/(arity x).
elim: {x}(arity x) {1 2 4}x Hx => //= [n Hrec] x Hx; congr Adds.
rewrite (fclosed1 HacF) in Hx.
by rewrite -{1}[x]Eface embedE (embedN (Hacbc Hx)) Enode Hrec.
Qed.
Notation orbitF_h1 := Embed_orbitF_h1.

Lemma embed_valid_contract : valid_contract seq0 ccr.
Proof.
split; try exact embed_sparse; rewrite ?disjoint_has // size_maps ?Ezh1;
 case: Hcc => [[Hrcc _ H3 H4] _] // H0; case/set0Pn: {H3 H4 H0}(H4 H0) => x.
move/and3P=> [Hx Hx2 Hx4]; rewrite disjoint_has has_sym in Hrcc.
apply/set0Pn; exists (h1 x); apply/and3P; split=> //.
  apply: leq_trans Hx2 _ {Hx4}; rewrite orbitF_h1 // /orbit.
  elim: {x Hx}(arity x) {1 3}x => [|n Hrec] x //=.
  move: {Hrec}(Hrec (face x)) => Hrec.
  case Hccx: (fband _ _); case Hcchx: (fband _ _); rewrite // ltnW //.
  case: (elimF hasP Hcchx); case: {Hcchx Hccx}(hasP Hccx) => [y Hy Hyx].
  by exists (h1 y); [ apply maps_f | rewrite -embedE; apply cface_h1 ].
apply/idP => [Hhx]; case/subsetP: Hx4 {Hx2} => y Hy.
have Hey: insertE cc (edge y) by apply HccE.
have Hhcc: forall z, insertE cc z -> adj (h1 x) (h1 z).
  by move=> z Hz; apply: (subsetP Hhx); apply maps_f.
have Hiey: bc (edge y) by apply: (hasPn Hrcc).
have Hhxn: cface x (node y) || cface x (node (edge y)).
  rewrite -!(cface_ac_h1 Hx) (embedN (hasPn Hrcc _ Hy)).
  rewrite (embedN Hiey) embedE -!mem_spoke_ring.
  by apply adj11_edge; auto; rewrite -embedE; auto.
case/orP: Hhxn => [Hxny|Hxney]; apply/adjP.
  by exists (node y); rewrite // /rlink cface1 Enode connect0.
exists (edge (face y)); last by rewrite /rlink De2c -cface1 connect0.
by rewrite -{1}[y]De2c -(Dn3c Hiey) cface1r !Enode.
Qed.

Definition embed_cotrace := ring_trace (rotr 1 embr_ring).

Lemma embed_closure : kempe_closed embed_cotrace.
Proof.
apply: kempe_map; split; [ split | exact planar_embr ].
  split; first by exact plain_embr.
  apply/subsetP => [w]; rewrite /setC mem_rotr; exact (subsetP cubic_embr w).
rewrite ucycle_rotr; exact ucycle_embr_ring.
Qed.

Lemma embed_contract : exists2 et, cc_ring_trace cc rrc et & embed_cotrace et.
Proof.
case: Hcc => [[Hrcc _ _ _] _]; rewrite disjoint_has has_sym in Hrcc.
case: (contract_coloring Hgm embed_valid_contract) => [k [HkE HkF]].
pose k' x := k (h1 x); exists (trace (maps k' rrc)).
  exists k'; split.
    have HbcE: forall x, bc x -> invariant edge k' x = insertE cc x.
      move=> x Hx; rewrite /invariant /k' embedE; apply: (etrans (HkE _)).
      rewrite Ezh1; apply/mapsP/idP; last by exists x.
      by move=> [y Hy Exy]; rewrite -(embed_inj (hasPn Hrcc _ Hy) Hx Exy).
    move=> x; case: (orP (edge_perimeter x)) => [Hx|Hex]; auto.
    rewrite mem_insertE // (eq_has (cedge1 x)) -mem_insertE // -HbcE //.
    by rewrite /invariant De2c eqd_sym.
  move=> x; rewrite /invariant /k'.
  by rewrite -(fconnect_invariant HkF (cface_h1 (fconnect1 face x))) set11.
exists (fun w => k (embr w)).
  split=> [] [u Hu].
    rewrite /invariant /eqdf /=; apply: (etrans (HkE _)); rewrite Ezh1.
    apply/mapsP => [] [x Hx Ex].
    have Hxd: codom embd x by rewrite codom_embd; apply: (hasPn Hrcc).
    case/set0Pn: Hu; exists (iinv Hxd); rewrite /setI /preimage /setC.
    rewrite -(mem_maps inj_embd) maps_embd_ring /embdd f_iinv Ex set11.
    rewrite -[x]De2c (mem_maps (Iedge gc)); apply: (hasPn Hrcc).
    by move: Hx; rewrite !mem_insertE // (eq_has (cedge1 x)).
  rewrite /invariant /eqdf /= /setA /= /embr_face.
  case: pickP => [[x Hx] Hxu|_]; last by apply: HkF.
  case/andP: Hxu; rewrite -(mem_maps inj_embd) maps_embd_ring /embdd /=.
  rewrite -{1 2}[x]De2c (mem_maps (Iedge gc)) embedE (inj_eqd (Iedge gm)).
  move=> Hiex Du; rewrite (eqP Du) /embd_edge /setC Hiex /=.
  apply/eqP; apply: (fconnect_invariant HkF); apply: cface_h1.
  by rewrite cface1 Enode connect0.
rewrite (maps_comp k h1) (maps_comp k embr) !maps_rotr.
rewrite maps_embr_ring /embdd (maps_comp h1 embd) maps_embd_ring.
rewrite /rrc !maps_rev -rev_rot; congr trace; congr rev.
case: rc Hrc => //= [x p]; rewrite rot1_adds.
elim: p {1 3}x => [|z p Hrec] y /=.
  rewrite andbT; move/eqP=> <-; congr Adds.
  apply: (fconnect_invariant HkF); apply: cface_h1.
  by rewrite cface1r Enode connect0.
case/andP=> [Dz Hp]; congr Adds; auto.
rewrite -(eqP Dz); apply: (fconnect_invariant HkF); apply: cface_h1.
by rewrite cface1r Enode connect0.
Qed.

Theorem not_embed_reducible : False.
Proof.
move: embed_contract => [et Hetc Hetr].
case: {et Hetc Hetr}(c_reducible_coclosure Hcc Hetc embed_closure Hetr).
move=> et [kc [HkcE HkcF] Detc] [kr Hkr Detr].
case: (minimal_counter_example_is_noncolorable Hgm).
case: (colorable_patch emb_patch) => _; apply; exists (rev et);
  last by rewrite rev_rev Detr -trace_rot -!maps_rot rot_rotr; exists kr.
exists (fun u => kc (embd u)).
  split.
    move=> [x Hx]; rewrite /invariant /= /embd_edge.
    case: (bc (edge x)); first by apply: HkcE.
    rewrite -(eqcP (HkcF (edge (node (edge x))))) Enode; exact: HkcE.
  move=> u; apply/eqP; apply: (fconnect_invariant HkcF).
  by rewrite -cface_embd -cface1 connect0.
rewrite (maps_comp kc embd) maps_embd_ring Detc /rrc maps_rev.
rewrite trace_rev rev_rot rev_rev; symmetry; apply: (monic_move (@rotr_rot _ _)).
rewrite -trace_rot; congr trace.
case: rc (andP HUrc) => [|x p] [Hp _] //; move: Hp.
rewrite /= rot1_adds; elim: p {1 4}x => [|z p Hrec] y /=.
  case/andP;  move/eqP=> <- _; congr Adds; symmetry.
  apply: eqP; rewrite -{1}[y]Enode; exact: HkcF.
case/andP; move/eqP=> <- Hp; congr Adds; auto.
symmetry; apply: eqP; rewrite -{1}[y]Enode; exact: HkcF.
Qed.

End Embeddings.

Unset Implicit Arguments.