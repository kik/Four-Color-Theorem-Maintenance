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
Require Import walkup.
Require Import geometry.
Require Import color.
Require Import coloring.
Require Import patch.
Require Import snip.
Require Import revsnip.
Require Import birkhoff.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The proof that there exists a contract coloring for any valid contract. *)
(* We will show in embed.v that contract validity is lifted by the         *)
(* embedding, except for the ring condition, which becomes moot.           *)

Definition contract_ring (g : hypermap) (cc r : seq g) : Prop :=
  and3 (scycle rlink r) (proper_ring r) (sub_set (behead r) (insertE cc)).

Section Contract.

Variable g : hypermap.
Hypothesis Hg : minimal_counter_example g.

Let Hpg : planar g := Hg.
Let Hbg : bridgeless g := Hg.
Let HgE : plain g := Hg.
Let HgN : cubic g := Hg.
Let HgF : pentagonal g := Hg.
Let Hcg : connected g := Hg.
Let Hkg := minimal_counter_example_is_noncolorable Hg.
Let Hmg := minimal_counter_example_is_minimal Hg.
Let De2 := plain_eq Hg.
Let He1 := plain_neq Hg.
Let Dn3 := cubic_eq Hg.
Let Hg' : planar_bridgeless_plain_connected g := Hg. (* revring assumption *)

Lemma sparse_contract_ring : forall cc : seq g, sparse (insertE cc) ->
 forall p, contract_ring cc p -> nontrivial_ring 0 p.
Proof.
intros cc Hcc; rewrite /sparse simple_recI /= in Hcc.
have HccF: forall p, contract_ring cc p -> ~ diskF p =1 set0.
  move=> p; elim: {p}(S (size p)) {-2}p (ltnSn (size p)) => // [n Hrec] p Hn.
  move=> [Hp HpE Hpcc] HpF; case Dp: p (HpE) => [|x [|x' p']] // _.
  move: (negbI (HpF (node x))) (negbI (HpF (node (node x)))).
  have Hpx: diskN p x by rewrite diskN_E /setU Dp /= setU11.
  rewrite /diskF /setD -!(fclosed1 (diskN_node p)) Hpx !andbT !negb_elim.
  case: (andP Hp) => _; move/simple_uniq=> Up Hnx Hnnx.
  case HnxE: (diskE p (node x)).
    have Henx: fband p (edge (node x)).
      apply/hasP; exists x; first by rewrite Dp /= setU11.
      by rewrite -{2}[x]Enode fconnect1.
    rewrite (fclosed1 (diskE_edge Hpg Hp)) in HnxE.
    set q := chord_ring p (edge (node x)).
    move: (fprojP Hnx) (fprojP Henx) => [Hpnx Hnxpnx] [Hpenx Hxpenx].
    have Dpenx: fproj p (edge (node x)) = x.
      rewrite cface1 Enode Sface in Hxpenx.
      by apply (scycle_cface Hp Hxpenx Hpenx); rewrite Dp /= setU11.
    case Hxpnx: (fproj p (node x) =d x).
      by move: Hnxpnx; rewrite (eqP Hxpnx) -{2}[x]Enode -cface1r (set0P Hbg).
    case Hxpnx': (fproj p (node x) =d x').
      move: Hnxpnx; rewrite (eqP Hxpnx').
      case: (andP Hp); rewrite Dp; move/andP=> [Dx' _] _.
      rewrite Sface -(same_cface Dx') -[node x]Enode -cface1r.
      by rewrite -{1}[x]Dn3 cface1 Enode (set0P Hbg).
    case: (rot_to_arc Up Hpenx Hpnx); first by rewrite Dpenx eqd_sym Hxpnx.
    move=> i p1 p2 Dp1 Dp2; rewrite Dpenx -cat_adds in Dp1 |- * => Eip.
    rewrite -{2}[node x]De2 in Dp2.
    apply (Hrec q).
    - rewrite ltnS -(size_rot i) in Hn; apply: leq_trans Hn.
      rewrite Eip size_cat Dp1 Dp2 {1}Dp {1}/arc /= set11 /= Hxpnx Hxpnx'.
      by rewrite /= !addSnnS leq_addl.
    - split; try by apply: scycle_chord_ring; rewrite ?De2.
        by apply: (proper_chord_ring Hg); rewrite ?De2.
      move=> y Hy; simpl in Hy; apply Hpcc.
      have Hpy: p y by rewrite -(mem_rot i) Eip mem_cat /setU Dp2 Hy orbT.
      move: Hpy; rewrite Dp /= /setU1; case: (x =P y) => // [Dy].
      rewrite -(uniq_rot i) Eip uniq_cat Dp1 Dp2 in Up.
      case/and3P: Up => _; case/hasP; exists y; first done.
      by rewrite {1}Dp /arc /= set11 /= Hxpnx /= -Dy setU11.
    by move=> y; rewrite /q diskF_chord_ring ?De2 // /setD HpF andbF.
  have Hpnx: p (node x).
    rewrite /diskE /setD -(fclosed1 (diskN_node p)) Hpx andbT in HnxE.
    exact (negbEf HnxE).
  case HnnxE: (diskE p (node (node x))).
    have Hennx: fband p (edge (node (node x))).
      apply/hasP; exists (node x); first done.
      by rewrite -{2}[node x]Enode fconnect1.
    set q := chord_ring p (edge (node (node x))).
    move: (fprojP Hnnx) (fprojP Hennx) => [Hpnnx Hnnxpnnx] [Hpennx Hnxpennx].
    have Dpennx: fproj p (edge (node (node x))) = node x.
      rewrite cface1 Enode Sface in Hnxpennx.
      by apply (scycle_cface Hp Hnxpennx Hpennx Hpnx).
    have Ep': last x' p' = node x.
      apply: (@monic_inj g _ _ _ (prev_next Up)).
      rewrite -(next_rotr 1 Up) {1}Dp lastI rotr1_add_last /= set11.
      apply (scycle_cface Hp); rewrite ?mem_next //; last by rewrite Dp /= setU11.
      case/andP: Hp => [Hp _]; rewrite Sface -(same_cface (next_cycle Hp Hpnx)).
      by rewrite -{2}[x]Enode fconnect1.
    case Hpnnxnx: (fproj p (node (node x)) =d node x).
      move: Hnnxpnnx; rewrite (eqP Hpnnxnx) -{2}[node x]Enode.
      by rewrite -cface1r (set0P Hbg).
    case Hpnnxx: (fproj p (node (node x)) =d x).
      move: Hnnxpnnx; rewrite (eqP Hpnnxx) -[node (node x)]Enode Dn3.
      by rewrite Sface -cface1r (set0P Hbg).
    case: (rot_to_arc Up Hpennx Hpnnx); first by rewrite Dpennx eqd_sym Hpnnxnx.
    move=> i p1 p2 Dp1 Dp2; rewrite Dpennx -cat_adds in Dp1 |- *.
    rewrite {p1}Dp1 {p2}Dp2 -{2}[p](rot_rotr 1) arc_rot ?uniq_rotr ?mem_rotr //.
    rewrite {2}Dp lastI rotr1_add_last {1}/arc /= Ep' set11 /= Hpnnxnx Hpnnxx.
    rewrite -{2}[node (node x)]De2 => Eip.
    apply (Hrec q) => [||y].
    - rewrite ltnS -(size_rot i) in Hn; apply: leq_trans Hn.
      by rewrite Eip size_cat /= !addSnnS leq_addl.
    - split; rewrite /q; first by apply: scycle_chord_ring; rewrite ?De2.
        apply: (proper_chord_ring Hg); rewrite ?De2 //.
        by rewrite -(fclosed1 (diskE_edge Hpg Hp)).
      move=> y Hy; simpl in Hy; apply Hpcc.
      have Hpy: p y by rewrite -(mem_rot i) Eip mem_cat /setU Hy orbT.
      move: Hpy; rewrite Dp /= /setU1; case: (x =P y) => // [Dy].
      rewrite -(uniq_rot i) Eip uniq_cat in Up.
      case/and3P: Up; clear; case/hasP; exists y; first done.
      by rewrite -Dy /= setU1r ?setU11.
    rewrite /q diskF_chord_ring ?De2 //; first by rewrite /setD HpF andbF.
    by rewrite -(fclosed1 (diskE_edge Hpg Hp)).
  have Hnxx := cubic_neq HgN x.
  have Hccnx: insertE cc (node x).
    by rewrite Dp /= /setU1 eqd_sym Hnxx in Hpnx; apply Hpcc; rewrite Dp.
  have Hccnnx: insertE cc (node (node x)).
    rewrite /diskE /setD -!(fclosed1 (diskN_node p)) Hpx andbT in HnnxE.
    rewrite Dp /= /setU1 -(inj_eqd (Inode g)) Dn3 Hnxx in HnnxE.
    by apply Hpcc; apply negbEf; rewrite Dp.
  clear Hrec Hn Hp HpE Hpcc HpF x' p' Dp Hpx Up Hnx Hnnx HnxE Hpnx HnnxE.
  elim: {n p}cc Hcc Hccnx Hccnnx => [|y cc Hrec] //=.
  rewrite /setU1; case/and3P; move/norP=> [_ Hy] Hey Hcc.
  case: (y =P node x) => [Dy|_].
    case: (edge y =P node (node x)) => [Dey|_] _.
      clear; move: (set0P Hbg x).
      by rewrite 2!cface1r -{2}[x]Dn3 -Dey Dy !Enode connect0.
    rewrite Dy (inj_eqd (Inode g)) eqd_sym Hnxx.
    move=> Hnnx; case/hasP: Hy; exists (node (node x)); auto.
    by rewrite Dy fconnect1.
  case: (edge y =P node x) => [Dey|_].
    case: (y =P node (node x)) => [Dy|_] _.
    clear; move: (set0P Hbg x).
      by rewrite 2!cface1r -{2}[x]Dn3 -Dy -{1}[y]De2 Dey !Enode connect0.
    rewrite Dey (inj_eqd (Inode g)) eqd_sym Hnxx.
    move=> Hnnx; case/hasP: Hey; exists (node (node x)); auto.
    by rewrite Dey fconnect1.
  simpl; case: (y =P node (node x)) => [Dy|_] Hnx.
    by case/hasP: Hy; exists (node x); rewrite //= Dy Snode fconnect1.
  case: (edge y =P node (node x)) => [Dey|_]; eauto.
  by case/hasP: Hey; exists (node x); rewrite //= Dey Snode fconnect1.
move=> p Hpcc; apply/(nontrivial0P p); split.
  exact (set0Pn (introN set0P (HccF p Hpcc))).
case: Hpcc => [HUp HpE Hpcc].
have HUp1: scycle rlink (rot 1 p) by rewrite scycle_rot.
case: (set0Pn (introN set0P (HccF (rev_ring (rot 1 p)) _))).
  split; first by apply: scycle_rev_ring.
    by rewrite proper_rev_ring // proper_ring_rot.
  move=> y Hy; have Hccey: insertE cc (edge y).
  apply Hpcc; case: (p) Hy => [|x p'] //=.
    rewrite rot1_adds /rev_ring -maps_rev rev_add_last /= -{1}[y]De2.
    by rewrite (mem_maps (Iedge g)) mem_rev.
  by move: Hccey; rewrite !mem_insertE // -(eq_has (cedge1 y)).
move=> y; rewrite diskF_rev_ring ?proper_ring_rot //.
move=> H; exists y; apply: etrans H.
rewrite /diskFC /setD /diskN /setC /fband.
rewrite -!disjoint_has !(eq_disjoint (mem_rot 1 p)) !(disjoint_sym p).
congr andb; apply: eq_disjoint => y'; apply: eq_connect => z z'.
by rewrite /dlink mem_rot.
Qed.

Remark contract_ring_max : forall cc p : seq g, contract_ring cc p ->
  size p <=S (size cc).
Proof.
move=> cc p [Hp Hpr Hpcc]; pose df x := setI cc (set2 x (edge x)).
have Hf: forall x, behead p x -> ~ df x =1 set0.
move=> x H Hccx; move: {H}(Hpcc _ H) => Hx.
  rewrite mem_insertE // in Hx; case/hasP: Hx => [y Hy Hxy].
  by rewrite plain_orbit // mem_seq2 in Hxy; case/andP: (Hccx y); split.
pose f (u : subFin (behead p)) :=
  let (x, _) := u in if pick (df x) is Some y then y else x.
have Uf: injective f.
  move=> [x Hx] [y Hy] /=; case: pickP => [x' Hx'|H]; last by case (Hf _ Hx H).
  case: pickP => [y' Hy'|H]; last by case (Hf _ Hy H).
  move=> Dx'; move: Dx' {Hx' Hy'}(andP Hx') (andP Hy') => <- {y'} [_ Dx] [_ Dy].
  apply: subdE_inj _ => /=; move: {Hx Hy}(mem_behead Hx) (mem_behead Hy) => Hx Hy.
  case/orP: Dx; move/eqP=> Dx'; rewrite -Dx' in Dy.
    case/orP: Dy; move/eqP => // Dx.
    by case/negP: (diskN_edge_ring Hg Hp Hpr Hy); rewrite Dx diskN_E /setU Hx.
  case/orP: Dy; move/eqP => // Dy; last exact: Iedge.
  by case/negP: (diskN_edge_ring Hg Hp Hpr Hx); rewrite -Dy diskN_E /setU Hy.
have Up: uniq (behead p).
  case: (p) (andP Hp) => [|x p'] [_ Up]; first done.
  by case (andP (simple_uniq Up)).
rewrite -add1n -leq_sub_add subn1 -size_behead -(card_uniqP Up).
rewrite -card_sub_dom -(card_image Uf).
apply: leq_trans (subset_leq_card _) (card_size _).
apply/subsetP => y; case/set0Pn=> [] [x Hx] /=; case/andP; move/eqP=> -> _ /=.
by case: pickP => [x' Hx'|H]; [ case (andP Hx') | case (Hf _ Hx H) ].
Qed.

Lemma contract3_valid : forall cc : seq g, sparse (insertE cc) ->
  size cc <= 3 -> forall p, ~ contract_ring cc p.
Proof.
move=> cc HccN Hcc p Hpcc; case: (Hpcc) => [Hp _ _].
have Hpn: size p <= 4 by apply: leq_trans (contract_ring_max Hpcc) _.
rewrite -ltnS ltn_neqAle in Hpn; move/andP: Hpn => [Ep5 Hp5].
case/idP: (birkhoff Hg Hp5 Hp); rewrite (negbE Ep5).
exact: (sparse_contract_ring HccN).
Qed.

Lemma triad_valid : forall (cc : seq g) x0, sparse (insertE cc) ->
  size cc =d 4 -> triad (insertE cc) x0 -> forall p, ~ contract_ring cc p.
Proof.
move=> cc x0 HccN Hcc Hx0 p Hpcc.
have Hp5: size p <= 5 by rewrite -(eqP Hcc); exact (contract_ring_max Hpcc).
case: Hpcc (sparse_contract_ring HccN Hpcc) => [Hp HprE Hpcc] Hpr.
case Ep5: (size p =d 5) (birkhoff Hg Hp5 Hp); [ move=> Hpr' | by rewrite /= Hpr ].
have [y0 Hy0p]: exists y0, sub_set (adj y0) (fband p).
  case: (pickP (fun y => subset (adj y) (fband p))) => [y Hy|Hp''].
    by exists y; exact (subsetP Hy).
  case/(nontrivial0P _): Hpr => [[y0 Hy0] [y1 Hy1]].
  case/(nontrivial1P _): Hpr'; split.
    exists y0; [ done | case/set0Pn: (Hp'' y0) => y; case/andP ].
    move/adjP=> [y' Hy0y' Hy'y] Hpy; rewrite /rlink cface1 in Hy'y.
    exists (face (edge y')).
      rewrite /diskF /setD (closed_connect (fbandF p) Hy'y) (negbE Hpy).
      rewrite (fclosed1 (diskN_node p)) Eedge.
      by rewrite (closed_connect (diskF_face p) Hy0y') in Hy0; case/andP: Hy0.
    by rewrite (same_cface Hy0y') -cface1r (set0P Hbg).
  exists y1; [ done | case/set0Pn: (Hp'' y1) => y; case/andP ].
  move/adjP=> [y' Hy1y' Hy'y] Hpy; rewrite /rlink cface1 in Hy'y.
  exists (face (edge y')).
    rewrite /diskFC /setD (closed_connect (fbandF p) Hy'y) (negbE Hpy).
    rewrite /setC (fclosed1 (diskN_node p)) Eedge.
    by rewrite (closed_connect (diskFC_face p) Hy1y') in Hy1; case/andP: Hy1.
  by rewrite (same_cface Hy1y') -cface1r (set0P Hbg).
have Hpy0: sub_set (fband p) (adj y0).
  move=> x Hx; apply/idPn => Hy0x.
  have:= HgF y0; rewrite -size_spoke_ring -(eqP Ep5) leqNgt; case/idP.
  have HUy0 := scycle_spoke_ring Hg y0.
  rewrite -(scycle_fcard_fband Hp) -(scycle_fcard_fband HUy0).
  rewrite {2}/n_comp (cardD1 (froot face x)) {1}/setI (roots_root (Sface g)).
  rewrite -(closed_connect (fbandF p) (connect_root _ x)) Hx.
  apply: subset_leq_card; apply/subsetP => y; move/andP=> [Hy Hy0y].
  rewrite fband_spoke_ring in Hy0y.
  rewrite /setI /setD1 Hy (Hy0p _ Hy0y) -(eqP Hy).
  by rewrite (sameP eqP (rootPx (Sface g) x y)) (no_adj_adj Hy0x Hy0y).
case: (pickP (setD (insertE cc) (fband p))) => [z Hz|Hccp].
  case/andP: Hz => [Hpz Hccz]; rewrite mem_insertE // in Hccz.
  move/hasP: Hccz => [z' Hz' Hzz']; case/rot_to: Hz' => [i cc' Dcc].
  rewrite -(size_rot i) Dcc /= eqdSS in Hcc.
  rewrite eqn_leq Hp5 ltnNge -(eqP Hcc) in Ep5; case/idP: Ep5.
  apply: contract_ring_max; split; auto.
  move=> t Ht; move/mem_behead: Ht (Hpcc _ Ht) => Ht.
  rewrite !mem_insertE // -(has_rot i) Dcc /=; case/orP=> //.
  rewrite Sedge -(same_cedge Hzz') plain_orbit // mem_seq2.
  case/orP; move/eqP=> Dt; case/hasP: Hpz.
    by exists t; last by rewrite Dt connect0.
  exists (next p t); first by rewrite mem_next.
  by rewrite -[z]De2 Dt; case/andP: Hp => [Hp _]; apply: (next_cycle Hp).
case Hxy0: (cface x0 y0); case/andP: Hx0.
  clear; case/subsetP=> x Hx; rewrite (adjF Hxy0); apply Hpy0.
  by apply negbEf; move: (Hccp x); rewrite /setD Hx andbT.
rewrite ltnNge; case/idP.
apply: leq_trans (fcard_adj_max Hg (negbI Hxy0)).
set acc := fband (insertE cc).
apply: (@leq_trans (count acc (spoke_ring x0))).
  rewrite /spoke_ring leq_eqVlt; apply/setU1P; left.
  elim: (orbit face x0) => [|z q Hrec] //=.
  rewrite rev_adds -cats1 maps_cat count_cat -{}Hrec addnC; congr addn.
  by rewrite /= /spoke -(fclosed1 (fbandF (insertE cc))) addn0.
rewrite count_filter -simple_fcard_fband.
  apply: subset_leq_card; apply/subsetP => z; rewrite /setI.
  case: (froots face z) => //; case/hasP=> t; rewrite mem_filter /=.
  move/andP=> [Ht Hx0t] Hzt; apply/andP; split.
    case/hasP: Ht => [t' Ht' Htt']; rewrite (adjFr Hzt) (adjFr Htt').
    move: (Hccp t'); rewrite /setD Ht' andbT; move/idP; auto.
  by rewrite -fband_spoke_ring; apply/hasP; exists t.
  case/andP: (scycle_spoke_ring Hg x0); clear.
  rewrite !simple_recI; elim: (spoke_ring x0) => [|z q Hrec] //=.
  move/andP=> [Hz Hq]; case: (acc z) => /=; auto; apply/andP; split; auto.
apply/hasP => [] [t Ht Hzt]; case/hasP: Hz; exists t; last done.
by rewrite mem_filter in Ht; case/andP: Ht.
Qed.

Theorem contract_coloring : forall r cc : seq g, valid_contract r cc ->
  cc_colorable cc.
Proof.
move=> r cc [_ HccN Hcc4 HccT].
have Hccg: 0 < (0  < size cc) by case: (size cc) Hcc4.
rewrite -(leq_add2r (card g)) add1n in Hccg.
have Hccp: forall p, ~ contract_ring cc p.
  case/or4P: Hcc4 => Dcc; try by apply: contract3_valid; rewrite -?(eqP Dcc).
  rewrite eqd_sym in Dcc.
  case/set0Pn: (HccT (eqP Dcc)) => // x0; case/andP=> _; exact: triad_valid.
move: {2}(size cc) (leqnn (size cc)) Hccg Hccp {r HccN HccT Hkg Hcg} => n.
move: {-2}(card g) Hmg (Hg : planar_bridgeless_plain_precubic g) => ng Hng.
elim: n g cc {Hcc4 HccN HccT} => [|n Hrec] g0 [|x cc] Hg0 //=.
- by move=> _ Hng0 _; case: (Hng _ Hg0 Hng0) => [k Hk]; exists k.
- clear; exact (Hrec g0 seq0 Hg0 (leq0n n)).
rewrite /= add1n !ltnS => Hn Hng0 Hcc.
have Hg0E: plain g0 := Hg0; have De20 := plain_eq Hg0.
have Hbg0 := bridgeless_cface Hg0.
have EcEx: forall y : g0, cedge x y = (x =d y) || (edge x =d y).
  by move=> y; rewrite (plain_orbit Hg0) mem_seq2.
pose g1 := walkupF x; pose h1 (u : g1) : g0 := subdE u.
have Hh1: injective h1 by exact: (@subdE_inj).
have Hex: setC1 x (edge x) by rewrite /setC1 eqd_sym (plain_neq Hg0).
pose uex : g1 := subdI Hex.
pose g2 := walkupF uex; pose h2 (w : g2) : g1 := subdE w.
have Hh2: injective h2 by exact: (@subdE_inj).
pose h w := h1 (h2 w); have Hh: injective h by exact: inj_comp Hh1 Hh2.
have Eh: codom h =1 (fun y => negb (cedge x y)).
  move=> y /=; rewrite EcEx; apply/set0Pn/norP => [[w Dy]|[Hxy Hexy]].
    rewrite (eqP Dy); split; [ exact (subd_mem (h2 w)) | exact (subd_mem w) ].
  exists (@subdI g1 (setC1 uex) (@subdI _ (setC1 x) _ Hxy) Hexy); exact (set11 y).
have HcEh: forall w', cedge x (h w') = false.
  by move=> w'; apply negbE; rewrite -Eh codom_f.
have HhN: forall w w', cnode w w' = cnode (h w) (h w').
  move=> *; apply: etrans (fconnect_skip (Iface _) _ _) _; exact: fconnect_skip.
have HhE: forall w w', cedge w w' = cedge (h w) (h w').
  move=> *; apply: etrans (fconnect_skip (Inode _) _ _) _; exact: fconnect_skip.
have HhE1: forall w, h (edge w) = edge (h w).
  move=> w; have Hew: codom h (edge (h w)) by rewrite Eh -cedge1r -Eh codom_f.
  rewrite -(f_iinv Hew); congr h; symmetry.
  do 2 apply: (subdE_skip (Inode _)); exact (f_iinv Hew).
pose cfx y := has (cface y) (seq2 x (edge x)).
have HhF: forall w w',
    cface w w' = if cfx (h w) then cfx (h w') else cface (h w) (h w').
  move=> w w'; transitivity (cface (h2 w) (h2 w')).
  apply: etrans (fconnect_skip (Iedge _) w w').
    apply: (eq_fconnect (glink_fp_skip_edge _)).
    by rewrite /glink /relU /setU /eqdf /eqd /= /skip1 /= De20 !set11 /= orbT.
  case Hw: (cfx (h w)); last exact: (same_cskip_edge (negbI _)).
  by apply: cskip_edge_merge; first rewrite /cross_edge /= Hbg0.
have De22: forall w : g2, edge (edge w) = w.
  by move=> w; apply Hh; rewrite !HhE1 De20.
have Hg2E: plain g2.
  by apply/plainP => [w _]; split; rewrite // -(inj_eqd Hh) HhE1 plain_neq.
have Hg2: planar_bridgeless_plain_precubic g2.
  repeat split; auto; first exact (planar_walkupF _ (planar_walkupF _ Hg0)).
    apply/set0Pn => [] [w Hw].
    have [y Hy Hwy]: exists2 y, cedge x y & cycle rlink (seq2 (h w) y).
      move: Hw; rewrite HhF HhE1 /= Hbg0.
      case Hwx: (cfx (h w)); [ move: Hwx; rewrite /cfx /= /setU1 !orbF | done ].
      case/orP=> Hw.
        rewrite Sface -(same_cface Hw) Hbg0 /= => Hew.
        exists (edge x); first by apply fconnect1.
        by rewrite /= /rlink Hew De20 Sface Hw.
      rewrite orbC Sface -(same_cface Hw) Hbg0 /=.
      move=> Hew; exists x; first by apply connect0.
      by rewrite /= /rlink Hew Sface Hw.
    case (Hcc (seq2 (h w) y)); split.
    - rewrite /scycle Hwy simple_recI /=; case/andP: Hwy => [Hewy _].
      by rewrite Sface -(same_cface Hewy) Sface Hbg0.
    - by apply/eqP => Dy; move: (codom_f h w); rewrite Eh cedge1r Dy Hy.
    by move=> y'; rewrite /= /setU1 orbF orbA -EcEx; move/eqP=> <-; rewrite Hy.
  apply/subsetP => w _; apply: leq_trans (precubic_leq Hg0 (h w)).
  rewrite /order -(card_image Hh); apply subset_leq_card; apply/subsetP => y.
  by case/set0Pn=> [w']; move/andP=> [Dy Hww']; rewrite (eqP Dy) -HhN.
pose cc1 := filter (setC (cedge x)) cc.
have Ecc1: cc1 =1 setD cc (cedge x) by exact: mem_filter.
have Ezcc1: insertE (Adds x cc) =1 setU (cedge x) (insertE cc1).
  move=> y; rewrite /= /setU1 orbA -EcEx /setU !mem_insertE //.
  rewrite !(eq_has (plain_orbit Hg0 y)) !(has_sym (seq2 y (edge y))) /= !orbF.
  by rewrite !Ecc1 /setD -cedge1r; case (cedge x y).
pose cc2 := preimage_seq h cc1.
have Ecc2: maps h cc2 = cc1.
  by apply: maps_preimage => y Hy; rewrite Eh; rewrite Ecc1 in Hy; case/andP: Hy.
have Ezcc2: forall w', insertE cc1 (h w') = insertE cc2 w'.
  move=> w'; rewrite !mem_insertE // -Ecc2 has_maps -(eq_has (a1 := cedge w')) //.
  by move=> w''; rewrite HhE.
have Hscc2: size cc2 <= size cc.
  rewrite -(count_setC (cedge x) cc) addnC count_filter -/cc1 -Ecc2 size_maps.
  by rewrite leq_addr.
case: {Hrec}(Hrec g2 cc2 Hg2 (leq_trans Hscc2 Hn)).
- have <-: (pred (pred (card g0)) = card g2).
    symmetry; apply: (etrans (card_walkup _)); congr pred; exact: card_walkup.
  case (0 < size cc2).
    rewrite /= add1n ltnS; apply: leq_trans _ Hng0.
    by rewrite -!subn1 subn_sub leq_subr.
  by apply: leq_trans _ Hng0; rewrite (cardD1 x) /= add1n ltnS -subn1 leq_subr.
- move=> [|w p] [HUp Hp2 Hpcc] //.
  case: (andP HUp) => [Hp UpF]; have Up := simple_uniq UpF.
  have Uhp: simple (maps h (Adds w p)).
    elim: (Adds w p) UpF => [|w1 q Hrec] //.
    rewrite maps_adds !simple_adds.
    move/andP=> [Hw1 Uq]; rewrite andbC {}Hrec //.
    apply/hasP; case=> hw2; move/mapsP=> [w2 Hw2 <-] {hw2} Hw12.
    case/hasP: Hw1; exists w2; rewrite // Sface HhF.
    case Hxw2: (cfx (h w2)); last by rewrite Sface.
    by rewrite /cfx (eq_has (same_cface Hw12)).
  have Hhpcc: sub_set (maps h p) (insertE cc).
    move=> y; move/mapsP=> [w' Hw' <-] {y}.
    move: (Ezcc1 (h w')); rewrite /setU /= /setU1 orbA -EcEx Ezcc2.
    by rewrite HcEh (Hpcc _ Hw').
  case HUhp: (scycleb rlink (maps h (Adds w p))).
    case (Hcc (maps h (Adds w p))); split; auto.
      by case: (p) Hp2 => [|w' [|w'' p']]; rewrite // /= -HhE1 (inj_eqd Hh).
    by move=> y Hy; rewrite /= /setU1 (Hhpcc _ Hy) !orbT.
  have Hw1: has (fun w1 => negb (rlink (h (prev (Adds w p) w1)) (h w1)))(Adds w p).
    apply/hasPn => [Hhp]; case/andP: HUhp; split; auto.
    apply cycle_from_prev; first exact: simple_uniq.
    move=> y1; move/mapsP=> [w1 Hw1 <-] {y1}.
    move: (Hhp w1); rewrite (prev_maps Hh Up) Hw1 negb_elim; auto.
  case/hasP: Hw1 => [w1 Hw1 Hw1p].
  have Hcfxw1: cfx (h w1).
    apply/idPn => Hcfxw1; case/idP: Hw1p; move: (prev_cycle Hp Hw1).
    by rewrite {1}/rlink Sface HhF HhE1 (negbE Hcfxw1) Sface.
  have := Hcfxw1; rewrite {1}/cfx; move/hasP=> [x1 Hx1 Hw1x1].
  case: (rot_to Hw1) Hp (Up) => [i1 p1 Dp1].
  rewrite -(cycle_rot i1) -(uniq_rot i1) Dp1 (cycle_path w1) /=.
  move/andP=> [Ep1 Hp1]; move/andP=> [Uw1 _].
  rewrite /rlink Sface HhF HhE1 Hcfxw1 /cfx in Ep1.
  case/hasP: Ep1 => [x2 Hx2 Ep1].
  have Hp1x: negb (has (fun w2 => cfx (h w2)) p1).
    apply/hasP => [] [w2 Hw2 Hw2x]; case/idP: Uw1.
    have Hw12: cface w1 w2 by rewrite HhF Hcfxw1.
    by rewrite (scycle_cface HUp Hw12 Hw1) // -(mem_rot i1) Dp1 /= setU1r.
  have Ex12: edge x2 = x1.
    have Ex12: cedge x2 x1.
      by rewrite -plain_orbit // in Hx2; rewrite -(same_cedge Hx2) plain_orbit.
    rewrite plain_orbit // mem_seq2 in Ex12.
    case/orP: Ex12; move/eqP=> Dx1; last done.
    have Ew1p: negb (rlink (h (last w1 p1)) (h w1)).
      move: Hw1p; rewrite -(prev_rot i1 Up) -(prev_rotr 1) ?uniq_rot // Dp1.
      by rewrite lastI rotr1_add_last; case p1; rewrite /= set11.
    by case/idP: Ew1p; rewrite /rlink (same_cface Ep1) Dx1 Sface.
  pose q1 := Adds x2 (maps h (Adds w1 p1)).
  have Hq1: cycle rlink q1.
    rewrite (cycle_path x) /= {1 2}/rlink Ex12 (Sface g0 x1) last_maps.
    apply/and3P; split; auto.
    clear i1 Dp1 Uw1 Hw1 Hw1p Hcfxw1 Hw1x1 Ep1 q1.
    elim: p1 w1 Hp1x Hp1 => [|w2 q Hrec] w1 //=.
    move/norP=> [Hw2x Hqx]; move/andP=> [Hw12 Hq].
    apply/andP; split; last exact (Hrec _ Hqx Hq).
    by move: Hw12; rewrite {1}/rlink Sface HhF HhE1 (negbE Hw2x) Sface.
  have Hq1w: q1 (h w).
    by rewrite /q1 -Dp1 /= /setU1 (mem_maps Hh) mem_rot /= setU11 orbT.
  case: (rot_to Hq1w) => [i2 q2 Dq2].
  have HUq2: scycle rlink (Adds (h w) q2).
    rewrite -Dq2 /scycle cycle_rot Hq1 /= simple_rot /q1 simple_adds.
    apply/andP; split; last by rewrite -Dp1 /= maps_rot simple_rot.
    apply/hasP => [[x3]]; case/mapsP=> [w3 Hw3 <-] {x3} Hw3x2.
    simpl in Hw3; case/setU1P: Hw3 => [Dw3|Hw3].
      by rewrite Dw3 -(same_cface Hw3x2) -Ex12 Hbg0 in Hw1x1.
    case/hasP: Hp1x; exists w3; first done.
    by apply/hasP; exists x2; last by rewrite Sface.
  case (Hcc (Adds (h w) q2)); split; auto.
    rewrite -Dq2 proper_ring_rot // /q1.
    by move: Hp2; rewrite -(proper_ring_rot i1) // Dp1; case p1.
  move=> y Hy; rewrite /= /setU1 orbA.
  move: (mem_behead Hy); rewrite -Dq2 mem_rot /q1 -Dp1 /=.
  move/setU1P=> [Dy|Hyp]; first by rewrite Dy mem_seq2 /set2 in Hx2; rewrite Hx2.
  case/mapsP: Hyp => [w' Hw' Dy]; rewrite mem_rot /= in Hw'.
  case/setU1P: Hw' => [Dw'|Hw'].
    by case/andP: HUq2 => _; move/simple_uniq; case/andP; case/idP; rewrite Dw' Dy.
  move: (Ecc1 y) (Ecc1 (edge y)); rewrite /setD -cedge1r -Eh -Dy codom_f /=.
  rewrite mem_insertE // (eq_has (plain_orbit Hg0E (h w'))) has_sym /= orbF.
  move=> <- <-; apply/orP; right; rewrite -Ecc2 -HhE1 !(mem_maps Hh).
  move: (Hpcc _ Hw'); rewrite mem_insertE //.
  by rewrite (eq_has (plain_orbit Hg2E w')) has_sym /= orbF.
move=> k [HkE H]; move/fconnect_invariant: H => HkF.
pose a y w := cface y (h w).
have Hah: forall w', ~ a (h w') =1 set0.
  by move=> w' H; move: (H w'); rewrite /a connect0.
have Ha0: forall y, a y =1 set0 -> a (edge y) =1 set0.
  rewrite /a; move=> y Hy w'; apply/idP => [Hw'].
  case Hxy: (codom h y).
    by move: (Hy (iinv Hxy)); rewrite /a f_iinv connect0.
  rewrite Eh in Hxy; move/idP: Hxy => Hxy.
  case Hxfy: (codom h (face y)).
    by move: (Hy (iinv Hxfy)); rewrite /a f_iinv fconnect1.
  rewrite Eh in Hxfy; move/idP: Hxfy => Hxfy.
  rewrite (same_cedge Hxy) plain_orbit // mem_seq2 /set2 orbC in Hxfy.
  case/orP: Hxfy; move/eqP=> Dfy.
    by move: (Hbg0 y); rewrite Dfy fconnect1.
    move: (precubic_leq Hg0 y) (f_finv (Inode _) y); rewrite /finv.
    case: (order node y) (orderSpred node y) => [|[|[|[|ny]]]] //= _ _ Ey.
      by move: (Hbg0 y); rewrite -{1}[y]Enode Ey Sface fconnect1.
    have HyF: fcycle face (seq1 (edge y)).
      by rewrite /= /eqdf -{1}Ey Enode {1}Dfy -{1}[y]De20 Eedge set11.
    rewrite (fconnect_cycle HyF (setU11 _ _)) mem_seq1 in Hw'.
    move: (HcEh w'); rewrite (same_cedge Hxy) plain_orbit // mem_seq2.
    by rewrite (eqP Hw') set22.
    move: (Hbg0 (face (edge y))).
  by rewrite -cface1 -{2}Ey cface1r !Enode {2}Dfy -{2}[y]De20 Eedge connect0.
pose k' y := if pick (a y) is Some w then k w else Color0.
have Ek'h: forall w, k' (h w) = k w.
  move=> w; rewrite /k'; case: pickP => [w' Hww'|Hw0]; last by case (Hah _ Hw0).
  apply: HkF; rewrite HhF {2}/cfx (eq_has (same_cface Hww')) Sface.
  by case Hw': (cfx (h w')).
have Ek'x: k' x = k' (edge x).
  rewrite /k'; case: pickP => [w Hwx|Hx0].
    case: pickP => [w' Hw'ex|Hex0]; last by rewrite -[x]De20 (Ha0 _ Hex0) in Hwx.
    apply: HkF; rewrite /a in Hwx Hw'ex; rewrite HhF /cfx /= Sface Hwx /=.
    by rewrite orbC Sface Hw'ex.
  by case: pickP => // [w' Hw'ex]; rewrite (Ha0 _ Hx0) in Hw'ex.
exists k'; split.
  move=> y; rewrite Ezcc1 /setU /invariant in HkE |- *.
  case Hy: (cedge x y).
    rewrite plain_orbit // mem_seq2 in Hy.
    by case/orP: Hy; move/eqP=> <-; rewrite ?De20 -Ek'x set11.
  move/idPn: Hy => Hy; rewrite -Eh in Hy.
  by rewrite -(f_iinv Hy) -HhE1 !Ek'h HkE Ezcc2.
move=> y; apply/eqP; rewrite /k' -(eq_pick (a := a y)) //.
by move=> w; rewrite /a cface1.
Qed.

End Contract.

Unset Implicit Arguments.