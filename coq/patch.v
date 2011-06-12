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
Require Import geometry.
Require Import jordan.
Require Import color.
Require Import coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Patch.

(* Patching two maps to cover a larger one. The relations established here *)
(* are used in both directions: with sew, to deduce the properties of the  *)
(* new map created by glueing, and in snip, to deduce the properties of    *)
(* the two maps created by cutting along an rlink cycle.                   *)
(* It is important to note that the relations between the two parts is     *)
(* not quite symmetrical: the border of the inside ("disk") map is an edge *)
(* cycle, while the border of the outer ("remainder") part is a node orbit *)
(* The disk border must be simple, but only in the "disk" map; the         *)
(* corresponding sequence in the main and remainder maps needs not be.     *)
(* At the end of this file is the first application of patching: we prove  *)
(* that a minimal counter example must be connected.                       *)

Variables (g gd gr : hypermap) (hd : gd -> g) (hr : gr -> g).
Variables (bgd : seq gd) (bgr : seq gr).

Record patch : Prop := Patch {
  patch_injd : injective hd;
  patch_injr : injective hr;
  patch_cycle_d : sfcycle edge bgd;
  patch_cycle_r : ufcycle node bgr;
  patch_maps_ring_r : maps hr bgr = rev (maps hd bgd);
  patch_codom_r : codom hr =1 setU (setC (codom hd)) (maps hd bgd);
  patch_edge_d : forall xd, setC bgd xd -> hd (edge xd) = edge (hd xd);
  patch_node_d : forall xd, hd (node xd) = node (hd xd);
  patch_edge_r : forall xr, hr (edge xr) = edge (hr xr);
  patch_node_r : forall xr, setC bgr xr -> hr (node xr) = node (hr xr)
}.

Hypothesis Hgh : patch.

Let Ihd := patch_injd Hgh.
Let Ihr := patch_injr Hgh.
Let Hbgd := patch_cycle_d Hgh.
Let Hbgr := patch_cycle_r Hgh.
Let bg := maps hd bgd.
Let Dbgr : maps hr bgr = rev bg := patch_maps_ring_r Hgh.
Let Ehr := patch_codom_r Hgh.
Remark Patch_Ebgr : maps hr bgr =1 bg. Proof. rewrite Dbgr; apply mem_rev. Qed.
Let Ebgr := Patch_Ebgr.
Remark Patch_Ehd : codom hd =1 setU (setC (codom hr)) bg.
Proof.
move=> x; rewrite /setU /setC Ehr /setU /setC negb_orb negb_elim andbC orbC -/bg.
by case Hx: (bg x); first by case/mapsP: Hx => [xd _ <-]; rewrite codom_f.
Qed.
Let Ehd := Patch_Ehd.
Let EdE := patch_edge_d Hgh.
Let EdN := patch_node_d Hgh.
Let ErE := patch_edge_r Hgh.
Let ErN := patch_node_r Hgh.

Remark Patch_Ubgd : uniq bgd. Proof. by case (andP (scycle_ucycle Hbgd)). Qed.
Let Ubgd := Patch_Ubgd.
Remark Patch_Ubgr : uniq bgr. Proof. by case (andP Hbgr). Qed.
Let Ubgr := Patch_Ubgr.
Remark Patch_Ubg : uniq bg. Proof. by rewrite /bg (uniq_maps Ihd) Ubgd. Qed.
Let Ubg := Patch_Ubg.

Remark Patch_Ebgdr : forall xd, codom hr (hd xd) = bgd xd.
Proof. by move=> *; rewrite Ehr /setU /setC codom_f /bg (mem_maps Ihd). Qed.
Let Ebgdr := Patch_Ebgdr.

Remark Patch_EbgdE : forall xd : gd, bgd xd -> cedge xd =1 bgd.
Proof. by apply: fconnect_cycle; case (andP Hbgd). Qed.
Let EbgdE := Patch_EbgdE.

Remark Patch_Ebgrd : forall xr : gr, codom hd (hr xr) = bgr xr.
Proof. by move=> *; rewrite Ehd /setU /setC codom_f -Ebgr (mem_maps Ihr). Qed.
Let Ebgrd := Patch_Ebgrd.

Remark Patch_EbgrN : forall xr : gr, bgr xr -> cnode xr =1 bgr.
Proof. by apply: fconnect_cycle; case (andP Hbgr). Qed.
Let EbgrN := Patch_EbgrN.

Remark Patch_EhdUr : setU (codom hd) (codom hr) =1 g.
Proof. by move=> x; rewrite /setU Ehr /setU /setC; case (codom hd x). Qed.
Let EhdUr := Patch_EhdUr.

Remark Patch_EhdIr : setI (codom hd) (codom hr) =1 bg.
Proof.
move=> x; rewrite /setI Ehr /setU /setC; case Hx: (codom hd x); auto.
by symmetry; apply/mapsP => [[xd _ Dx]]; rewrite -Dx codom_f in Hx.
Qed.
Let EhdIr := Patch_EhdIr.

Lemma card_patch : card gd + card gr = size bg + card g.
Proof.
rewrite -(card_codom Ihd) -(card_codom Ihr) -cardUI (eq_card EhdUr) addnC.
by rewrite (eq_card EhdIr) (card_uniqP Ubg).
Qed.

Remark Patch_HbgdE : fclosed edge bgd.
Proof.
apply: (intro_closed (Sedge _)) => [xd yd Dyd Hxd] /=.
move/andP: Hbgd => [H _]; rewrite -{H}(fconnect_cycle H Hxd); exact (connect1 Dyd).
Qed.
Let HbgdE := Patch_HbgdE.

Remark Patch_HbgrN : fclosed node bgr.
Proof.
apply: (intro_closed (Snode _)) => [xr yr Dyr Hxr] /=.
case/andP: Hbgr => [H _]; rewrite -{H}(fconnect_cycle H Hxr); exact (connect1 Dyr).
Qed.
Let HbgrN := Patch_HbgrN.

Remark Patch_EdErN : forall xd xr,
  (hd (edge xd) =d hr xr) = (hd xd =d hr (node xr)).
Proof.
move=> xd xr; case Hxd: (bgd xd).
  case/andP: Hbgd => [CdE _]; case/andP: Hbgr => [CrN _].
  rewrite (eqP (next_cycle CdE Hxd)) -(next_maps Ihd Ubgd) -/bg.
  rewrite (monic2F_eqd (prev_next Ubg)) -(next_rev Ubg) -Dbgr.
  rewrite (next_maps Ihr Ubgr).
  case Hxr: (bgr xr); first by rewrite -(eqP (next_cycle CrN Hxr)).
  have Hxdr: (maps hr bgr (hd xd)) by rewrite Ebgr /bg (mem_maps Ihd).
  apply/eqP/eqP => Exr.
    by rewrite Exr (mem_maps Ihr) mem_next Hxr in Hxdr.
  by rewrite Exr (mem_maps Ihr) -(HbgrN (x := xr) (set11 _)) Hxr in Hxdr.
apply/eqP/eqP => Exd.
move: (EhdIr (hr xr)); rewrite /setI codom_f -Exd codom_f.
  by rewrite /bg (mem_maps Ihd) -(HbgdE (x := xd) (set11 _)) Hxd.
  move: (EhdIr (hr (node xr))); rewrite /setI codom_f -Exd codom_f.
by rewrite /bg (mem_maps Ihd) Hxd.
Qed.
Let EdErN := Patch_EdErN.

Remark Patch_HbgdP : forall xd, bgd xd ->
  exists2 xr, hd (edge xd) = hr xr & hd xd = hr (node xr).
Proof.
move=> xd Hxd; have Hxr: (codom hr (hd xd)).
  by rewrite Ehr /setU /bg (mem_maps Ihd) Hxd orbT.
case/set0Pn: Hxr => [xr Dxr]; rewrite /preimage -(Eedge _ xr) in Dxr.
by exists (face (edge xr)); apply: eqP; first by rewrite EdErN.
Qed.
Let HbgdP := Patch_HbgdP.

Remark Patch_HbgrP : forall xr, bgr xr ->
  exists2 xd, hd (edge xd) = hr xr & hd xd = hr (node xr).
Proof.
move=> xr Hxr; have Hxd: (codom hd (hr xr)).
  by rewrite Ehd /setU -Ebgr (mem_maps Ihr) Hxr orbT.
case/set0Pn: Hxd => [xd Dxd]; rewrite /preimage -(Eface _ xd) in Dxd.
by exists (node (face xd)); apply: eqP; rewrite -?EdErN eqd_sym.
Qed.
Let HbgrP := Patch_HbgrP.

Remark Patch_EdF : forall xd, setC bgd xd -> hd (face xd) = face (hd xd).
Proof.
move=> xd Hxd; apply (monic_move (monicF_sym (Eface g))).
rewrite /setC -(Eface _ xd) -(fun yd => HbgdE (x := yd) (set11 _)) in Hxd.
by rewrite -EdN -EdE ?Eface.
Qed.
Let EdF := Patch_EdF.

Remark Patch_ErF : forall xr, setC bgr (face xr) -> face (hr xr) = hr (face xr).
Proof. by move=> xr Hxr; rewrite -{1}[xr]Eface ErE (ErN Hxr) Enode. Qed.
Let ErF := Patch_ErF.

Remark Patch_EdrF : forall xd xr,
  (hr (face xr) =d hd xd) = (hd (face xd) =d face (hr xr)).
Proof.
move=> xd xr; rewrite -{2}[xr]Eface -{1}[xd]Eface ErE.
by rewrite -(monic2F_eqd (Enode g)) -EdN eqd_sym EdErN.
Qed.
Let EdrF := Patch_EdrF.

Let bbd := fband bgd.

Lemma patch_fcard_face_d : fcard face gd = size bg + fcard face (setC bbd).
Proof. rewrite /bg size_maps -(scycle_fcard_fband Hbgd); apply: n_compC. Qed.

Definition outer := fclosure face (codom hr).

Lemma closed_gr : fclosed edge (codom hr).
Proof.
apply: (intro_closed (Sedge g))=> [x y Dy Hx].
by rewrite -(eqP Dy) -(f_iinv Hx) -ErE codom_f.
Qed.

Lemma closed_outer : fclosed face outer.
Proof. apply: (closure_closed (Sface g)). Qed.

Remark closed_outerC : fclosed face (setC outer).
Proof. exact (setC_closed closed_outer). Qed.

Lemma closed_gd : fclosed node (codom hd).
Proof.
apply: (intro_closed (Snode g)) => [x y Dy Hx].
by rewrite -(eqP Dy) -(f_iinv Hx) -EdN codom_f.
Qed.

Lemma plain_patch : plain g = plainb (setC bgd) && plainb gr.
Proof.
PropCongr; apply/idP/andP => [HgE|[HgdE HgrE]].
move: {HgE}(plain_eq HgE) (plain_neq HgE) => De2 He1.
  split; apply/plainP => [x Hx].
    split; last by rewrite -(inj_eqd Ihd) EdE // He1.
    by apply Ihd; rewrite !EdE -?(fclosed1 (setC_closed HbgdE)) // De2.
  by split; [ apply Ihr; rewrite !ErE De2 | rewrite -(inj_eqd Ihr) ErE He1 ].
  apply/plainP => [x _]; case Hxr: (codom hr x).
  case/set0Pn: Hxr => [xr]; move/eqP=> Dx.
  by rewrite Dx -!ErE (inj_eqd Ihr) plain_eq // plain_neq.
rewrite Ehr in Hxr; case/norP: Hxr; move/negbE2; move/set0Pn=> [xd].
move/eqP=> Dx; rewrite Dx /bg (mem_maps Ihd); move=> Hxd.
case: (plainP HgdE _ Hxd) => [De2 He1].
by rewrite -!EdE -?(fclosed1 (setC_closed HbgdE)) // (inj_eqd Ihd) De2 He1.
Qed.

Lemma cubic_patch : cubic g = cubicb gd && cubicb (setC bgr).
Proof.
PropCongr; apply/idP/andP => [HgN|[HgdN HgrN]].
move: {HgN}(cubic_eq HgN) (cubic_neq HgN) => De2 He1.
  split; apply/cubicP => [x Hx].
    by split; [ apply Ihd; rewrite !EdN De2 | rewrite -(inj_eqd Ihd) EdN He1 ].
  split; last by rewrite -(inj_eqd Ihr) ErN // He1.
  by apply Ihr; rewrite !ErN -?(fclosed1 (setC_closed HbgrN)) // De2.
  apply/cubicP => [x _]; case Hxd: (codom hd x).
  case/set0Pn: Hxd => [xd]; move/eqP=> Dx.
  by rewrite Dx -!EdN (inj_eqd Ihd) cubic_eq // cubic_neq.
rewrite Ehd in Hxd; case/norP: Hxd; move/negbE2; move/set0Pn=> [xd].
move/eqP=> Dx; rewrite Dx -Ebgr (mem_maps Ihr); move=> Hxr.
case: (cubicP HgrN _ Hxr) => [De2 He1].
by rewrite -!ErN -?(fclosed1 (setC_closed HbgrN)) // (inj_eqd Ihr) De2 He1.
Qed.

Lemma outer_hd : forall xd, outer (hd xd) = bbd xd.
Proof.
move=> xd; rewrite [outer]lock; apply/idP/idP; unlock.
  case/set0Pn=> [z]; case/andP; case/connectP=> [p Hp <-].
  elim: p xd Hp => [|y p Hrec] xd /=.
    by clear; rewrite Ebgdr; apply: (subsetP (ring_fband _)).
  move/andP=> [Dy].
  case Hxd: (bgd xd); first by do 2 clear; apply: (subsetP (ring_fband _)).
  rewrite -(eqP Dy) -(EdF (negbI Hxd)); move=> Hp Hz.
  by rewrite /bbd (fclosed1 (fbandF bgd)); auto.
move/hasP=> [zd Hzd Hxzd]; move/connectP: Hxzd Hzd => [p Hp <-] {zd}.
elim: p xd Hp => [|yd p Hrec] xd /=.
  by move=> _ Hxd; apply: (subsetP (subset_closure _ _)); rewrite Ebgdr.
move/andP=> [Dxd Hp] Hzd.
case Hxd: (bgd xd); first by apply: (subsetP (subset_closure _ _)); rewrite Ebgdr.
rewrite /outer (fun b => closure_closed (Sface g) b (x := hd xd) (set11 _)).
rewrite -(EdF (negbI Hxd)) (eqP Dxd); exact (Hrec _ Hp Hzd).
Qed.

Remark Patch_adj_hd : fun_adjunction hd face face (setC outer).
Proof.
apply: (strict_adjunction (Sface _) closed_outerC Ihd).
  apply/subsetP => [x Hxn]; rewrite Ehd; apply/orP; left; apply/idP => [Hx].
  by case/set0Pn: Hxn; exists x; rewrite /setI connect0.
move=> xd yd; move/negbE2=> Hxd; rewrite /eqdf -EdF ?(inj_eqd Ihd) //.
rewrite /setC outer_hd in Hxd.
by apply/idP => [Hxd']; case/idP: Hxd; apply: (subsetP (ring_fband _)).
Qed.
Let adj_hd := Patch_adj_hd.

Lemma patch_face_d : forall xd yd, setC outer (hd xd) ->
  cface xd yd = cface (hd xd) (hd yd).
Proof. exact (rel_functor adj_hd). Qed.

Remark Patch_IhdF : forall xd, cface (hd xd) (hd (face xd)).
Proof.
move=> xd; case Hxd: (bgd xd); last by rewrite (EdF (negbI Hxd)) fconnect1.
case/connectP: (etrans (Sface _ _ _) (fconnect1 _ xd)) => [p].
elim: p (face xd) => [|yd' p Hrec] yd /=; first by move=> _ <-; apply connect0.
move=> Hyp Ep; move: (andP Hyp) => [Dyd Hp].
case Hyd: (bgd yd).
  rewrite -(scycle_cface Hbgd (x := yd) (y := xd)) ?connect0 //.
  by apply/connectP; exists (Adds yd' p).
apply: (connect_trans (Hrec _ Hp Ep)).
by rewrite Sface -(eqP Dyd) (EdF (negbI Hyd)) fconnect1.
Qed.
Let IhdF := Patch_IhdF.

Lemma patch_face_d' : forall xd yd, cface xd yd -> cface (hd xd) (hd yd).
Proof.
move=> xd yd; move/connectP=> [p Hp <-] {yd}.
elim: p xd Hp => [|yd p Hrec] xd /=; first by clear; apply: connect0.
move/andP=> [Dxd Hp].
by apply: (connect_trans _ (Hrec _ Hp)); rewrite -(eqP Dxd) IhdF.
Qed.

Lemma patch_face_r : forall xr yr, cface xr yr = cface (hr xr) (hr yr).
Proof.
move=> xr yr; apply/idP/idP.
  move/connectP=> [p Hp <-] {yr}.
  elim: p xr Hp => [|yr p Hrec] xr /=; first by clear; apply: connect0.
  move/andP=> [Dxr Hp]; apply: {p Hp Hrec}(connect_trans _ (Hrec _ Hp)).
  rewrite -{yr Dxr}(eqP Dxr).
  case Hfxr: (bgr (face xr)).
    case/HbgrP: Hfxr => [xd Dfxr _]; rewrite -Dfxr.
    move/(introT eqP): Dfxr => Dfxr; rewrite eqd_sym EdrF in Dfxr.
    by rewrite cface1 -(eqP Dfxr) Sface IhdF.
  by rewrite -(ErF (negbI Hfxr)) fconnect1.
set x := hr xr; move/connectP=> [p Hp Ep].
have Hhp: if codom hr x then x = hr xr else
          exists2 xd, x = hd xd & exists2 yd, hd yd = hr xr & cface yd xd.
  by rewrite /x codom_f.
elim: p {xr}x (xr) Hp Ep Hhp => [|z p Hrec] x xr /=.
  move=> _ Dx; rewrite Dx codom_f; move=> Dxr.
  by rewrite (Ihr Dxr) connect0.
case/andP; move/eqP=> Dz Hp Ep.
case Ihrx: (codom hr x).
  move=> Dx; apply: (connect_trans (fconnect1 face _)).
  apply: {Hp Ep Hrec}(Hrec _ _ Hp Ep); rewrite -{z}Dz.
  case Ihrfx: (codom hr (face x)).
  case Hfxr: (bgr (face xr)); last by rewrite -(ErF (negbI Hfxr)) Dx.
    case/HbgrP: Hfxr => [xd Dxd _]; rewrite -Dxd.
    have Dfxd := introT eqP Dxd; rewrite eqd_sym EdrF in Dfxd.
    rewrite Dx -(eqP Dfxd); congr hd; apply: (scycle_cface Hbgd).
    - by rewrite Sface fconnect1.
    - by rewrite -Ebgdr (eqP Dfxd) -Dx.
    by rewrite -Ebgdr Dxd codom_f.
  rewrite Ehr in Ihrfx; case/norP: Ihrfx; move/negbE2; case/set0Pn=> [xd].
  move/eqP=> Dfx; exists xd; first done.
  exists (edge (node xd)); last by rewrite -{2}[xd]Enode fconnect1.
  by apply: eqP; rewrite EdErN EdN -Dfx Dx -{1}[xr]Eface ErE Eedge set11.
move=> [xd Dxd [yd Dyd Hxyd]]; apply: {Hp Ep Hrec}(Hrec _ _ Hp Ep).
rewrite Ehr Dxd /setU /setC codom_f /bg (mem_maps Ihd) /= in Ihrx.
have Efxd := EdF (negbI Ihrx); rewrite -{z}Dz.
case Ihrfx: (codom hr (face x)).
  rewrite Dxd -Efxd -Dyd; congr hd; apply: (scycle_cface Hbgd).
  - by rewrite -cface1 Sface.
  - by rewrite -Ebgdr Efxd -Dxd.
  by rewrite -Ebgdr Dyd codom_f.
exists (face xd); first by rewrite Dxd.
by exists yd; last by rewrite -cface1r.
Qed.

Lemma patch_face_dr : forall xd, outer (hd xd) ->
 {yd : gd & {yr : gr | hd yd = hr yr /\ cface xd yd
                     & cface (hd xd) =1 cface (hr yr)}}.
Proof.
move=> xd Hxd; case/pickP: (setI (cface xd) bgd) => [yd Hyd|Hnxd].
  exists yd; case/andP: Hyd => [Hxyd Hyd].
  have Hyr: codom hr (hd yd).
    by rewrite Ehr /setU /bg (mem_maps Ihd) Hyd orbT.
  exists (iinv Hyr); rewrite f_iinv; first by split.
  exact (same_cface (patch_face_d' Hxyd)).
rewrite outer_hd in Hxd; case/hasPn: Hxd => [yd Hyd]; apply/idP => [Hxyd].
by case/andP: (Hnxd yd); split.
Qed.

Lemma patch_bridgeless : bridgeless g -> bridgeless gd /\ bridgeless gr.
Proof.
move=> Hgl; split.
  apply/set0P => [xd]; rewrite cface1r; apply/idP => [Hfexd].
  case/set0Pn: Hgl; exists (hd xd).
  by rewrite cface1r -{2}[xd]Eedge EdN Enode; apply patch_face_d'.
by apply/set0P => xr; rewrite patch_face_r ErE (set0P Hgl).
Qed.

Lemma bridgeless_patch :
  bridgeless gd -> bridgeless gr -> chordless bgd -> bridgeless g.
Proof.
move=> Hgdl Hgrl Hgdc; apply/set0P => x; apply/idP => [Hnex].
case Hx: (codom hr x).
  move/set0Pn: Hx => [xr Dx]; rewrite (eqP Dx) -ErE in Hnex.
  by case/set0Pn: Hgrl; exists xr; rewrite patch_face_r.
rewrite Ehr in Hx; case/norP: Hx; move/negbE2.
case/set0Pn=> [xd]; move/eqP=> Dx Hbx.
rewrite /bg Dx (mem_maps Ihd) in Hbx; rewrite Dx -(EdE Hbx) in Hnex.
case Hxr: (outer (hd xd));
 last by case/idP: (set0P Hgdl xd); rewrite patch_face_d // /setC Hxr.
have Hexr: outer (hd (edge xd)).
  apply: etrans Hxr; symmetry; apply: (closed_connect _ Hnex).
  apply: closure_closed; apply: Sface.
rewrite !outer_hd in Hxr Hexr; move/hasP: Hxr => [yd Hyd Hxyd].
move/hasP: Hexr => [zd Hzd Hexzd].
case/set0Pn: (subsetP Hgdc _ Hyd); exists zd.
apply/andP; split; first by apply/adjP; exists xd; first by rewrite Sface.
case/HbgdP: (Hyd) => [yr Dyr Dnyr]; rewrite /setD1 Hzd andbT.
case/andP: Hbgd => [Dbgd _].
apply/andP; split; apply/eqP => Dzd; case/set0Pn: Hgrl.
  exists (node yr); rewrite cface1r Enode.
  rewrite patch_face_r -Dnyr -Dyr (eqP (next_cycle Dbgd Hyd)) Dzd.
  apply: (connect_trans (connect_trans _ Hnex)); last exact: patch_face_d'.
  rewrite Sface; exact: patch_face_d'.
exists (node (node yr)); rewrite cface1r Enode.
have Dnnyr := introT eqP Dnyr; rewrite -{1}[yd]Eface EdErN in Dnnyr.
rewrite patch_face_r -Dnyr -(eqP Dnnyr) -{1}(eqP (prev_cycle Dbgd Hyd)).
rewrite Eedge Dzd Sface; apply: (connect_trans (connect_trans _ Hnex)).
  rewrite Sface; exact: patch_face_d'.
exact: patch_face_d'.
Qed.

Let ag := closure glink (codom hr).

Remark Patch_Hag : closed glink ag.
Proof. apply: (closure_closed (Sglink _)). Qed.
Let Hag := Patch_Hag.

Remark Patch_Hagr : n_comp glink gr = n_comp glink ag.
Proof.
have Hgg := Sglink g; have Hggr := Sglink gr.
rewrite (adjunction_n_comp hr Hgg Hggr Hag).
  apply: eq_card => [xr]; rewrite /setI /preimage /ag.
  by rewrite (subsetP (subset_closure (d := g) glink _) _ (codom_f hr xr)).
split.
  move=> x Hx; case: (pickP (setI (gcomp x) (codom hr))).
    by move=> y; move/andP=> [Hxy Hy]; exists (iinv Hy); rewrite f_iinv.
  by move=> Hnx; case/set0P: Hx.
move=> xr zr _; apply/idP/idP; rewrite -clink_glink.
  move/connectP=> [p Hp <-] {zr}.
  elim: p xr Hp => [|yr p Hrec] xr /=; first by rewrite connect0.
  move/andP=> [Hxr Hp]; apply: {Hrec Hp}(connect_trans _ (Hrec _ Hp)).
  have Hfzr: forall zr, gcomp (hr zr) (hr (face zr)).
    move=> zr; move: (fconnect1 face zr); rewrite patch_face_r.
    apply: {zr}connect_sub => [x y]; move/eqP => <-; exact (connect1 (glinkF _)).
  case/clinkP: Hxr => [Dxr|Dfxr]; last by rewrite -Dfxr Hfzr.
  by apply: (connect_trans (connect1 (glinkE _))); rewrite -[yr]Enode -Dxr -ErE.
set x := hr xr; move/connectP=> [p Hp Ep].
have Hxr: if codom hr x then x = hr xr else bgr xr by rewrite /x codom_f.
elim: p {xr}x (xr) Hp Ep Hxr => [|y p Hrec] x xr /=.
  move=> _ Dx; rewrite Dx codom_f; move=> Dxr.
  by rewrite (Ihr Dxr) connect0.
move/andP=> [Hxy Hp] Ep.
case Hyd: (codom hd y).
  have Hbzr: forall yr, bgr yr -> gcomp yr zr.
    move{x xr Hxy} => xr Hxr.
    case Hyr: (codom hr y) {Hrec Hp Ep}(Hrec y _ Hp Ep); last by auto.
    rewrite Ehd /setU /setC {}Hyr -Ebgr in Hyd; move/mapsP: Hyd => [yr Hyr Dy].
    move=> Hrec; apply: connect_trans _ {Hrec Dy}(Hrec _ (esym Dy)).
    rewrite -{Hxr}(EbgrN Hxr) in Hyr; apply: connect_sub xr yr Hyr => xr yr.
    by move/eqP=> Dyr; apply connect1; rewrite -Dyr glinkN.
  case (codom hr x); [ move=> Dx | by auto ]; rewrite {x}Dx in Hxy.
  case/clinkP: Hxy => [Dxrn|Dfxr].
    by apply Hbzr; rewrite -Ebgrd Dxrn -(f_iinv Hyd) -EdN codom_f.
  apply: (connect_trans (connect1 (glinkF _))); apply: Hbzr.
  apply/idPn => [Hfxr]; rewrite (ErF Hfxr) in Dfxr.
  by rewrite -Ebgrd Dfxr Hyd in Hfxr.
rewrite Ehd in Hyd; case/norP: Hyd; move/negbE2; case/set0Pn=> [yr].
move/eqP=> Dy Hyr; rewrite Dy -Ebgr (mem_maps Ihr) in Hyr; move=> Hx.
apply: {Hp Ep Hrec}(connect_trans _ (Hrec _ yr Hp Ep _));
  last by rewrite Dy codom_f.
rewrite -clink_glink; apply connect1.
case/clinkP: Hxy => [Dny|Dfx].
  rewrite Dy -(ErN Hyr) in Dny; rewrite Dny codom_f in Hx.
  by rewrite -(Ihr Hx) clinkN.
rewrite -{1}[y]Enode Dy -(ErN Hyr) -ErE in Dfx.
rewrite (Iface _ Dfx) codom_f in Hx.
by rewrite -{1}[yr]Enode (Ihr Hx) clinkF.
Qed.
Let Hagr := Patch_Hagr.

Lemma patch_connected_r : connected g -> negb (set0b gr) -> connected gr.
Proof.
move=> Hcg Hgr; rewrite /connected Hagr -(eq_n_comp_r (a := g)) //.
case/set0Pn: Hgr => [xr _] y; symmetry; apply/set0Pn.
exists (hr xr); rewrite /setI codom_f andbT -clink_glink.
apply/connectP; apply: (connected_clink Hcg).
Qed.

Lemma patch_fcard_face_r : fcard face gr = fcard face outer.
Proof.
rewrite /= (adjunction_n_comp hr (Sface _) (Sface _) closed_outer).
  apply: eq_card => [xr]; rewrite /setI /preimage andbC /outer.
  by rewrite (subsetP (subset_closure (eqdf face) (codom hr))) ?codom_f ?andbT.
split; last by move=> *; apply: patch_face_r.
move=> x Hx; case: (pickP (setI (cface x) (codom hr))).
  by move=> y; move/andP=> [Hxy Hy]; exists (iinv Hy); rewrite f_iinv.
by move=> Hnxr; case/set0P: Hx.
Qed.

Lemma genus_patch : genus g = genus gd + genus gr.
Proof.
pose ebg := size bg =d 0.
have Hebgd: if ebg then bgd = seq0 else exists xd, bgd xd.
  by rewrite /ebg /bg; case: bgd => [|x p] //; exists x; rewrite /= setU11.
have Hebgr: if ebg then bgr = seq0 else exists xr, bgr xr.
  rewrite /ebg -size_rev -Dbgr; case: bgr => [|x p] //.
  by exists x; rewrite /= setU11.
have HcdE: fcard edge gd = negb ebg + fcard edge (setC (codom hr)).
  rewrite (n_compC bgd); congr addn.
    case: (ebg) Hebgd; [ move=>Dbgd | move=> [x Hx] ].
      by apply: eq_card0 => [x]; rewrite Dbgd /= /setI andbF.
    rewrite -(eq_n_comp_r (EbgdE Hx)); apply: (n_comp_connect (Sedge _)).
  have closed_grC := setC_closed closed_gr.
  rewrite (adjunction_n_comp hd (Sedge _) (Sedge _) closed_grC).
    apply: eq_n_comp_r => [x]; congr negb.
    by rewrite Ehr /setU /setC codom_f /= /bg (mem_maps Ihd).
  apply (strict_adjunction (Sedge _) closed_grC Ihd).
    apply/subsetP => [x Hx]; rewrite /setC Ehr in Hx.
    by case/norP: Hx; rewrite /setC negb_elim.
  move=> xd yd; rewrite /setC Ehr /setU /setC codom_f /= /bg (mem_maps Ihd).
  by move/negbE2=> Hxd; rewrite /eqdf /= -(EdE Hxd) (inj_eqd Ihd).
have HcdF: fcard face gd = size bg + fcard face (setC outer).
  rewrite patch_fcard_face_d; congr addn.
  rewrite (adjunction_n_comp _ (Sface _) (Sface _) closed_outerC adj_hd).
  by apply: eq_card => [xd]; rewrite /setI /setC -outer_hd.
have HcdN: fcard node gd = fcard node (codom hd).
  rewrite (adjunction_n_comp hd (Snode _) (Snode _) closed_gd).
    by apply: eq_card => [xd]; rewrite /setI /preimage codom_f.
  apply: (strict_adjunction (Snode _) closed_gd Ihd (subset_refl _)) => xd yd _.
  by rewrite /eqdf -EdN (inj_eqd Ihd).
have HcdG: n_comp glink gd = negb ebg + n_comp glink (setC ag).
  have Hgg := (Sglink g); have Hggd := (Sglink gd).
  have Eggd: forall x y, setC bgd x -> glink (hd x) (hd y) = glink x y.
    move=> x y Hx; rewrite {1}/glink /relU /setU /eqdf.
    by rewrite -(EdE Hx) -EdN -(EdF Hx) !(inj_eqd Ihd).
  have HagC := setC_closed Hag.
  have Hhdg: rel_adjunction hd glink glink (setC ag).
    apply (strict_adjunction Hggd HagC Ihd).
    apply/subsetP => [x Hxn]; case/orP: (EhdUr x) => // Hx.
      by case/idP: Hxn; apply: (subsetP (subset_closure _ _)).
    move=> xd yd; move/negbE2=> Hx; apply Eggd; apply/idP => Hxd; case/idP: Hx.
    by apply: (subsetP (subset_closure _ _)); rewrite Ebgdr.
  rewrite (adjunction_n_comp hd Hgg Hggd HagC Hhdg).
  rewrite (n_compC (preimage hd ag)); congr addn.
  case: (ebg) Hebgd; [ move=> Dbgd | move=> [x Hx] ].
    apply: eq_card0 => x; apply/nandP; right; apply/set0Pn; case=> y Hy.
    case/andP: Hy; rewrite -clink_glink; move/connectP=> [p Hp <-] {y}.
    elim: p x Hp => [|y p Hrec] xd; first by rewrite /= Ebgdr Dbgd.
    case/andP; move/clinkP=> [Dx|Dy].
      rewrite -{1}[xd]Eedge EdN in Dx; rewrite -(Inode g Dx); eauto.
    by rewrite -Dy -EdF ?Dbgd; eauto.
  apply: etrans (n_comp_connect Hggd x); apply: eq_n_comp_r => y.
  rewrite /preimage /ag; apply/set0Pn/idP.
    case=> z; case/andP; rewrite -clink_glink; move/connectP=> [p Hp <-] {z}.
    elim: p y Hp => [|z p Hrec] y /=.
      clear; rewrite Ebgdr -{Hx}(EbgdE Hx); apply: connect_sub x y => x y.
      by case/eqP=> <-; apply connect1; rewrite glinkE.
    case/andP; move/clinkP=> [Dy|Dz].
      rewrite -{1}[y]Eedge EdN in Dy; rewrite -(Inode g Dy).
      move=> Hq Eq; apply: {Hrec Hq Eq}(connect_trans (Hrec _ Hq Eq)).
      by apply connect1; rewrite -{2}[y]Eedge glinkN.
    case Hy: (bgd y).
      move=> _ _ {q z Hrec Dz}; rewrite -(EbgdE Hx) in Hy.
      apply: connect_sub x y Hy {Hx} => x y; case/eqP=> <-; apply connect1.
      by rewrite glinkE.
    rewrite -(EdF (negbI Hy)) in Dz; rewrite -Dz.
    move=> Hq Eq; apply: {Hrec Hq Eq}(connect_trans (Hrec _ Hq Eq)).
    by rewrite Hggd connect1 ?glinkF.
  rewrite Hggd; move/connectP=> [p Hp Dx]; move: Dx Hx => <- {x}.
  elim: p y Hp => [|y p Hrec] x /=.
    by move=> _ Hx; exists (hd x); rewrite /setI connect0 Ebgdr.
  case Hx: (bgd x).
    by do 2 clear; exists (hd x); rewrite /setI connect0 Ebgdr.
  move/andP=> [Hxy Hp] Ep.
  case: {p Hrec Hp Ep}(Hrec _ Hp Ep) => [z Hz]; exists z.
  rewrite -(Eggd x y (negbI Hx)) in Hxy.
  by rewrite /setI (same_connect Hgg (connect1 Hxy)).
have HcrE: fcard edge gr = fcard edge (codom hr).
  rewrite (adjunction_n_comp hr (Sedge _) (Sedge _) closed_gr).
    by apply: eq_card => [z]; rewrite /setI /preimage codom_f.
  apply (strict_adjunction (Sedge _) closed_gr Ihr (subset_refl _)).
  by move=> xr yr _; rewrite {1}/eqdf -ErE (inj_eqd Ihr).
have HcrN: fcard node gr = negb ebg + fcard node (setC (codom hd)).
  have HafC := setC_closed closed_gd.
  rewrite (adjunction_n_comp hr (Snode _) (Snode _) HafC).
    rewrite (n_compC (fun x => codom hd (hr x))); congr addn.
    case: (ebg) Hebgr; [ move=> Dbgr0 | move=> [x Hx] ].
      by apply: eq_card0 => [x]; rewrite /setI Ebgrd Dbgr0 andbF.
      apply: etrans (n_comp_connect (Snode _) x); apply: eq_n_comp_r => y.
    by rewrite Ebgrd (EbgrN Hx).
  apply (strict_adjunction (Snode _) HafC Ihr).
    apply/subsetP => [x]; rewrite /setC Ehd /setC.
    by case/norP; rewrite negb_elim.
  move=> xr yr; rewrite /setC Ebgrd /eqdf; move/negbE2=> Hxr.
  by rewrite -(ErN Hxr) (inj_eqd Ihr).
rewrite {1}/genus -(subn_add2l (genus_lhs gd + genus_lhs gr)).
rewrite addnC {1 4 5}/genus_lhs !even_genusP /genus_rhs.
rewrite (n_compC ag) (n_compC (codom hr)) (n_compC (codom hd)) (n_compC outer).
rewrite HcdE HcdF -HcdN HcdG -HcrE -patch_fcard_face_r HcrN -Hagr !double_add.
rewrite -!addnA (double_addnn (negb ebg)) (addnCA (card gd)).
rewrite (addnA (card gd)) card_patch -!addnA -!(addnCA (negb ebg)).
rewrite !subn_add2l addnCA !subn_add2l -(addnCA (card g)) subn_add2l addnC.
rewrite -!addnA !(addnCA (double (genus gr))) -double_add.
do 2 rewrite addnA addnCA subn_add2l; rewrite -!addnA !subn_add2l.
by do 2 rewrite addnCA subn_add2l; rewrite subn_addr half_double addnC.
Qed.

Lemma planar_patch : planar g = planarb gd && planarb gr.
Proof. by PropCongr; rewrite genus_patch eqn_add0. Qed.

Lemma colorable_patch :
  four_colorable g <->
    (exists2 et, ring_trace bgd et & ring_trace bgr (rot 1 (rev et))).
Proof.
split.
  move=> [k [HkE HkF]]; exists (trace (maps k bg)).
    exists (comp k hd); last by rewrite (maps_comp k hd).
    have Hk'F: (invariant face (comp k hd) =1 gd).
      move=> x; apply/eqcP; apply: (fconnect_invariant HkF); apply patch_face_d'.
      by rewrite Sface fconnect1.
    split; last done; move=> xd; rewrite /invariant -{2}[xd]Eedge.
    rewrite -(eqcP (Hk'F (edge xd))) /comp EdN; set y := hd (face (edge xd)).
    rewrite -{1}[y]Enode (eqcP (HkF (edge (node y)))); apply: HkE.
  exists (comp k hr); last by rewrite -trace_rev -maps_rev -Dbgr -maps_comp.
  split; first by move=> x; rewrite /invariant /comp ErE; apply: HkE.
  move=> x; apply/eqcP; apply: (fconnect_invariant HkF).
  by rewrite -patch_face_r Sface fconnect1.
move=> [et [kd [HkdE HkdF] Ekd] [kr [HkrE HkrF] Ekr]]; simpl in Ekd, Ekr.
pose c0 := head_color (maps kd (rev bgd)) +c head_color (maps kr bgr).
pose kd' := comp (addc c0) kd.
have Ic0 := monic_inj (addc_inv c0 : monic _ (addc c0)).
have Hkd'E: invariant edge kd' =1 set0.
  by move=> x; rewrite -(HkdE x); apply: invariant_inj.
have Hkd'F: invariant face kd' =1 gd.
  by move=> x; rewrite -(HkdF x); apply: invariant_inj.
have Ebkd'r: rev (maps kd' bgd) = maps kr bgr.
  move: Ekr; rewrite Ekd -trace_rev -!maps_rev /kd' (maps_comp (addc c0) kd) /c0.
  case: (rev bgd) => [|xd bgd']; first by case: bgr; move=> // xr; case.
  case: bgr => [|xr bgr'] Ekdr; first by case: bgd' Ekdr.
  rewrite /= -untrace_trace -maps_adds trace_addc addcC addc_inv.
  by rewrite -maps_adds Ekdr maps_adds untrace_trace.
move: {kd c0}kd' Hkd'E Hkd'F Ebkd'r {Ic0 HkdE HkdF Ekd Ekr} => kd HkdE HkdF Ebkdr.
have Ekdr: forall xd xr, hd xd = hr xr -> kd xd = kr xr.
  move=> xd xr Dx; have Hxd: bgd xd by rewrite -Ebgdr Dx codom_f.
  have Hxr: rev bgr xr by rewrite mem_rev -Ebgrd -Dx codom_f.
  rewrite -(sub_index xd Hxd) -(sub_index xr Hxr).
  rewrite -index_mem in Hxd; rewrite -index_mem in Hxr.
  rewrite -(sub_maps xr Color0) // maps_rev -Ebkdr rev_rev.
  rewrite -(sub_maps xd Color0) //; congr (sub Color0).
  by rewrite -(index_maps Ihd) -(index_maps Ihr) maps_rev Dbgr rev_rev Dx.
pose dhd := _ =d hd _; pose dhr := _ =d hr _.
pose k x := if pick (dhr x) is Some xr then kr xr else
            if pick (dhd x) is Some xd then kd xd else Color0.
have Hkk := introT set0P.
have HkF: invariant face k =1 g.
  move=> x; rewrite /invariant /k /setA; apply/eqP.
  case: (pickP (dhr x)) => [xr Dx|Hxr].
    case: (pickP (dhr (face x))) => [yr Dy|Hyr].
      apply: (fconnect_invariant HkrF).
      by rewrite patch_face_r -(eqP Dx) -(eqP Dy) Sface fconnect1.
    case: (pickP (dhd (face x))) => [yd Dy|Hyd].
      rewrite (eqP Dx) /dhd -{1}[yd]Enode eqd_sym -EdrF in Dy.
      rewrite -(eqcP (HkrF xr)) -{1}[yd]Enode (eqcP (HkdF _)).
      by apply: Ekdr; rewrite -(eqP Dy).
    by move: (EhdUr (face x)); rewrite /setU /codom !Hkk.
  case: (pickP (dhd x)) => [xd Dx|Hxd].
    have Hxd: negb (bgd xd) by rewrite -Ebgdr /codom Hkk -?(eqP Dx).
    rewrite -(eqcP (HkdF xd)) (eqP Dx) -(EdF Hxd).
    case: (pickP (dhr (hd (face xd)))) => [yr Dy|Hyr].
      by symmetry; apply: Ekdr; move/eqP: Dy => <-.
    case: (pickP (dhd (hd (face xd)))) => [yd Dy|Hyd].
      by rewrite (Ihd (eqP Dy)).
    by case/eqP: (Hyd (face xd)).
  by move: (EhdUr x); rewrite /setU /codom !Hkk.
exists k; split; last done; move=> x; rewrite /invariant /k.
 case: (pickP (dhr x)) => [xr Dx|Hxr].
  rewrite (eqP Dx) -ErE.
  case: (pickP (dhr (hr (edge xr)))) => [yr Dy|Hyr].
    rewrite -(Ihr (eqP Dy)); exact: HkrE.
  by case/eqP: (Hyr (edge xr)).
case: (pickP (dhd x)) => [xd Dx|Hxd].
  have Hxd: negb (bgd xd) by rewrite -Ebgdr /codom Hkk -?(eqP Dx).
  have HxdE := HkdE xd; rewrite (eqP Dx) -(EdE Hxd).
  case: (pickP (dhr (hd (edge xd)))) => [yr Dy|Hyr].
    by rewrite -(Ekdr _ _ (eqP Dy)).
  case: (pickP (dhd (hd (edge xd)))) => [yd Dy|Hyd].
    by rewrite -(Ihd (eqP Dy)).
  by case/eqP: (Hyd (edge xd)).
by move: (EhdUr x); rewrite /setU /codom !Hkk.
Qed.

End Patch.

(* Patching disjoint components of the map along empty borders. Used to *)
(* show that the minimal counter example is connected.                  *)

Section PatchGcomp.

Variables (g : hypermap) (z : g).

Definition gcompd_dart : finSet := subFin (gcomp z).

Remark Hgcompd_edge : forall u : gcompd_dart, gcomp z (edge (subdE u)).
Proof. by move=> [x Hx]; exact (connect_trans Hx (connect1 (glinkE _))). Qed.

Remark Hgcompd_node : forall u : gcompd_dart, gcomp z (node (subdE u)).
Proof. by move=> [x Hx]; exact (connect_trans Hx (connect1 (glinkN _))). Qed.

Remark Hgcompd_face : forall u : gcompd_dart, gcomp z (face (subdE u)).
Proof. by move=> [x Hx]; exact (connect_trans Hx (connect1 (glinkF _))). Qed.

Definition gcompd_edge u : gcompd_dart := subdI (Hgcompd_edge u).
Definition gcompd_node u : gcompd_dart := subdI (Hgcompd_node u).
Definition gcompd_face u : gcompd_dart := subdI (Hgcompd_face u).

Remark gcompd_monic : monic3 gcompd_edge gcompd_node gcompd_face.
Proof. move=> [x Hx]; apply: subdE_inj; apply: Eedge. Qed.

Definition gcomp_disk := Hypermap gcompd_monic.
Definition gcompd (u : gcomp_disk) := subdE u.

Lemma inj_gcompd : injective gcompd. Proof. apply: subdE_inj. Qed.
Lemma codom_gcompd : codom gcompd =1 gcomp z.
Proof.
move=> x; apply/set0Pn/idP => [[[y Hy] Dy]|Hx]; first by rewrite (eqP Dy).
exists (subdI Hx : gcomp_disk); apply: set11.
Qed.

Definition gcompr_dart : finSet := subFin (setC (gcomp z)).

Remark gcompr_edgeP : forall u : gcompr_dart, setC (gcomp z) (edge (subdE u)).
Proof.
move=> [x Hx]; apply/idP => /= [Hx']; case/idP: Hx.
apply: (connect_trans Hx'); rewrite Sglink /=; apply connect1; exact: glinkE.
Qed.

Remark gcompr_nodeP : forall u : gcompr_dart, setC (gcomp z) (node (subdE u)).
Proof.
move=> [x Hx]; apply/idP => /= [Hx']; case/idP: Hx.
apply: (connect_trans Hx'); rewrite Sglink /=; apply connect1; exact: glinkN.
Qed.

Remark gcompr_faceP : forall u : gcompr_dart, setC (gcomp z) (face (subdE u)).
Proof.
move=> [x Hx]; apply/idP => /= [Hx']; case/idP: Hx.
apply: (connect_trans Hx'); rewrite Sglink /=; apply connect1; exact: glinkF.
Qed.

Definition gcompr_edge u : gcompr_dart := subdI (gcompr_edgeP u).
Definition gcompr_node u : gcompr_dart := subdI (gcompr_nodeP u).
Definition gcompr_face u : gcompr_dart := subdI (gcompr_faceP u).

Remark gcompr_monic : monic3 gcompr_edge gcompr_node gcompr_face.
Proof. move=> [x Hx]; apply: subdE_inj; exact: Eedge. Qed.

Definition gcomp_rem := Hypermap gcompr_monic.
Definition gcompr (u : gcomp_rem) := subdE u.
Lemma inj_gcompr : injective gcompr. Proof. apply: subdE_inj. Qed.
Lemma codom_gcompr : codom gcompr =1 setC (gcomp z).
Proof.
move=> x; apply/set0Pn/idP => [[[y Hy] Dy]|Hx]; first by rewrite (eqP Dy).
exists (subdI Hx : gcomp_rem); exact: set11.
Qed.

Lemma patch_gcomp : patch gcompd gcompr seq0 seq0.
Proof.
repeat split; try done; try apply inj_gcompd; try apply inj_gcompr.
by move=> x; rewrite /setU /setC /= orbF codom_gcompd codom_gcompr.
Qed.

End PatchGcomp.

Lemma minimal_counter_example_is_connected : forall g,
  minimal_counter_example g -> connected g.
Proof.
move=> g Hg; apply/idPn => Hcg; case (minimal_counter_example_is_noncolorable Hg).
case: (pickP g) => [z _|Hg0];
  last by exists (fun _ : g => Color0); split; move=> x; move: (Hg0 x).
have Hpgdr := patch_gcomp z; have Hpg := Hg : planar g.
rewrite (planar_patch Hpgdr) in Hpg; move/andP: Hpg => [Hpgd Hpgr].
case: (patch_bridgeless Hpgdr Hg) => [Hgbd Hgbr].
have HgE := Hg : plain g; have HgN := Hg : cubic g.
rewrite (plain_patch Hpgdr) in HgE; move/andP: HgE => [HgdE HgrE].
rewrite (cubic_patch Hpgdr) in HgN; case/andP: HgN.
move/cubic_precubic=> HgdN; move/cubic_precubic=> HgrN.
have Hng := card_patch Hpgdr; rewrite /= add0n in Hng.
have Hmg := minimal_counter_example_is_minimal Hg.
case: (colorable_patch Hpgdr) => _; apply; exists (seq0 : colseq).
  case: (Hmg (gcomp_disk z)); try solve [repeat split; auto];
    last by move=> kd Hkd; exists kd.
  rewrite -addn1 -Hng /= leq_add2l ltnNge leqn0.
  apply/eqP => Hgr; case/eqnP: Hcg; rewrite -(n_comp_connect (Sglink _) z).
  apply: eq_n_comp_r => x; symmetry.
  exact (negbEf (set0P (introT eqP (etrans (esym (card_sub_dom _)) Hgr)) x)).
case: (Hmg (gcomp_rem z)); try solve [repeat split; auto];
  last by move=> kr Hkr; exists kr.
rewrite -add1n -Hng leq_add2r ltnNge leqn0; apply/eqP => [Hgd].
case/idP: (card0_eq (etrans (esym (card_sub_dom _)) Hgd) z); apply: connect0.
Qed.

Coercion minimal_counter_example_is_connected :
  minimal_counter_example >-> connected.

Definition minimal_counter_example_is_planar_bridgeless_plain_connected :
  forall g, minimal_counter_example g -> planar_bridgeless_plain_connected g.
move=> g Hg; split; exact Hg.
Defined.

Coercion minimal_counter_example_is_planar_bridgeless_plain_connected :
 minimal_counter_example >-> planar_bridgeless_plain_connected.

Definition minimal_counter_example_is_planar_plain_cubic_connected :
 forall g, minimal_counter_example g -> planar_plain_cubic_connected g.
repeat move=> g Hg; repeat split; exact Hg.
Defined.

Coercion minimal_counter_example_is_planar_plain_cubic_connected :
  minimal_counter_example >-> planar_plain_cubic_connected.

Unset Implicit Arguments.
