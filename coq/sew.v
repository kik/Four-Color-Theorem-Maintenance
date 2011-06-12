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
Require Import color.
Require Import geometry.
Require Import patch.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Sew.

Variables (gd gr : hypermap) (bgd : seq gd) (bgr : seq gr).

Hypothesis Hbgd : sfcycle edge bgd.
Hypothesis Hbgr : ufcycle node bgr.
Hypothesis Hrs : size bgd = size bgr.

Lemma HbgdE : forall xd, bgd xd -> cedge xd =1 bgd.
Proof. by move=> *; apply fconnect_cycle; case (andP Hbgd). Qed.

Lemma HbgdE1 : forall xd, bgd (edge xd) -> bgd xd.
Proof. by move=> xd Hxd; rewrite -(HbgdE Hxd) Sedge fconnect1. Qed.

Lemma HbgrN : forall xr, bgr xr -> cnode xr =1 bgr.
Proof. by move=> *; apply fconnect_cycle; case (andP Hbgr). Qed.

Lemma HbgrN1 : forall xr, bgr (node xr) -> bgr xr.
Proof. by move=> xr Hxr; rewrite -(HbgrN Hxr) Snode fconnect1. Qed.

Remark in_bgd : forall xd, {xr0 : gr | bgd xd} + {setC bgd xd}.
Proof.
move=> xd; rewrite /setC; case Hxd: (bgd xd); [ left | by right ].
by case: bgr Hxd Hrs => [|xr0 pr]; [ case bgd | exists xr0 ].
Qed.

Remark in_bgr : forall xr, {xd0 : gd | bgr xr} + {setC bgr xr}.
Proof.
move=> xr; rewrite /setC; case Hxr: (bgr xr); [ left | by right ].
by case: bgd Hxr Hrs => [|xd0 pd]; [ case bgr | exists xd0 ].
Qed.

Let hdr xr0 xd := sub xr0 (rev bgr) (index xd bgd).

Let hrd xd0 xr := sub xd0 bgd (index xr (rev bgr)).

Remark bgr_hdr : forall xd,  bgd xd -> forall xr0, bgr (hdr xr0 xd).
Proof.
by move=> *; rewrite /hdr -mem_rev mem_sub // size_rev -Hrs index_mem.
Qed.

Remark bgd_hrd : forall xr, bgr xr -> forall xd0, bgd (hrd xd0 xr).
Proof.
by move=> *; rewrite /hrd mem_sub // Hrs -size_rev index_mem mem_rev.
Qed.

Remark hrd_hdr : forall xd, bgd xd -> forall xd0 xr0, hrd xd0 (hdr xr0 xd) = xd.
Proof.
move=> xd Hxd xd0 xr0; rewrite /hrd /hdr index_uniq ?sub_index //.
  by rewrite size_rev -Hrs index_mem.
by rewrite uniq_rev; case: (andP Hbgr).
Qed.

Remark hdr_hrd : forall xr, bgr xr -> forall xd0 xr0, hdr xr0 (hrd xd0 xr) = xr.
Proof.
move=> xr Hxr xd0 xr0; rewrite /hrd /hdr index_uniq ?sub_index ?mem_rev //.
  by rewrite Hrs -size_rev index_mem mem_rev.
by apply simple_uniq; case: (andP Hbgd).
Qed.

Remark node_hdr : forall xd, bgd xd ->
  forall xr0, node (hdr xr0 xd) = hdr xr0 (node (face xd)).
Proof.
case: (andP Hbgd) (andP Hbgr) => [HdE Ud] [HrN Ur] xd Hxd xr0.
move/simple_uniq: Ud => Ud; set xr := hdr xr0 xd.
have Hxr: bgr xr by rewrite /xr bgr_hdr.
rewrite -(eqP (prev_cycle HdE Hxd)) Eedge (eqP (next_cycle HrN Hxr)).
rewrite -(rev_rev bgr) next_rev ?uniq_rev // !prev_sub Hxd mem_rev Hxr.
case Dbgr: {1}(rev bgr) => [|xr1 bgr']; first by rewrite -mem_rev Dbgr in Hxr.
rewrite /xr {1}/hdr.
case Dbgd: {1 2}bgd => [|xd1 bgd'] /=; first by rewrite Dbgd in Hxd.
set i := index xd bgd'.
have Hi: i < size bgd by rewrite Dbgd /= ltnS /i index_size.
rewrite /hdr index_uniq //; rewrite Hrs -size_rev in Hi.
apply: (etrans (congr1 (sub _ _) _) (set_sub_default Hi _ _)).
rewrite -uniq_rev Dbgr /= in Ur; case/andP: Ur => [Hxr1' Ur'].
rewrite Dbgd /= in Ud; case/andP: Ud => [Hxd1' _].
have Hrs' := Hrs; rewrite Dbgd -(size_rev bgr) Dbgr /= in Hrs'.
move: Hrs' => [Hrs'].
rewrite Dbgd /= /setU1 eqd_sym in Hxd; case Hxd1: (xd =d xd1) Hxd.
  rewrite Dbgr /= /i -(cats0 bgr') -(cats0 bgd') !index_cat /= !addn0.
  by clear; rewrite (eqP Hxd1) (negbE Hxr1') (negbE Hxd1').
by rewrite Dbgr /= -index_mem; move=> *; rewrite index_uniq // -Hrs'.
Qed.

Remark edge_hrd : forall xr, bgr xr -> forall xd0,
  edge (hrd xd0 xr) = hrd xd0 (face (edge xr)).
Proof.
move=> xr Hxr xd0; set yr := face (edge xr).
have Hyr: bgr yr by apply HbgrN1; rewrite /yr Eedge.
rewrite -{1}[xr]Eedge -/yr -{1}(hdr_hrd Hyr xd0 xr).
set yd := hrd xd0 yr; have Hyd: bgd yd by rewrite /yd bgd_hrd.
by rewrite node_hdr // hrd_hdr ?Eface // HbgdE1 ?Eface.
Qed.

Inductive sew_tag : Set :=
  | SewDisk : sew_tag
  | SewRest : sew_tag.

Definition sew_tag_eq pt1 pt2 : bool :=
  match pt1, pt2 with
  | SewDisk, SewDisk => true
  | SewRest, SewRest => true
  | _, _ => false
  end.

Definition sew_tag_data : dataSet.
apply (@DataSet _ sew_tag_eq); abstract by do 2 case; constructor.
Defined.
Canonical Structure sew_tag_data.

Definition sew_tag_set : finSet.
apply (@FinSet _ (Seq SewDisk SewRest)); abstract by case.
Defined.
Canonical Structure sew_tag_set.
Notation ptag := sew_tag_set (only parsing).

Let sew_sub_map (i : sew_tag_set) : finSet :=
  match i with
  | SewDisk => gd
  | SewRest => subFin (setC bgr)
  end.

Definition sew_dart := sumFin sew_sub_map.

Definition sewd xd : sew_dart := @sumdI _ sew_sub_map SewDisk xd.

Definition sewr_r xr Hxr : sew_dart :=
  @sumdI _ sew_sub_map SewRest (@subdI _ _ xr Hxr).

Definition sewr xr :=
  match in_bgr xr with
  | inleft u => let (xd0, _) := u in sewd (hrd xd0 xr)
  | inright Hxr => sewr_r Hxr
  end.

Lemma inj_sewd : injective sewd.
Proof.
move=> xd yd; move/(introT eqP); rewrite /sewd /= sumd_eqdr; exact (xd =P yd).
Qed.

Lemma inj_sewr : injective sewr.
Proof.
move=> xr yr; move/(introT eqP); rewrite /sewr.
case: (in_bgr xr) (in_bgr yr) => [[xd0 Hxr]|Hxr] [[xd1 Hyr]|Hyr] //=.
  by move=> Hxy; rewrite -(hdr_hrd Hxr xd0 xr) (inj_sewd (eqP Hxy)) hdr_hrd.
rewrite /sewr_r sumd_eqdr /eqd /=; exact (xr =P yr).
Qed.

Remark sewr_bgr : forall xd0 xr, bgr xr -> sewr xr = sewd (hrd xd0 xr).
Proof.
move=> xd0 xr Hxr; rewrite /sewr; case: (in_bgr xr) => [[xd1 _]|Hxr'].
  by rewrite -{1}(hdr_hrd Hxr xd0 xr) hrd_hdr ?bgd_hrd.
by case/idP: Hxr'.
Qed.

Remark sewr_gr : forall xr Hxr, sewr xr = @sewr_r xr Hxr.
Proof.
move=> xr Hxr; rewrite /sewr.
case: (in_bgr xr) => [[xd0 Hxr']|Hxr']; first by rewrite (negbE Hxr) in Hxr'.
by rewrite (bool_eqT Hxr Hxr').
Qed.

Remark sewr_hdr : forall xd, bgd xd -> forall xr0, sewr (hdr xr0 xd) = sewd xd.
Proof. by move=> xd Hxd xr0; rewrite (sewr_bgr xd) ?hrd_hdr ?bgr_hdr. Qed.

Definition sew_edge (w : sew_dart) : sew_dart :=
  match w with
  | sumdI SewDisk xd =>
    if in_bgd xd is inleft (exist xr _) then sewr (edge (hdr xr xd)) else
    sewd (edge xd)
  | sumdI SewRest ur =>
    let (xr, _) := ur in sewr (edge xr)
  end.

Definition sew_face_r (xr : gr) : sew_dart :=
  match sewr (face xr) with
  | sumdI SewDisk xd => sewd (face xd)
  | ufr => ufr
  end.

Definition sew_face (w : sew_dart) : sew_dart :=
  match w with
  | sumdI SewDisk xd =>
    if in_bgd xd is inleft (exist xr _) then sew_face_r (hdr xr xd) else
    sewd (face xd)
  | sumdI SewRest ur =>
    let (xr, _) := ur in sew_face_r xr
  end.

Definition sew_node (w : sew_dart) : sew_dart :=
  match w with
  | sumdI SewDisk xd => sewd (node xd)
  | sumdI SewRest ur => let (xr, _) := ur in sewr (node xr)
  end.

Lemma Esew_map : monic3 sew_edge sew_node sew_face.
Proof.
move=> [[|] xd]; [ simpl | case: xd => [xr Hxr] /= ].
  case: (in_bgd xd) => [[xr0 Hxd]|Hxd] /=.
    set exr := edge (hdr xr0 xd); transitivity (sew_node (sew_face_r exr)).
    rewrite /sewr; case: (in_bgr exr) => [[xd0 Hexr]|Hexr] //=.
    case: (in_bgd (hrd xd0 exr)); last by rewrite /setC bgd_hrd.
      by move=> [xr1 _]; rewrite /= hdr_hrd.
    rewrite /= /sew_face_r (sewr_bgr xd) /=.
      by rewrite /exr -edge_hrd ?bgr_hdr // Eedge (hrd_hdr Hxd).
    by apply HbgrN1; rewrite /exr Eedge bgr_hdr.
    case: (in_bgd (edge xd)) => [[xr0 Hexd]|Hexd]; rewrite /= ?Eedge //.
  by case (negP Hxd); apply HbgdE1.
transitivity (sew_node (sew_face_r (edge xr))).
rewrite /sewr; case: (in_bgr (edge xr)) => [[xd0 Hexr]|Hexr] //=.
  case: (in_bgd _) => [[xr0 Hexd]|Hexd] /=; first by rewrite hdr_hrd.
  by rewrite /setC bgd_hrd in Hexd.
have Hfexr: setC bgr (face (edge xr)).
  apply/idP => [Hfexr]; case/idP: Hxr.
  by rewrite -{1}[xr]Eedge -(HbgrN Hfexr) fconnect1.
by rewrite /sew_face_r (sewr_gr Hfexr) /= Eedge (sewr_gr Hxr).
Qed.

Definition sew_map := Hypermap Esew_map.

Lemma sewr_rev_sewd : maps sewr bgr = rev (maps sewd bgd).
Proof.
apply: (etrans (esym (rev_rev _)) (congr1 rev _)); rewrite -maps_rev.
move: (andP Hbgd) sewr_hdr Hrs => [_ Ud]; rewrite /hdr -(size_rev bgr).
elim: bgd (rev bgr) {Ud}(simple_uniq Ud) => [|xd pd Hrec] [|xr pr] //=.
move/andP=> [Hpxd Upd] Edr; rewrite -(Edr _ (setU11 _ _) xr) set11 /=.
move=> [Hsz]; congr Adds; apply: Hrec => // yd Hyd yr0.
rewrite -(Edr _ (setU1r _ Hyd) yr0).
by case: (yd =P xd) Hpxd => [<-|_]; rewrite ?Hyd.
Qed.

Lemma sew_map_patch : @patch sew_map _ _ sewd sewr bgd bgr.
Proof.
split=> //.
- exact inj_sewd.
- exact inj_sewr.
- exact sewr_rev_sewd.
- move=> x; case Dx: {0}x => [[|] xd]; move: Dx; last move: xd => [xr Hxr].
    rewrite -[sumdI _]/(sewd xd) => Dx.
    rewrite /setU /setC Dx codom_f (mem_maps inj_sewd) /=.
    case: (in_bgd xd) => [[xr0 Hxd]|Hxd].
      rewrite Hxd; apply/set0Pn; exists (hdr xr0 xd).
      by rewrite /preimage (sewr_hdr Hxd) set11.
    rewrite (negbE Hxd); apply/set0Pn => [] [xr H]; case/idP: Hxd; move: H.
    rewrite /preimage /sewr; case: (in_bgr xr) => [[xd0 Hxr]|Hxr]; last done.
    by rewrite (inj_eqd inj_sewd); move/eqP=> Dxd; rewrite Dxd bgd_hrd.
  rewrite -[sumdI _]/(sewr_r Hxr); move=> Dx.
  rewrite Dx /setU /setC {2}/codom /set0b eq_card0 //=.
  by apply/set0Pn; exists xr; rewrite /preimage (sewr_gr Hxr) set11.
- by move=> xd Hxd /=; case: (in_bgd xd) => // [[xr0 Hxd']]; case/idP: Hxd.
- move=> xr; rewrite {2}/sewr; case: (in_bgr xr) => [[xd0 Hxr]|Hxr] //=.
  case: (in_bgd (hrd xd0 xr)) => [[xr0 _]|Hxd']; first by rewrite hdr_hrd.
  by case (negP Hxd'); rewrite bgd_hrd.
by move=> xr Hxr; rewrite (sewr_gr Hxr).
Qed.

End Sew.

Unset Implicit Arguments.