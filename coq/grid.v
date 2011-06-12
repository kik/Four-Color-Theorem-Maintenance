(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import hypermap.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import paths.
Require Import znat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*    Geometry over an integer grid, that is, raster graphics.         *)
(* We define integer point arithmetic, which we then use to define     *)
(* coordinates for four kinds of basic geometric objects:              *)
(*   - grid points                                                     *)
(*   - grid squares (pixels), whose vertices are adjacent gid points   *)
(*     They are referenced by their lower left corner.                 *)
(*   - grid darts, the sides of the grid squares, oriented counter-    *)
(*     clockwise. The coordinates of a dart is the sum of the          *)
(*     coordinates of its start point and the coordinates of the       *)
(*     square it belongs to.                                           *)
(*   - rectangles composed of grid squares. The coordinates of a       *)
(*     rectangle are the coordinates of the left/right/top/bottom-most *)
(*     pixel it contains (thus the top/right coordinates are one less  *)
(*     than the coordiates of the top/right-most grid points in the    *)
(*     frame).                                                         *)
(* The coordinate system for darts has some nice properties: it's easy *)
(* to recover the coordinates of the corresponding pixel (just divide  *)
(* the coordinates by 2) and the orientation (the remainder of that    *)
(* division by 2). Thus we can use integer arithmetic to put an        *)
(* infinite hypermap structure on the integer grid. These coordinates  *)
(* also behave nicely with respect to binary subdivision, which we use *)
(* heavily in the discretization proof.                                *)
(*   Finally, we define some intersection and union operations on      *)
(* integer rectangles (with half-planes and individual pixels, resp.). *)

Inductive gpoint : Set := Gpoint (x y : znat).

Definition eqgp p1 p2 :=
  let: Gpoint x1 y1 := p1 in let: Gpoint x2 y2 := p2 in (x1 =d x2) && (y1 =d y2).

Lemma eqgpP : reflect_eq eqgp.
Proof.
move=> [x1 y1] [x2 y2]; apply: (iffP andP) => /=.
  by case; do 2 move/eqP=> ->.
by case=> -> ->; split; exact: set11.
Qed.

Canonical Structure gpointData := DataSet eqgpP.

Definition gpointset : Set := set gpointData.

Definition gpointseq : Set := seq gpointData.

Identity Coercion seq_gpointseq : gpointseq >-> seq.
Identity Coercion set_gpointset : gpointset >-> set.

Definition addg p1 p2 :=
  let: Gpoint x1 y1 := p1 in let: Gpoint x2 y2 := p2 in
  Gpoint (x1 + x2) (y1 + y2).

Notation "p1 +g p2" := (addg p1 p2) (at level 50).

Lemma addgA : forall p1 p2 p3, p1 +g (p2 +g p3) = p1 +g p2 +g p3.
Proof. by move=> [x1 y1] [x2 y2] [x3 y3]; rewrite /= !addzA. Qed.

Lemma addgC : forall p1 p2, p1 +g p2 = p2 +g p1.
Proof. by move=> [x1 y1] [x2 y2]; rewrite /= addzC (addzC y1). Qed.

Lemma addgCA : forall p1 p2 p3, p1 +g (p2 +g p3) = p2 +g (p1 +g p3).
Proof. by move=> p1 *; rewrite !addgA (addgC p1). Qed.

Definition halfg p := let: Gpoint x y := p in Gpoint (halfz x) (halfz y).

Lemma halfg_add_double : forall p1 p2, halfg (p1 +g (p2 +g p2)) = (halfg p1) +g p2.
Proof. by move=> [x1 y1] [x2 y2]; rewrite /= !halfz_add_double. Qed.

Lemma halfg_double : forall p, halfg (p +g p) = p.
Proof. by move=> [x y]; rewrite /= !halfz_double. Qed.

(* An explicit enumeration for the parity of points on an even grid.         *)

Inductive gbits : Set := Gb00 | Gb10 | Gb11 | Gb01.

Definition eqgb d1 d2 :=
  match d1, d2 with
  | Gb00, Gb00 => true
  | Gb10, Gb10 => true
  | Gb11, Gb11 => true
  | Gb01, Gb01 => true
  | _, _ => false
  end.

Lemma eqgbP : reflect_eq eqgb. Proof. by do 2 case; constructor. Qed.

Canonical Structure gbitsData := DataSet eqgbP.

Coercion gbits_to_gpoint d :=
  match d with
  | Gb00 => Gpoint 0 0
  | Gb10 => Gpoint 1 0
  | Gb11 => Gpoint 1 1
  | Gb01 => Gpoint 0 1
  end.

Definition oddg p :=
  let: Gpoint x y := p in
  match oddz x, oddz y with
  | false, false => Gb00
  | true,  false => Gb10
  | true,  true  => Gb11
  | false, true  => Gb01
  end.

Lemma oddg_add_double : forall p1 p2, oddg (p1 +g (p2 +g p2)) = oddg p1.
Proof. by move=> [x1 y1] [x2 y2] /=; rewrite !oddz_add !addbb !addbF.  Qed.

Lemma oddg_double : forall p, oddg (p +g p) = Gb00.
Proof. by move=> [x y] /=; rewrite !oddz_add !addbb. Qed.

Lemma oddg_bits : forall d : gbits, oddg d = d. Proof. by case. Qed.

Lemma halfg_bits : forall d : gbits, halfg d = Gb00. Proof. by case. Qed.

Lemma gb00I : Gpoint 0 0 = Gb00. Proof. done. Qed.
Lemma gb11I : Gpoint 1 1 = Gb11. Proof. done. Qed.

Lemma add0g : forall p, Gb00 +g p = p.
Proof. by case=> [[mx|nx] [my|ny]]. Qed.

Lemma addg0 : forall p, p +g Gb00 = p.
Proof. by move=> *; rewrite addgC add0g. Qed.

Definition oppg p := let: Gpoint x y := p in Gpoint (- x) (- y).

Lemma addg_opp : forall p, p +g oppg p = Gb00.
Proof. by move=> [x y]; rewrite /= !subzz. Qed.

Lemma addg_inv : forall p, monic (addg p) (addg (oppg p)).
Proof. by move=> p1 p2; rewrite addgCA addgA addg_opp add0g. Qed.

Definition consg (d : gbits) p := d +g (p +g p).

Lemma consgI : forall (d : gbits) p, d +g (p +g p) = consg d p.
Proof. done. Qed.

Lemma consg_odd_half : forall p, consg (oddg p) (halfg p) = p.
Proof.
move=> [x y]; rewrite -{3}[x]odd_double_halfz -{3}[y]odd_double_halfz /=.
by case (oddz x); case (oddz y).
Qed.

Lemma oddg_cons : forall d p, oddg (consg d p) = d.
Proof. by move=> *; rewrite /consg oddg_add_double oddg_bits. Qed.

Lemma halfg_cons : forall d p, halfg (consg d p) = p.
Proof. by move=> *; rewrite /consg halfg_add_double halfg_bits add0g. Qed.

Lemma halfg_add : forall p1 p2,
  halfg (p1 +g p2) = halfg (p1 +g oddg p2) +g halfg p2.
Proof.
by move=> p1 p2; rewrite -{1}[p2]consg_odd_half /consg addgA halfg_add_double.
Qed.

Lemma oddg_add : forall p1 p2, oddg (p1 +g p2) = oddg (p1 +g oddg p2).
Proof.
by move=> p1 p2; rewrite -{1}[p2]consg_odd_half /consg addgA oddg_add_double.
Qed.

(* Turning counterclockwise around a pixel square.   *)

Definition ccw d :=
  match d with
  | Gb00 => Gb10
  | Gb10 => Gb11
  | Gb11 => Gb01
  | Gb01 => Gb00
  end.

Lemma ccw4 : forall d, ccw (ccw (ccw (ccw d))) = d. Proof. by case. Qed.

Lemma addg_ccw2 : forall d : gbits, d +g ccw (ccw d) = Gb11. Proof. by case. Qed.

(* The dart interpretation of points: the half point gives the coordinates of *)
(* the origin of the square, the parity bits specify the side. The origin and *)
(* target of each dart (end0g and end1g, respectively) are computed using the *)
(* functions below.                                                           *)

Definition end0g p := halfg p +g oddg p.
Definition end1g p := halfg p +g ccw (oddg p).

Lemma halfg_add_odd : forall p, halfg (p +g oddg p) = end0g p.
Proof. by move=> p; rewrite addgC halfg_add halfg_double addgC. Qed.

Lemma halfg_add1 : forall p, halfg (p +g Gb11) = end0g p.
Proof. by move=> p; rewrite addgC halfg_add addgC /end0g; case (oddg p). Qed.

(* The infinite hypermap of a grid. *)

Definition gedge p := let d := ccw (oddg p) in p +g (d +g oppg (ccw (ccw d))).

Lemma oddg_edge : forall p, oddg (gedge p) = ccw (ccw (oddg p)).
Proof. by move=> p; rewrite /gedge addgC oddg_add; case (oddg p). Qed.

Lemma gedge2 : forall p, gedge (gedge p) = p.
Proof.
move=> p; rewrite {1}/gedge oddg_edge /gedge ccw4 -!addgA addg_inv addg_opp.
exact: addg0.
Qed.

Definition neg1g := Gpoint (Zneg 0) (Zneg 0).

Lemma halfg_edge : forall p,
  halfg (gedge p) = halfg p +g (oddg p +g (ccw (oddg p) +g neg1g)).
Proof. by move=> p; rewrite /gedge addgC halfg_add addgC; case (oddg p). Qed.

Lemma neq_halfg_edge : forall p, (halfg p =d halfg (gedge p)) = false.
Proof.
move=> p; rewrite -[halfg p]addg0 halfg_edge (monic_eqd (addg_inv (halfg p))).
by case (oddg p).
Qed.

Lemma end0g_edge : forall p, end0g (gedge p) = end1g p.
Proof.
by move=> p; rewrite /end0g halfg_edge oddg_edge -addgA /end1g; case (oddg p).
Qed.

Lemma end1g_edge : forall p, end1g (gedge p) = end0g p.
Proof.
by move=> p; rewrite /end1g halfg_edge oddg_edge -addgA /end0g; case (oddg p).
Qed.

Definition gnode p :=  p +g (oddg p +g oppg (ccw (oddg p))).

Definition gface p := consg (ccw (oddg p)) (halfg p).

Lemma gface_def : forall p, gface p = p +g (ccw (oddg p) +g oppg (oddg p)).
Proof.
by move=> p; rewrite -{2}[p]consg_odd_half addgC /consg -!addgA addg_inv.
Qed.

Lemma gface4 : forall p, gface (gface (gface (gface p))) = p.
Proof.
by move=> p; rewrite /gface !oddg_cons !halfg_cons ccw4 consg_odd_half.
Qed.

Lemma oddg_face : forall p, oddg (gface p) = ccw (oddg p).
Proof. move=> p; apply: oddg_cons. Qed.

Lemma halfg_face : forall p, halfg (gface p) = halfg p.
Proof. move=> p; apply: halfg_cons. Qed.

Lemma end0g_face : forall p, end0g (gface p) = end1g p.
Proof. by move=> p; rewrite /end0g oddg_face halfg_face. Qed.

Lemma gnode_face : forall p, gnode (gface p) = gedge p.
Proof.
move=> p; rewrite /gedge addgC /gnode oddg_face /gface addgC.
by rewrite -{7}[p]consg_odd_half /consg !addgA; case (oddg p).
Qed.

Lemma gmonicE : monic3 gedge gnode gface.
Proof. by move=> p; rewrite /= gnode_face gedge2. Qed.

Lemma gmonicF : monic3 gface gedge gnode.
Proof. by move=> p; rewrite /= gnode_face gedge2. Qed.

Lemma gmonicN : monic3 gnode gface gedge.
Proof. by move=> p; rewrite -[p]gface4 gnode_face gedge2. Qed.

Lemma end0g_node : forall p, end0g (gnode p) = end0g p.
Proof. by move=> p; rewrite -{2}[p]gmonicN end0g_face end1g_edge. Qed.

Lemma oddg_node : forall p, oddg (gnode p) = ccw (oddg p).
Proof. by move=> p; rewrite -{2}[p]gmonicN oddg_face oddg_edge ccw4. Qed.

Lemma gnode4 : forall p, gnode (gnode (gnode (gnode p))) = p.
Proof.
move=> p; do 4 rewrite {1}/gnode ?oddg_node ?ccw4.
by rewrite -!addgA !addg_inv addg_opp addg0.
Qed.

Lemma same_end0g : forall p q, end0g p = end0g q -> traject gnode p 4 q.
Proof.
move=> p q; move/esym=> Epq; rewrite /end0g addgC in Epq.
rewrite -[q]consg_odd_half /consg addgA Epq.
rewrite (monic_move (addg_inv _) Epq) addgCA addgC -!addgA addgCA 2!addgA.
rewrite -(addgA (oddg p)) consgI consg_odd_half.
rewrite /= /setU1 {1 2 4}/gnode !oddg_node {1 2}/gnode oddg_node.
rewrite /gnode -!addgA !addg_inv -{1}[p]addg0 !(monic_eqd (addg_inv p)).
by case (oddg p); case (oddg q).
Qed.

Lemma halfg_iter_face : forall i p, halfg (iter i gface p) = halfg p.
Proof. by elim=> //= [i Hrec] p; rewrite halfg_face. Qed.

Lemma oddg_iter_face : forall i p, oddg (iter i gface p) = iter i ccw (oddg p).
Proof. by elim=> //= [i Hrec] p; rewrite oddg_face Hrec. Qed.

(* Local grid refinement. *)

Definition refined_in (m r : gpointset) :=
  forall p q, r p -> halfg q = halfg p -> m q = m p.

Lemma refined_in_face : forall m r, refined_in m r ->
  forall p, r p -> forall i, m (iter i gface p) = m p.
Proof.
by move=> m r Hm p Hp i; apply: Hm; last by apply halfg_iter_face. Qed.

(* Rectangles on the grid. *)

Inductive grect : Set := Grect (xmin xmax ymin ymax : znat).

Definition mem_grect r : gpointset :=
  fun p => let: Grect xmin xmax ymin ymax := r in let: Gpoint x y := p in
  and4b (xmin <= x)%Z (x <= xmax)%Z (ymin <= y)%Z (y <= ymax)%Z.

Coercion mem_grect : grect >-> gpointset.

Definition zwidth xmin xmax := if (xmax - xmin)%Z is Zpos w then S w else 0.

Definition gwidth r := let: Grect xmin xmax _ _ := r in zwidth xmin xmax.

Definition gheight r := let: Grect _ _ ymin ymax := r in zwidth ymin ymax.

Definition zspan xmin xmax := traject incz xmin (zwidth xmin xmax).

Lemma size_zspan : forall xmin xmax, size (zspan xmin xmax) = zwidth xmin xmax.
Proof. by move=> *; rewrite /zspan size_traject. Qed.

Lemma mem_zspan : forall xmin xmax x,
  zspan xmin xmax x = (xmin <= x)%Z && (x <= xmax)%Z.
Proof.
move=> x0 x1 x; rewrite -{2}[x1](subz_add x0) -addz_subA /zspan /zwidth.
case: {x1}(x1 - x0)%Z => [n|m].
  elim: n x0 => [|n Hrec] x0; first by rewrite addz0 -eqz_leq /= /setU1 orbF.
    rewrite leqz_inc /= {1}/setU1; case: (x0 =P x) => [<-|_].
    by rewrite /= -{1}[x0]addz0 leqz_add2l.
  by rewrite -add1n zpos_addn addzA -incz_def /= -Hrec.
by rewrite /leqz -subz_sub -oppz_sub; case: (x - x0)%Z => [[|n]|m'].
Qed.

Lemma uniq_zspan : forall xmin xmax, uniq (zspan xmin xmax).
Proof.
move=> x0 x1; rewrite /zspan /zwidth; case: {x1}(x1 - x0)%Z => // [n].
elim: {n}(S n) x0 => //= [n Hrec] x0; rewrite {}Hrec andbT; case: n => // [n].
apply negbI; move: (mem_zspan (incz x0) (incz x0 + n) x0).
by rewrite {1}/leqz {3}(incz_def x0) /zspan /zwidth !subz_add.
Qed.

Definition enum_grect r :=
  let: Grect xmin xmax ymin ymax := r in
  foldr (fun x => cat (maps (Gpoint x) (zspan ymin ymax))) seq0 (zspan xmin xmax).

Lemma mem_enum_grect : forall r, enum_grect r =1 r.
Proof.
move=> [x0 x1 y0 y1] [x y] /=; rewrite andbA -!mem_zspan.
elim: {x0 x1}(zspan x0 x1) => //= [x0 xs Hrec].
rewrite /setU1 demorgan2 mem_cat /setU {}Hrec; congr orb.
rewrite andbC; elim: {y0 y1}(zspan y0 y1) => //= [y0 ys Hrec].
by rewrite /setU1 demorgan2 {}Hrec; congr orb; rewrite andbC.
Qed.

Lemma uniq_enum_grect : forall r, uniq (enum_grect r).
Proof.
move=> [x0 x1 y0 y1] /=.
elim: {x0 x1}(zspan x0 x1) (uniq_zspan x0 x1) => //= [x0 xs Hrec].
move/andP=> [Hx0 Hxs]; rewrite uniq_cat {}Hrec {Hxs}// andbT.
rewrite uniq_maps ?uniq_zspan; last by move=> y y' [Dy].
elim: xs Hx0 => //= [x1 xs Hrec]; move/norP=> [Hx01 Hx0].
rewrite has_cat {Hrec Hx0}(negbE (Hrec Hx0)) orbF.
apply/hasP => [[p]]; move/mapsP=> [y _ <-]; move/mapsP=> [y' _ [Dx0 _]].
by case/eqP: Hx01.
Qed.

Definition garea r := gwidth r * gheight r.

Lemma size_enum_grect : forall r, size (enum_grect r) = garea r.
Proof.
move=> [x0 x1 y0 y1]; rewrite /garea /= -!size_zspan.
elim: {x0 x1}(zspan x0 x1) => //= [x0 xs Hrec].
by rewrite size_cat size_maps Hrec.
Qed.

Lemma ltn0_garea : forall (r : grect) p, r p -> 0 < garea r.
Proof.
by move=> r p; rewrite -mem_enum_grect -size_enum_grect; case (enum_grect r).
Qed.

Definition sub_grect r1 r2 :=
  let: Grect xmin1 xmax1 ymin1 ymax1 := r1 in
  let: Grect xmin2 xmax2 ymin2 ymax2 := r2 in
  and4b (xmin2 <= xmin1)%Z (xmax1 <= xmax2)%Z
        (ymin2 <= ymin1)%Z (ymax1 <= ymax2)%Z.

Lemma mem_sub_grect : forall r1 r2, sub_grect r1 r2 -> sub_set r1 r2.
Proof.
move=> [x10 x11 y1x y11] [x20 x21 y20 y21]; move/and4P=> [Hx0 Hx1 Hy0 Hy1] [x y].
move/and4P=> [Hxx0 Hxx1 Hyy0 Hyy1]; apply/and4P; split; eapply leqz_trans; eauto.
Qed.

Lemma garea_sub_rect : forall r1 r2 : grect, sub_set r1 r2 -> garea r1 <= garea r2.
Proof.
move=> r1 r2 Hr12; rewrite -!size_enum_grect; have:= uniq_enum_grect r1.
set p1 := enum_grect r1; set p2 := enum_grect r2.
have Hp12: sub_set p1 p2.
  by move=> p; rewrite /p1 /p2 !mem_enum_grect; apply: Hr12.
elim: p1 p2 Hp12 {Hr12} => //= [p p1 Hrec] p2 Hp12; move/andP=> [Hp1p Hp1].
case/rot_to: (Hp12 _ (setU11 _ _)) => [i p2' Dp2].
rewrite -(size_rot i p2) Dp2 /= ltnS {}Hrec //.
move=> q Hq; move: (Hp12 _ (setU1r _ Hq)); rewrite -(mem_rot i) Dp2.
by case/setU1P=> // [Dp]; case/idP: Hp1p; rewrite Dp.
Qed.

Lemma ltn_garea_sub_rect : forall r1 r2 : grect, sub_set r1 r2 ->
 forall p, setD r2 r1 p -> garea r1 < garea r2.
Proof.
move=> r1 r2 Hr12 p0; rewrite /setD -!mem_enum_grect -!size_enum_grect.
have:= uniq_enum_grect r1; set p1 := enum_grect r1; set p2 := enum_grect r2.
have Hp12: sub_set p1 p2 by move=> p; rewrite /p1 /p2 !mem_enum_grect; exact: Hr12.
elim: p1 p2 Hp12 {Hr12} => [|p p1 Hrec] p2 Hp12; first by case p2.
move/andP=> [Hp1p Hp1] Hp0; case/rot_to: (Hp12 _ (setU11 _ _)) => [i p2' Dp2].
rewrite -(size_rot i p2) Dp2 /= ltnS {}Hrec //.
move=> q Hq; move: (Hp12 _ (setU1r _ Hq)); rewrite -(mem_rot i) Dp2.
  by case/setU1P=> // [Dp]; case/idP: Hp1p; rewrite Dp.
by move: Hp0; rewrite -(mem_rot i p2) Dp2 /= /setU1; case (p =d p0).
Qed.

(* Grid refinement simply doubles the rectangle bounds. *)

Definition refine_rect r :=
  let: Grect xmin xmax ymin ymax := r in
  Grect (xmin + xmin)%Z (incz (xmax + xmax)) (ymin + ymin)%Z (incz (ymax + ymax)).

Lemma mem_refine_rect : forall r x, refine_rect r x = r (halfg x).
Proof. by move=> [x0 x1 y0 y1] [x y] /=; rewrite !leqz_halfl !leqz_halfr. Qed.

Lemma garea_refine_rect :
  forall r, garea (refine_rect r) = double (double (garea r)).
Proof.
have Ezw: forall x y, zwidth (x + x) (incz (y + y)) = double (zwidth x y).
  move=> x y; rewrite /zwidth incz_def -addzA addzCA -addzA -subz_sub.
  rewrite (addzC (y - x)) (addzA y); case: (y - x)%Z => [n|m] //=.
  by rewrite -double_addnn doubleS.
move=> [x0 x1 y0 y1]; rewrite /garea /gwidth /gheight /= !Ezw !double_addnn.
by rewrite muln_addl !muln_addr.
Qed.

Lemma refine_rect_refined : forall r, refined_in (refine_rect r) (fun _ => true).
Proof. by move=> r p q _ Hpq; rewrite !mem_refine_rect Hpq. Qed.

(* The 3x3 rectangle of squares that surround a central square. *)

Definition gtouch p :=
  let: Gpoint x y := p in Grect (decz x) (incz x) (decz y) (incz y).

Lemma gtouch_refl : forall p, gtouch p p.
Proof. by move=> [x y]; rewrite /= !leq_z_incz !leq_decz_z. Qed.

Lemma gtouch_edge : forall p, gtouch (halfg p) (halfg (gedge p)).
Proof.
move=> p; rewrite halfg_edge; case: (halfg p) => [x y].
case (oddg p); rewrite /= addz0 -?incz_def -?decz_def;
  by rewrite leqzz leq_decz_incz leq_decz_z leq_z_incz.
Qed.

Lemma zspan_dec_inc :  forall x, zspan (decz x) (incz x) = Seq (decz x) x (incz x).
Proof.
move=> x; rewrite /zspan /zwidth incz_def decz_def subz_add2l -!incz_def -decz_def.
by rewrite /= incz_dec.
Qed.

(* The half-grid that lies counter-clockwise from a dart. *)

Definition gchop p q :=
  let: Gpoint xp yp := halfg p in
  let: Gpoint xq yq := q in
  match oddg p with
  | Gb00 => (yp <= yq)%Z
  | Gb10 => (xq <= xp)%Z
  | Gb11 => (yq <= yp)%Z
  | Gb01 => (xp <= xq)%Z
  end.

Lemma gchop_halfg : forall p, gchop p (halfg p).
Proof.
by move=> p; rewrite /gchop; case: (halfg p) => *; case (oddg p); apply leqzz.
Qed.

Lemma eq_gchop_halfg : forall p q, halfg p = q -> gchop p q.
Proof. by move=> p q <-; apply gchop_halfg. Qed.

Lemma gchop_edge : forall p, gchop (gedge p) =1 setC (gchop p).
Proof.
move=> p; rewrite /gchop halfg_edge oddg_edge; case: (halfg p) => [x y] [x' y'].
case (oddg p); rewrite /= /addn /setC /= -?incz_def -?decz_def negb_leqz //;
 by rewrite -leqz_inc_dec.
Qed.

Lemma gchopFEF : forall p, gchop (gface (gedge (gface p))) = gchop p.
Proof.
move=> p; do 2 rewrite /gchop halfg_face oddg_face ?halfg_edge ?oddg_edge.
by case: (halfg p) => [x y]; case (oddg p); rewrite /= addz0.
Qed.

(* Same as above, but extended by a unit band.              *)

Definition gchop1 p : gpointset := gchop (gface (gface (gedge p))).

Lemma gchop1I : forall p, gchop (gface (gface (gedge p))) = gchop1 p.
Proof. done. Qed.

Lemma gchop_chop1 : forall p, sub_set (gchop p) (gchop1 p).
Proof.
move=> p; rewrite /gchop1 /gchop !halfg_face halfg_edge !oddg_face !oddg_edge.
 case: (halfg p) => [x y] [x' y']; case: (oddg p) => *;
 rewrite /= /addn /= -?incz_def -?decz_def leqz_inc ?incz_dec ?leqz_inc2;
 by apply/orP; right.
Qed.

Lemma gtouch_chop1 : forall p,
 gtouch (halfg p) =1 (fun q => all (fun p' => gchop1 p' q) (traject gface p 4)).
Proof.
move=> p [x' y']; rewrite /traject /all /gchop1 /gchop andbT.
rewrite !halfg_face !halfg_edge !halfg_face !oddg_face !oddg_edge !oddg_face.
by case: (halfg p) => [x y]; case (oddg p);
  rewrite /gtouch /= /addn /setC /= -?incz_def -?decz_def;
  repeat BoolCongr.
Qed.

Section ChopRect.

(* Chopping off half of a rectangle (and excluding the boundary). *)
(* The dividing line is given as the side of an internal square.  *)

Variable r : grect.

Definition gchop_rect p :=
  let: Grect xmin xmax ymin ymax := r in
  let: Gpoint x y := halfg p in
  match oddg p with
  | Gb00 => Grect xmin xmax (if (ymin <= y)%Z then y else ymin) ymax
  | Gb10 => Grect xmin (if (x <= xmax)%Z then x else xmax) ymin ymax
  | Gb11 => Grect xmin xmax ymin (if (y <= ymax)%Z then y else ymax)
  | Gb01 => Grect (if (xmin <= x)%Z then x else xmin) xmax ymin ymax
  end.

Lemma mem_gchop_rect : forall p, gchop_rect p =1 setI r (gchop p).
Proof.
move=> p; rewrite /gchop_rect /gchop /setI.
case: r (halfg p) => [x0 x1 y0 y1] [xp yp] [x y]; rewrite andbC.
case: (oddg p) => /=; repeat BoolCongr; rewrite ?andbA; repeat congr andb.
case Hyp: (y0 <= yp)%Z; case Hy: (y0 <= y)%Z; rewrite ?andbF ?andbT //.
- by apply: (introF idP) => H; case: (elimTn negPf (leqz_trans Hyp H)).
- by symmetry; apply: leqz_trans Hy; rewrite leqz_inc -negb_leqz Hyp orbT.
- case Hxp: (xp <= x1)%Z; case Hx: (x <= x1)%Z; rewrite ?andbF ?andbT //.
    by apply: (introF idP) => H; case: (elimTn negPf (leqz_trans H Hxp)).
  by symmetry; apply: (leqz_trans Hx); rewrite leqz_inc -negb_leqz Hxp orbT.
- case Hyp: (yp <= y1)%Z; case Hy: (y <= y1)%Z; rewrite ?andbF ?andbT //.
    by apply: (introF idP) => H; case: (elimTn negPf (leqz_trans H Hyp)).
  by symmetry; apply: (leqz_trans Hy); rewrite leqz_inc -negb_leqz Hyp orbT.
case Hxp: (x0 <= xp)%Z; case Hx: (x0 <= x)%Z; rewrite ?andbF ?andbT //.
  by apply: (introF idP) => H; case: (elimTn negPf (leqz_trans Hxp H)).
by symmetry; apply: leqz_trans Hx; rewrite leqz_inc -negb_leqz Hxp orbT.
Qed.

Lemma gchop_rect_sub : forall p, sub_set (gchop_rect p) r.
Proof. by move=> p q; rewrite mem_gchop_rect; case/andP. Qed.

Lemma gchop_rect_edge : forall p, r (halfg (gedge p)) ->
  forall q, gchop_rect p q -> gchop_rect p (halfg p).
Proof.
move=> p Hep [x' y']; rewrite !mem_gchop_rect /setI gchop_halfg andbT /gchop.
case: r Hep => [x0 x1 y0 y1]; rewrite halfg_edge; move: (halfg p) => [x y].
case: {p}(oddg p); rewrite /= /addn /= ?addz0 -?incz_def -?decz_def -!andbA;
 move/and4P=> [Hx0 Hx1 Hy0 Hy1]; move/and5P=> [Hx0' Hx1' Hx2' Hx3' Hq];
 apply/and4P; split; first [ assumption
 | by rewrite leqz_dec; apply/orP; right
 | by rewrite leqz_inc; apply/orP; right
 | eapply leqz_trans; eauto ].
Qed.

Definition gchop1_rect p := gchop_rect (gface (gface (gedge p))).

Lemma gchop1_rectI : forall p,
  gchop_rect (gface (gface (gedge p))) = gchop1_rect p.
Proof. done. Qed.

Lemma mem_gchop1_rect : forall p, gchop1_rect p =1 setI r (gchop1 p).
Proof. move=> *; apply: mem_gchop_rect. Qed.

End ChopRect.

(* Extending a recangle to cover a specific pixel.                          *)

Definition extend_grect p r :=
  let: Grect xmin xmax ymin ymax := r in
  let: Gpoint x y := p in
  Grect (if (xmin <= x)%Z then xmin else x) (if (x <= xmax)%Z then xmax else x)
        (if (ymin <= y)%Z then ymin else y) (if (y <= ymax)%Z then ymax else y).

Lemma mem_extend_grect : forall p (r : grect),
  sub_set (setU1 p r) (extend_grect p r).
Proof.
move=> [x y] [x0 x1 y0 y1] q; case/setU1P=> [<-|] /=.
  apply/and4P; split.
  - by case Hx: (x0 <= x)%Z; last exact: leqzz.
  - by case Hx: (x <= x1)%Z; last exact: leqzz.
  - by case Hy: (y0 <= y)%Z; last exact: leqzz.
  by case Hy: (y <= y1)%Z; last exact: leqzz.
case: q => [x' y'] /=; move/and4P=> [Hx0 Hx1 Hy0 Hy1]; apply/and4P.
split; rewrite -if_negb negb_leqz.
- case Hx: (incz x <= x0)%Z; last done.
  by rewrite leqz_inc; apply/orP; right; eapply leqz_trans; eauto.
- case Hx: (incz x1 <= x)%Z; last done.
  by apply: (leqz_trans Hx1); rewrite leqz_inc Hx orbT.
- case Hy: (incz y <= y0)%Z; last done.
  by rewrite leqz_inc; apply/orP; right; eapply leqz_trans; eauto.
case Hy: (incz y1 <= y)%Z; last done.
by apply: (leqz_trans Hy1); rewrite leqz_inc Hy orbT.
Qed.

Set Strict Implicit.
Unset Implicit Arguments.

