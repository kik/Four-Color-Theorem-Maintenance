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
Require Import color.
Require Import coloring.
Require Import patch.
Require Import snip.
Require Import grid.
Require Import matte.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section GridMap.

(* The construction of a hypermap, from a finite set of disjoint mattes and *)
(* a set of adjacency boxes. These sets are simply represented by functions *)
(* on `nat' integers. The construction starts by extending the mattes so    *)
(* that mattes that meet a common adjacency box share a contour edge. Then  *)
(* we compute a bounding box for the mattes, and create a plain planar      *)
(* connected hypermap by framing the bounding box. The matte rings then map *)
(* to simple rings of this map with disjoint disks, so we can use the       *)
(* "snip" operation to turn them into node rings (we need to operate in the *)
(* dual map to make this work), by removing their interiors. Dualizing the  *)
(* resulting hypermap gives us a map whose coloring solves the initial      *)
(* coloring problem.                                                        *)

Definition cmatte := nat -> matte.
Definition adjbox := nat -> nat -> grect.

Variables (nbreg : nat) (ab0 : adjbox) (cm0 : cmatte).

Definition regpair i j := (i < j) && (j < nbreg).

Definition cm_mem (cm : cmatte) : gpointset :=
  fun p => iter_n nbreg (fun i => orb (cm i p)) false.

Definition cm_proper (cm : cmatte) :=
  forall i j, regpair i j -> negb (has (cm i) (cm j)).

Definition ab_adj (ab : adjbox) i j := 0 < garea (ab i j).

Definition ab_proper (ab : adjbox) :=
  forall i1 j1 i2 j2, regpair i1 j1 -> regpair i2 j2 ->
  forall p, ab i1 j1 p -> ab i2 j2 p -> i1 = i2 /\ j1 = j2.

Definition ab_cm_proper (ab : adjbox) (cm : cmatte) :=
  forall i j, regpair i j -> ab_adj ab i j ->
     has (inset (ab i j)) (cm i)
  /\ (fun k => (k < nbreg) && has (ab i j) (cm k)) =1 set2 i j.

Hypotheses (Hab0 : ab_proper ab0) (Hcm0 : cm_proper cm0).
Hypothesis Habcm0 : ab_cm_proper ab0 cm0.

(* We first do a global refinement, so that we can use the extend_meet lemma. *)
(* This operation will also be used in the topological construction, to       *)
(* rescale the mattes and boxes.                                              *)

Definition refine_cmatte : cmatte := fun i => refine_matte (cm0 i).
Definition refine_adjbox : adjbox := fun i j => refine_rect (ab0 i j).

Notation cm1 := refine_cmatte.
Notation ab1 := refine_adjbox.

Lemma cm_proper_refine : cm_proper cm1.
Proof.
move=> i j Hij; apply/hasPn => [p].
rewrite /cm1 /= !mem_refine_mdisk; exact: (hasPn (Hcm0 Hij)).
Qed.

Lemma refine_cmatte_refined : forall i j, refined_in (cm1 i : set _) (ab1 i j).
Proof. move=> *; exact: refine_matte_refined. Qed.

Lemma ab_proper_refine : ab_proper ab1.
Proof.
move=> i1 j1 i2 j2 Hij1 Hij2 p; rewrite /ab1 !mem_refine_rect.
exact: (Hab0 Hij1 Hij2).
Qed.

Lemma ab_adj_refine : ab_adj ab1 =2 ab_adj ab0.
Proof.
by move=> i j; rewrite /ab_adj /ab1 garea_refine_rect; case (garea (ab0 i j)).
Qed.

Lemma ab_cm_proper_refine : ab_cm_proper ab1 cm1.
Proof.
move=> i j Hij; rewrite ab_adj_refine; case/(Habcm0 Hij)=> [Habcmi Habij].
split.
  case/hasP: Habcmi => [q Hcmq Habq]; apply/hasP; exists (q +g q).
    by rewrite /cm1 mem_refine_matte halfg_double.
  suffice: inset2 (ab1 i j) (q +g q) by case/andP.
  by apply: inset2_refine; rewrite halfg_double.
move=> k; rewrite -Habij /cm1 /ab1; congr andb.
apply/hasP/hasP; case=> q Hcmq Habq.
  by rewrite mem_refine_matte mem_refine_rect in Hcmq Habq; exists (halfg q).
by exists (q +g q); rewrite ?mem_refine_matte ?mem_refine_rect halfg_double.
Qed.

(* The second stage of the construction eliminates the adjbox data by        *)
(* entending the mattes so that they meet in each box.                       *)

Definition cm_adj (cm : cmatte) i j :=
  has (fun p => mring (cm i) (gedge p)) (mring (cm j)).

Definition subregpair i1 j1 i2 j2 :=
  if j2 =d j1 then i2 < i1 else (i2 < j2) && (j2 < j1).

Lemma cm_extend_meet : {cm2 : cmatte | cm_proper cm2
  &  forall i j, regpair i j -> ab_adj ab1 i j -> cm_adj cm2 i j}.
Proof.
suffice: {cm : cmatte | cm_proper cm /\ ab_cm_proper ab1 cm
   & forall i j : nat, regpair i j ->
     if subregpair nbreg nbreg i j then ab_adj ab1 i j -> cm_adj cm i j else
     refined_in (cm j : set _) (ab1 i j)}.
  move=> [cm [Hcm _] Hadj]; exists cm; first done.
  move=> i j Hij; move: (Hadj _ _ Hij); rewrite /regpair in Hij.
  case: (andP Hij) => _; rewrite ltn_neqAle; move/andP=> [Hj _].
  by rewrite /subregpair (negbE Hj) Hij.
elim: nbreg => [|j1 Hrecj] /=.
  exists cm1; first by split; [exact cm_proper_refine | exact ab_cm_proper_refine].
  move=> i [|j] // _; rewrite /subregpair andbF; apply: refine_matte_refined.
  elim: {-2}(S j1) => [|i1 Hreci].
  move: Hrecj => [cm Hcm Hadj]; exists cm; auto.
  move=> i j Hij; move: {Hadj}(Hadj _ _ Hij); rewrite /subregpair.
  case: (j =P S j1) => [Dj|_].
    by rewrite Dj eqn_leq !ltnn /= andbC ltn_neqAle ltnn andbF.
  by rewrite ltnS (leq_eqVlt j); case: (j =P j1) => [<-|_] //; rewrite andbT.
move/S: j1 Hreci {Hrecj} => j1 [cm Hcm Hadj].
case Hij1: (negb (regpair i1 j1 && ab_adj ab1 i1 j1)).
  exists cm; first done.
  move=> i j Hij; move: (Hadj _ _ Hij); rewrite /subregpair ltnS (leq_eqVlt i).
  case: (j =P j1) => // Dj; case: (i =P i1) => //= Di _ Haij.
  by case/idP: Hij1; rewrite -Dj -Di Hij.
move/andP: Hij1 Hcm => [Hij1 Haij1] [Hcm Habcm].
case: {Haij1}(Habcm _ _ Hij1 Haij1); set r1 := ab1 i1 j1 => Hr1i1 Hr1.
have Hr1j1: has r1 (cm j1) by move: (Hr1 j1); rewrite set22; case/andP.
have Hr1cm: refined_in (cm j1 : set _) (ab1 i1 j1).
  by move: (Hadj _ _ Hij1); rewrite /subregpair set11 ltnn.
case: (extend_meet Hr1cm Hr1j1 Hr1i1); first by rewrite has_sym; apply Hcm.
rewrite -/r1 => xm [Hxm Hxmr] Hxmi.
pose xcm i := if i =d j1 then xm else cm i.
have Excm: forall i, sub_set (cm i) (xcm i).
  by move=> i; rewrite /xcm; case: (i =P j1) => [->|_].
have Hxcm: cm_proper xcm /\ ab_cm_proper ab1 xcm.
  split=> i j Hij; case: (andP Hij); rewrite ltn_neqAle; case/andP=> Hi _ Hj.
    rewrite /xcm; case: (j =P j1) => [Dj|_].
      rewrite -Dj (negbE Hi); apply/hasP => [[p Hxmp Hip]].
      case/andP: (Hxmr _ Hxmp) => Hi1p; case/orP=> Hp.
        have Hr1i: (i < nbreg) && has r1 (cm i).
          apply/andP; split; last by apply/hasP; exists p.
          by case/andP: Hij ltn_trans; eauto.
        rewrite Hr1 /set2 -Dj orbC eqd_sym (negbE Hi) /= in Hr1i.
        by rewrite (eqP Hr1i) Hip in Hi1p.
      by rewrite -Dj in Hp; case/hasP: (Hcm _ _ Hij); exists p.
    case: (i =P j1) => [Di|_]; last exact: Hcm.
    apply/hasP => [[p Hjp Hxmp]].
    case/andP: (Hxmr _ Hxmp) => Hi1p; case/orP=> Hp.
      have Hr1j: (j < nbreg) && has r1 (cm j) by rewrite Hj; apply/hasP; exists p.
      rewrite Hr1 /set2 -Di orbC (negbE Hi) /= in Hr1j.
      by rewrite (eqP Hr1j) Hjp in Hi1p.
    by rewrite -Di in Hp; case/hasP: (Hcm _ _ Hij); exists p.
  move=> Haij; case: (Habcm _ _ Hij Haij) => Hcmi Habij; split.
    by case/hasP: Hcmi => p Hcmp Hp; apply/hasP; exists p; first exact: Excm.
  move=> k; rewrite -{}Habij /xcm; case: (k =P j1) => // ->.
  congr andb; apply/hasP/hasP; case=> p Hcmp Habp; last by exists p; auto.
  case/andP: (Hxmr _ Hcmp) => Hi1p; case/orP=> Hp; last by exists p.
  by case: (ab_proper_refine Hij Hij1 Habp Hp) => -> ->; exact: hasP.
exists xcm; first done; move: Hxcm => [Hxcm _] i j Hij.
move: (Hadj _ _ Hij); case Hsij: (subregpair (S i1) j1 i j).
  case Hs'ij: (subregpair i1 j1 i j).
    move=> H; move/H {H}; rewrite /cm_adj; case/hasP=> p.
    rewrite !mring_def; move/andP=> [Hip _]; move/andP=> [Hjp _].
    have Hxcmij := Hxcm _ _ Hij.
    apply/hasP; exists p; rewrite mring_def Excm ?gedge2 //=.
      by rewrite has_sym in Hxcmij; apply: (hasPn Hxcmij); exact: Excm.
    by apply: (hasPn Hxcmij); exact: Excm.
  do 2 clear; move: Hsij Hs'ij; rewrite /subregpair ltnS leq_eqVlt.
  case: (i =P i1); last by move=> _ H; case/idP.
  case: (j =P j1); last by move=> _ _ H; case/idP.
  case/andP: Hij1 => Hi1 _ -> -> _ _; rewrite /cm_adj /xcm set11.
  by rewrite eqn_leq andbC leqNgt Hi1.
move: Hsij; rewrite /subregpair ltnS leqNgt /xcm.
case: (j =P j1) => [Dj|Hj] /=; last by move->.
move/idP=> Hi; rewrite ltnNge (ltnW Hi) /= {1}Dj.
have Hr1i: forall p, ab1 i j p -> r1 p = false.
  move=> p Hp; apply/idP => Hp1.
  by case: (ab_proper_refine Hij Hij1 Hp Hp1) Hi => [<- _]; rewrite ltnn.
move=> Hcmj1 p q Hp Epq.
have Hq: (ab1 i j q) by move: Hp; rewrite /ab1 !mem_refine_rect Epq.
apply/idP/idP; move/Hxmr; case/andP=> _; rewrite /setU Hr1i //=.
  rewrite (Hcmj1 _ _ Hp Epq); exact: Hxm.
rewrite -(Hcmj1 _ _ Hp Epq); exact: Hxm.
Qed.

Let cm2 := let: exist2 cm _ _ := cm_extend_meet in cm.

Remark GMap_Hcm2 : cm_proper cm2. Proof. by rewrite /cm2; case cm_extend_meet. Qed.
Notation Hcm2 := GMap_Hcm2.

Remark GMap_Habcm2 : forall i j, regpair i j -> ab_adj ab1 i j -> cm_adj cm2 i j.
Proof. by rewrite /cm2; case cm_extend_meet. Qed.
Notation Habcm2 := GMap_Habcm2.

(* Now we compute a bounding box for the extended mattes. *)

Definition grect0 := Grect 0 0 0 0.

Definition cm_bbox  :=
  iter_n nbreg (fun i r => foldr extend_grect r (cm2 i)) grect0.

Notation bb := cm_bbox.

Lemma sub_cm_bbox : sub_set (cm_mem cm2) bb.
Proof.
move=> p; rewrite /cm_mem /bb /=; elim: nbreg => //= [n Hrec].
move: (iter_n n (fun i (r : grect) => foldr extend_grect r (cm2 i)) grect0) Hrec.
move=> r Hrec Hprec.
have Hp: cm2 n p || r p by apply/orP; case/orP: Hprec; auto.
elim: {n cm}(cm2 n : gpointseq) Hp {Hprec Hrec} => //= [q m Hrec] Hp.
apply mem_extend_grect; apply/orP; rewrite /setU1 -orbA in Hp; case/orP: Hp; auto.
Qed.

Notation bbw := (gwidth bb).
Notation bbh := (gheight bb).

Remark GMap_Hbb0 : 0 < garea bb.
Proof.
case Dn: nbreg => [|n]; first by rewrite /bb Dn.
case Dcm2n: (cm2 n) => [[|p m] c Hm Hc Uc Dc] //.
have Hp: bb p.
  apply sub_cm_bbox; rewrite /cm_mem Dn; apply/orP; left.
  by rewrite Dcm2n /= setU11.
by move: Hp; rewrite -mem_enum_grect -size_enum_grect; case (enum_grect bb).
Qed.
Notation Hbb0 := GMap_Hbb0.

(* Now we define a frame around the box. *)

Definition frs_step p := gface (gedge (gface p)).

Definition halfg_n_frs (n : nat) d p :=
  let: Gpoint x y := p in
  match d with
  | Gb00 => Gpoint (x + n) y
  | Gb11 => Gpoint (x - n) y
  | Gb10 => Gpoint x (y + n)
  | Gb01 => Gpoint x (y - n)
  end.

Lemma iter_frs_step : forall n d p,
   iter n frs_step (consg d p) = consg d (halfg_n_frs n d p).
Proof.
elim=> [|n Hrec]; first by case; case=> *; rewrite /= ?addz0.
move=> d p; rewrite /= {}Hrec /frs_step {1}/gface oddg_edge halfg_edge oddg_face.
rewrite halfg_face ccw4 oddg_cons halfg_cons; congr consg; move: p => [x y].
by case: d; rewrite /= -?addzA /= ?addn0 ?addn1 ?addz0 // -decz_def; case: n.
Qed.

Definition frs_base d x y := consg (ccw d) (Gpoint x y +g (d +g oppg (ccw d))).

Lemma frs_base_eq : forall d x y, frs_base d x y = gnode (consg d (Gpoint x y)).
Proof.
move=> d x y; rewrite /gnode oddg_cons /consg -addgA addgCA /frs_base /consg.
by move: (Gpoint x y) => p; rewrite -!addgA -!(addgCA p); case d.
Qed.

Definition cm_frame : gpointseq :=
  let: Grect xmin xmax ymin ymax := bb in
  cat (traject frs_step (frs_base Gb00 xmin ymin) bbh)
 (cat (traject frs_step (frs_base Gb01 xmin ymax) bbw)
 (cat (traject frs_step (frs_base Gb11 xmax ymax) bbh)
      (traject frs_step (frs_base Gb10 xmax ymin) bbw))).

Notation bbf := cm_frame.

Lemma cm_frame_size : size bbf = double (bbh + bbw).
Proof.
rewrite /bbf; case: {1}bb => [x0 x1 y0 y1] /=.
by rewrite !size_cat !size_traject !double_addnn -!addnA.
Qed.

Lemma zwidth_eq : forall x0 x1,
  x1 = if zwidth x0 x1 is S n then (x0 + n)%Z else x1.
Proof.
move=> x0 x1; rewrite -{1 3}[x1](subz_add x0) -addz_subA /zwidth.
by case (x1 - x0)%Z.
Qed.

Lemma cycle_cm_frame : cycle mrlink bbf.
Proof.
have Hfrs: forall n p, path mrlink p (traject frs_step (frs_step p) n).
  move=> n p; apply: {p}(sub_path _ (fpath_traject frs_step _ _)) => p q.
  rewrite /eqdf /mrlink; move/eqP=> <-; apply/eqP.
  by rewrite /frs_step end0g_face end1g_edge end0g_face.
move: Hbb0; rewrite /garea /bbf /gwidth /gheight; move: bb => [x0 x1 y0 y1].
case: (zwidth x0 x1) (zwidth_eq x0 x1) => // w Dx1; rewrite mulnC.
case: (zwidth y0 y1) (zwidth_eq y0 y1) => //= [h] Dy1 _.
rewrite -cats1; repeat rewrite path_cat ?last_cat /= ?Hfrs.
rewrite !last_traject /frs_base !iter_frs_step /halfg_n_frs [addz]lock [oppz]lock.
rewrite /mrlink /end0g /end1g !oddg_cons !halfg_cons /= -!lock -!addzA !addz0.
by rewrite !add0z !addzA Dx1 Dy1 !set11 (addzC x0 w) (addzC y0 h) !subz_add !set11.
Qed.

Lemma uniq_cm_frame : uniq bbf.
Proof.
have Ufrs1: forall n p, uniq (traject frs_step p n).
  move=> [|n] // p; rewrite looping_uniq; apply/trajectP; move=> [i Hi Dp].
  rewrite ltn_neqAle in Hi; case/andP: Hi; case/eqP; move/(congr1 halfg): Dp.
  rewrite -[p]consg_odd_half !iter_frs_step !halfg_cons.
  case/oddg: p (halfg p) => [] [x y]; rewrite /halfg_n_frs [oppz]lock; case;
  by move/addz_inj; unlock; try move/(monic_inj oppz_opp); case.
have Ufrs2: forall n1 n2 d1 d2 p1 p2, negb (d1 =d d2) ->
    has (traject frs_step (consg d1 p1) n1) 
        (traject frs_step (consg d2 p2) n2) = false.
  move=> n1 n2 d1 d2 p1 p2 Hd; apply/hasP; case=> q.
  move/trajectP=> [i2 _ <-] {q}; move/trajectP=> [i1 _ Ei]; case/eqP: Hd.
  by move: (congr1 oddg Ei); rewrite !iter_frs_step !oddg_cons.
rewrite /bbf /frs_base; move: bb => [x0 x1 y0 y1].
repeat rewrite uniq_cat !Ufrs1 ?has_cat !Ufrs2 //.
Qed.

Lemma cm_frame_def : bbf =1 (fun p => bb (halfg (gedge p)) && negb (bb (halfg p))).
Proof.
have Efrs: forall n1 d d1 p p1,
    @traject gpointData frs_step (consg d1 p1) (locked S n1) (consg d p)
     = if d =d d1 then
         locked (@traject) _ frs_step (consg d1 p1) (S n1) (consg d p)
       else false.
  unlock; move/S=> n1 d d1 p p1.
  case: (d =P d1) => // Hd; apply/trajectP => [[i _ Dp]]; case: Hd.
  by move: (congr1 oddg Dp); rewrite iter_frs_step !oddg_cons.
have leqz_pos: forall x (n : nat), (x <= x + n)%Z.
  by move=> x n; rewrite /leqz -subz_sub subzz; case n.
have leqz_wid: forall x0 x1, (x0 <= x1)%Z -> {w : nat | (x0 + w)%Z = x1}.
  move=> x0 x1 Hx01; exists (pred (zwidth x0 x1)); move: (zwidth_eq x0 x1) Hx01.
  by rewrite /leqz -oppz_sub /zwidth; case (x1 - x0)%Z.
move=> p; rewrite -{1}[p]consg_odd_half halfg_edge.
case/halfg: p (oddg p) => [x y] d.
move: Hbb0; rewrite /garea /bbf /gwidth /gheight; move: bb => [x0 x1 y0 y1].
case: (zwidth x0 x1) (zwidth_eq x0 x1) => // [w] Dx1; rewrite mulnC.
case: (zwidth y0 y1) (zwidth_eq y0 y1) => // [h] Dy1 _.
rewrite [S]lock /frs_base; repeat rewrite mem_cat /setU !Efrs.
case: d; rewrite /= !addz0 !addn0 ?orbF -!andbA -lock;
 (apply/trajectP/idP;
   [ move=> [i Hi Dp]; move/(congr1 halfg): Dp;
     rewrite iter_frs_step !halfg_cons /= -?incz_def -?decz_def => [[<- <-]]
   | rewrite -?incz_def -?decz_def; move/and5P=> [Hx0 Hx1 Hy0 Hy1] ]).
- rewrite decz_inc -negb_leqz leqzz !andbF Dy1 !leqz_pos !andbT Dx1 leqz_add2l.
  by rewrite leqz_nat.
- rewrite Hx0 Hx1 leqz_dec {}Hy0 orbT /= negb_leqz leqz_inc -negb_leqz orbC.
  rewrite -leqz_dec_inc {}Hy1 /=; move/eqP=> <-.
  case: (leqz_wid _ _ Hx0) Hx1 => [i <-]; rewrite Dx1 leqz_add2l leqz_nat => Hi.
  by exists i; rewrite // iter_frs_step.
- rewrite incz_dec -leqz_inc_dec -negb_leqz leqzz Dx1 !leqz_pos !andbT.
  by rewrite Dy1 leqz_add2l leqz_nat.
- rewrite Hy0 Hy1 !andbT andbC leqz_inc {}Hx1 orbT /= negb_leqz leqz_inc.
  rewrite -negb_leqz {}Hx0 orbF; move/eqP=> <-; rewrite decz_inc.
  case: (leqz_wid _ _ Hy0) Hy1 => [i <-]; rewrite Dy1 leqz_add2l leqz_nat.
  by move=> Hi; exists i; rewrite // iter_frs_step.
- rewrite incz_dec -leqz_inc_dec -negb_leqz leqzz !andbF Dy1 leqz_pos !andbT.
  rewrite -[(x1 + _)%Z]/(x1 - i)%Z andbC -leqz_opp2 oppz_sub addzC leqz_pos andTb.
  by move: (zpos_subn w i); rewrite -ltnS Hi Dx1 -addz_subA => <-.
- rewrite Hx0 Hx1 /= andbC leqz_inc {}Hy1 orbT /= negb_leqz leqz_inc -negb_leqz.
  rewrite {}Hy0 orbF; move/eqP=> <-.
  case: (leqz_wid _ _ Hx0) Hx1 => [i <-]; rewrite Dx1 leqz_add2l leqz_nat.
  move=> Hi; exists (w - i); first by rewrite ltnS leq_subr.
  rewrite iter_frs_step decz_inc; congr consg; congr Gpoint.
  by rewrite zpos_subn Hi oppz_sub -addzA addz_subA subz_add.
- rewrite decz_inc -negb_leqz leqzz !andbF Dx1 leqz_pos !andbT /=.
  rewrite -[addz _ _]/(y1 - i)%Z andbC -leqz_opp2 oppz_sub addzC leqz_pos.
  by move: (zpos_subn h i); rewrite -ltnS Hi Dy1 -addz_subA => <- /=.
rewrite Hy0 Hy1 !andbT leqz_dec {}Hx0 orbT /= negb_leqz leqz_inc -negb_leqz.
rewrite -leqz_dec_inc {}Hx1 orbF; move/eqP=> <-.
case: (leqz_wid _ _ Hy0) Hy1 => [i <-]; rewrite Dy1 leqz_add2l leqz_nat.
move=> Hi; exists (h - i); first by rewrite ltnS leq_subr.
rewrite iter_frs_step; congr consg; congr Gpoint.
by rewrite zpos_subn Hi oppz_sub -addzA addz_subA subz_add.
Qed.

(* We build a dual hypermap (that is gmface == gnode^-1 & gmnode == gface^-1) *)
(* so that we use the definitions from snip.v and patch.v directly.           *)

Definition gm_grid := enum_grect (refine_rect bb).

Notation gbg := gm_grid.

Lemma gm_grid_def : forall p, gbg p = bb (halfg p).
Proof. by move=> p; rewrite /gbg mem_enum_grect mem_refine_rect. Qed.

Lemma size_gm_grid : size gbg = double (double (garea bb)).
Proof. by rewrite /gbg size_enum_grect garea_refine_rect. Qed.

Definition gmdartseq : gpointseq := cat bbf gbg.

Definition gmdart := SeqFinSet gmdartseq.

Lemma gmedgeP : forall u : gmdart, gmdartseq (gedge (subdE u)).
Proof.
case=> [x] /=; rewrite /gmdartseq !mem_cat /setU !cm_frame_def -!gm_grid_def.
by rewrite gedge2; case (gbg x); case (gbg (gedge x)).
Qed.

Definition gmnode p := if bbf p then prev bbf p else gedge (gnode p).

Lemma gmnodeP : forall u : gmdart, gmdartseq (gmnode (subdE u)).
Proof.
case=> [x] /=; rewrite /gmdartseq !mem_cat /setU /gmnode.
case Hx: (bbf x); first by rewrite mem_prev Hx.
by rewrite /= !gm_grid_def; move=> H; rewrite -halfg_face gmonicN H orbT.
Qed.

Definition gmface p :=
  if bbf (gedge p) then next bbf (gedge p) else gface (gedge p).

Lemma gmfaceP : forall u : gmdart, gmdartseq (gmface (subdE u)).
Proof.
move=> u; case: u (gmedgeP u) => [x _] /=.
rewrite /= /gmdartseq !mem_cat /setU /gmface.
case Hx: (bbf (gedge x)); first by rewrite mem_next Hx.
by rewrite /= !gm_grid_def; move=> H; rewrite halfg_face H orbT.
Qed.

Let gm_edge u : gmdart := subdI (gmedgeP u).
Let gm_node u : gmdart := subdI (gmnodeP u).
Let gm_face u : gmdart := subdI (gmfaceP u).

Lemma gm_boxmapP : @monic3 gmdart gm_edge gm_node gm_face.
Proof.
case=> [x Hx] /=; apply: subdE_inj; rewrite /= /gmface gedge2.
rewrite /gmdartseq mem_cat /setU in Hx.
case Hx': (bbf x) Hx; rewrite /gmnode.
  by rewrite mem_next Hx' prev_next // uniq_cm_frame.
by rewrite cm_frame_def halfg_face -!gm_grid_def andbC /= gmonicF => ->.
Qed.

Definition gm_boxmap := Hypermap gm_boxmapP.

Notation gmb := gm_boxmap.

Let gmbE : gmb -> gpoint := @subdE _ _.
Remark GMap_HgmbE : injective gmbE. Proof. apply: subdE_inj. Qed.
Notation HgmbE := GMap_HgmbE.

Definition gm_ring i := preimage_seq gmbE (mring (cm2 i)).

Lemma cm_memPx : forall (cm : cmatte) p,
 reflect (exists2 i, i < nbreg & cm i p) (cm_mem cm p).
Proof.
move=> cm p; rewrite /cm_mem; elim: nbreg => [|n Hrec]; first by right; case.
rewrite /= orbC; case: Hrec => Hp /=.
  by left; case: Hp => [i]; exists i; first by apply leqW.
apply introP; first by exists n; first by apply leqnn.
move=> Hnp [i Hi Hp']; rewrite ltnS leq_eqVlt in Hi.
by case/setU1P: Hi => [Di|Hi]; [ rewrite -Di Hp' in Hnp | case Hp; exists i ].
Qed.

Notation cm_memP := (cm_memPx _ _).

Lemma maps_gm_ring : forall i, i < nbreg -> maps gmbE (gm_ring i) = mring (cm2 i).
Proof.
move=> i Hi; apply: maps_preimage => [x Hix].
case: (subdIoptP gmdartseq x); first by move=> u _ <-; rewrite /gmbE codom_f.
rewrite /gmdartseq mem_cat /setU gm_grid_def; case/orP; right.
rewrite mring_def in Hix; case/andP: Hix => [Hx _].
by apply: sub_cm_bbox; apply/cm_memP; exists i.
Qed.

Lemma rect_gnode2 : forall p (r : grect),
  r p -> r (gnode (gnode p)) -> r (gnode p).
Proof.
move=> p [x0 x1 y0 y1]; rewrite {1}/gnode oddg_node /gnode -!addgA addg_inv.
case: p (oddg p) => [x y] /= d; move/and4P=> [Hx0 Hx1 Hy0 Hy1].
case: d; rewrite /= ?addz0 -?incz_def -?decz_def; case/and4P=> *;
by apply/and4P; split.
Qed.

Lemma end0g_gmcface : forall u v, cface u v = (end0g (gmbE u) =d end0g (gmbE v)).
Proof.
move=> u v; apply/idP/eqP.
  case/connectP=> p; move/fpathP=> [n <-] <- {p v}.
  rewrite last_traject; elim: n u => // [n Hrec] u; rewrite -iter_f -{}Hrec.
  case: u => [x _] /=; rewrite /gmface; case Hx: (bbf (gedge x)).
    move: (next_cycle cycle_cm_frame Hx); rewrite /mrlink; move/eqP=> <-.
    by rewrite end1g_edge.
  by rewrite end0g_face end1g_edge.
have Ehen: forall p, halfg (gedge (gnode p)) = halfg p.
  by move=> p; rewrite -halfg_face gmonicN.
have Hn1: forall w1 w2, gmbE w1 = gnode (gmbE w2) -> cface w1 w2.
  move=> [nx Hx] [x Hnx] /= Dnx; apply connect1; rewrite /eqdf /eqd /= /gmface.
  apply/eqP; move: Hx Hnx; rewrite /gmdartseq !mem_cat /setU !cm_frame_def.
  rewrite Dnx gedge2 -halfg_face gmonicN -!gm_grid_def -Dnx.
  case Hx: (gbg x); rewrite ?andbF //= ?orbF andbT Dnx.
  move: Hx; rewrite -{1 2}[x]gmonicE; move=> Hx1 Hx2 Hx0; case/idP: Hx1.
  rewrite gm_grid_def -halfg_face -gm_grid_def in Hx0.
  move: Hx0 Hx2; rewrite /gbg !mem_enum_grect; exact: rect_gnode2.
move/same_end0g; case/setU1P; first by move/HgmbE=> <-; exact: connect0.
case/setU1P; first by rewrite Sface; auto.
rewrite /setU1 orbF orbC; case/orP; move/eqP.
  move/(congr1 gnode); rewrite gnode4; auto.
  case: (subdIoptP gmdartseq (gnode (gmbE u))) => [u' _ Du'|Hn1u].
  rewrite -Du' Sface; move=> Dv; apply connect_trans with u'; auto.
  case: (subdIoptP gmdartseq (gnode (gmbE v))) => [v' _ Dv'|Hn1v].
  do 2 move/(congr1 gnode); rewrite gnode4 -Dv'.
  by move=> Du; apply connect_trans with v'; auto.
move=> Dv; case/idP: Hn1v; move: u v Dv Hn1u => [x Hx] [y Hy] /= Dy; move: Hx Hy.
rewrite /gmdartseq !mem_cat /setU -Dy !cm_frame_def -{1}[x]gnode4 !Ehen Dy.
rewrite -!gm_grid_def.
by case (gbg x); case (gbg y); case (gbg (gnode y)); case (gbg (gnode x)).
Qed.

Lemma scycle_gm_ring : forall i, i < nbreg -> scycle rlink (gm_ring i).
Proof.
move=> i Hi; have Ur: simple (gm_ring i).
move: (mring (cm2 i)) (gm_ring i) (maps_gm_ring Hi) (simple_mring (cm2 i)).
  elim=> [|_ c Hrec] [|[x Hx] c'] //= [<- Dc].
  move/andP=> [Hcx Uc]; rewrite (@simple_adds gmb) {}Hrec {Uc}// andbT.
  apply/hasP => [[u Hu Hux]]; case/mapsP: Hcx; exists (gmbE u).
    by rewrite -Dc maps_f.
  by rewrite end0g_gmcface in Hux; move/eqP: Hux.
apply/andP; split; last done; move/simple_uniq: Ur => Ur.
apply: cycle_from_next => // [u Hu]; rewrite /rlink end0g_gmcface.
rewrite -(next_maps HgmbE) // maps_gm_ring //.
rewrite -(mem_maps HgmbE) maps_gm_ring // in Hu.
by move: (next_cycle (cycle_mring _) Hu); rewrite /= end0g_edge.
Qed.

Lemma gm_plain : plain gmb.
Proof.
apply/plainP => [[x Hx]] /= _; split; first by apply HgmbE; rewrite /= gedge2.
by rewrite /eqd /= /gedge -{4}[x]addg0 (monic_eqd (addg_inv x)); case (oddg x).
Qed.

Lemma gm_disk_def : forall i, i < nbreg ->
   sub_set (diskN (gm_ring i)) (fun u => cm2 i (halfg (gmbE u))).
Proof.
move=> i Hi u; case/hasP=> v Hv; move/connectP=> [p Hp <-] {u}.
set v' := finv node v in Hp |- *.
have Hbbi: sub_set (cm2 i) bb.
  by move=> x Hx; apply sub_cm_bbox; apply/cm_memP; exists i.
have Hv': cm2 i (halfg (gmbE v')).
  rewrite -(mem_maps HgmbE) maps_gm_ring // mring_def in Hv.
  move/andP: Hv => [Hvi _].
  case Hvb: (bbf (subdE v)); first by rewrite cm_frame_def andbC Hbbi //= in Hvb.
  move: Hvb Hvi; rewrite -(f_finv (Inode gmb) v) -/v' /= /gmnode.
  case Hv': (bbf (subdE v')); first by rewrite mem_prev Hv'.
  by rewrite -halfg_face gmonicN.
elim: p {v Hv}v' Hv' Hp => [|v p Hrec] u //= Hu.
case/andP; move/andP=> [Heu Huv]; apply: Hrec.
rewrite -(mem_maps HgmbE) maps_gm_ring // mring_def Hu /= negb_elim in Heu.
case/clinkP: Huv; move/(congr1 gmbE)=> /=.
case Hu': (bbf (subdE u)); first by rewrite cm_frame_def andbC Hbbi // in Hu'.
  rewrite /gmnode; case Hv: (bbf (subdE v)) => Du.
    by rewrite [subdE u]Du mem_prev Hv in Hu'.
  by move: Hu; rewrite -halfg_face Du gmonicN.
by move <-; rewrite /gmface cm_frame_def andbC Hbbi //= halfg_face.
Qed.

Lemma disjoint_gm_disk : forall i j, regpair i j ->
  disjoint (diskN (gm_ring i)) (diskN (gm_ring j)).
Proof.
move=> i j Hij; move: (andP Hij) => [Hi' Hj]; have Hi := ltn_trans Hi' Hj.
apply/set0Pn => [[u]]; move/andP=> [Hui Huj].
by case/hasP: (Hcm2 Hij); exists (halfg (gmbE u)); apply gm_disk_def.
Qed.

Lemma gm_connected : connected gmb.
Proof.
pose hE u := halfg (gmbE u).
have DhE: forall u, halfg (gmbE u) = hE u by done.
have [u0 Hu0]: exists u0, bb (hE u0).
  move: Hbb0 (mem_enum_grect bb); rewrite -size_enum_grect.
  case: (enum_grect bb) => // [p er] _ Hbb.
  case: (subdIoptP gmdartseq (consg Gb00 p)) => [u _ Du|].
    by exists u; rewrite /hE /gmbE Du halfg_cons -Hbb /= setU11.
  rewrite /gmdartseq mem_cat /setU gm_grid_def halfg_cons -Hbb /=.
  by rewrite setU11 orbT.
suffice Hg: forall v, bb (hE v) -> connect glink u0 v.
  rewrite /connected /n_comp (cardD1 (root glink u0)).
  rewrite /setI (roots_root (Sglink gmb)); apply/set0P => [v].
  apply/and3P => [[Huv Dv _]]; case/eqP: Huv; move/(_ =P v): Dv => <-.
  apply: (rootP (Sglink gmb)); move: (subd_mem v); rewrite -/(gmbE v).
  rewrite /gmdartseq mem_cat; case/orP; last by rewrite gm_grid_def; auto.
  rewrite cm_frame_def; move/andP=> [Hev _].
  by apply connect_trans with (edge v); auto; rewrite Sglink connect1 ?glinkE.
move: u0 Hu0; have: sub_set bb bb by move.
elim: (S (garea bb)) {-2 4}bb (ltnSn (garea bb)) => // [n Hrec] r Hn.
move=> Hr u Hu v Hv; case: (pickP (fun w => (hE w =d hE u) && r (hE (edge w)))).
  rewrite ltnS in Hn; move=> w; case/andP; set p := gmbE w; move/eqP=> Dp Hrw.
  pose r1 := gchop_rect r p; pose r2 := gchop_rect r (gedge p).
  have Hr1w: r1 (hE w).
    by rewrite /r1 mem_gchop_rect /setI {2}/hE gchop_halfg Dp andbT.
  have Hr1: forall v', r1 (hE v') -> connect glink u v'.
    have Hr1: sub_set r1 r by move=> q; rewrite /r1 mem_gchop_rect; case/andP.
    apply: Hrec; [ idtac | by move; auto | by rewrite -Dp ].
    apply: leq_trans Hn; apply ltn_garea_sub_rect with (hE (edge w)); auto.
    rewrite /setD Hrw /r1 mem_gchop_rect -[p]gedge2 /setI gchop_edge.
    by rewrite /setC /hE /= gchop_halfg andbF.
  case Hr1v: (r1 (hE v)); auto.
  have Hr2v: r2 (hE v).
    by move/negbI: Hr1v; rewrite /r1 /r2 !mem_gchop_rect /setI Hv gchop_edge.
  apply: (connect_trans (Hr1 _ Hr1w)); apply connect_trans with (edge w).
    by apply connect1; exact: glinkE.
  have Hr2: sub_set r2 r by  move=> q; rewrite /r2 mem_gchop_rect; case/andP.
  apply Hrec with r2; auto; try by move; auto.
    apply: leq_trans Hn; apply ltn_garea_sub_rect with (hE u); auto.
    rewrite /setD Hu -Dp /r2 mem_gchop_rect /setI gchop_edge /setC.
    by rewrite /hE gchop_halfg andbF.
  by rewrite /r2 mem_gchop_rect /setI Hrw /hE /= gchop_halfg.
set p := hE u => Hp; have Hrp: r =1 set1 p.
  move=> q; apply/idP/eqP => [Hq|<-] //.
  have Hrq: all (fun d => gchop (consg d p) q) (traject ccw Gb00 4).
    apply/allPn => [[d _ Hqd]]; case (subdIoptP gmdartseq (consg d p)).
      move=> w _ Dw; case/idP: (Hp w).
      rewrite /hE [gmbE w]Dw halfg_cons /= set11 andTb.
      rewrite -/p -(halfg_cons d p) -[consg d p]gedge2 in Hu.
      move: ((gchop_rect_edge Hu) q).
      rewrite !mem_gchop_rect /setI gchop_edge /setC Hqd andbT -Dw.
      by move=> H; case/andP: (H Hq).
    by rewrite /gmdartseq mem_cat /setU gm_grid_def halfg_cons orbC Hr.
  rewrite /= /gchop !halfg_cons !oddg_cons andbCA andbC -!andbA /= andbA in Hrq.
  case/andP: Hrq; move: (p) (q) => [x y] [x' y']; rewrite -!eqz_leq.
  by do 2 move/eqP=> <-.
have Huv: traject gface (gmbE u) 4 (gmbE v).
  rewrite Hrp in Hv; rewrite -[gmbE v]consg_odd_half DhE -(eqP Hv).
  rewrite -[gmbE u]consg_odd_half DhE -/p /= /setU1.
  rewrite {1 2 4}/gface !halfg_face !oddg_face halfg_cons oddg_cons.
  by case (oddg (gmbE u)); case (oddg (gmbE v)); rewrite /= set11 ?orbT.
move/trajectP: Huv => [i _ Dv] {n Hrec Hv p Hp Hrp Hn}; rewrite Sglink.
elim: i u {r Hr Hu}(Hr _ Hu) Dv => [|i Hrec] u Hu Dv.
  by apply eq_connect0; exact: HgmbE.
have Hfeu: gmbE (face (edge u)) = gface (gmbE u).
  by rewrite /= /gmface -/(gmbE u) gedge2 cm_frame_def DhE Hu andbF.
apply: (connect_trans (Hrec (face (edge u)) _ _) _).
- by rewrite /hE Hfeu halfg_face.
- by rewrite Hfeu iter_f.
by apply connect1; rewrite -{2}[u]Eedge glinkN.
Qed.

Lemma gm_planar : planar gmb.
Proof.
pose ngm := double (garea bb) + (bbw + bbh).
have Engm: card gmb = double ngm.
  pose egmb := preimage_seq gmbE gmdartseq.
  have Degmb: maps gmbE egmb = gmdartseq.
    apply: maps_preimage => [x Hx]; apply/set0Pn.
    exists (@subdI _ gmdartseq _ Hx); exact: set11.
  have Uegmb: uniq egmb.
    rewrite -(uniq_maps HgmbE) Degmb /gmdartseq uniq_cat uniq_cm_frame.
    rewrite {2}/gbg uniq_enum_grect andbT.
    by apply/hasPn => [x Hx]; rewrite cm_frame_def andbC -gm_grid_def Hx.
  apply: (etrans (etrans (eq_card _) (card_uniqP Uegmb))).
    by move=> [x Hx]; rewrite -(mem_maps HgmbE) Degmb.
  rewrite -(size_maps gmbE) Degmb /gmdartseq size_cat /bbf.
  move: {1}bb => [x0 x1 y0 y1]; rewrite !size_cat !size_traject {x0 x1 y0 y1}.
  rewrite size_gm_grid addnC /ngm double_add; congr addn.
  by symmetry; rewrite addnC double_addnn -!addnA.
have EgmbE: fcard edge gmb = ngm.
  apply: eqP; rewrite -(order_div_card (Iedge gmb) gm_plain) // Engm.
  by apply/eqP; rewrite /= addn0 double_addnn.
have EgmbN: fcard node gmb = S (garea bb).
  pose ebf := preimage_seq gmbE (rev bbf).
  have Debf: (maps gmbE ebf = rev bbf).
    apply: maps_preimage => [x Hx]; apply/set0Pn.
    case: (subdIoptP gmdartseq x) => [u _ <-|]; first by exists u; apply: set11.
    by rewrite /gmdartseq mem_cat /setU -mem_rev Hx.
  have Uebf: uniq ebf by rewrite -(uniq_maps HgmbE) Debf uniq_rev uniq_cm_frame.
  have Hebf: fcycle node ebf.
    apply: (cycle_from_next Uebf) {u Hu} => [u Hu]; apply/eqP; apply HgmbE.
    rewrite -(next_maps HgmbE Uebf) Debf (next_rev uniq_cm_frame) /= -/(gmbE u).
    by rewrite /gmnode -mem_rev -Debf (mem_maps HgmbE) Hu.
  rewrite -add1n (n_compC ebf); congr addn.
    have [u Hu]: exists u, ebf u.
      have [x Hx]: exists x, rev bbf x.
        move: Hbb0; rewrite /garea /bbf mulnC.
        case: {3}bb => [x0 x1 y0 y1]; case: bbh => // [n] _.
        by exists (frs_base Gb00 x0 y0); rewrite mem_rev /= setU11.
      by rewrite -Debf in Hx; move/mapsP: Hx => [u Hu _]; exists u.
    apply: (etrans (esym (eq_n_comp_r _ _)) (n_comp_connect (Snode gmb) u)).
    exact: fconnect_cycle.
  have Hebf4: subset (setC ebf) (order_set node 4).
    apply/subsetP => [[x Hx] Hex]; rewrite /setC -(mem_maps HgmbE) Debf /= in Hex.
    set p := halfg x; have Hp := Hx; rewrite /gmdartseq mem_cat in Hp.
    rewrite /setU -mem_rev (negbE Hex) gm_grid_def /= -/p in Hp.
    have Hpd: forall d, gmdartseq (consg d p).
      move=> d; rewrite /gmdartseq mem_cat /setU gm_grid_def halfg_cons Hp.
      exact: orbT.
    pose pd d : gmb := subdI (Hpd d); have Epd: injective pd.
      move=> d d'; move/(congr1 gmbE); move/(congr1 oddg).
      by rewrite /pd /= !oddg_cons.
    have EpdN: forall d, node (pd d) = pd (ccw (ccw (ccw d))).
      move=> d; apply HgmbE; rewrite /= /gmnode cm_frame_def /pd halfg_cons.
      rewrite Hp andbF; symmetry; apply (monic_move gmonicF).
      by rewrite /gface halfg_cons oddg_cons ccw4.
    apply/eqP; apply: (@order_cycle _ _ (maps pd (Seq Gb01 Gb11 Gb10 Gb00))).
    - by rewrite /= /eqdf !EpdN !(inj_eqd Epd).
    - by rewrite /= /setU1 !(inj_eqd Epd).
    rewrite -(mem_maps HgmbE) [maps]lock /= -!lock.
    have <-: (gmbE (pd (oddg x)) = x) by rewrite /= /p consg_odd_half.
    by rewrite (mem_maps HgmbE) /= /setU1 !(inj_eqd Epd); case (oddg x).
  have HebfN: fclosed node (setC ebf).
    apply setC_closed; apply: (intro_closed (Snode _)) => [x y] Dy Hx.
    by rewrite -((_ =P y) Dy) -(fconnect_cycle Hebf Hx) fconnect1.
  apply: eqP; rewrite -(order_div_card (Inode gmb) Hebf4 HebfN) //; apply/eqP.
  rewrite -[4]/(2 * 2) -mulnA -2!double_mul2 -size_gm_grid.
  pose ebb := preimage_seq gmbE gbg; have Debb: maps gmbE ebb = gbg.
   apply: maps_preimage => [x Hx]; case: (subdIoptP gmdartseq x).
      by move=> u _ <-; rewrite codom_f.
    by rewrite /gmdartseq mem_cat /setU Hx orbT.
  have Uebb: uniq ebb.
    rewrite -(uniq_maps HgmbE) Debb; exact: uniq_enum_grect.
  rewrite -Debb size_maps; apply: (etrans (eq_card _) (card_uniqP Uebb)).
  move=> u; rewrite -(mem_maps HgmbE) Debb /setC -(mem_maps HgmbE) Debf mem_rev.
  case: u => [x] /=; rewrite /gmdartseq mem_cat /setU orbC.
  case Hx: (gbg x); last by rewrite /= => ->.
  by clear; rewrite cm_frame_def -!gm_grid_def Hx andbF.
pose rgmc := let: Grect x0 x1 y0 y1 := bb in Grect x0 (incz x1) y0 (incz y1).
have Ergmc: garea rgmc = S bbw * S bbh.
  rewrite {}/rgmc; case: bb Hbb0 => [x0 x1 y0 y1]; rewrite /garea /=.
  rewrite /zwidth !incz_def -!(addzC 1) -!addz_subA.
  by case: (x1 - x0)%Z => // [w]; rewrite mulnC; case (y1 - y0)%Z.
pose dnbb p := let: Gpoint x y := p in let: Grect x0 x1 y0 y1 := bb in
               oddg (Gpoint (x <= x1) (y <= y1)).
have Hnbb: forall p, rgmc p -> gmdartseq (dnbb p +g neg1g +g (p +g p)).
  move=> p Hp; rewrite /gmdartseq mem_cat; apply/orP; right.
  move: Hp; rewrite gm_grid_def halfg_add_double addgC /rgmc /dnbb.
  case Dbb: bb p => [x0 x1 y0 y1] [x y] /=.
  rewrite (leqz_inc y) orbC (leqz_inc x) orbC !leqz_inc2.
  have [Hx01 Hy01]: (x0 <= x1)%Z /\ (y0 <= y1)%Z.
    have [[x' y'] Hp]: exists p, enum_grect bb p.
      move: Hbb0; rewrite -size_enum_grect.
      case: (enum_grect bb) => // [p bb']; exists p; exact: setU11.
   rewrite mem_enum_grect Dbb in Hp; case/and4P: Hp.
   split; eapply leqz_trans; eauto.
   case Hx1: (x <= x1)%Z; case Hy1: (y <= y1)%Z;
   move/and4P=> /= [Hx0 Dx1 Hy0 Dy1]; rewrite ?addz0 -?decz_def; apply/and4P;
   split; auto; first
   [ by rewrite leqz_inc incz_def; apply/orP; right
   | by rewrite ?(eqP Dy1) ?(eqP Dx1) decz_inc ?leqzz ].
have EgmbF: fcard face gmb = garea rgmc.
  pose e0gm u := end0g (gmbE u).
  pose ergmc := preimage_seq e0gm (enum_grect rgmc).
  have Dergmc: maps e0gm ergmc = enum_grect rgmc.
    apply: maps_preimage => [x Hx]; rewrite mem_enum_grect in Hx.
    apply/set0Pn; exists (subdI (Hnbb _ Hx) : gmb).
    rewrite /preimage /e0gm /= /end0g halfg_add_double oddg_add_double.
    by rewrite -addgA addgCA; case: (dnbb x); rewrite addg0 set11.
  have UergmcF: uniq (maps (froot face) ergmc).
    move: Dergmc (uniq_enum_grect rgmc) => <-.
    elim: ergmc => //= [u ec Hrec]; move/andP=> [Hu Hec].
    rewrite {}Hrec {Hec}// andbT; apply/mapsP => [[v Hv Dv]].
    case/mapsP: Hu; exists v; first done.
    by apply: eqP; rewrite /e0gm -end0g_gmcface; apply/(rootP (Sface gmb)).
  rewrite -size_enum_grect -Dergmc size_maps -(size_maps (froot (@face gmb))).
  rewrite -(card_uniqP UergmcF); apply: eq_card => u; apply/idP/idP.
    rewrite /roots; case/andP; move/eqP=> <- _.
      have Hu: rgmc (e0gm u).
        have Hbb: forall p, bb (halfg p) -> rgmc (end0g p).
          rewrite /rgmc /end0g; case: bb => [x0 y0 x1 y1] p.
          case/halfg: p (oddg p) => [x y] d /=; move/and4P=> [Hx0 Hx1 Hy0 Hy1].
          case: d => /=; rewrite -?incz_def ?addz0 ?leqz_inc2;
          by repeat rewrite ?Hx0 ?Hx1 ?Hy0 ?Hy1 ?orbT // leqz_inc leqz_inc2.
       case: u => [x Hx]; rewrite /e0gm /= /gmdartseq mem_cat in Hx |- *.
       case/orP: Hx => Hx; last by rewrite Hbb -?gm_grid_def.
       rewrite cm_frame_def in Hx; case/andP: Hx => [Hex _].
       by rewrite -end1g_edge -end0g_face Hbb ?halfg_face.
     rewrite -mem_enum_grect -Dergmc in Hu; move/mapsP: Hu => [v Hv Dv].
     apply/mapsP; exists v; first done; apply: (rootP (Sface _)).
     by rewrite end0g_gmcface; apply/eqP.
  by move/mapsP=> [v _ <-]; rewrite /setI (roots_root (Sface gmb)).
apply/eqP; rewrite /genus /genus_lhs Engm ((_ =P 1) gm_connected).
rewrite /genus_rhs EgmbE EgmbN EgmbF Ergmc /= !double_addnn addn1 !addSn.
rewrite !addnS add0n !subSS subn_add2l /ngm double_addnn -!addnA subn_add2l.
by rewrite mulnC /= mulnC addnC -!addnA addnCA subnn.
Qed.

Inductive gm_cutout (n : nat) : Type :=
  GmCutout : forall (g : hypermap) (h : g -> gmb),
    injective h -> planar g ->
    (forall u, (exists2 i, i < n & diskE (gm_ring i) u) \/ (exists x, h x = u)) ->
    (forall x, h (edge x) = edge (h x)) ->
    (forall x, (exists2 i, i < n & gm_ring i (h x)) \/ h (node x) = node (h x)) ->
    (forall x y, cface (h x) (h y) = cface x y) ->
    (forall i, i < n -> fcycle node (rev (preimage_seq h (gm_ring i)))) ->
  gm_cutout n.

Lemma has_cutout : gm_cutout nbreg.
Proof.
elim: {-2}nbreg (leqnn nbreg) => [|j Hrec] Hj.
  exists gmb (fun u : gmb => u); auto; try exact gm_planar; try by move.
  by move=> u; right; exists u.
move: {Hrec}(Hrec (ltnW Hj)) => [g h Ih Hg Hh HhE HhN HhF HgN].
pose rj := preimage_seq h (gm_ring j).
have Drj: maps h rj = gm_ring j.
  apply: maps_preimage => [u Hu].
  case: (Hh u) => [[i Hi Hui]|[x <-]]; last exact: codom_f.
  have Hij: regpair i j by apply/andP; split.
  case/set0Pn: (disjoint_gm_disk Hij); exists u.
  by rewrite /setI !diskN_E /setU Hu Hui orbT.
have Hrj: scycle rlink rj.
  case/andP: (scycle_gm_ring Hj) => [Hgrj Ugrj].
  have Urj: simple rj by rewrite -(simple_maps HhF) Drj.
  rewrite /scycle Urj andbT; move/simple_uniq: Urj => Urj.
  apply: cycle_from_next => // [x]; rewrite -(mem_maps Ih) /rlink -HhF.
  rewrite -(next_maps Ih Urj) Drj HhE; exact: (next_cycle Hgrj).
have HhjN: forall x, diskN rj x = diskN (gm_ring j) (h x).
  have HdN: forall y, diskN (gm_ring j) (h y) -> node (h y) = h (node y).
  move=> y Hy; case: (HhN y) => // [[i Hi Hiy]].
    have Hij: regpair i j by apply/andP; split.
    case/set0Pn: (disjoint_gm_disk Hij); exists (h y).
    by rewrite /setI diskN_E /setU Hy Hiy.
  have ErjN := fclosed1 (diskN_node (gm_ring j)).
  have ErjE := fclosed1 (diskE_edge gm_planar (scycle_gm_ring Hj)).
  have HdN': forall y, diskN (gm_ring j) (h (node y)) -> node (h y) = h (node y).
    move=> y Hy; apply HdN; rewrite -(finv_f (Inode g) y) /finv.
    elim: {y}(pred (order node (node y))) {-2}(node y) Hy => // [k Hrec] y Hy.
    by rewrite -iter_f; apply: Hrec; rewrite -(HdN _ Hy) -ErjN.
  move=> x; apply/idP/idP.
    case/hasP=> y Hy; move/connectP=> [p Hp <-] {x}; move: Hp.
    set x := finv node y; have Hx: diskN (gm_ring j) (h (node x)).
      by rewrite /x (f_finv (Inode g)) diskN_E /setU -Drj mem_maps ?Hy.
    elim: p {y Hy}x Hx => [|y p Hrec] x Hx /=; first by clear; rewrite ErjN HdN'.
    case/andP=> Hxy; apply: {Hrec}Hrec; case/andP: Hxy => Hrjx.
    case/clinkP=> <-; first by rewrite ErjN HdN'.
    rewrite diskN_E; apply/orP; right; rewrite ErjE -HhE Eface.
    by rewrite /diskE /setD -Drj (mem_maps Ih) Hrjx Drj ErjN HdN'.
  move=> Hx; case: (hasP Hx) => u Hu; case/connectP=> p.
  elim/last_ind: p x Hx => [|p v Hrec] x Hx.
    rewrite (fclosed1 (diskN_node rj)) diskN_E /setU -(mem_maps Ih) Drj -HdN //.
    by move=> _ <-; rewrite /last (f_finv (Inode gmb)) Hu.
  rewrite last_add_last -cats1 path_cat; move/and3P=> [Hp Huv _] Dv.
  rewrite (fclosed1 (diskN_node rj)); rewrite {v}Dv in Huv.
  case/andP: Huv => Hrv; case/clinkP=> Ep.
    move: (Hx) Hp Ep; rewrite ErjN HdN //; exact: Hrec.
  rewrite diskN_E /setU; case Hnx: (rj (node x)) => //.
  move/(monic_move (Eface _)): Ep => Ep.
  rewrite (fclosed1 (diskE_edge Hg Hrj)) /diskE /setD -(mem_maps Ih) Drj HhE.
  rewrite -HdN // -Ep Hrv; move: Hp (Ep); rewrite HdN // -HhE; apply: Hrec.
  rewrite diskN_E; apply/orP; right; rewrite HhE -ErjE /diskE /setD.
  by rewrite -Drj (mem_maps Ih) Hnx Drj -HdN // -ErjN.
have HhjE: forall x, diskE rj x = diskE (gm_ring j) (h x).
 by move=> x; rewrite /diskE /setD -HhjN -Drj (mem_maps Ih).
have Hgrj := snip_patch Hg Hrj; case: Hgrj (patch_face_r Hgrj).
move=> _ Ih' _ Hrj' _ _ _ _; move: (codom_snipr Hg Hrj) Ih' Hrj'.
move: (@snipr _ Hg _ Hrj) (snipr_ring Hg Hrj) (maps_snipr_ring Hg Hrj).
set g' := snip_rem _ _ => h' rj' Drj' Hh' Ih' Hrj' Hh'E Hh'N Hh'F.
exists g' (comp h h'); rewrite /comp.
- exact: (inj_comp Ih).
- exact: planar_snipr.
- move=> u; case: (Hh u) => [[i Hi Hu]|[x <-]].
    by left; exists i; first by apply ltnW.
  case Hx: (codom h' x); first by right; exists (iinv Hx); rewrite f_iinv.
  by left; exists j; [exact: leqnn | rewrite Hh' /setC HhjE in Hx; move/idP: Hx ].
- by move=> x'; rewrite Hh'E HhE.
- move=> x'; case Hx': (gm_ring j (h (h' x'))).
    by left; exists j; first by apply leqnn.
  case: (HhN (h' x')) => [[i Hi Hhx']|<-].
    by left; exists i; first by apply ltnW.
  right; congr h; apply Hh'N; rewrite /setC -(mem_maps Ih') Drj'.
  by rewrite mem_rev -(mem_maps Ih) Drj Hx'.
- by move=> *; rewrite HhF Hh'F.
move=> i; rewrite ltnS leq_eqVlt; case/setU1P=> [-> {i}|Hi].
  have <-: rev rj' = preimage_seq (fun x : g' => h (h' x)) (gm_ring j).
    symmetry; apply: (inj_maps Ih'); apply: (inj_maps Ih).
    rewrite -maps_comp maps_rev Drj' rev_rev Drj; apply: maps_preimage.
    move=> u Hu; case: (Hh u) => [[i' Hi' Hui]|[x Du]].
      have Hi'j: regpair i' j by apply/andP; split.
      case/set0Pn: (disjoint_gm_disk Hi'j); exists u.
      by rewrite /setI !diskN_E /setU Hu Hui orbT.
    have Hx: codom h' x by rewrite Hh' /setC /diskE /setD -(mem_maps Ih) Drj Du Hu.
    rewrite -Du -(f_iinv Hx); exact: codom_f.
  by rewrite rev_rev; case/andP: Hrj'.
move: (HgN _ Hi); set ri := preimage_seq h (gm_ring i) => Hri.
have Dri: maps h ri = gm_ring i.
  apply: maps_preimage => [u Hu].
  case: (Hh u) => [[i' Hi'j Hui]|[x <-]]; last by apply codom_f.
 case: (ltnP i' i) => Hi'.
    have Hi'i: regpair i' i by apply/andP; split; last by eapply ltn_trans; eauto.
    case/set0Pn: (disjoint_gm_disk Hi'i); exists u.
    by rewrite /setI !diskN_E /setU Hu Hui orbT.
  rewrite leq_eqVlt in Hi'; case/setU1P: Hi' => [Di'|Hi'].
    by rewrite -Di' /diskE /setD Hu in Hui.
  have Hii': regpair i i' by apply/andP; split; last by eapply ltn_trans; eauto.
  case/set0Pn: (disjoint_gm_disk Hii'); exists u.
  by rewrite /setI !diskN_E /setU Hu Hui orbT.
set ri' := preimage_seq h' ri.
have Hij: regpair i j by apply/andP; split.
have Dri': maps h' ri' = ri.
  apply: maps_preimage => [x Hx]; rewrite Hh' /setC HhjE; apply/nandP; right.
  move: (negbI (set0P (disjoint_gm_disk Hij) (h x))).
  by rewrite /setI diskN_E /setU -Dri (mem_maps Ih) Hx.
have <-: ri' = preimage_seq (fun x : g' => h (h' x)) (gm_ring i).
  apply (inj_maps Ih'); apply (inj_maps Ih); rewrite Dri' Dri -maps_comp.
  apply: esym; apply: maps_preimage => u Hu.
  rewrite -Dri -Dri' -maps_comp in Hu; case/mapsP: Hu => [x _ <-]; exact: codom_f.
have Uri': uniq (rev ri').
  rewrite uniq_rev -(uniq_maps Ih') Dri' -(uniq_maps Ih) Dri; apply simple_uniq.
  by case/andP: (scycle_gm_ring (ltn_trans Hi Hj)).
apply: (cycle_from_next Uri') => x Hx; apply/eqP; apply Ih'.
rewrite -(next_maps Ih' Uri') -(mem_maps Ih') maps_rev Dri' in Hx |- *.
rewrite -((node (h' x) =P _) (next_cycle Hri Hx)); apply Hh'N.
rewrite /setC -(mem_maps Ih') Drj' mem_rev; apply/idP => Hxj.
case/set0Pn: (disjoint_gm_disk Hij); exists (h (h' x)).
by rewrite /setI !diskN_E /setU -Dri -Drj !(mem_maps Ih) Hxj -mem_rev Hx.
Qed.

Definition grid_map : hypermap :=
  let: GmCutout g _ _ _ _ _ _ _ _ := has_cutout in dual g.

Lemma planar_bridgeless_grid_map : planar_bridgeless grid_map.
Proof.
rewrite /grid_map; case: has_cutout => [g h Ih Hg Hh HhE HhN HhF Hgr].
split; rewrite ?planar_dual ?bridgeless_dual //.
have EitS: forall n, iter n S 0 = n by elim=> // *; congr S.
pose ri i := preimage_seq h (gm_ring i).
have Eri: forall i, i < nbreg -> maps h (ri i) = gm_ring i.
  move=> i Hi; apply: maps_preimage => u Hu.
  case: (Hh u) => [[j Hj Huj]|[x <-]]; last exact: codom_f.
 case: (ltnP i j) => Hij.
    have Hijn: regpair i j by rewrite /regpair Hij.
    case/idP: (set0P (disjoint_gm_disk Hijn) u).
    by rewrite /setI !diskN_E /setU Hu Huj orbT.
  rewrite leq_eqVlt in Hij; case/setU1P: Hij => [Dj|Hji].
    by rewrite /diskE /setD Dj Hu in Huj.
  have Hjin: regpair j i by rewrite /regpair Hji.
  case/idP: (set0P (disjoint_gm_disk Hjin) u).
  by rewrite /setI !diskN_E /setU Hu Huj orbT.
have Hri: forall i, i < nbreg -> forall x, gm_ring i (h x) -> cnode x =1 ri i.
  move=> i Hi x Hx y; rewrite -mem_rev; apply: fconnect_cycle; first exact: Hgr.
  by rewrite mem_rev -(mem_maps Ih) Eri.
apply/set0P => x; case: (hasPx (fun i => gm_ring i (h x)) (traject S 0 nbreg)).
  case=> i'; move/trajectP=> [i Hi <-] {i'}; rewrite EitS.
  move=> Hx; rewrite (Hri _ Hi) // -(mem_maps Ih) HhE Eri //.
  move: Hx; rewrite -!(mem_maps HgmbE) maps_gm_ring //= !mring_def gedge2 /gmbE.
  case/andP => -> _; exact: andbF.
move=> Hx'; have Hx: forall i, i < nbreg -> gm_ring i (h x) = false.
  move=> i Hi; apply/idP => [Hx]; case: Hx'; exists i; last done.
  by apply/trajectP; exists i.
apply/idP => Hex {Hx'}; have Hhex: cnode (h x) (h (edge x)).
  move/connectP: Hex => [p Hp <-].
  elim: p x Hx Hp => [|y p Hrec] x Hx; first by rewrite connect0.
  case: (HhN x) => [[i Hi Hix]|Dnx]; first by rewrite Hx in Hix.
  rewrite cnode1 -Dnx; case/andP; move/eqP=> <- {y}; apply: Hrec.
  move=> i Hi; apply/idP => [Hnx]; case/idP: (Hx _ Hi); rewrite -Eri ?maps_f //.
  by rewrite -(Hri _ Hi _ Hnx) Snode fconnect1.
rewrite HhE in Hhex; move/h: x Hhex {Hx Hex} => u Hu.
case Hfu: (bbf (gmbE u)).
  pose ebf := preimage_seq gmbE (rev bbf).
  have Debf: maps gmbE ebf = rev bbf.
    apply: maps_preimage => [x Hx]; apply/set0Pn.
    case: (subdIoptP gmdartseq x) => [v _ <-|]; first by exists v; exact: set11.
    by rewrite /gmdartseq mem_cat /setU -mem_rev Hx.
  have Uebf: uniq ebf by rewrite -(uniq_maps HgmbE) Debf uniq_rev uniq_cm_frame.
  have Hebf: fcycle node ebf.
    apply: (cycle_from_next Uebf) {u Hu Hfu} => [u Hu]; apply/eqP; apply HgmbE.
    rewrite -(next_maps HgmbE Uebf) Debf (next_rev uniq_cm_frame) /= -/(gmbE u).
    by rewrite /gmnode -mem_rev -Debf (mem_maps HgmbE) Hu.
  have Hfeu: bbf (gmbE (edge u)).
    rewrite -mem_rev -Debf (mem_maps HgmbE) in Hfu.
    by rewrite -mem_rev -Debf (mem_maps HgmbE) -(fconnect_cycle Hebf Hfu).
  by move: Hfu Hfeu; rewrite !cm_frame_def /= /gmbE; case/andP=> ->; rewrite andbF.
suffice: halfg (gmbE u) = halfg (gmbE (edge u)).
  apply: (elimF eqP); exact: neq_halfg_edge.
move/connectP: Hu => [p Hp <-]; elim: p u Hfu Hp => //= [v p Hrec] u Hu.
rewrite {1}/eqdf /eqd /= -/(gmbE u) -/(gmbE v) {1}/gmnode Hu; case/andP.
rewrite -{2}[gmbE u]gmonicN halfg_face; move/eqP=> Dv; rewrite Dv; apply: Hrec.
rewrite -Dv cm_frame_def andbC -halfg_face gmonicN -gm_grid_def.
by move: (subd_mem u); rewrite -/(gmbE u) /gmdartseq mem_cat /setU Hu /= => ->.
Qed.

Lemma grid_map_coloring : four_colorable grid_map ->
  exists2 k, (forall i, i < nbreg -> k i < 4)
          &  (forall i j, regpair i j -> ab_adj ab0 i j -> negb (k i =d k j)).
Proof.
rewrite /grid_map; move: has_cutout => [g h Ih Hg Hh HhE HhN HhF Hgr].
case: (four_colorable_dual g) => [H _]; case/H {H} => [k [HkE HkN]].
pose ri i := preimage_seq h (gm_ring i).
have Eri: forall i, i < nbreg -> maps h (ri i) = gm_ring i.
  move=> i Hi; apply: maps_preimage => u Hu.
  case: (Hh u) => [[j Hj Huj]|[x <-]]; last exact: codom_f.
  case: (ltnP i j) => Hij.
    have Hijn: regpair i j by rewrite /regpair Hij.
    case/idP: (set0P (disjoint_gm_disk Hijn) u).
    by rewrite /setI !diskN_E /setU Hu Huj orbT.
  rewrite leq_eqVlt in Hij; case/setU1P: Hij => [Dj|Hji].
    by rewrite /diskE /setD Dj Hu in Huj.
  have Hjin: regpair j i by rewrite /regpair Hji.
  case/idP: (set0P (disjoint_gm_disk Hjin) u).
  by rewrite /setI !diskN_E /setU Hu Huj orbT.
have Hri: forall i, i < nbreg -> forall x, ri i x -> cnode x =1 ri i.
  move=> i Hi x Hx y; rewrite -mem_rev.
  by apply: fconnect_cycle; [ exact: Hgr | rewrite mem_rev ].
pose sc := Seq Color0 Color1 Color2 Color3.
exists (fun i => if pick (ri i) is Some x then index (k x) sc else 0).
  by move=> i _; case: (pick (ri i)) => // [x]; case (k x).
move=> i j Hij; rewrite -ab_adj_refine; move/(Habcm2 Hij); rewrite /cm_adj.
case/hasP=> x0; move: (andP Hij) => [Hi' Hj]; have Hi := ltn_trans Hi' Hj.
rewrite -!maps_gm_ring //; move/mapsP=> [u Hui Dx0].
have <-: gmbE (edge u) = gedge x0 by rewrite -Dx0.
rewrite {x0 Dx0}(mem_maps HgmbE); move: Hui; rewrite -!Eri //.
move/mapsP=> [x Hx <-] {u}; rewrite -HhE (mem_maps Ih) => Hex.
case: (pickP (ri i)) => [ex' Hex'|Dri']; last by rewrite Dri' in Hex.
rewrite -(Hri _ Hi _ Hex') in Hex; rewrite (fconnect_invariant HkN Hex).
case: (pickP (ri j)) => [x' Hx'|Drj']; last by rewrite Drj' in Hx.
rewrite -(Hri _ Hj _ Hx') in Hx; rewrite (fconnect_invariant HkN Hx).
by move: (HkE x); rewrite /invariant; case (k x); case (k (edge x)).
Qed.

End GridMap.

Set Strict Implicit.
Unset Implicit Arguments.

