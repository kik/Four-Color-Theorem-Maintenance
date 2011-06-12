(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import paths.
Require Import znat.
Require Import grid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Mattes are finite sets of grid squares that are delimited by a simple grid  *)
(* ring; we explicitly include the enumeration of the region and the ring.     *)
(* Mattes will be used to define conservative approximations of aribitrary     *)
(* connected open sets of points (regions). We therefore need to provide       *)
(* operations for extending a matte in order to improve the approximation.     *)
(* This involves three different operations :                                  *)
(*   - adding pixels within a specified rectangle that the matte meets, so     *)
(*     that a specific pixel is covered.                                       *)
(*   - adding the pixels surrounding a grid point of the matte boundary.       *)
(*   - refining the grid to ensure that the two previous operations are safe.  *)
(* Note that we can't add large rectangle blindly to a matte if we want to     *)
(* preserve its geometrical properties (we might end up with a disconnected    *)
(* contour). We reduce the first two operations above to two primitives, which *)
(* add a pixel that has exactly one or two consecutive sides in common with    *)
(* the matte, respectively (more precisely, 2 or 3 consecutive vertices in     *)
(* common with the matte contour vertices). We don't actually provide the      *)
(* second operation here, because it requires multiple grid refinement.        *)
(* Instead we provide a basic have that needs to be iterated to accomplish the *)
(* operation, along with the metric ("matte_order") that decreases with that   *)
(* step.                                                                       *)

Definition mrlink p1 p2 := end1g p1 =d end0g p2.

Record matte : Set := Matte {
  mdisk :> gpointseq;
  mring : gpointseq;
  matte_ne : 0 < size mdisk;
  cycle_mring : cycle mrlink mring;
  simple_mring : uniq (maps end0g mring);
  mring_def : mring =1 (fun x => mdisk (halfg x) && negb (mdisk (halfg (gedge x))))
}.

Lemma mring_edge : forall m p, mring m p -> negb (mring m (gedge p)).
Proof.
by case=> /= [c d _ _ _ Dc] p; rewrite !Dc; move/andP=> [_ H]; rewrite (negbE H).
Qed.

(* Initial single_square matte. *)

Section PointMatte.

Variable p : gpoint.

Let pmdisk : gpointseq := Adds p seq0.
Let pmring : gpointseq := maps (fun d => consg d p) (Seq Gb00 Gb10 Gb11 Gb01).

Lemma pmatte_ne : 0 < size pmdisk. Proof. done. Qed.

Lemma cycle_pmring : cycle mrlink pmring.
Proof. by rewrite /= /mrlink /end0g /end1g !halfg_cons !oddg_cons /= !set11. Qed.

Lemma simple_pmring : uniq (maps end0g pmring).
Proof.
by rewrite /= /setU1 /end0g !halfg_cons !oddg_cons !(monic_eqd (addg_inv p)).
Qed.

Lemma pmring_def :
  pmring =1 (fun x => pmdisk (halfg x) && negb (pmdisk (halfg (gedge x)))).
Proof.
move=> x; rewrite -{1}[x]consg_odd_half halfg_edge.
case Hx: (pmdisk (halfg x)).
  rewrite /= /setU1 orbF in Hx; rewrite -(eqP Hx) /= /setU1 !orbF.
  rewrite -{9}[p]addg0 (monic_eqd (addg_inv p)).
  by case (oddg x); rewrite set11 ?orbT.
apply/mapsP => [[d _ Dx]]; move: (congr1 halfg Dx); rewrite !halfg_cons.
by move=> Dp; rewrite /pmdisk Dp /= setU11 in Hx.
Qed.

Definition point_matte := Matte pmatte_ne cycle_pmring simple_pmring pmring_def.

End PointMatte.

(* Grid refinement for mattes.                                                  *)

Section RefineMatte.

Fixpoint refine_mring (c : gpointseq) : gpointseq :=
  if c is Adds p c' then
    Seq (consg (oddg p) p) (consg (oddg p) (gface p)) & (refine_mring c')
  else seq0.

Fixpoint refine_mdisk (md : gpointseq) : gpointseq :=
  if md is Adds p md' then
    Seq (consg Gb00 p) (consg Gb10 p) (consg Gb11 p) (consg Gb01 p)
      & (refine_mdisk md')
  else seq0.

Lemma mem_refine_mdisk : forall md p, refine_mdisk md p = md (halfg p).
Proof.
move=> md p; elim: md => //= [q md Hrec]; rewrite /setU1 Hrec !orbA; congr orb.
rewrite -!orbA; apply/idP/eqP; first by case/or4P=> H; rewrite -(eqP H) halfg_cons.
by rewrite -{-1}[p]consg_odd_half=> <-; case (oddg p); rewrite set11 /= ?orbT.
Qed.

Variable m : matte.

Lemma refine_matte_ne : 0 < size (refine_mdisk m).
Proof. by case: (mdisk m) (matte_ne m). Qed.

Lemma cycle_refine_mring : cycle mrlink (refine_mring (mring m)).
Proof.
case: (mring m) (cycle_mring m) => // [p0 c]; rewrite !(cycle_path p0).
rewrite {1}/last -/(last p0); set q := last p0 c.
have <-: consg (oddg q) (gface q) = last p0 (refine_mring (Adds p0 c)).
  by rewrite {}/q /=; elim: c p0 => /=.
elim: {p0 c}(Adds p0 c) q => //= [p c Hrec] q; move/andP=> [Hqp Hc]; move: Hqp.
rewrite {}Hrec {c Hc}// andbT /mrlink /end0g /end1g !halfg_cons !oddg_cons.
move/eqP=> Dp; rewrite /gface -{1 3}[p]consg_odd_half /consg.
rewrite addgA -addgA -(addgC (halfg q)) {}Dp addgA (addgC (halfg p)) !addgA set11.
by rewrite addgC -!addgA addgCA addgC -!addgA set11.
Qed.

Lemma mem_refine_mring : forall (c : gpointseq) p,
 reflect (exists2 q, c q & p = consg (oddg q) q \/ p = consg (oddg q) (gface q))
         (refine_mring c p).
Proof.
move=> c p; elim: c => [|q c Hrec] /=; first by right; case.
apply: (iffP setU1P).
  case; first by exists q; [ exact: setU11 | left ].
  case/setU1P; first by exists q; [ exact: setU11 | right ].
  by case/Hrec=> [q' Hq' Dp]; exists q'; first exact: setU1r.
case=> q'; case/setU1P=> [<-|Hq'].
  by case=> <-; [ left | right; exact: setU11 ].
by right; apply setU1r; apply/Hrec; exists q'.
Qed.

Lemma simple_refine_mring : uniq (maps end0g (refine_mring (mring m))).
Proof.
elim: (mring m) (simple_mring m) (@mring_edge m) => //= [p c Hrec].
move/andP=> [Hp Uc] HpcE.
have HcE: forall q, c q -> negb (c (gedge q)).
  by move=> q Hq; case/norP: (HpcE _ (setU1r _ Hq)).
rewrite {}Hrec {Hc HcE}// andbT; apply/andP; split.
  apply/setU1P => [[Dp|Hp']].
    rewrite /end0g !halfg_cons !oddg_cons -!(addgC (oddg p)) in Dp.
    move: (congr1 oddg (monic_inj (addg_inv _) Dp)).
    by rewrite oddg_face; case (oddg p).
  case/mapsP: Hp' => [q Hq Dq].
  case/mem_refine_mring: Hq => [q' Hq' [Dq'|Dq']].
    case/mapsP: Hp; exists q'; auto; rewrite -halfg_add_odd addgC.
    move: Dq; rewrite -!halfg_add_odd Dq' !oddg_cons addgC /consg addgA.
    rewrite (addgC (oddg p)) -(addgA (p +g p)) !halfg_add_double !halfg_double.
    by move <-.
  move: Dq; rewrite -!halfg_add_odd Dq' !oddg_cons addgC /consg addgA.
  rewrite (addgC (oddg p)) -(addgA (p +g p)) !halfg_add_double !halfg_double.
  move/(congr1 oddg); rewrite /gface /consg addgA oddg_add_double.
  rewrite (addgC p) -{2}[p]consg_odd_half /consg addgA oddg_add_double oddg_double.
  by case (oddg q').
apply/mapsP => [[q Hq]]; move/esym; rewrite -!halfg_add_odd oddg_cons.
rewrite addgC /consg addgA halfg_add_double halfg_double (addgC q).
case/mem_refine_mring: Hq => [q' Hq' [Dq|Dq]];
  rewrite {}Dq oddg_cons /consg addgA halfg_add_double halfg_double.
- move/(congr1 oddg); rewrite /gface /consg addgA oddg_add_double.
  rewrite -{2}[q']consg_odd_half /consg addgA oddg_add_double oddg_double.
  by case (oddg p).
case/norP: {HpcE}(HpcE _ (setU1r _ Hq')) => [Epq' _].
rewrite /gface /consg addgCA -/(consg (oddg p) (halfg p)) consg_odd_half.
rewrite addgCA consgI consg_odd_half=> Dq'.
rewrite /gedge addgA (addgC q') -Dq' -addgA addgCA -{1}[p]addg0 in Epq'.
rewrite (monic_eqd (addg_inv p)) in Epq'.
have Dq1: oddg q' = oddg p.
  move: (congr1 oddg Dq'); rewrite oddg_add {1}[oddg]lock oddg_add -lock.
  by case: (oddg p) Epq'; case: (oddg q').
rewrite Dq1 in Dq'; case/mapsP: Hp; exists q'; auto.
by rewrite (monic_inj (addg_inv _) Dq').
Qed.

Lemma refine_mring_def : let md' := refine_mdisk (mdisk m) in
 refine_mring (mring m)
   =1 (fun p => md' (halfg p) && negb (md' (halfg (gedge p)))).
Proof.
move: (mdisk m) (mring_def m) (mem_refine_mdisk (mdisk m)) => md Dmd Dmd' /= p.
rewrite /= !{}Dmd' halfg_edge.
apply/(mem_refine_mring _ _)/andP => [[q Hq Dp]|[Hp Hep]].
  rewrite Dmd halfg_edge addgC in Hq; case/andP: Hq => [Hq HqE].
  by case: Dp => ->; rewrite !halfg_cons oddg_cons ?halfg_face; split;
    rewrite // addgC halfg_add ?halfg_face ?oddg_face; case: (oddg q) HqE.
set q := halfg p; set d := oddg p; rewrite addgC halfg_add addgC -/q -/d in Hep.
have Hqd: set2 d (ccw d) (oddg q).
  move: Hp Hep; rewrite -/q -{1}[halfg q]addg0.
  by case: d; case: (oddg q) => //= H; case/idP.
exists (consg (oddg p) (halfg (halfg p))).
  rewrite Dmd halfg_edge halfg_cons oddg_cons Hp -/q -/d /=.
  by case: (oddg q) Hqd Hep; case d.
rewrite oddg_cons /gface oddg_cons halfg_cons -/d -/q.
case/orP: Hqd; move/eqP=> Dq; rewrite {2}[d]Dq /q /d !consg_odd_half; auto.
Qed.

Definition refine_matte :=
  Matte refine_matte_ne cycle_refine_mring simple_refine_mring refine_mring_def.

Lemma mem_refine_matte : forall p, refine_matte p = m (halfg p).
Proof. exact: mem_refine_mdisk. Qed.

Lemma refine_matte_refined : forall r, refined_in (refine_matte : set _) r.
Proof. by move=> r p q _ Dq; rewrite !mem_refine_matte Dq. Qed.

End RefineMatte.

Section ExtendMatte.

Variable m : matte.

Definition ext_mdisk p : gpointseq := Adds (halfg p) m.

Lemma ext_mdisk_ne : forall p, 0 < size (ext_mdisk p).
Proof. done. Qed.

Definition ehex p := gchop_rect (gtouch (halfg p)) p.

Definition equad p := gchop_rect (ehex p) (gface p).

Lemma ehexF : forall p, sub_set (equad p) (ehex (gface p)).
Proof.
move=> p q; rewrite /equad /ehex halfg_face !mem_gchop_rect /setI.
by rewrite mem_gchop_rect /setI -andbA andbCA; case/andP.
Qed.

Lemma end0g_equad : forall p, negb (has (equad (gface p)) m) ->
  m (end0g p) = false.
Proof.
move=> p Hp; apply/idP => [Hmp]; case/idP: {Hp Hmp}(hasPn Hp _ Hmp).
rewrite /equad /ehex /gchop_rect !halfg_face !oddg_face /= /end0g.
case: (halfg p) => [x y] /=; rewrite !leq_decz_z !leq_z_incz.
case (oddg p); rewrite /= ?addz0 -?incz_def -?decz_def;
 do 2 rewrite ?leqzz ?leq_decz_z ?leq_z_incz //.
Qed.

Lemma mring_equad : forall p, negb (has (equad (gface p)) m) ->
  maps end0g (mring m) (end0g p) = false.
Proof.
move=> p Hp; apply/mapsP => [[q Hq Eqp]].
rewrite mring_def in Hq; move/andP: Hq => [Hq _]; case/idP: (hasPn Hp _ Hq).
rewrite /equad /ehex /gchop_rect !halfg_face !oddg_face /=.
rewrite /end0g addgC in Eqp; rewrite (monic_move (addg_inv _) Eqp) addgC -addgA.
case: (halfg p) => [x y] /=; rewrite !leq_decz_z !leq_z_incz.
case (oddg p); case (oddg q); rewrite /= ?addz0 -?incz_def -?decz_def;
 do 2 rewrite ?leqzz ?leq_decz_z ?leq_z_incz //.
Qed.

Section Extend1.

Variable p : gpoint.

Definition ext1_hex := m (halfg (gedge p)) && negb (has (ehex p) m).

Hypothesis HpE : ext1_hex.

Remark Extend1_HpF : mdisk m (halfg p) = false.
Proof.
apply/idP => [Hdp]; case/andP: HpE => _; case/hasP; exists (halfg p); auto.
by rewrite /ehex mem_gchop_rect /setI gtouch_refl gchop_halfg.
Qed.
Let HpF := Extend1_HpF.

Remark Extend1_Hp : mring m (gedge p).
Proof. by rewrite mring_def gedge2 HpF andbT; case/andP: HpE. Qed.
Let Hp := Extend1_Hp.

Remark Extend1_Hp1 : negb (has (equad (iter 3 gface p)) m).
Proof.
apply/hasP => [[q Hmq Hq]]; case/andP: HpE => _; case/hasP; exists q; first done.
by rewrite -[p]gface4; apply ehexF.
Qed.
Let Hp1 := Extend1_Hp1.

Remark Extend1_Hp2 : negb (has (equad (iter 4 gface p)) m).
Proof.
apply/hasP => [[q Hmq Hq]]; case/andP: HpE => _; case/hasP; exists q; first done.
by rewrite /iter gface4 /equad mem_gchop_rect in Hq; case/andP: Hq.
Qed.
Let Hp2 := Extend1_Hp2.

Definition ext1_mring : gpointseq :=
  let: RotToSpec _ c _ := rot_to Hp in cat (traject gface (gface p) 3) c.

Lemma cycle_ext1_mring : cycle mrlink ext1_mring.
Proof.
rewrite /ext1_mring; case: (rot_to Hp) (cycle_mring m) => [i c Dc].
rewrite -(cycle_rot i) {i}Dc !(cycle_path p) /=.
rewrite {1 3 4 5}/mrlink !end0g_face !set11 /= end0g_edge.
case: c => [|q c] /=; first by rewrite end1g_edge -{1}[p]gface4 end0g_face.
by rewrite {1 3}/mrlink end1g_edge -{2}[p]gface4 end0g_face.
Qed.

Lemma simple_ext1_mring : uniq (maps end0g ext1_mring).
Proof.
rewrite /ext1_mring; move: (mring_equad Hp2) (simple_mring m).
case: (rot_to Hp) => [i c Dc]; rewrite -(uniq_rot i) -(mem_rot i).
move: (mring_equad Hp1); rewrite -(mem_rot i) -maps_rot.
rewrite {i}Dc [uniq]lock /= !end0g_edge -!end0g_face -lock.
move: {c}(maps end0g c) (gface p) => c q /=; rewrite /setU1.
move/norP=> [Uqq1 Ucq1]; move/norP=> [Uqq2 Ucq2]; move/andP=> [Ucq Uc].
rewrite {}Uc (negbE Ucq) (negbE Ucq1) (negbE Ucq2) eqd_sym (negbE Uqq1).
rewrite eqd_sym (negbE Uqq2) /= orbF andbT end0g_face; apply/eqP.
by move/(monic_inj (addg_inv _)); case (oddg (gface q)).
Qed.

Remark Extend1_HpEF :
  all (fun q => negb (m (halfg (gedge q)))) (traject gface (gface p) 3).
Proof.
apply/allP => [q Hq]; apply/idP => [Hmq]; case/andP: HpE => _; case/hasP.
exists (halfg (gedge q)); first done; case/trajectP: Hq => [i Hi <-] {q Hmq}.
rewrite halfg_edge iter_f halfg_iter_face oddg_iter_face /ehex /gchop_rect.
case: (halfg p) => [x y]; rewrite /= ?leq_decz_z ?leq_z_incz.
case (oddg p); case: i Hi => [|[|[|i]]] //= _; rewrite ?addz0 -?incz_def;
 by rewrite -?decz_def ?leqzz ?leq_decz_z ?leq_z_incz ?leq_decz_incz.
Qed.
Let HpEF := Extend1_HpEF.

Lemma ext1_mring_def :
  ext1_mring
    =1 (fun q => ext_mdisk p (halfg q) && negb (ext_mdisk p (halfg (gedge q)))).
Proof.
move=> q; rewrite /ext1_mring; case: (rot_to Hp) => [i c Dc] /=.
case/and4P: HpEF => [Hep1 Hep2 Hep3 _].
rewrite /setU1; case Hq1: (gface p =d q).
  move/eqP: Hq1 => <- {q}/=; rewrite halfg_face set11 /=.
  by rewrite -halfg_face neq_halfg_edge /=.
case Hq2: (gface (gface p) =d q).
  move/eqP: Hq2 => <- {q Hq1}/=; rewrite !halfg_face set11 /=; symmetry.
  by rewrite -2!halfg_face neq_halfg_edge /=.
case Hq3: (gface (gface (gface p)) =d q).
  move/eqP: Hq3 => <- {q Hq1 Hq2}/=; rewrite !halfg_face set11 /=; symmetry.
  by rewrite -3!halfg_face neq_halfg_edge /=.
case Hcq: (mring m q).
  move: (Hcq) (maps_uniq (simple_mring m)) (Hcq) => Hdq.
  rewrite -(mem_rot i) -(uniq_rot i) Dc /= /setU1; case/andP.
  case Hpq: (gedge p =d q).
    by move/eqP: Hpq => <-; rewrite gedge2 set11 andbF; move/negPf.
  rewrite mring_def in Hdq; case/andP: Hdq => [Hdq Hdeq] _ _ /= Hcq'.
  rewrite {}Hcq' {}Hdq {Hdeq}(negbE Hdeq) orbT orbF; symmetry; apply/eqP => Dp.
  move: (Hcq); rewrite mring_def; case/nandP; left.
  case Heq1: (gedge (gface p) =d q); first by move/eqP: Heq1 => <-.
  case Heq2: (gedge (gface (gface p)) =d q); first by move/eqP: Heq2 => <-.
  case Heq3: (gedge (gface (gface (gface p))) =d q); first by move/eqP: Heq3 => <-.
  elimtype False; move: Hpq Heq1 Heq2 Heq3; rewrite !(monic2_eqd gedge2 gedge2).
  rewrite -[gedge q]consg_odd_half -{1}[p]consg_odd_half -Dp.
  rewrite {1 2 4}/gface !halfg_face !oddg_face /consg.
  set p2 := halfg p +g halfg p; rewrite -!(addgC p2) !(monic_eqd (addg_inv p2)).
  by case (oddg p); case (oddg (gedge q)).
move: (Hcq); rewrite -(mem_rot i) Dc /=; move/norP=> [Hpq Hcq'].
rewrite (negbE Hcq') /=; symmetry.
case Hpq': (halfg p =d halfg q).
  case Hq0: (p =d q).
    move: Hp; rewrite (eqP Hq0) mring_def; move/andP=> [Dp _].
    by rewrite Dp orbT andbF.
  move: Hq0 Hq1 Hq2 Hq3; rewrite -[p]consg_odd_half -[q]consg_odd_half (eqP Hpq').
  rewrite /gface !oddg_cons !halfg_cons /consg.
  set q2 := halfg q +g halfg q; rewrite -!(addgC q2) !(monic_eqd (addg_inv q2)).
  by case (oddg p); case (oddg q).
case: (halfg p =d halfg (gedge q)); first by rewrite andbF.
by rewrite /= -mring_def.
Qed.

Definition ext1_matte :=
  Matte (ext_mdisk_ne _) cycle_ext1_mring simple_ext1_mring ext1_mring_def.

End Extend1.

Section Extend2.

Variable p : gpoint.

Definition ext2_quad :=
  and3b (mdisk m (halfg (gedge p))) (mdisk m (halfg (gedge (gface p))))
        (negb (has (equad p) m)).

Hypothesis HpE : ext2_quad.

Remark Extend2_HpF : m (halfg p) = false.
Proof.
apply/idP => Hp; case/and3P: HpE => _ _; case/hasP; exists (halfg p); auto.
rewrite /equad /ehex /gchop_rect halfg_face oddg_face.
case: (halfg p) => [x y]; rewrite /= ?leq_decz_z ?leq_z_incz.
by case (oddg p); rewrite /= ?leq_decz_z ?leq_z_incz ?leqzz.
Qed.
Let HpF := Extend2_HpF.

Remark Extend2_Hp1 : negb (has (equad (iter 4 gface p)) m).
Proof. by rewrite /iter gface4; case/and3P: HpE. Qed.
Let Hp1 := Extend2_Hp1.

Remark Extend2_Hefp : mring m (gedge (gface p)).
Proof. by rewrite mring_def gedge2 halfg_face HpF andbT; case/and3P: HpE. Qed.
Let Hefp := Extend2_Hefp.

Remark Extend2_Hep : mring m (gedge p).
Proof. by rewrite mring_def gedge2 HpF andbT; case/andP: HpE. Qed.
Let Hep := Extend2_Hep.

Remark Extend2_Hp : {c : gpointseq & {i : nat |
  rot i (mring m) = Seq (gedge (gface p)) (gedge p) & c}}.
Proof.
case/rot_to: Hefp => [i [|p' c] Dp].
move: (cycle_mring m); rewrite -(cycle_rot i) Dp /= /mrlink.
  rewrite /end0g /end1g (monic_eqd (addg_inv _)) oddg_edge oddg_face.
  by case (oddg p).
exists c; exists i; rewrite Dp; do 2 congr Adds.
move: (cycle_mring m) Hep (simple_mring m).
rewrite -(cycle_rot i) -(mem_rot i) -(uniq_rot i) -maps_rot Dp /mrlink.
move/andP=> [Dp' _]; rewrite end1g_edge end0g_face in Dp'.
rewrite -(mem_rot 1) -(uniq_rot 1) -maps_rot rot1_adds /=.
case/setU1P=> // [Hp']; case/andP; case/mapsP; exists (gedge p); auto.
by rewrite end0g_edge (eqP Dp').
Qed.
Let Hp := Extend2_Hp.

Definition ext2_mring : gpointseq :=
  let: existS c _ := Hp in cat (traject gface (gface (gface p)) 2) c.

Lemma cycle_ext2_mring : cycle mrlink ext2_mring.
Proof.
rewrite /ext2_mring; case: Hp (cycle_mring m) => [c [i Dc]].
rewrite -(cycle_rot i) {i}Dc !(cycle_path p) /=.
rewrite {1 2 4 5}/mrlink end1g_edge !end0g_face !end0g_edge !set11 /=.
case: c => [|q c] /=; first by rewrite end1g_edge -{1}[p]gface4 end0g_face.
by rewrite {1 3}/mrlink end1g_edge -{2}[p]gface4 end0g_face.
Qed.

Lemma simple_ext2_mring : uniq (maps end0g ext2_mring).
Proof.
rewrite /ext2_mring -(uniq_rot 1).
case: Hp (mring_equad Hp1) (simple_mring m) => [c [i Dc]].
rewrite -(uniq_rot i) -(mem_rot i) -(uniq_rot 1) -(mem_rot 1) -!maps_rot.
rewrite {i}Dc [maps]lock /= -!lock !rot1_adds /= !maps_add_last.
by rewrite !end0g_edge !end0g_face; move/norP=> [_ ->]; case/andP.
Qed.

Remark Extend2_HpEF :
  all (fun q => negb (m (halfg (gedge q)))) (traject gface (gface (gface p)) 2).
Proof.
apply/allP => q Hq; apply/idP => Hmq; case/and3P: HpE => _ _; case/hasP.
exists (halfg (gedge q)); first done; case/trajectP: Hq => [i Hi <-] {q Hmq}.
rewrite halfg_edge !iter_f halfg_iter_face oddg_iter_face.
rewrite /equad /ehex /gchop_rect halfg_face oddg_face.
case: (halfg p) => [x y]; rewrite /= ?leq_decz_z ?leq_z_incz.
case (oddg p); rewrite /= ?leq_decz_z ?leq_z_incz;
 case: i Hi => [|[|i]] //= _; rewrite ?addz0 -?incz_def -?decz_def;
 by rewrite ?leqzz ?leq_decz_z ?leq_z_incz.
Qed.
Let HpEF := Extend2_HpEF.

Lemma ext2_mring_def :
 ext2_mring
   =1 (fun q => ext_mdisk p (halfg q) && negb (ext_mdisk p (halfg (gedge q)))).
Proof.
move=> q; rewrite /ext2_mring; case: Hp => [c [i Dc]] /=; rewrite /setU1.
case/and3P: HpEF => Hep2 Hep3 _.
case Hq2: (gface (gface p) =d q).
  move/eqP: Hq2 => <- {q}/=; rewrite !halfg_face set11 /=; symmetry.
  by rewrite -2!halfg_face neq_halfg_edge /=.
case Hq3: (gface (gface (gface p)) =d q).
  move/eqP: Hq3 => <- {q Hq2}/=; rewrite !halfg_face set11 /=; symmetry.
  by rewrite -3!halfg_face neq_halfg_edge /=.
case Hcq: (mring m q).
  move: (Hcq) (maps_uniq (simple_mring m)) (Hcq) => Hdq.
  rewrite -(mem_rot i) -(uniq_rot i) Dc /= /setU1; case/and3P; case/norP=> _.
  case Hepq: (gedge (gface p) =d q).
    by rewrite -(eqP Hepq) gedge2 halfg_face set11 andbF; move/negPf.
  case Hpq: (gedge p =d q).
    by rewrite -(eqP Hpq) gedge2 set11 andbF; clear; move/negPf.
  rewrite mring_def in Hdq; case/andP: Hdq => Hdq Hdeq _ _ _ /= ->.
  rewrite {}Hdq {Hdeq}(negbE Hdeq) orbT orbF; symmetry; apply/eqP => Dp.
  move: (Hcq); rewrite mring_def; case/nandP; left.
  case Heq2: (gedge (gface (gface p)) =d q); first by rewrite -(eqP Heq2).
  case Heq3: (gedge (gface (gface (gface p))) =d q); first by rewrite -(eqP Heq3).
  elimtype False; move: Hpq Hepq Heq2 Heq3; rewrite !(monic2_eqd gedge2 gedge2).
  rewrite -[gedge q]consg_odd_half -{1}[p]consg_odd_half -Dp.
  rewrite {1 2 4}/gface !halfg_face !oddg_face /consg.
  set p2 := halfg p +g halfg p; rewrite -!(addgC p2) !(monic_eqd (addg_inv p2)).
  by case (oddg p); case (oddg (gedge q)).
move: (Hcq); rewrite -(mem_rot i) Dc /=.
case/norP=> Hpq; case/norP=> Hpeq Hcq'; rewrite (negbE Hcq') /=; symmetry.
case Hpq': (halfg p =d halfg q).
  case Hq0: (p =d q).
    by move: Hep; rewrite (eqP Hq0) mring_def; case/andP=> ->; rewrite orbT andbF.
  case Hq1: (gface p =d q).
    by move: Hefp; rewrite (eqP Hq1) mring_def; case/andP=> ->; rewrite orbT andbF.
  move: Hq0 Hq1 Hq2 Hq3; rewrite -[p]consg_odd_half -[q]consg_odd_half (eqP Hpq').
  rewrite /gface !oddg_cons !halfg_cons /consg.
  set q2 := halfg q +g halfg q; rewrite -!(addgC q2) !(monic_eqd (addg_inv q2)).
  by case (oddg p); case (oddg q).
case: (halfg p =d halfg (gedge q)); first by rewrite andbF.
by rewrite /= -mring_def.
Qed.

Definition ext2_matte :=
  Matte (ext_mdisk_ne _) cycle_ext2_mring simple_ext2_mring ext2_mring_def.

End Extend2.

End ExtendMatte.

Section MatteExtension.

Variable m : matte.

Inductive matte_extension : matte -> Set :=
  | Mext_nil : matte_extension m
  | Mext_add : forall (p : gpoint) (xm' xm : matte),
      matte_extension xm' -> mring xm' (gedge p) -> xm =1 ext_mdisk xm' p ->
    matte_extension xm.

Implicit Arguments Mext_add [].

Lemma mem_extension : forall xm, matte_extension xm -> sub_set m xm.
Proof.
move=> xm; elim: xm / => [|p xm' xm _ Hrec _ Dxm] q Hq //.
by rewrite Dxm /= setU1r ?Hrec.
Qed.

Inductive extends_in (r : grect) (p : gpoint) : Set :=
    ExtendIn (xm : matte)
      (_ : matte_extension xm) (_ : sub_set xm (setU r m)) (_ : xm p).

Lemma extends_in_sub : forall r1 r2 : grect, sub_set r1 r2 ->
  forall p, extends_in r1 p -> extends_in r2 p.
Proof.
move=> r1 r2 Hr12 p [xm Hxm Hxmr Hp]; exists xm; auto.
by move=> q Hq; apply/orP; case/orP: (Hxmr _ Hq); auto.
Qed.

Definition inset r p := sub_grect (gtouch p) r.

Lemma refined_extends_in : forall r : grect,
   refined_in (m : set _) r -> has r m ->
  forall p, inset r p -> extends_in r p.
Proof.
move=> r Hr0m Hrm p Hirp; have Hrr0: sub_set r r by move.
have Hr0r: sub_set (setI r m) r by move=> q; case/andP.
have Hr0p: sub_set (gtouch p) r by apply mem_sub_grect.
have Hrp: r p by apply Hr0p; exact: gtouch_refl.
move: {-1}r {1 3 4 5 8 11}r p (ltnSn (garea r)) Hrm Hrp Hrr0 Hr0r Hr0p Hr0m {Hirp}.
elim: {r}(S (garea r)) => // [n Hrec] r0 r p Hn Hrm Hrp Hrr0 Hr0r Hr0p Hr0m.
set G := extends_in r p; rewrite ltnS in Hn.
case Hmp: (mdisk m p).
  by exists m; try first [ left | move=> q Hq; rewrite /setU Hq orbT ].
have Hxm1: forall p', halfg p' = p -> negb (has (ehex p') m) ->
    extends_in (gchop_rect r (gedge p')) (halfg (gedge p')) -> G.
  move=> p' Dp' Hep' [xm Hxm Hxmr' Hxmp'].
  have Hp': ext1_hex xm p'.
    rewrite /ext1_hex Hxmp'; apply/hasPn => q Hq.
    case/orP: {Hq}(Hxmr' _ Hq); last by move=> *; apply (hasPn Hep').
    rewrite /ehex !mem_gchop_rect /setI gchop_edge.
    by case/andP=> *; apply/nandP; right.
  exists (ext1_matte Hp'); rewrite /= ?Dp' ?setU11 //.
    right with p' xm; rewrite // mring_def gedge2 Dp' Hxmp'.
    apply/idP; move/Hxmr'; rewrite /setU Hmp mem_gchop_rect /setI gchop_edge.
    by rewrite -Dp' /setC gchop_halfg andbF.
  move=> q; case/setU1P=> [<-|Hq]; first by rewrite /setU Hrp.
  apply/orP; case/orP: (Hxmr' _ Hq); try (rewrite mem_gchop_rect; case/andP); auto.
have Hcut: forall p', halfg p' = p -> has (setD r0 (gchop1 p')) m -> G.
  move=> p' Dp' Hr0p'; set r0' := gchop1_rect r0 p'.
  case Hr0': (has r0' m).
    set r' := gchop1_rect r p'.
    have Hr'r: sub_set r' r by exact: gchop_rect_sub.
    apply: (extends_in_sub Hr'r); apply (Hrec r0').
    - case/hasP: Hr0p' => [q Hmq]; move/andP=> [Hp'q Hr0q].
      apply: leq_trans Hn; apply: ((ltn_garea_sub_rect Hr'r) q).
      by rewrite /setD /r' mem_gchop1_rect /setI (negbE Hp'q) Hr0r //= /setI Hr0q.
    - case/hasP: Hr0' => [q Hmq]; rewrite /r0' mem_gchop1_rect.
      move/andP=> [Hr0q Hp'q]; apply/hasP; exists q; first done.
      by rewrite /r' mem_gchop1_rect /setI Hp'q Hr0r //= /setI Hr0q.
    - by rewrite /r' mem_gchop1_rect /setI Hrp gchop_chop1 // -Dp' gchop_halfg.
    - move=> q; rewrite /r' /r0' !mem_gchop1_rect /setI.
      by case/andP=> *; apply/andP; auto.
    - move=> q; rewrite /r' /r0' /setI !mem_gchop1_rect /setI -andbA andbCA.
      by case/andP=> *; apply/andP; auto.
    - move=> q Hq; rewrite /r0' mem_gchop1_rect; apply/andP; split; auto.
      by move: Hq; rewrite -Dp' gtouch_chop1; case/andP.
    move=> q q' Hq; exact (Hr0m q q' (gchop_rect_sub Hq)).
  apply (Hxm1 _ Dp').
    apply/hasP => [[q Hmq]]; rewrite /ehex mem_gchop_rect Dp'.
    move/andP=> [Hpq _]; case/hasP: Hr0'; exists q; first done.
    rewrite /r0' mem_gchop1_rect /setI Hr0p //=.
    by move: Hpq; rewrite -Dp' gtouch_chop1; case/andP.
  set r' := gchop_rect r (gedge p').
  have Hr'r: sub_set r' r by exact: gchop_rect_sub.
  have Hr'm: has r' m.
    case/hasP: Hr0p' => [q Hmq]; move/andP=> [Hp'q1 Hr0q]; apply/hasP.
    exists q; rewrite // /r' mem_gchop_rect /setI Hr0r /setI ?Hr0q // gchop_edge.
    by apply/idP => Hp'q; case/idP: Hp'q1; apply gchop_chop1.
  apply (Hrec r0); auto.
  - apply: leq_trans Hn; apply ((ltn_garea_sub_rect Hr'r) p); rewrite /setD /r'.
    by rewrite mem_gchop_rect /setI Hrp gchop_edge /setC -Dp' gchop_halfg.
  - by case/hasP: Hr'm => q _ Hq; apply: gchop_rect_edge Hq; rewrite gedge2 Dp'.
  - by move; auto.
  - move=> q Hq; rewrite /r' mem_gchop_rect /setI Hr0r //= gchop_edge.
    apply/idP => [Hp'q]; case/andP: Hq => [Hr0q Hmq]; case/hasP: Hr0'.
    by exists q; rewrite // /r0' mem_gchop1_rect /setI Hr0q; apply: gchop_chop1.
  set p2 := gedge (gface (gface (gedge p'))).
  have Hp2: gchop_rect r0 p2 (halfg p2).
    case/hasP: Hr0p' => [q Hmq Hq0]; apply gchop_rect_edge with q.
      by apply Hr0p; rewrite /p2 gedge2 !halfg_face -Dp' gtouch_edge.
    by rewrite mem_gchop_rect /p2 /setI gchop_edge andbC.
  rewrite mem_gchop_rect /setI gchop_halfg andbT in Hp2.
  have Hp1: r0 (halfg (gedge (gface p'))).
    by apply Hr0p; rewrite -Dp' -halfg_face gtouch_edge.
  have Hp3: r0 (halfg (gedge (gface (gface (gface p'))))).
    by apply Hr0p; rewrite -Dp' -3!halfg_face gtouch_edge.
  apply mem_sub_grect; move: Hp1 Hp2 Hp3.
  rewrite /p2 !halfg_edge !oddg_face !halfg_face !oddg_edge halfg_edge ccw4 Dp'.
  rewrite -!addgA; case: (r0) (p) => [x0 x1 y0 y1] [x y].
  case (oddg p'); case/and4P=> [Hx01 Hx11 Hy01 Hy11];
   case/and4P=> [Hx02 Hx12 Hy02 Hy12]; case/and4P=> [Hx03 Hx13 Hy03 Hy13];
   by rewrite /= ?incz_def ?decz_def -!addzA; apply/and4P; split.
pose np q := consg (ccw (ccw (ccw (oddg q)))) q.
have Enph: forall q, halfg (np q) = q by move=> *; rewrite /np halfg_cons.
have Enpo: forall q, oddg (np q) = ccw (ccw (ccw (oddg q))).
  by move=> *; rewrite /np oddg_cons.
have EnpE: forall q, halfg (gedge (np q)) = gnode q.
  by move=> q; rewrite halfg_edge /gnode /np halfg_cons oddg_cons; case (oddg q).
have DnpN: forall q, np (gnode q) = gedge (gnode (gedge (np q))).
  move=> q; apply (monic_move gmonicF).
  by rewrite /gface Enph Enpo oddg_node -Enpo -oddg_edge -EnpE consg_odd_half.
have Hnp4: forall q, r0 q -> has (equad (np q)) m -> m q.
  move=> q0 Hr0q0; move/hasP=> [q Hmq Hq]; rewrite -(Hr0m _ q Hr0q0) //.
  apply: eqP; move: Hq {Hmq}; rewrite /equad /ehex /gchop_rect halfg_face.
  rewrite oddg_face Enph Enpo ccw4 -{1 2 4}[q0]consg_odd_half /consg addgC.
  case: (halfg q0) q => [x y] [x' y']; rewrite eqd_sym /eqd /=.
  rewrite !eqz_leq -!andbA !leqz_halfl !leqz_halfr.
  case (oddg q0);
    by rewrite /= ?addz0 ?addn0 ?leq_decz_z ?leq_z_incz -?incz_def ?decz_inc.
have Eq2x2: forall q q', ehex q q' \/ ehex (gface (gedge (gface q))) q' ->
                        equad q q' \/ equad (gedge (gface q)) q'.
  have Ec1c: forall q q' b, gchop1 q q' && b && gchop q q' = gchop q q' && b.
    move=> q q' b; case Hqq': (gchop q q'); last by rewrite andbF.
    by rewrite andbT (gchop_chop1 Hqq').
  move=> q q'; repeat rewrite /equad /ehex mem_gchop_rect /setI.
  rewrite !gtouch_chop1 /all /traject !andbT gface4 !Ec1c.
  rewrite {-12 13}[andb]lock andbCA -!lock Ec1c gchopFEF.
  case (gchop q q'); rewrite // !andTb Ec1c.
  set q2q' := gchop1 (gface (gface q)) q'.
  have <-: q2q' = gchop1 (gface (gface (gface (gedge (gface q))))) q'.
    rewrite /gchop1 -gchopFEF -!gnode_face !gface4; congr gchop; congr gface.
    by symmetry; apply: (monic_move gmonicN); rewrite gnode4.
  case: q2q'; rewrite ?andbF // !andTb !andbT gchop_edge /setC.
  case Hqq': (gchop (gface q) q').
    by case; case/andP; left; rewrite // -[gface q]gedge2; apply: gchop_chop1.
  by case; case/andP; right; first exact: gchop_chop1.
have Hr0np: r0 (gnode p) by apply Hr0p; rewrite -EnpE -{1}[p]Enph gtouch_edge.
have EnpFE: forall q, np (gface (gedge q)) = gedge (gface (np q)).
  by move=> q; rewrite -{2}[q]gmonicE DnpN gmonicN gedge2.
have Hr0fep: r0 (gface (gedge p)).
  apply Hr0p; rewrite -[gface (gedge p)]Enph -[np (gface (gedge p))]gedge2.
  by rewrite -{1}[p]gmonicE -EnpE gtouch_edge.
case Hqpm: (has (equad (np p)) m); first by rewrite Hnp4 ?Hrr0 in Hmp.
case Hhpm: (has (ehex (np p)) m).
  have Hmefp: m (halfg (gedge (gface (np p)))).
    rewrite -EnpFE Enph Hnp4 //.
    case/hasP: Hhpm => [q Hmq Hq]; apply/hasP; exists q; first done.
    case: (Eq2x2 (np p) q) => //; rewrite -?EnpFE //; first by left.
    by move=> *; case/hasP: Hqpm; exists q.
  case Hhfpm: (has (ehex (gface (np p))) m).
    have Hmep: m (halfg (gedge (np p))).
      rewrite EnpE Hnp4 //; case/hasP: Hhfpm => [q Hmq Hq].
      case: (Eq2x2 (np (gnode p)) q); try rewrite -EnpFE gmonicN; auto.
        by move=> *; apply/hasP; exists q.
      by move=> *; case/hasP: Hqpm; exists q.
    have Hext: ext2_quad m (np p) by rewrite /ext2_quad Hmep Hmefp Hqpm.
    exists (ext2_matte Hext); rewrite /= ?Enph ?setU11 //.
      right with (np p) m; [ left | idtac | split ].
      by rewrite mring_def gedge2 Enph Hmp Hmep.
    by move=> q; case/setU1P=> [<-|Hq]; apply/orP; auto.
  apply: (Hxm1 (gface (np p))); rewrite ?Hhfpm ?halfg_face //.
  exists m; [ left | move=> q Hq; apply/orP; auto | done ].
case Hpm: (negb (has (gtouch p) m)).
  pose hrp i := has (setD r0 (gchop1 (iter i gface (np p)))) m.
  suffice: {i : nat | hrp i} by case=> i; apply: Hcut; rewrite halfg_iter_face.
  case Hh0: (hrp 0); first by exists 0.
  case Hh1: (hrp 1); first by exists 1.
  case Hh2: (hrp 2); first by exists 2.
  case Hh3: (hrp 3); first by exists 3.
  case/hasP: Hpm; case/hasP: Hrm => [q Hmq Hq]; exists q; first done.
  rewrite -[p]Enph gtouch_chop1; apply/allP => p'; move/trajectP=> [i Hi <-].
  case Hhi: (hrp i); first by case/negPf: Hhi; case: i Hi => [|[|[|[|i]]]] //.
  by move: (elimFn hasPn Hhi _ Hmq); rewrite /setD Hrr0 //= andbT negb_elim.
apply: (Hxm1 (np p)); rewrite ?Hhpm // EnpE.
case Hmnp: (m (gnode p)).
  by exists m; try first [ left | move=> q Hq; rewrite /setU Hq orbT ].
case Hqnpm: (has (equad (np (gnode p))) m); first by rewrite Hnp4 in Hmnp.
have Hr0n2p: r0 (gnode (gnode p)).
  rewrite {1}/gnode oddg_node /gnode -!addgA; apply Hr0p; case: {1 2}p => [x y].
  by case (oddg p); rewrite /= -?incz_def -?decz_def !leqzz !leq_decz_incz.
have Hmn2p: m (gnode (gnode p)).
  apply: Hnp4 => //; apply/hasP; move/hasP: Hpm => [q Hmq Hq]; exists q; auto.
  have Hnpq: gchop (gface (np (gnode p))) q.
    rewrite DnpN gmonicN gchop_edge; apply/idP => [Hpq]; case/hasP: Hhpm.
    by exists q; last by rewrite /ehex mem_gchop_rect Enph /setI Hq.
  case: (Eq2x2 (np (gnode (gnode p))) q) => //.
    right; rewrite /ehex -EnpFE gmonicN mem_gchop_rect /setI Hnpq halfg_face Enph.
    move: Hq Hnpq; rewrite /gchop halfg_face oddg_face Enph Enpo oddg_node ccw4.
    rewrite /gnode; case: (p) (q) (oddg p) => [x y] [x' y'] /=.
    case; rewrite /= -?incz_def -?decz_def ?addz0 ?decz_inc ?incz_dec andbT;
    rewrite !leqz_dec_inc ?leqz_inc_dec; case/and4P=> *; apply/and4P; split;
    by rewrite // leqz_dec ?decz_inc; apply/orP; right.
  by rewrite -EnpFE gmonicN; move=> *; case/hasP: Hqnpm; exists q.
have Hrnp: r (gnode p).
  have Hrn2p: r (gnode (gnode p)) by apply Hr0r; rewrite /setI Hr0n2p.
  move: Hrn2p; do 3 rewrite {1}/gnode ?oddg_node; rewrite -!addgA.
  case: (r) (p) (oddg p) Hrp => [x0 x1 y0 y1] [x y].
  by case; rewrite /= -?incz_def -?decz_def ?decz_inc ?incz_dec ?addz0;
     move/and4P=> [Hx0 Hx1 Hy0 Hy1]; case/and4P=> *; apply/and4P; split.
have Hext: ext1_hex m (np (gnode p)).
  rewrite /ext1_hex EnpE Hmn2p; apply/hasP => [[q Hmq Hq]].
  case: (Eq2x2 (np (gnode p)) q); rewrite -?EnpFE ?gmonicN; auto.
    by move=> *; case/hasP: Hqnpm; exists q.
  by move=> *; case/hasP: Hqpm; exists q.
exists (ext1_matte Hext); rewrite /= ?Enph ?setU11 //.
  right with (np (gnode p)) m; try by try left.
  by rewrite mring_def EnpE Hmn2p gedge2 Enph Hmnp.
move=> q /=; case/setU1P=> [<-|Hq]; apply/orP; [ left | by right ].
rewrite mem_gchop_rect /setI Hrnp /gchop EnpE oddg_edge Enpo ccw4.
by case: (gnode p) (oddg p) => [x y]; case; apply: leqzz.
Qed.

(* The refined_extends_in lemma is used directly to show that the union of a   *)
(* set of extension mattes included in a region is closed (relatively to the   *)
(* region). To show that this union is open we will need the MatteOrder lemmas *)
(* below. We use the refined_extend_meet lemma to extend the mattes of         *)
(* adjacent regions so that their contours have a common edge.                 *)

Lemma extend_meet : forall (m2 : matte) (r : grect),
   refined_in (m : set _) r -> has r m -> has (inset r) m2 -> negb (has m m2) ->
 {xm : matte | sub_set m xm /\ sub_set xm (setD (setU r m) m2) &
               has (fun q => mring m2 (gedge q)) (mring xm)}.
Proof.
move=> m2 r Hmr Hrm Hrm2 Hmm2; rewrite has_sym in Hmm2.
have [p Hm2p Hp]: {p : gpoint | m2 p &  inset r p}.
  exists (sub neg1g m2 (find (inset r) m2)); last by apply: sub_find.
  by apply: mem_sub; rewrite -has_find.
  case: (refined_extends_in Hmr Hrm Hp) => [xm Hxm Hxmr Hxmp].
have Hxm2: has m2 xm by apply/hasP; exists p.
elim: {xm}Hxm Hxmr Hxm2 {p Hm2p Hrm2 Hp Hxmp}; first by rewrite (negbE Hmm2).
move=> p xm' xm Hxm' Hrec Hxm'p Dxm Hxmr Hxm2.
have Hxm'r: sub_set xm' (setU r m).
  by move=> q Hq; apply Hxmr; rewrite Dxm /= /setU1 Hq orbT.
case Hxm'2: (has m2 xm'); [ eauto | exists xm' ].
  split; [ by apply mem_extension | move=> q Hq; rewrite /setD andbC Hxm'r //= ].
  by apply (elimFn hasPn Hxm'2).
apply/hasP; exists (gedge p); rewrite // gedge2 mring_def; apply/andP; split.
  apply/idPn => Hm2p; case/hasPn: Hxm2; move=> q; rewrite Dxm /=.
  by case/setU1P=> [<-|Hq] //; apply (elimFn hasPn Hxm'2).
by apply (elimFn hasPn Hxm'2); rewrite mring_def in Hxm'p; case/andP: Hxm'p.
Qed.

End MatteExtension.

Section MatteOrder.

Definition matte_order (m : matte) p : nat :=
  let m' := setC m in
  double (m' (p +g oppg Gb01) + m' (p +g oppg Gb10))
       + (m' (p +g oppg Gb11) + m' (p +g oppg Gb00)).

Lemma zspan_decz_z : forall x, zspan (decz x) x = Seq (decz x) x.
Proof.
move=> x; rewrite /zspan /zwidth {2}(decz_def x) -subz_sub subzz /=.
by rewrite incz_dec.
Qed.

Definition ltouch p := let: Gpoint mx my := p in Grect (decz mx) mx (decz my) my.

Lemma matte_order0 : forall m p, matte_order m p = 0 -> sub_set (ltouch p) m.
Proof.
move=> m p; move/(introT eqP); rewrite /matte_order double_addnn !eqn_add0 andbb.
have Em': (fun q => (setC m q : nat) =d 0) =1 m by rewrite /setC /eqfun; case/m.
case: p => [x y] Hp q; rewrite -mem_enum_grect /= !zspan_decz_z /=.
rewrite !Em' /= !addz0 -!decz_def -!andbA in Hp.
by case/and4P: Hp => [Hp01 Hp10 Hp11 Hp00]; do 4 case/setU1P=> [<-|] //.
Qed.

Definition inset2 r p := inset r p && inset r (p +g neg1g).

Lemma inset2_refine : forall r p, inset r (halfg p) -> inset2 (refine_rect r) p.
Proof.
move=> [x0 x1 y0 y1] [x y]; rewrite /inset2 /inset /= -?decz_def.
rewrite !leqz_inc2 -2!leqz_inc_dec !leqz_halfr 4!incz_def -!addzA.
rewrite -!(addzCA x0) -!(addzCA y0) !addzA -!incz_def 6!leqz_inc_dec !leqz_halfl.
rewrite 2!incz_def (decz_def x1) (decz_def y1) -!addzA !addz0.
rewrite -!(addzC x1) -!(addzC y1) !addzA -?decz_def.
move/and4P=> [Hx0 Hx1 Hy0 Hy1]; rewrite Hx0 Hy0 leqz_dec Hx0 leqz_dec Hx1.
rewrite leqz_dec Hy0 leqz_dec Hy1 2!leqz_dec leqz_dec2 Hx1.
by rewrite 2!leqz_dec leqz_dec2 Hy1 !orbT.
Qed.

Lemma refine_matte_order : forall (m : matte) r p,
   m (halfg p) -> inset r (halfg p) -> 0 < matte_order m (halfg p) ->
 {xm : matte | sub_set (fun q => m (halfg q)) xm /\
               sub_set xm (fun q => setU r m (halfg q)) &
             matte_order xm p < matte_order m (halfg p)}.
Proof.
move=> m r p Hmp Hrp; pose dp (d : gbits) :=  p +g oppg d.
have Hdp: forall d,
    {xm : matte | sub_set (fun q => m (halfg q)) xm /\
                  sub_set xm (fun q => setU r m (halfg q)) &
       forall d' : gbits,
       xm (p +g oppg d') = or3b (d =d d') (m (halfg (dp d'))) (xm (dp d'))}.
  pose r' := refine_rect r; pose m' := refine_matte m.
  have Hr'p: forall d, inset r' (dp d).
    move=> d; case/andP: (inset2_refine Hrp); rewrite -/r' {}/dp {Hmp Hrp}.
    case: p r' => [x y] [x0 x1 y0 y1].
    rewrite /inset /= -?decz_def ?incz_dec.
    move/and4P=> [Hx0 Hx1 Hy0 Hy1]; move/and4P=> [Hx0' Hx1' Hy0' Hy1'].
    case: d; 
      by rewrite /= -?decz_def -?incz_def ?incz_dec ?addz0; apply/and4P; split.
  have Hm'r': refined_in (m' : set _) r' by exact: refine_matte_refined.
  have Hr'm': has r' m'.
    apply/hasP; exists (dp Gb00); first by rewrite /m' mem_refine_matte /dp addg0.
    apply (mem_sub_grect (Hr'p Gb00)); exact: gtouch_refl.
  move=> d; case: (refined_extends_in Hm'r' Hr'm' (Hr'p d)) => [xm Hxm Hxmr' Hxmd].
  exists xm.
    split; move=> q Hq.
      by apply (mem_extension Hxm); rewrite /m' mem_refine_matte.
    apply/orP; case/orP: (Hxmr' _ Hq).
      by rewrite /r' mem_refine_rect; left.
    by rewrite /m' mem_refine_matte; right.
  move=> d'; rewrite -/(dp d') -mem_refine_matte -/m'.
  case: (d =P d') => [<-|_]; first by rewrite Hxmd orbT.
  by case Hd': (m' (dp d')); first by rewrite (mem_extension Hxm).
have leq_norb: forall b b', negb (b || b') <= negb b by do 2 case.
have Edp: forall d, halfg (dp d) = halfg p +g halfg (oddg p +g oppg d).
  by move=> d; rewrite /dp addgC halfg_add addgC; congr addg; rewrite addgC.
case Dp: (oddg p) Edp => [|||] Edp.
- move=> Hmp0; pose dhp d := negb (m (halfg p +g oppg d)).
  have [d Dd Hd]: {d : gbits | setC1 d Gb00 &  dhp d}.
    move: Hmp0; rewrite /matte_order /setC addg0 Hmp.
    rewrite -/(dhp Gb01) -/(dhp Gb10) -/(dhp Gb11).
    case H01: (dhp Gb01); first by exists Gb01.
    case H10: (dhp Gb10); first by exists Gb10.
    by case H11: (dhp Gb11); first by exists Gb11.
  rewrite {}/dhp in Hd; case: (Hdp d) => [xm Hxm Dxm]; exists xm; first done.
  rewrite /matte_order /setC !Dxm !Edp !addg0 Hmp !addn0.
  by case: (d) Dd Hd => [|||] //= _ Hd;
    rewrite (negbE Hd) /= ?addn1 ?add1n ?doubleS ?addSn ltnS ?addn0 ?add0n;
    try apply leqW; try apply leq_add2; rewrite ?leq_double; try apply leq_add2.
- case: (Hdp Gb01) => [xm Hxm Dxm] Hmp0; exists xm; first done.
  rewrite {1}/matte_order /setC !Dxm !Edp !addg0 Hmp /= add0n addn0.
  case Hm01: (m _) => //.
  by rewrite /matte_order /= /setC Hm01 /= add1n doubleS; case (xm (dp Gb11)).
- case: (Hdp Gb00) => [xm Hxm Dxm] Hmp0; exists xm; first done.
  by rewrite {1}/matte_order /setC !Dxm !Edp !addg0 Hmp.
case: (Hdp Gb10) => [xm Hxm Dxm] Hmp0; exists xm; first done.
rewrite {1}/matte_order /setC !Dxm !Edp !addg0 Hmp /= add0n addn0.
case Hm01: (m _) => //.
by rewrite /matte_order /= /setC Hm01 /= addn1 doubleS; case (xm (dp Gb11)).
Qed.

End MatteOrder.

Set Strict Implicit.
Unset Implicit Arguments.

