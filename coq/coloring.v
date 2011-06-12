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
Require Import walkup.
Require Import geometry.
Require Import color.
Require Import chromogram.

(* Hypermap, graph and contract colorings, colorable maps, ring traces, valid *)
(* contracts, and the definition of the special maps used in the proof:       *)
(* minimal counter example, C-reducible, and  embeddable.                     *)
(*   Results established here include the decidability of coloring, and the   *)
(* proof that minimal counter examples are also cubic.                        *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Coloring.

Variable g : hypermap.

Definition coloring (k : g -> color) :=
  invariant edge k =1 set0 /\ invariant face k =1 g.

Lemma coloring_inj : forall h, injective h ->
  forall k, coloring k -> coloring (comp h k).
Proof.
move=> h Hh k [HkE HkF]; split; move=> x; rewrite /invariant.
  by move: (HkE x); rewrite -(invariant_inj edge Hh k).
by move: (HkF x); rewrite -(invariant_inj face Hh k).
Qed.

Definition ring_trace r et := exists2 k, coloring k & et = trace (maps k r).

Definition four_colorable := exists k, coloring k.

Lemma colorable_bridgeless : four_colorable -> bridgeless g.
Proof.
move=> [k [HkE HkF]]; apply/set0Pn => [[x Hx]]; case/idP: (HkE x); apply/eqP.
by rewrite -(fconnect_invariant HkF Hx).
Qed.

Definition graph_coloring (k : g -> color) :=
  invariant edge k =1 set0 /\ invariant node k =1 g.

Definition graph_four_colorable : Prop := exists k, graph_coloring k.

Definition cc_coloring cc (k : g -> color) :=
  invariant edge k =1 insertE cc /\ invariant face k =1 g.

Definition cc_colorable cc := exists k, cc_coloring cc k.

Definition cc_ring_trace cc r et :=
  exists2 k, cc_coloring cc k & et = trace (maps k r).

End Coloring.

Prenex Implicits coloring ring_trace cc_coloring cc_colorable cc_ring_trace.

Section ColoringDual.

Variable g : hypermap.

Lemma coloring_dual :
  forall k : g -> color, @coloring (dual g) k <-> graph_coloring k.
Proof.
move=> k; split.
  move=> [HkE' HkF']; split; move=> x; rewrite /invariant eqd_sym.
    rewrite -{1}(finv_f (Iedge g) x); exact: HkE' (edge x).
  rewrite -{1}(finv_f (Inode g) x); exact: HkF' (node x).
move=> [HkE HkN]; split; move=> x; rewrite /invariant eqd_sym.
  rewrite -{1}(f_finv (Iedge g) x); exact: HkE.
rewrite -{1}(f_finv (Inode g) x); exact: HkN.
Qed.

Lemma four_colorable_dual :
 four_colorable (dual g) <-> graph_four_colorable g.
Proof. split; move=> [k Hk]; exists k; case (coloring_dual k); auto. Qed.

Lemma coloring_mirror :
 forall k : g -> color, @coloring (mirror g) k -> coloring k.
Proof.
move=> k [HkE' HkF']; have HkF: (invariant face k =1 g).
  move=> x; rewrite /invariant eqd_sym -{1}(finv_f (Iface g) x); exact: HkF'.
split; move=> // x; rewrite /invariant eqd_sym.
rewrite -((_ =P k x) (HkF _)) -((_ =P k (edge x)) (HkF _)) -{1}[x]Eedge.
exact: HkE'.
Qed.

Lemma colorable_mirror : four_colorable (mirror g) -> four_colorable g.
Proof. by move=> [k Hk]; exists k; apply coloring_mirror. Qed.

End ColoringDual.

Section EqmColorable.

Variable g g' : hypermap.
Hypothesis Eg' : eqm g g'.

Lemma eqm_colorable : four_colorable g -> four_colorable g'.
Proof.
case: g Eg' => [d e n f EgE] [e' n' f' Eg'E Ee _ Ef] [k [HkE HkF]]; exists k.
split; move=> x; rewrite /invariant /= -?Ee -?Ef; [ apply: HkE | apply: HkF ].
Qed.

Lemma eqm_graph_colorable : graph_four_colorable g -> graph_four_colorable g'.
Proof.
case: g Eg' => [d e n f EgE] [e' n' f' Eg'E Ee En _] [k [HkE HkN]]; exists k.
split; move=> x; rewrite /invariant /= -?Ee -?En; [ apply: HkE | apply: HkN ].
Qed.

End EqmColorable.

Section DecideColorable.

Variable g : hypermap.

(* We need decidability of ring traces in birkhoff.                           *)
Lemma decide_ring_trace :
  forall (r : seq g) et, {ring_trace r et} + {~ ring_trace r et}.
Proof.
move=> r et.
pose kpr k p lc := (maps k p =d lc) && ((trace (maps k r) : (seq _)) =d et).
pose ekpr := exists2 k, coloring k & kpr k _ _.
suffice: {ekpr seq0 seq0} + {~ ekpr seq0 seq0}.
  move=> [Hk|Hnk]; [ left | right ].
    move: Hk => [k Hk Det]; exists k; auto; exact (esym (eqseqP Det)).
  by move=> [k Ht Det]; case Hnk; exists k; auto; rewrite /kpr Det !set11.
move Dn: (card (setC (Seq0 g))) => n.
elim: n (Seq0 g) (seq0 : colseq) Dn => [|n Hrec] p lc Dn.
  have Hp: forall x, p x by move=> x; apply negbEf; apply: card0_eq Dn x.
  pose kp := sub Color0 lc (index _ p).
  pose kkp x := setU1 (kp (edge x)) (setC1 (kp (face x))) (kp x).
  case Hkp: (set0b kkp && kpr kp p lc).
    case/andP: Hkp => [Hkp Det]; left; exists kp; auto.
    by split; move=> x; [apply negbE | apply negbE2]; case/norP: (set0P Hkp x).
  right; case; move=> k [HkE HkF]; case/andP=> [Dlc Det].
  have Dkp: kp =1 k.
    move=> x; rewrite /kp -(eqP Dlc).
    apply: (etrans (sub_maps x _ k _)); first by rewrite /= index_mem.
    by rewrite sub_index.
  rewrite /kpr !(eq_maps Dkp) Dlc Det /= andbT in Hkp; case/set0Pn: Hkp.
  move=> x; rewrite /kkp /setU1 /setC1 !Dkp.
  by rewrite -/(invariant edge k x) -/(invariant face k x) HkE HkF.
case: (pickP (setC p)) => [x Hx|Hp]; last by rewrite (eq_card0 Hp) in Dn.
pose ekprx := ekpr (Adds x p) (Adds _ lc).
have Hekprx: forall c, {ekprx c} + {~ ekprx c}.
  move=> c; apply: Hrec; rewrite (cardD1 x) Hx in Dn; move: Dn => [<-].
  by apply: eq_card => y; rewrite /= /setU1 /setC negb_orb.
have Hekpr: forall c, ekprx c -> ekpr p lc.
  move=> c [k Hk Hkpr]; rewrite /kpr {1}/eqd /= -andbA in Hkpr.
  by case (andP Hkpr); exists k.
case (Hekprx Color0); [ left; eauto | move=> Hc0 ].
case (Hekprx Color1); [ left; eauto | move=> Hc1 ].
case (Hekprx Color2); [ left; eauto | move=> Hc2 ].
case (Hekprx Color3); [ left; eauto | move=> Hc3 ].
right; move=> [k Hk Hkpr]; suffice: (ekprx (k x)) by case (k x).
by exists k; last by rewrite /kpr {1}/eqd /= set11.
Qed.

Lemma decide_colorable : {four_colorable g} + {~ four_colorable g}.
Proof.
case: (decide_ring_trace (Seq0 g) seq0) => [Hk|Hnk].
  by left; move: Hk => [k Hk _]; exists k.
by right; move=> [k Hk]; case: Hnk; exists k.
Qed.

End DecideColorable.

Section MinimalCounterExample.

Variable g : hypermap.

Record minimal_counter_example : Prop := MinimalCounterExample {
  minimal_counter_example_is_planar_bridgeless_plain_precubic :>
    planar_bridgeless_plain_precubic g;
  minimal_counter_example_is_noncolorable :
    ~ four_colorable g;
  minimal_counter_example_is_minimal : forall g',
    planar_bridgeless_plain_precubic g' -> card g' < card g -> four_colorable g'
}.

Lemma minimal_counter_example_is_cubic : minimal_counter_example -> cubic g.
Proof.
move=> Hg; have Hbg := bridgeless_cface Hg.
have HgE := Hg : plain g ; have HgN := precubic_leq Hg.
apply/subsetP => [x _]; apply/negPf => Hx.
have Hnx: setC1 x (node x).
  by apply/eqP=> [Dnx]; move: (Hbg x); rewrite {2}Dnx cface1r Enode connect0.
have Dnnx: node (node x) = x.
  rewrite /order_set in Hx; apply: eqP; apply/negPf => Hnnx.
  move: (HgN x); rewrite leq_eqVlt Hx /order.
  rewrite (cardD1 x) (cardD1 (node x)) (cardD1 (node (node x))) /setD1 -!cnode1r.
  by rewrite connect0 (inj_eqd (Inode g)) (negbE Hnx) eqd_sym Hnnx.
pose g' := walkupE x; pose h' (u : g') := subdE u.
pose unx := subdI Hnx : g'; pose g'' := walkupE unx.
pose h'' (w : g'') := subdE w; pose h := h' (h'' _).
have Hh': injective h' by apply: subdE_inj.
have Hh'': injective h'' by apply: subdE_inj.
have Hh: injective h by exact (inj_comp Hh' Hh'').
have HhF: forall w1 w2, cface w1 w2 = cface (h w1) (h w2).
  move=> w1 w2; apply: (etrans _ (fconnect_skip (Iface _) _ _)).
  exact (fconnect_skip (Iface _) _ _).
have HhN: forall w1 w2, cnode w1 w2 = cnode (h w1) (h w2).
  move=> w1 w2; apply: (etrans _ (fconnect_skip (Inode _) _ _)).
  exact (fconnect_skip (Inode _) _ _).
have HhN1: forall w, h (node w) = node (h w).
  move=> w; pose nw' := walkupI unx (node (h w)); pose nw := walkupI w nw'.
  have Dnw': h' nw' = node (h w).
    rewrite /h' /nw' walkupI_eq -{1}Dnnx (inj_eqd (Inode g)).
    by case Hnxw: (node x =d h w); first by case: (negP (subd_mem w)).
  have Dnw: h nw = node (h w).
    rewrite /nw {1}/h /h'' walkupI_eq -(inj_eqd Hh') Dnw' /= (inj_eqd (Inode g)).
    by case Hxhw: (eqd x (h w)); first by case (negP (subd_mem (h'' w))).
  by rewrite -Dnw; congr h; symmetry; do 2 apply: (subdE_skip (Inode _)).
have Hg''g: card g'' < card g.
  by rewrite /g'' /g' !card_walkup (cardD1 x) /= -subn1 add1n ltnS leq_subr.
have Hh''E: forall w, order edge w = card (setD1 (cedge (h'' w)) unx).
  move=> w; rewrite /order -(card_image Hh''); apply: eq_card => [u].
  rewrite /setD1 -/(setC1 unx u); case Hu: (setC1 unx u).
    set wu := subdI Hu : g''; rewrite -{1}[u]/(h'' wu) (image_f Hh'') /=.
    apply: (etrans (eq_fconnect (glink_fp_skip_edge _) w wu)).
      by rewrite /glink /relU /setU /eqdf /eqd /= /skip1 Dnnx !set11 /= orbT.
    exact (fconnect_skip (Iedge _) w wu).
  apply/set0Pn; case; move=> wu; move/andP=> [Du _]; case/idPn: Hu.
  rewrite ((u =P _) Du); exact (subd_mem wu).
  case: (minimal_counter_example_is_minimal Hg _ Hg''g); repeat split.
   by do 2 apply: planar_walkupE; exact Hg.
   apply/set0P => w; rewrite -{1}[w]Eedge cface1r HhF HhN1.
    by move: (h (face (edge w))) => y; rewrite -{2}[y]Enode -cface1r Hbg.
   apply/subsetP => [w _]; rewrite /order_set Hh''E; set u := h'' w.
    case Hu: (negb (has (cedge (h' u)) (seq2 x (node x)))).
      rewrite -(eqnP (subsetA HgE (h w))) -(card_image Hh').
      apply/eqP; apply: eq_card => y.
      case Hy: (setC1 x y).
        pose v : g' := subdI Hy.
        rewrite -{1}[y]/(h' v) (image_f Hh') /= /setD1 /eqd /=.
        case: (node x =P y) => [Dnx|_]; last exact (same_cskip_edge Hu v).
        by symmetry; apply: negbE; rewrite /= orbF Dnx in Hu; case/norP: Hu.
      case/norP: Hu; move/negPf=> H _; move/eqP: Hy => <- {y}; rewrite /h -/u {}H.
      by apply/set0Pn; case=> v; move/andP=> [Dv _]; case/idP: (subd_mem v).
    have HxX: negb (cross_edge x).
      move: Hu; rewrite /= orbF /cross_edge Sedge !fconnect_orbit /orbit.
      rewrite !(eqnP (subsetA HgE _)) /= /setU1 !orbF (negbE Hnx).
      move=> H; apply/eqP => Dnx; move: H; rewrite -Dnx (inj_eqd (Iedge g)).
      rewrite orbA orbC !orbA eqd_sym orbb -orbA orbC eqd_sym orbb eqd_sym Dnx.
      case/norP; split; [exact (subd_mem w) | exact (subd_mem u)].
    move: (cardD1 unx (cedge u)).
    rewrite /g' (cskip_edge_merge HxX unx (negbEf Hu)) -/g' /= connect0 orbT /=.
    rewrite -2!eqdSS add1n => <-; move: (cardUI (cedge x) (cedge (node x))).
    rewrite -/(order edge x) -/(order edge (node x)).
    rewrite !(eqnP (subsetA HgE _)) addnC /addn /=.
    have HxnxI: setI (cedge x) (cedge (node x)) =1 set0.
      move=> y; apply/andP => [] [Hyx Hynx].
      by case/idP: HxX; rewrite /cross_edge (same_cedge Hyx) Sedge.
    rewrite (eqnP (introT set0P HxnxI)) /= (cardD1 x) {1}/setU connect0.
    rewrite /= add1n => <-; rewrite eqdSS -(card_image Hh').
    apply/eqP; apply: eq_card => y; rewrite /setD1 -/(setC1 x y).
    case Hy: (setC1 x y).
      set v := subdI Hy : g'; rewrite -{1}[y]/(h' v) (image_f Hh') /= /setU.
      apply: (etrans (cskip_edge_merge HxX v (negbEf Hu))).
      by rewrite /= orbF !(Sedge g y).
    apply/set0Pn;  case=> v; move/andP=> [Dv _].
    by case (negP (subd_mem v)); rewrite {1}(eqP (negbEf Hy)).
  apply/subsetP => [w _]; rewrite /order_set.
  apply: leq_trans (HgN (h w)); rewrite leq_eqVlt; apply/orP; left.
  rewrite /order -(card_image Hh); apply/eqP; apply: eq_card => [y].
  have HxN: fcycle node (seq2 x (node x)) by rewrite /= /eqdf Dnnx !set11.
  case Hxy: (cnode x y).
    transitivity false.
      apply/set0Pn; case=> wy; move/andP=> [Dy _].
      rewrite (fconnect_cycle HxN (setU11 _ _)) /= /setU1 orbF in Hxy.
      rewrite (eqP Dy) in Hxy; case/orP: Hxy => [Hxy|Hnxy].
        by case (negP (subd_mem (h'' wy))).
      by case (negP (subd_mem wy)).
    rewrite Snode -(same_cnode Hxy) (fconnect_cycle HxN (setU11 _ _)) /=.
    rewrite /setU1 orbF; symmetry; apply/norP.
    split; [ exact (subd_mem (h'' w)) | exact (subd_mem w) ].
  rewrite (fconnect_cycle HxN (setU11 _ _)) /= /setU1 orbF in Hxy.
  move/norP: Hxy => [Hxy Hnxy].
  pose wy := subdI (Hnxy : setC1 unx (subdI (Hxy : setC1 x y))) : g''.
  by rewrite -{1 2}[y]/(h wy) (image_f Hh) HhN.
move=> k [HkE HkF]; case: (minimal_counter_example_is_noncolorable Hg).
pose a' := cface _ (h _).
have Ha'x: forall y, a' y =1 set0 -> set2 x (node x) y.
  move=> y Ha'y; apply/norP => [[Hxy Hnxy]].
  pose wy  : g'' := subdI (Hnxy : setC1 unx (subdI (Hxy : setC1 x y))).
  by case/idP: (Ha'y wy); rewrite /a' /= connect0.
have Ha'F: forall y, a' y =1 set0 -> forall z, cface y z -> y = z.
  move=> y Ha'y z Hyz.
  have Hz: set2 x (node x) z.
    apply Ha'x; move=> w; rewrite /a' -(same_cface Hyz); exact (Ha'y w).
    case Hynz: (set2 y (node y) z).
    case/orP: Hynz; move=> Dz; first by apply: eqP.
    by rewrite -{1}[y]Enode (eqP Dz) -cface1 Sface Hbg in Hyz.
  case/idP: Hynz; rewrite /set2.
  by case/orP: (Ha'x _ Ha'y); move/eqP=> <- //; rewrite orbC Dnnx.
pose k' := fun y => if pick (a' y) is Some z then k z else ccons false (y =d x).
have HkFF: forall w w', cface w w' -> k w = k w'.
  move=> w w'; move/connectP=> [p Hp <-] {w' Hw Hw'}.
  elim: p w Hp => // [fw p Hrec] w; move/andP=> [Dfw Hp].
  rewrite -(eqcP (HkF w)) ((face w =P _) Dfw); exact (Hrec _ Hp).
have Hk'F: forall y z, cface y z -> k' y = k' z.
  move=> y z Hyz; rewrite /k'.
  case: (pickP (a' y)) => [w Hw|Hy].
    rewrite /a' (same_cface Hyz) in Hw.
    case: (pickP (a' z)) => [w' Hw'|Hz].
      by apply HkFF; rewrite HhF -(same_cface Hw).
    by case/idP: (Hz w).
  rewrite -(Ha'F _ Hy _ Hyz).
  by case: (pickP (a' y)) => [w Hw|_]; first by case/idP: (Hy w).
have Hk'E: forall y, negb (set2 x (node x) y) -> k' y <> k' (edge y).
  move=> y; move/norP=> [Hxy Hnxy].
  pose w := subdI (Hnxy : setC1 unx (subdI (Hxy : setC1 x y))) : g''.
  have Dfey: (face (edge y) = h (face (edge w))).
    by apply Inode; rewrite -HhN1 !Eedge.
  rewrite (Hk'F (edge y) _ (fconnect1 _ _)) /k'.
  case: (pickP (a' y)) => [w' Hw'|Hy];
    last by case/idP: (Hy w); rewrite /a' /= connect0.
  case: (pickP (a' (face (edge y)))) => [w'' Hw''|Hfey];
    last by case/idP: (Hfey (face (edge w))); rewrite /a' Dfey /= connect0.
  move=> Hkw; case/eqcP: (HkE w); rewrite -(eqcP (HkF (edge w))); symmetry.
  by apply: (etrans (etrans _ Hkw)); apply HkFF; rewrite HhF // -Dfey Sface.
exists k'.
split; last by move=> y; apply/eqP; apply: Hk'F; rewrite Sface fconnect1.
move=> y; apply/eqcP.
case Hy: (set2 x (node x) y); last by apply: nesym; apply Hk'E; apply negbI.
have De2y := plain_eq Hg y.
case Hey: (set2 x (node x) (edge y));
  last by rewrite -{2}De2y; apply Hk'E; apply negbI.
rewrite /k'; case: (pickP (a' y)) => [w Hw|_].
  have Hfy: set2 x (node x) (face y).
    by rewrite -De2y /set2 -!(monic2F_eqd (Enode g)) Dnnx orbC.
  have HyF: fcycle face (seq1 y).
    case HyN: (set2 y (node y) (face y)).
    case: (orP HyN); move/eqP=> Dfy; first by rewrite /= /eqdf -Dfy set11.
      by case/idP: (Hbg (node y)); rewrite cface1r Enode Sface Dfy fconnect1.
    case/idP: HyN; rewrite /set2.
    by case: (orP Hy); move/eqP=> Dy; rewrite -{1 3}Dy // orbC Dnnx.
  rewrite /a' (fconnect_cycle HyF (setU11 _ _)) /= /setU1 orbF in Hw.
  rewrite (eqP Hw) in Hy.
  case: (orP Hy); move=> Dy; first by case (negP (subd_mem (h'' w))).
  by case (negP (subd_mem w)).
case: (pickP (a' (edge y))) => [w Hw|Ha'ey].
  have Hfey: set2 x (node x) (face (edge y)).
    by rewrite /set2 -!(monic2F_eqd (Enode g)) Dnnx orbC.
  have HyF: fcycle face (seq1 (edge y)).
    case HyN: (set2 (edge y) (node (edge y)) (face (edge y))).
      case: (orP HyN); move/eqP=> Dfey; first by rewrite /= /eqdf -Dfey set11.
      case/idP: (Hbg (node (edge y))).
      by rewrite cface1r Enode Sface Dfey fconnect1.
    case/idP: HyN; rewrite /set2.
    by case: (orP Hey) => Dey; rewrite -{1 3}(eqP Dey) // orbC Dnnx.
  rewrite /a' (fconnect_cycle HyF (setU11 _ _)) /= /setU1 orbF in Hw.
  rewrite (eqP Hw) in Hey.
  case: (orP Hey) => Dey; first by case (negP (subd_mem (h'' w))).
  by case (negP (subd_mem w)).
move: Hy; rewrite (eqd_sym y) /set2.
case: (x =P y) => [<-|_] /= Dy; first by rewrite plain_neq.
by rewrite (Ha'F _ Ha'ey _ (fconnect1 _ _)) -(eqP Dy) Enode set11.
Qed.

Coercion minimal_counter_example_is_cubic : minimal_counter_example >-> cubic.

End MinimalCounterExample.

(* Used for symmetrydisposition, and flipped configuration match. *)
Lemma minimal_counter_example_mirror : forall g,
  minimal_counter_example g -> minimal_counter_example (mirror g).
Proof.
move=> g; do 4 case; move=> Hpg Hbg HgE HgN Hkg Htg.
split; auto; last by move=> Hkmg; case Hkg; apply colorable_mirror.
split; last by rewrite precubic_mirror.
split; last by rewrite plain_mirror.
split; last by rewrite bridgeless_mirror.
by rewrite planar_mirror.
Qed.

Section ConfigurationProperties.

Variables (n0 : nat) (g : hypermap) (r cc : seq g).

(* We state and prove separately the geometrical and semantic requirements  *)
(* on configurations. The former ("embeddable") are established by the quiz *)
(* construction; the latter ("c_reducible") by the reducibility check.      *)
(* The geometrical requirements are that configuration maps must be plain   *)
(* quasicubic planar bridgeless maps with a simple ring, that satisfy two   *)
(* additional conditions: the ring faces arities must be in the 3..6 range, *)
(* and the kernel must have radius 2. These two additional properties are   *)
(* used in embed.v to extend a partial hypermap morphism into an embedding. *)

Definition good_ring_arity (x : g) : bool := set4 3 4 5 6 (order face x).

Section Radius2.

(* Since our configuration maps have at most one "bridge" face, we can use *)
(* a slightly more restrictive definition of "radius 2" : we insist that   *)
(* every region is a exactly two adj "hops" away from the center rather    *)
(* than just "at most two" (the extra requirement will always be met,      *)
(* because we can always take a detour through an adjacent spoke.          *)
(* The waeker definition is more complex, and in particular it's eaasier   *)
(* to check the stricter condition on the configurations' data.            *)

Variable a : set g.

Definition at_radius2 x y := negb (disjoint (adj y) (setI (adj x) a)).

Lemma at_radius2P : fclosed face a -> forall x y,
 reflect (exists x', exists2 y', cface x x' /\ cface y y'
                               & a (edge x') /\ cface (edge x') (edge y'))
         (at_radius2 x y).
Proof.
move=> HaF x y; apply: (iffP (set0Pnx (setI _ _))); case.
  move=> z; case/and3P; move/adjP=> [y' Hyy' Hy'z]; move/adjP=> [x' Hxx' Hx'z] Haz.
  exists x'; exists y'; auto; split; first by rewrite (closed_connect HaF Hx'z).
  by rewrite (same_cface Hx'z) Sface.
move=> x' [y' [Hxx' Hyy'] [Haex' Hexy']]; exists (edge x').
by rewrite /setI (adjF Hxx') (adjF Hyy') (adjFr Hexy') !adjE.
Qed.

Definition radius2 := negb (disjoint a (fun x => subset a (at_radius2 x))).

Lemma radius2P : reflect (exists2 x, a x & sub_set a (at_radius2 x)) radius2.
Proof.
apply: (iffP (set0Pnx (setI _ _))) => [] [x].
  by case/andP=> [Hx]; move/subsetP; exists x.
by move=> Hx Ha; exists x; rewrite /setI {}Hx; apply/subsetP.
Qed.

End Radius2.

Record embeddable : Prop := Embeddable {
  embeddable_base :> scycle_planar_bridgeless_plain_quasicubic_connected r;
  embeddable_ring : all good_ring_arity r;
  embeddable_kernel : radius2 (kernel r)
}.

Definition sparse (p : seq g) := simple (p : seq (permF g)).

Lemma sparse_adds : forall x p,
  sparse (Adds x p) = negb (has (cnode x) p) && sparse p.
Proof. exact (@simple_adds (permF g)). Qed.

Lemma sparse_catC : forall p1 p2, sparse (cat p1 p2) = sparse (cat p2 p1).
Proof. exact (@simple_catC (permF g)). Qed.

Lemma sparse_catCA : forall p1 p2 p3,
 sparse (cat p1 (cat p2 p3)) = sparse (cat p2 (cat p1 p3)).
Proof. exact (@simple_catCA (permF g)). Qed.

Lemma sparse_rot : forall p, sparse (rot n0 p) = sparse p.
Proof. exact (@simple_rot n0 (permF g)). Qed.

Definition triad (p : seq g) x :=
  let adjp y := fband p (edge y) in
  (2 < count adjp (orbit face x)) && negb (subset p (adj x)).

Record valid_contract : Prop := ValidContract {
  valid_contract_is_off_ring : disjoint r (insertE cc);
  valid_contract_is_sparse : sparse (insertE cc);
  valid_contract_size : set4 1 2 3 4 (size cc);
  valid_contract_triad :
     size cc = 4 -> negb (disjoint (kernel r) (triad (insertE cc)))
}.

Record c_reducible : Prop := Creducible {
  c_reducible_base :> valid_contract;
  c_reducible_coclosure : forall et : colseq,
    cc_ring_trace cc (rev r) et -> kempe_coclosure (ring_trace (rev r)) et
}.

End ConfigurationProperties.

Prenex Implicits radius2 sparse good_ring_arity triad.

Section Preembedding.

(* The properties of the partial morphism contructed in quiz, and extended  *)
(* to an embedding in embed. The morphism is only defined on the kernel of  *)
(* the configuration. On this subset, it should be a strict morphism for    *)
(* face and arity. The darts on which it commutes with edge should form an  *)
(* rlink-connected cover of the kernel, up to cface.                        *)

Variables (g g' : hypermap) (a : set g) (h : g -> g').

Definition edge_central x := h (edge x) =d edge (h x).

Lemma edge_central_edge : plain g -> plain g' ->
  forall x, edge_central (edge x) = edge_central x.
Proof.
move=> HgE Hg'E x; rewrite /edge_central eqd_sym plain_eq //.
by rewrite (monic2F_eqd (plain_eq Hg'E)).
Qed.

Record preembedding : Prop := Preembedding {
  preembedding_face : forall x, a x -> h (face x) = face (h x);
  preembedding_arity : forall x, a x -> order face (h x) = order face x;
  preembedding_cover : subset a (fclosure face edge_central);
  preembedding_rlinked : rlink_connected (setI a edge_central)
}.

Lemma preembedding_simple_path : preembedding -> fclosed face a ->
    forall x y, a (edge x) -> a y ->
 exists2 p, and3 (path rlink x p) (cface (last x p) y) (negb (p =d seq0))
          & simple p /\ all (setI a edge_central) p.
Proof.
move=> [_ _ HhaF HhaE] HaF x y Hx Hy; set a' := setI a edge_central.
case/set0Pn: (subsetP HhaF _ Hx) => [x']; move/andP=> [Hxx' Hx'E].
case/set0Pn: {HhaF}(subsetP HhaF _ Hy) => [y']; move/andP=> [Hyy' Hy'E].
have Hx': a' x' by rewrite /a' /setI -(closed_connect HaF Hxx') Hx.
have Hy': a' y' by rewrite /a' /setI -(closed_connect HaF Hyy') Hy.
case: {HhaE}(HhaE _ _ Hx' Hy') => [p Hp Hpa']; rewrite -/a' in Hpa'.
have Hxp: path rlink x (add_last p y').
  by move: Hp; rewrite headI /= {1}/rlink Eface -(same_cface Hxx').
  case: (simplify_rlink Hxp) => [p' [Hp' Up'] [Ep' Ep'0 Hpp']].
exists p'; split; try by rewrite -?Ep'0 1?headI.
  by rewrite -Ep' last_add_last Sface.
rewrite -!subset_all in Hpp' |- *; apply: (subset_trans Hpp').
by rewrite subset_all -cats1 all_cat Hpa' /= Hy'.
Qed.

End Preembedding.

Prenex Implicits edge_central.

Unset Implicit Arguments.