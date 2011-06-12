(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import paths.
Require Import hypermap.
Require Import geometry.
Require Import coloring.
Require Import znat.
Require Import grid.
Require Import matte.
Require Import real.
Require Import realmap.
Require Import realsyntax.
Require Import Setoid.
Require Import realprop.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section ApproxMap.

(*   Approximations of real scalar, points, regions and rectangles, used for *)
(* casting the continuous four color problem into a combinatorial form.      *)
(*   Because the grid decomposition is based on dichotomy, we choose to      *)
(* approximate the real coordinates with binary decimals (i.e., floating     *)
(* nubers, rather than arbitrary rationals.                                  *)

Variable R : real_model.

Notation point := (point R).
Notation region := (region R).
Notation map := (map R).
Notation rect := (rect R).
Notation interval := (interval R).

(* Because of the limitations of Coq v8.0 Setoid tactics, we need to repeat *)
(* some of the boilerplate from file realprop.v. here.                      *)

Let RR : Type := R.
Let isR (x : RR) : RR := x.
Let leqR : RR -> RR -> Prop := locked (@leqr _).
Let eqR : RR -> RR -> Prop := @eqr _.
Let addR : RR -> RR -> RR := locked (@addr _).
Let oppR : RR -> RR := locked (@oppr _).
Let mulR : RR -> RR -> RR := locked (@mulr _).
Let selR : Prop -> RR -> RR -> RR := locked (@selr _).
Let minR : RR -> RR -> RR := locked (@minr _).
Let maxR : RR -> RR -> RR := locked (@maxr _).
Let range1R : RR -> RR -> Prop := @range1r _.
Coercion Local natR := natr R.
Coercion Local znatR := znatr R.

Open Scope real_scope.

Remark rwR : forall x1 x2 : R, x1 == x2 -> eqR (isR x1) (isR x2).
Proof. done. Qed.

Remark leqRI : forall x1 x2 : R, (x1 <= x2) = leqR (isR x1) (isR x2).
Proof. by unlock leqR. Qed.

Remark eqRI : forall x1 x2 : R, (x1 == x2) = eqR (isR x1) (isR x2).
Proof. by unlock eqR. Qed.

Remark addRI : forall x1 x2 : R, x1 + x2 = addR (isR x1) (isR x2).
Proof. by unlock addR. Qed.

Remark oppRI : forall x : R, - x = oppR (isR x).
Proof. by unlock oppR. Qed.

Remark mulRI : forall x1 x2 : R, x1 * x2 = mulR (isR x1) (isR x2).
Proof. by unlock mulR. Qed.

Remark selRI : forall P (x1 x2 : R),
  select {x1 if P, else x2} = selR P (isR x1) (isR x2).
Proof. by unlock selR. Qed.

Remark minRI : forall x1 x2 : R, min x1 x2 = minR (isR x1) (isR x2).
Proof. by unlock minR. Qed.

Remark maxRI : forall x1 x2 : R, max x1 x2 = maxR (isR x1) (isR x2).
Proof. by unlock maxR. Qed.

Lemma range1RI : forall x1 x2 : R, range1r x1 x2 = range1R (isR x1) (isR x2).
Proof. done. Qed.

Add Setoid RR eqR (eqr_theory R).

Hint Unfold eqR.

Let eqR_refl : forall x, eqR x x := @eqr_refl R.
Hint Resolve eqr_refl leqrr ltrW ltr01 ltr02.

Let ltr01 := (ltr01 R).
Let ltr02 := (ltr02 R).
Notation znatr_leqP := (znatr_leqPx R _ _).
Notation znatr_ltP := (znatr_ltPx R _ _).

Add Morphism isR : discrmap_isr_morphism. Proof. done. Qed.

Add Morphism leqR : discrmap_leqr_morphism. Proof. exact: leqR_morphism. Qed.

Add Morphism addR : discrmap_addr_morphism. Proof. exact: addR_morphism. Qed.

Add Morphism oppR : discrmap_oppr_morphism. Proof. exact: oppR_morphism. Qed.

Add Morphism mulR : discrmap_mulr_morphism. Proof. exact: mulR_morphism. Qed.

Add Morphism minR : discrmap_minr_morphism.
Proof. unlock minR; exact: minr_morphism. Qed.

Add Morphism maxR : discrmap_maxr_morphism.
Proof. unlock maxR; exact: maxr_morphism. Qed.

Add Morphism selR : discrmap_selR_morphism.
Proof. unlock selR; exact: selr_morphism. Qed.

Add Morphism range1R : discrmap_range1r_morphism.
Proof. exact: range1r_morphism. Qed.

(* Real powers of 2, for scaling approximations.                          *)

Fixpoint exp2 (s : nat) : R := if s is S s' then 2 * exp2 s' else 1.

Lemma leqr1exp2 : forall s, 1 <= exp2 s.
Proof.
elim=> [|s]; [ exact: leqrr | rewrite -(leqr_pmul2l 1 (exp2 s) ltr02) /= ].
apply: leqr_trans; rewrite leqRI (rwR (mulr1 2)) -leqRI.
exact: (znatr_leqPx _ 1%nat 2%nat).
Qed.

Lemma ltr0exp2 : forall s, 0 < exp2 s.
Proof. move=> s; apply: (ltr_leq_trans ltr01); exact: leqr1exp2. Qed.
Implicit Arguments ltr0exp2 [].

Lemma exp2_add : forall s1 s2, exp2 (s1 + s2) == exp2 s1 * exp2 s2.
Proof.
move=> s1 s2; elim: s1 => [|s1 Hrec] /=.
  by rewrite eqRI (rwR (mul1r (exp2 s2))).
rewrite eqRI mulRI addnI (rwR Hrec) -mulRI; apply: mulrA.
Qed.

Lemma leq_exp2 : forall s1 s2, (s1 <= s2)%dnat -> exp2 s1 <= exp2 s2.
Proof.
move=> s1 s2 Hs12; rewrite -(leq_add_sub Hs12).
move: {s2 Hs12}(s2 - s1)%dnat => s2.
rewrite leqRI -(rwR (mulr1 (exp2 s1))) (rwR (exp2_add s1 s2)) -leqRI.
rewrite (leqr_pmul2l 1 (exp2 s2) (ltr0exp2 s1)); exact: leqr1exp2.
Qed.

Lemma ltr1exp2S : forall s, 1 < exp2 (S s).
Proof.
move=> s; apply: ltr_leq_trans (leq_exp2 (ltn0Sn s)).
rewrite /= leqRI (rwR (mulr1 2)) -leqRI; exact: ltrSr.
Qed.
Implicit Arguments ltr1exp2S [].

(* Scalar decimal approximation.                                       *)

Definition approx s (x : RR) (m : znat) := range1r m (exp2 s * x).

Add Morphism approx : approx_morphism.
Proof. by move=> s x y m Dx; rewrite /approx range1RI !mulRI Dx. Qed.

Lemma approxI : forall s (x : R), approx s x = approx s (isR x).
Proof. done. Qed.

Lemma approx_inj : forall s (x : R) m1 m2,
  approx s x m1 -> approx s x m2 -> m1 = m2.
Proof. move=> s x; apply: range1z_inj. Qed.

Lemma approx_exists : forall s (x : R), exists m, approx s x m.
Proof. by move=> s x; apply: find_range1z. Qed.

Definition scale s (m : znat) : R := m / exp2 s.

Lemma approx_scale : forall s m, approx s (scale s m) m.
Proof.
move=> s m; rewrite /approx /scale range1RI.
rewrite (rwR (mulrCA (exp2 s) m (invr (exp2 s)))).
rewrite mulRI (rwR (divrr (gtr_neq (ltr0exp2 s)))) -mulRI.
rewrite (rwR (mulr1 m)); exact: range1zz.
Qed.

Lemma approx_halfz : forall s (x : R) m, approx (S s) x m -> approx s x (halfz m).
Proof.
rewrite /approx /=; move/exp2=> y x m; rewrite range1RI -(rwR (mulrA 2 y x)).
move: {y x}(y * x) => x; rewrite /range1R /range1r /isR !leqRI !addRI /znatR.
rewrite (rwR (znatr_addbit _ m)) -/znatR -/natR -!addRI -!leqRI.
move/halfz: m (oddz m) => m b [Hxm Hmx].
rewrite -(leqr_pmul2l m x ltr02) -(leqr_pmul2l (m + 1) x ltr02); split.
  apply: leqr_trans Hxm; rewrite leqRI -(rwR (add0r (2 * m))) -leqRI.
  rewrite (leqr_add2r (2 * m) 0 b); exact: leqr0n.
apply: (ltr_leq_trans Hmx); rewrite leqRI (rwR (mulr_addr 2 m 1)).
rewrite (addRI (2 * m)) (rwR (mulr1 2)) -addRI (rwR (addrCA (2 * m) 1 1)).
rewrite -(rwR (addrA b (2 * m) 1)) -leqRI (leqr_add2r (2 * m + 1) b 1).
by case: (b) => /=; auto.
Qed.

Lemma scale_exists : forall x : R, x > 0 -> exists s, exp2 s * x > 1.
Proof.
move=> x Hx; case: (find_range1z (/ x)) => [[s|s'] [_]].
  rewrite /= -/natR -(leqr_pmul2l (s + 1) (/ x) Hx) leqRI.
  rewrite (rwR (divrr (gtr_neq Hx))) /natR mulRI -(rwR (natr_S _ s)) -/natR.
  rewrite -mulRI -leqRI => Hs.
  exists s; elim: s x Hx Hs => [|s Hrec] x Hx Hs /=.
    by rewrite leqRI (rwR (mulrC 1 x)) -leqRI.
  rewrite leqRI -(rwR (mulrA 2 (exp2 s) x)).
  rewrite (rwR (mulrCA 2 (exp2 s) x)) -leqRI; apply Hrec.
    by rewrite leqRI -(rwR (mulr0 2)) -leqRI (leqr_pmul2l x 0 ltr02).
  apply: (ltr_leq_trans Hs); rewrite leqRI -(rwR (mulrA 2 x (S s))).
  rewrite (rwR (mulrCA 2 x (S s))) -leqRI.
  rewrite (leqr_pmul2l (S (S s)) (2 * S s) Hx).
  rewrite leqRI (rwR (mulr_addl (S s) 1 1)) addRI (rwR (mul1r (S s))) -addRI.
  rewrite /natR (rwR (natr_S _ (S s))) -/natR -leqRI (leqr_add2l (S s) 1 (S s)).
  by apply: (znatr_leqPx R 1%nat (S s)) => /=; rewrite leqz_nat.
case; apply ltrW; apply: leqr_lt_trans (posr_inv Hx).
rewrite leqRI -/znatR (rwR (addrC (Zneg s') 1)).
rewrite addRI /znatR /znatr oppRI (rwR (natr_S _ s')) -/natR -oppRI.
rewrite (rwR (oppr_add s' 1)) -addRI (rwR (addrCA 1 (- s') (- 1))).
rewrite addRI (rwR (subrr 1)) -addRI (rwR (addr0 (- s'))) -(rwR (oppr0 _)).
rewrite -leqRI (leqr_opp2 s' 0); exact: leqr0n.
Qed.

Lemma approx_between : forall s (x1 x2 : R) m1 m2,
   approx (S s) x1 m1 -> approx (S s) x2 m2 -> 1 < exp2 s * (x2 - x1) ->
  exists2 m, (incz m1 <= m)%Z & (incz m <= m2)%Z.
Proof.
move=> s x1 x2 m1 m2; set s2 := exp2 s; set z := s2 * (x2 - x1).
case: (approx_exists s (x1 + x2)) => m; rewrite /approx /= -/s2.
set y := s2 * (x1 + x2).
have Dx1: 2 * s2 * x1 == y - z.
  rewrite eqRI -(rwR (mulrA 2 s2 x1)) (rwR (mulrCA 2 s2 x1)).
  rewrite mulRI (rwR (mulr_addl x1 1 1)) addRI (rwR (mul1r x1)).
  rewrite /y /z addRI -(rwR (mulr_oppr s2 (x2 - x1))) !mulRI.
  rewrite (rwR (oppr_sub x2 x1)) -!mulRI -!addRI.
  rewrite -(rwR (mulr_addr s2 (x1 + x2) (x1 - x2))) !mulRI.
  rewrite (rwR (addrCA (x1 + x2) x1 (- x2))) 2!addRI.
  rewrite -(rwR (addrA x1 x2 (- x2))) addRI (rwR (subrr x2)) -!addRI 2!addRI.
  by rewrite (rwR (addr0 x1)).
have Dx2: 2 * s2 * x2 == y + z.
  rewrite eqRI -(rwR (mulrA 2 s2 x2)) (rwR (mulrCA 2 s2 x2)).
  rewrite mulRI (rwR (mulr_addl x2 1 1)) addRI (rwR (mul1r x2)).
  rewrite /y /z -(rwR (mulr_addr s2 (x1 + x2) (x2 - x1))) !mulRI.
  rewrite (rwR (addrCA (x1 + x2) x2 (- x1))) addRI.
  rewrite -(rwR (addrA x1 x2 (- x1))) (rwR (addrCA x1 x2 (- x1))) addRI.
  by rewrite (rwR (subrr x1)) -!addRI 2!addRI (rwR (addr0 x2)).
move=> [Hmy Hym]; rewrite range1RI (rwR Dx1) /isR {Dx1} => [[Hm1 _]].
case=> _; rewrite leqRI -/znatR {Dx2}(rwR Dx2) -leqRI => Hm2 Hz.
exists m; apply/znatr_ltP; rewrite -/znatR.
  apply: (leqr_lt_trans Hm1); rewrite -(leqr_add2l z m (y - z)) leqRI.
  rewrite (rwR (addrCA z y (- z))) 2!addRI (rwR (subrr z)) -!addRI.
  rewrite (rwR (addr0 y)) (rwR (addrC z m)) -leqRI; apply: (ltr_leq_trans Hym).
  by apply ltrW; rewrite -/znatR (leqr_add2l m z 1).
apply: (leqr_lt_trans Hmy); rewrite -(leqr_add2r z m2 y).
by apply: (ltr_leq_trans Hm2); apply ltrW; rewrite (leqr_add2l m2 z 1).
Qed.

(* Geometrical binary approximation.                                   *)

Definition approx_point s (z : point) p :=
  let: Point x y := z in let: Gpoint mx my := p in approx s x mx /\ approx s y my.

Lemma approx_point_inj : forall s z p1 p2,
  approx_point s z p1 -> approx_point s z p2 -> p1 = p2.
Proof.
move=> s [x y] [mx1 my1] [mx2 my2] [Hx1 Hy1] [Hx2 Hy2].
congr Gpoint; eapply approx_inj; eauto.
Qed.

Lemma approx_point_exists : forall s z, exists p, approx_point s z p.
Proof.
move=> s [x y]; case: (approx_exists s x) (approx_exists s y) => [mx Hmx] [my Hmy].
by exists (Gpoint mx my); split.
Qed.

Definition scale_point s p : point :=
  let: Gpoint mx my := p in Point (scale s mx) (scale s my).

Lemma approx_scale_point : forall s p, approx_point s (scale_point s p) p.
Proof. move=> s [mx my]; split; apply approx_scale. Qed.

Lemma approx_halfg : forall s z p,
   approx_point (S s) z p -> approx_point s z (halfg p).
Proof. by move=> s [x y] [mx my] [Hx Hy]; split; apply approx_halfz. Qed.

Notation gpset := (set gpointData).

Definition mem_approx s (gr : gpset) : region :=
   fun z => exists2 p, approx_point s z p & gr p.

Lemma sub_mem_approx : forall s (gr1 gr2 : gpointset),
  sub_set gr1 gr2 -> subregion (mem_approx s gr1) (mem_approx s gr2).
Proof. move=> s gr1 gr2 Hgr12 z [p Dp Hp]; exists p; auto. Qed.

Lemma mem_approx_scale : forall s gr p,
  reflect (mem_approx s gr (scale_point s p)) (gr p).
Proof.
move=> s gr p; apply: (iffP idP) => [Hp|[p' Dp' Hp']].
  by exists p; first by apply approx_scale_point.
by rewrite (approx_point_inj (approx_scale_point _ _) Dp').
Qed.

Lemma mem_approx_refine1_rect : forall s b z,
  mem_approx (S s) (refine_rect b) z <-> mem_approx s b z.
Proof.
move=> s b z; split; move=> [p Dp Hp].
  by exists (halfg p); [ apply approx_halfg | rewrite -mem_refine_rect ].
  case: (approx_point_exists (S s) z) => [p' Dp']; exists p'; first done.
by rewrite mem_refine_rect (approx_point_inj (approx_halfg Dp') Dp).
Qed.

Lemma mem_approx_refine_rect : forall s s' b z,
  mem_approx (s + s') (iter s refine_rect b) z <-> mem_approx s' b z.
Proof.
move=> s s' b z; elim: s => //= [|s Hrec]; first by split.
rewrite -Hrec addSn; apply mem_approx_refine1_rect.
Qed.

Lemma mem_approx_refine1_matte : forall s mm z,
  mem_approx (S s) (refine_matte mm) z <-> mem_approx s mm z.
Proof.
move=> s mm z; split; move=> [p Dp Hp].
  by exists (halfg p); [ apply approx_halfg | rewrite -mem_refine_matte ].
  case: (approx_point_exists (S s) z) => [p' Dp']; exists p'; first done.
by rewrite mem_refine_matte (approx_point_inj (approx_halfg Dp') Dp).
Qed.

Lemma mem_approx_refine_matte : forall s s' mm z,
  mem_approx (s + s') (iter s refine_matte mm) z <-> mem_approx s' mm z.
Proof.
move=> s s' b z; elim: s => //= [|s Hrec]; first by split.
rewrite -Hrec addSn; apply: mem_approx_refine1_matte.
Qed.

Lemma mem_approx_inset2 : forall s b,
  subregion (mem_approx s (inset b)) (mem_approx (S s) (inset2 (refine_rect b))).
Proof.
move=> s b z [p Dp Hp].
case: (approx_point_exists (S s) z) => [p' Dp']; exists p'; first done.
by apply inset2_refine; rewrite (approx_point_inj (approx_halfg Dp') Dp).
Qed.

Lemma mem_approx_inset1 : forall s b,
  subregion (mem_approx s (inset b)) (mem_approx (S s) (inset (refine_rect b))).
Proof.
by move=> s r z; case/mem_approx_inset2=> [p Dp Hp]; case/andP: Hp; exists p.
Qed.

Lemma mem_approx_inset : forall s s' b,
 subregion (mem_approx s' (inset b))
           (mem_approx (s + s') (inset (iter s refine_rect b))).
Proof.
move=> s s' b z; elim: s => [|s Hrec] //= Hz; rewrite addSn.
apply: mem_approx_inset1; auto.
Qed.

Lemma approx_rect : forall z (r : rect), r z ->
 exists s, exists2 b, mem_approx s (inset b) z & subregion (mem_approx s b) r.
Proof.
move=> [x y] [[xx zx] [xy zy]] [Hrx Hry].
have [s [Hsxx Hszx] [Hsxy Hszy]]:
     exists2 s, 1 < exp2 s * (x - xx) /\ 1 < exp2 s * (zx - x)
              & 1 < exp2 s * (y - xy) /\ 1 < exp2 s * (zy - y).
  case Hrx; rewrite (leqr_sub0 x xx) (leqr_sub0 zx x).
  move/scale_exists=> [s1 Hs1]; move/scale_exists=> [s2 Hs2].
  case Hry; rewrite (leqr_sub0 y xy) (leqr_sub0 zy y).
  move/scale_exists=> [s3 Hs3]; move/scale_exists=> [s4 Hs4].
  have Hleql: forall n1 n2 n3, (n1 <= n2)%dnat -> (n1 <= n2 + n3)%dnat.
    move=> n1 n2 n3 Hn12; apply: (leq_trans Hn12); apply leq_addr.
  have Hleqr: forall n1 n2 n3, (n1 <= n3)%dnat -> (n1 <= n2 + n3)%dnat.
    move=> n1 n2 n3 Hn13; apply: (leq_trans Hn13); apply leq_addl.
  have Hleqs: forall n1 n2 u,
      1 < exp2 n1 * u -> (n1 <= n2)%dnat -> 1 < exp2 n2 * u.
    move=> n1 n2 u Hu1 Hn12.
    have Hu: u > 0.
      rewrite -(leqr_pmul2l u 0 (ltr0exp2 n1)) leqRI (rwR (mulr0 (exp2 n1))).
      by rewrite -leqRI; exact: ltr_trans Hu1.
    apply: (ltr_leq_trans Hu1).
    rewrite leqRI (rwR (mulrC (exp2 n1) u)) (rwR (mulrC (exp2 n2) u)) -leqRI.
    by move/leq_exp2: Hn12; rewrite (leqr_pmul2l (exp2 n1) (exp2 n2) Hu).
  move: leqnn; exists (addn (addn s1 s2) (addn s3 s4)); split; eapply Hleqs; eauto.
case: (approx_exists (S s) x) (approx_exists (S s) y) => [mx Dmx] [my Dmy].
case: (approx_exists (S s) xx) (approx_exists (S s) xy) => [mxx Dmxx] [mxy Dmxy].
case: (approx_exists (S s) zx) (approx_exists (S s) zy) => [mzx Dmzx] [mzy Dmzy].
case: (approx_between Dmxx Dmx) => // [nxx Hnxx Hnxxx].
case: (approx_between Dmx Dmzx) => // [nzx Hxnzx Hnzx].
case: (approx_between Dmxy Dmy) => // [nxy Hnxy Hnxyy].
case: (approx_between Dmy Dmzy) => // [nzy Hynzy Hnzy].
rewrite leqz_inc_dec in Hnxxx; rewrite leqz_inc_dec in Hnxyy.
exists (S s); exists (Grect nxx nzx nxy nzy).
  by exists (Gpoint mx my); try apply/and4P; split.
have Hap: forall u v nu nv,
    approx (S s) u nu -> approx (S s) v nv -> (incz nu <=nv)%Z -> u < v.
  rewrite /approx; move=> u v nu nv [_ Hnu] [Hnv _] Huv.
  rewrite -(leqr_pmul2l v u (ltr0exp2 (S s))).
  apply: (ltr_leq_trans Hnu); apply: leqr_trans Hnv.
  by rewrite leqRI /znatR -(rwR (znatr_inc _ nu)) -leqRI; exact: znatr_leqP.
move=> [x' y'] [[mx' my'] [Dmx' Dmy']]; move/and4P=> [Hmxxx' Hx'mzx Hmxyy' Hy'mzy].
by split; split; eapply Hap; eauto; eapply leqz_trans; eauto; rewrite leqz_inc2.
Qed.

Lemma rect_approx : forall s z p, approx_point s z p ->
  exists2 r : rect, r z & subregion r (mem_approx s (ltouch p)).
Proof.
move=> s [x y] [mx my] [H H']; case: H'; case: H; set s1 := exp2 s.
have Hs1: s1 > 0 by exact: ltr0exp2.
have Es1: forall u, s1 * (u / s1) == u.
  move=> u; rewrite eqRI (rwR (mulrCA s1 u (/ s1))) mulRI.
  by rewrite (rwR (divrr (gtr_neq Hs1))) -mulRI (rwR (mulr1 u)).
move=> Hmxx Hxmx Hmyy Hymy.
pose int_pm1 (m : znat) := Interval ((m - 1) / s1) ((m + 1) / s1).
exists (Rect (int_pm1 mx) (int_pm1 my)).
  split; split.
  - rewrite -(leqr_pmul2l x ((mx - 1) / s1) Hs1) leqRI (rwR (Es1 (mx - 1))).
    rewrite /znatR -(rwR (znatr_dec _ mx)) -/znatR -leqRI.
    by apply: ltr_leq_trans Hmxx; apply: znatr_ltP; rewrite incz_dec leqzz.
  - rewrite -(leqr_pmul2l ((mx + 1) / s1) x Hs1) leqRI (rwR (Es1 (mx + 1))).
    by rewrite -leqRI.
  - rewrite -(leqr_pmul2l y ((my - 1) / s1) Hs1) leqRI (rwR (Es1 (my - 1))).
    rewrite /znatR -(rwR (znatr_dec _ my)) -/znatR -leqRI.
    by apply: ltr_leq_trans Hmyy; apply: znatr_ltPx; rewrite incz_dec leqzz.
  rewrite -(leqr_pmul2l ((my + 1) / s1) y Hs1) leqRI (rwR (Es1 (my + 1))).
  by rewrite -leqRI.
move=> [x' y'] [H H']; case: H'; case: H.
rewrite -(leqr_pmul2l x' ((mx - 1) / s1) Hs1) leqRI (rwR (Es1 (mx - 1))).
rewrite /znatR -(rwR (znatr_dec _ mx)) -/znatR -leqRI => Hmxx'.
rewrite -(leqr_pmul2l ((mx + 1) / s1) x' Hs1) leqRI (rwR (Es1 (mx + 1))).
rewrite -leqRI => Hx'mx.
rewrite -(leqr_pmul2l y' ((my - 1) / s1) Hs1) leqRI (rwR (Es1 (my - 1))).
rewrite /znatR -(rwR (znatr_dec _ my)) -/znatR -leqRI => Hmyy'.
rewrite -(leqr_pmul2l ((my + 1) / s1) y' Hs1) leqRI (rwR (Es1 (my + 1))).
rewrite -leqRI => Hy'my.
case: (approx_point_exists s (Point x' y')) => [p' Hp']; exists p'; auto.
case: p' Hp' => [mx' my'] [H H']; case: H'; case: H; rewrite -/s1.
move=> Hmx'x Hxmx' Hmy'y Hymy'; apply/and4P; split; rewrite -leqz_inc2;
 apply/znatr_ltP; rewrite leqRI /znatR;
 rewrite ?(rwR (znatr_inc _ mx')) ?(rwR (znatr_inc _ mx));
 rewrite ?(rwR (znatr_inc _ my')) ?(rwR (znatr_inc _ my)) -/znatR -leqRI;
 eapply leqr_lt_trans; eauto; eapply ltr_trans; eauto.
Qed.

(* Some rectangle operations.                                                   *)

Definition cap_interval (xz1 xz2 : interval) :=
  let: Interval x1 z1 := xz1 in let: Interval x2 z2 := xz2 in
  Interval (max x1 x2) (min z1 z2).

Lemma mem_cap_interval : forall (xz1 xz2 : interval) y,
  xz1 y /\ xz2 y <-> cap_interval xz1 xz2 y.
Proof.
move=> [x1 z1] [x2 z2] y /=; rewrite (ltr_max x1 x2 y) (ltr_min z1 z2 y); tauto.
Qed.

Definition cap_rect (r1 r2 : rect) :=
  let: Rect xint1 yint1 := r1 in let: Rect xint2 yint2 := r2 in
  Rect (cap_interval xint1 xint2) (cap_interval yint1 yint2).

Lemma mem_cap_rect : forall (r1 r2 : rect) p, r1 p /\ r2 p <-> cap_rect r1 r2 p.
Proof.
move=> [xint1 yint1] [xint2 yint2] [px py] /=.
rewrite -(mem_cap_interval xint1 xint2 px) -(mem_cap_interval yint1 yint2 py).
tauto.
Qed.

Definition sep_interval (x z : R) :=
  let y := (x + z) / 2 in
  Interval (select {z - 1 if z <= y, else y}) (select {z + 1 if z >= y, else y}).

Lemma mem_sep_interval : forall x y : R, sep_interval x y y.
Proof.
move=> x z; rewrite /sep_interval; move: {x}((x + z) / 2) => y; split.
  case: (selr_cases (z <= y) (z - 1) y) => t.
  case; case=> Ht Dt; rewrite leqRI (rwR Dt) -leqRI //; exact: ltPrr.
case: (selr_cases (z >= y) (z + 1) y) => t.
case; case=> Ht Dt; rewrite leqRI (rwR Dt) -leqRI //; exact: ltrSr.
Qed.

Lemma meet_sep_interval : forall x y t,
  sep_interval x y t -> sep_interval y x t -> x == y.
Proof.
suffice Hle: forall t x y, sep_interval x y t -> sep_interval y x t -> x <= y.
  by move=> x y t *; split; apply: (Hle t).
move=> t x y Hxyt Hyxt; case: (reals_classic R (x <= y)) => // Hyx.
case: Hyxt; case: Hxyt.
rewrite !selRI !mulRI !leqRI (rwR (addrC y x)) -!mulRI -!leqRI -!selRI.
set z := (x + y) / 2; have Ez2: 2 * z == x + y.
rewrite /z eqRI (rwR (mulrCA 2 (x + y) (/ 2))) mulRI.
  rewrite (rwR (divrr (gtr_neq ltr02))) -mulRI; exact: mulr1.
have [Hyz Hzx]: y < z < x.
  rewrite -(leqr_pmul2l z y ltr02) -(leqr_pmul2l x z ltr02) !leqRI (rwR Ez2).
  rewrite (rwR (mul2r x)) (rwR (mul2r y)) -!leqRI.
  by rewrite (leqr_add2l x x y) (leqr_add2r y x y); split.
clear; case: (selr_cases (z <= y) (y + 1) z) => z'.
case=> [[Hz _]|[_ Dz']]; first by case Hyz.
rewrite leqRI {z' Dz'}(rwR Dz') -leqRI => Hzt.
case: (selr_cases (x <= z) (x - 1) z) => z'.
case=> [[Hz _]|[_ Dz']]; first by case Hzx.
by rewrite leqRI {z' Dz'}(rwR Dz') -leqRI; case; exact: ltrW.
Qed.

Definition sep_rect z1 z2 :=
  let: Point x1 y1 := z1 in let: Point x2 y2 := z2 in
  Rect (sep_interval x1 x2) (sep_interval y1 y2).

Lemma mem_sep_rect : forall z1 z2, sep_rect z1 z2 z2.
Proof. by move=> [x1 y1] [x2 y2] /=; split; apply mem_sep_interval. Qed.

Lemma meet_sep_rect : forall z1 z2, meet (sep_rect z1 z2) (sep_rect z2 z1) ->
  forall rr : rect, rr z1 -> rr z2.
Proof.
move=> [x1 y1] [x2 y2] [[x y] [[Hx12 Hy12] [Hx21 Hy21]]] [[t1 t2] [t3 t4]] Hrz1.
rewrite /= !leqRI -(rwR (meet_sep_interval Hx12 Hx21)).
by rewrite -(rwR (meet_sep_interval Hy12 Hy21)) -!leqRI.
Qed.

End ApproxMap.

Set Strict Implicit.
Unset Implicit Arguments.

