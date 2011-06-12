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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The walkup construction (due to Stahl) removes a point from the domain of *)
(* a hypermap, suppressing it from two of the three permutations. The third  *)
(* permutation then needs a slightly more complex adjustment in order to     *)
(* reestablish the triangular identity. Because of this asymmetry, there are *)
(* are actually three ways of applying the transformation. It turns out that *)
(* all three variants are useful in proving the Jordan/Euler equivalence,    *)
(* and later in the four color theorem proof (walkupE is used in cubic.v,    *)
(* walkupN in kempe.v, and walkupF in contract.v)!                           *)

Section Walkup.

Variables (g : hypermap) (z : g).

Let d' := subFin (setC1 z).
Let to_d' : forall x, setC1 z x -> d' := @subdI _ _.
Let to_g : d' -> g := @subdE _ _.

Remark z_to_g : forall u, (z =d to_g u) = false.
Proof. by move=> [x Hx]; apply negbE. Qed.

Remark to_g_inj : injective to_g. Proof. apply: subdE_inj. Qed.

Section Skip.

Variable f : g -> g.
Hypothesis Hf : injective f.

Definition skip1 x := if z =d f x then f z else f x.

Lemma skipP : forall u, setC1 z (skip1 (to_g u)).
Proof.
move=> [x Hx]; rewrite /skip1 /setC1 /=.
case Hfx: (eqd z (f x)); last by rewrite Hfx.
by apply/eqP => [Dfz]; case/idP: Hx; rewrite -(inj_eqd Hf) -Dfz.
Qed.

Definition skip u := to_d' (skipP u).

Remark inj_skip : injective skip.
Proof.
move=> [x Hx] [y Hy] [Hxy]; apply: to_g_inj; move: Hxy; rewrite /= /skip1.
case: (z =P f x) => [Dfx|_].
  rewrite {2}Dfx (inj_eqd Hf); case: (x =P y) => [H|_] //.
  by move=> Dy; rewrite (Hf Dy) setC11 in Hy.
case (eqd z (f y)); last by apply Hf.
by move=> Dx; rewrite (Hf Dx) setC11 in Hx.
Qed.

Lemma subdE_skip : forall u v, to_g v = f (to_g u) -> v = skip u.
Proof.
move=> [x Hx] [y Hy] /= Dy; apply: to_g_inj.
by rewrite /= /skip1 -Dy (negbE Hy).
Qed.

Lemma base_skip : fun_base to_g f skip (set1 (finv f z)).
Proof.
move=> [x Hx] y'; rewrite /eqdf {3}/eqd /= /skip1.
by rewrite (monic2F_eqd (f_finv Hf)); move/negbE=> ->.
Qed.

Lemma fconnect_skip : forall u v, fconnect skip u v = fconnect f (to_g u) (to_g v).
Proof.
move=> u v; apply/idP/idP; move/connectP=> [p Hp Ep].
  rewrite -{v}Ep; elim: p u Hp => [|v p Hrec] u; first by rewrite connect0.
  move/andP=> [Dv H]; apply: connect_trans {H Hrec}(Hrec _ H).
  rewrite {2}/to_g -{v Dv}(eqP Dv); move: u => [x Hx]; rewrite /= /skip1.
  case: (z =P f x) => [Dfx|_]; last by apply fconnect1.
  rewrite Dfx; exact (fconnect_iter f 2 x).
elim: {p}(S (size p)) {-2}p u (ltnSn (size p)) Hp Ep => [|n Hrec] // [|y p] u /=.
  by move=> _ _ Dv; apply eq_connect0; apply: to_g_inj.
move=> Hn; move/andP=> [Dy Hp] Ep.
case Hy: (setC1 z y).
  apply: (connect_trans (connect1 _) (Hrec p (to_d' Hy) Hn Hp Ep)).
  by rewrite /eqdf /= /eqd /= /skip1 (eqP Dy) (negbE Hy) set11.
case: p Hn Hp Ep => [|fy p] Hn /= Hp Ep; first by rewrite /setC1 Ep z_to_g in Hy.
have Hfy: setC1 z (f y).
  rewrite /setC1 (eqP (negbEf Hy)) -{1}(eqP Dy) (inj_eqd Hf).
  by rewrite -(eqP (negbEf Hy)) eqd_sym z_to_g.
move/andP: Hp => [Dfy Hp]; rewrite (eqP Dfy) in Hfy.
apply: (connect_trans (connect1 _) (Hrec p (to_d' Hfy) (ltnW Hn) Hp Ep)).
by rewrite /eqdf /= /eqd /= /skip1 (eqP Dy) (eqP (negbEf Hy)) set11.
Qed.

Lemma fcard_skip : (z =d f z) + fcard skip d' = fcard f g.
Proof.
have Hfg := fconnect_sym Hf; have Hsf := fconnect_sym inj_skip.
pose a := fconnect f z.
have Ha: fclosed f (setC a) by apply setC_closed; apply: connect_closed.
have Haf: fun_adjunction to_g f skip (setC a).
  apply: (strict_adjunction Hsf Ha to_g_inj).
  apply/subsetP => [x Hax]; case Hx: (z =d x).
    by rewrite -(eqP Hx) /setC /(a) connect0 in Hax.
    exact (codom_f _ (to_d' (negbI Hx))).
  move=> u v Hu; apply: base_skip; apply/eqP => /= Du.
  by rewrite -Du /setC /(a) fconnect_finv in Hu.
rewrite (n_compC a) (n_compC (preimage to_g a)) {3}/a (n_comp_connect Hfg).
rewrite (adjunction_n_comp _ Hfg Hsf Ha Haf) addnA; congr addn.
case Hfz: (z =d f z).
  apply: eqP; apply/set0P => [[x Hx]]; apply/andP => [[_ Hzx]].
  rewrite /preimage /= in Hzx; case/eqP: Hx; move/connectP: Hzx => [p Hp <-] {x}.
  elim: p (z) (eqP Hfz) Hp => [|y p Hrec] x //= Dx; case/andP; case/eqP=> <-.
  rewrite -(Dx); exact: Hrec Dx.
apply: etrans (n_comp_connect Hsf (to_d' (negbI Hfz))); apply: eq_n_comp_r.
move=> u; apply/idP/idP => Hu.
  rewrite /preimage /a Hfg in Hu; move/connectP: Hu => [p Hp Dz].
  rewrite Hsf; elim: p u Hp Dz => [|x p Hrec] u /=.
    by move=> _ Dz; case/eqP: (z_to_g u); rewrite -Dz.
  case/andP; move/eqP=> Hx Hp Dz; case Hv: (z =d x).
    by apply connect1; rewrite /eqdf /eqd /= /skip1 Hx eqd_sym Hv set11.
  apply: (connect_trans (connect1 _) (Hrec (to_d' (negbI Hv)) Hp Dz)).
  by rewrite /eqdf /eqd /= /skip1 Hx eqd_sym Hv set11.
rewrite Hsf in Hu; move/connectP: Hu => [p Hp Dfz].
elim: p u Hp Dfz => [|v p Hrec] u /=.
  by move=> _ Du; rewrite Du /preimage /= /a fconnect1.
move/andP=> [Huv Hp] Dfz; move: u Huv => [x Hx].
rewrite /eqdf /eqd /= -/to_g /skip1.
case: (z =P f x) => [Dz|_] Dfx.
  by rewrite /preimage /a /= Dz Hfg fconnect1.
by apply: (connect_trans (Hrec _ Hp Dfz)); rewrite Hfg; apply connect1.
Qed.

End Skip.

Definition skip_edge1 x :=
  if z =d edge z then edge x else
  if z =d face (edge x) then edge z else
  if z =d edge x then edge (node z) else edge x.

Lemma skip_edgeP : forall u, setC1 z (skip_edge1 (to_g u)).
Proof.
move=> [x Hx]; rewrite /= /skip_edge1 /setC1; case Hez: (z =d edge z).
  by rewrite (eqP Hez) (inj_eqd (Iedge g)).
  case Hfex: (z =d face (edge x)); first by rewrite Hez.
  case Hex: (z =d edge x); last by rewrite Hex.
by rewrite -(inj_eqd (Iface g)) {1}(eqP Hex) Enode eqd_sym Hfex.
Qed.

Definition skip_edge u := to_d' (skip_edgeP u).

Lemma Eskip : monic3 skip_edge (skip (Inode g)) (skip (Iface g)).
Proof.
move=> [x Hx]; apply: to_g_inj; rewrite /= /skip_edge1 /skip1.
case Hez: (z =d edge z).
  case: (z =P face (edge x)) => [Dz|_]; last by rewrite Eedge (negbE Hx).
  by rewrite {2}(eqP Hez) Eedge set11 Dz Eedge.
case Hfex: (z =d face (edge x)).
  rewrite {2 6}(eqP Hfex) (inj_eqd (Iface g)) (inj_eqd (Iedge g)).
  by rewrite (eqd_sym x) (negbE Hx) !Eedge set11.
case Hex: (z =d edge x); last by rewrite Hfex Eedge (negbE Hx).
by rewrite Enode set11 {2 4}(eqP Hex) Eedge (negbE Hx).
Qed.

Definition walkupE := Hypermap Eskip.

Notation Local g' := walkupE.

Notation Local "'@' 'g'' H" := ((to_d' H) : g') (at level 10, H at level 8).
Notation Local "'@' 'g'" := (to_g : g' -> g) (at level 10).

Definition walkupI u x := if subdIopt (setC1 z) x is Some v then v : g' else u.

Lemma walkupI_eq : forall u x, @g (walkupI u x) = (if z =d x then @g u else x).
Proof.
move=> u x; rewrite /walkupI; case: (subdIoptP (setC1 z) x) => [v Hx Dv|Hx].
  by rewrite (negbE Hx).
by rewrite (negbE2 Hx).
Qed.

Lemma walkup_seq : forall p : seq g, setC p z -> {q : seq g' | p = maps (@g) q}.
Proof.
elim=> [|x p Hrec]; [ by exists (Seq0 walkupE) | rewrite /= /setU1 ].
move/norP=> [Hx Hp]; rewrite eqd_sym in Hx.
by case: (Hrec Hp) => [q Dp]; exists (Adds (@g' Hx) q); rewrite Dp.
Qed.

Lemma not_glink_fp : negb (glink z z) ->
  and3 ((z =d edge z) = false) ((z =d node z) = false) ((z =d face z) = false).
Proof.
case/norP; move=> Hez; move/norP=> [Hnz Hfz].
by split; rewrite eqd_sym; apply negbE.
Qed.

Lemma base_skip_edge : fun_base (@g) edge edge (seq2 (node (face z)) (node z)).
Proof.
move=> [x Hx] [y Hy]; rewrite /setC mem_seq2 /eqdf {2}/eqd /=.
move/norP=> [Hex Hfex] .
rewrite (monic2F_eqd (monicF_sym (Eedge g))) in Hex.
rewrite (monic2F_eqd (Enode g)) in Hfex.
by rewrite /skip_edge1 (negbE Hex) (negbE Hfex) if_same eqd_sym.
Qed.

Lemma glink_fp_skip_edge : glink z z -> skip_edge =1 skip (Iedge g).
Proof.
move=> H [x Hx]; apply: to_g_inj; move: H.
rewrite /glink /relU /setU /eqdf /= /skip1 /skip_edge1 eqd_sym.
case: (z =P edge z) => [Dz|_].
  by clear; rewrite Dz (inj_eqd (Iedge g)) (negbE Hx).
case: (node z =P z) => [Dnz|_] Dfz.
  by rewrite -(monic2F_eqd (Enode g)) Dnz (negbE Hx).
by rewrite -{1}(eqP Dfz) (inj_eqd (Iface g)); case (eqd z (edge x)).
Qed.

Definition cross_edge := cedge z (node z).

Let z_comp := closure clink (preimage (@g) (clink z)).

Let z_barb := subset (clink z) (set1 z).

Remark z_barb_z : z_barb = and3b (z =d edge z) (z =d node z) (z =d face z).
Proof.
apply/subsetP/and3P => [Hbz|[_ Hnz Hfz] x].
  have Hfz := Hbz _ (clinkF _); rewrite -{1}[z]Eedge in Hbz.
  have Hfez := Hbz _ (clinkN _); split; auto.
    by rewrite -(inj_eqd (Iface g)) -(eqP Hfz).
  by rewrite {2}(eqP Hfez) Eedge set11.
rewrite /clink /relU /setU /eqdf.
by rewrite {1}(eqP Hnz) (finv_f (Inode g)) -(eqP Hfz) orbb.
Qed.

Remark clink_at_g' : forall u v, clink (@g u) (@g v) -> clink u v.
Proof.
move=> [x Hx] [y Hy] /= Hxy; apply/clinkP; case/clinkP: Hxy => [Dx|Dy].
  by left; apply to_g_inj; rewrite /= /skip1 -Dx (negbE Hx).
by right; apply to_g_inj; rewrite /= /skip1 Dy (negbE Hy).
Qed.

Remark clink_at_g : forall u v, connect clink u v -> connect clink (@g u) (@g v).
Proof.
move=> u v; move/connectP=> [p Hp <-] {v}.
elim: p u Hp => [|v p Hrec] u /=; first by rewrite connect0.
move/andP=> [Hu Hp]; apply: (connect_trans _ (Hrec _ Hp)).
(case/clinkP: Hu; move/(congr1 to_g); rewrite /= /skip1) => [->|<-].
  case Hnv: (z =d node (@g v)); last by exact (connect1 (clinkN _)).
  apply: (connect_trans (connect1 (clinkN _))).
  rewrite {1}(eqP Hnv); exact (connect1 (clinkN _)).
case: (z =P face (@g u)) => [Dz|_];
 apply: (connect_trans (connect1 (clinkF _))); last by apply: connect0.
rewrite Dz; exact (connect1 (clinkF _)).
Qed.

Remark z_comp_preimage : z_comp =1 preimage (@g) (connect clink z).
Proof.
move=> v; apply/set0Pn/idP.
  case; move=> u; case/andP; rewrite /preimage Sclink; move=> Huv Hu.
  exact (connect_trans (connect1 Hu) (clink_at_g Huv)).
case/connectP=> p0; case/shortenP=> [] [|x p] /= Hp Up _ Dv {p0}.
  by case/eqP: (z_to_g v); rewrite -Dv.
move/andP: Hp => [Hu Hp]; case/andP: Up; rewrite -mem_adds.
case/walkup_seq; case=> [|x' p'] //= [Dx Dp] _.
exists x'; rewrite /setI /preimage /= -(Dx) Hu andbT.
apply: (etrans (Sclink walkupE _ _)); apply/connectP.
exists p'; last by rewrite Dx Dp last_maps in Dv; exact (to_g_inj Dv).
apply/(pathP x') => [i Hi]; apply clink_at_g'.
rewrite -!(sub_maps x' x) //; last by exact (leqW Hi).
rewrite {1}[sub]lock /= -Dx -Dp -lock.
by apply: ((pathP _) Hp); rewrite Dp size_maps.
Qed.

Remark z_barb_comp : z_barb = (n_comp clink z_comp =d 0).
Proof.
apply/subsetP/set0P => [Hbz u|Hcz x Hx].
  apply/andP; case; clear; case/set0Pn; move=> [x Hx]; move/andP=> [_ Hzx].
  by rewrite /preimage /= in Hzx; rewrite /setC1 (Hbz _ Hzx) in Hx.
apply/idPn => [Hv]; pose v := @g' Hv; pose u := root clink v.
case/idP: (Hcz u); rewrite /setI {1}/u (roots_root (Sclink walkupE)).
by apply/set0Pn; exists v; rewrite /setI Sclink /u connect_root.
Qed.

Let disconnected := 1 < n_comp clink z_comp.

Let n_comp_z disc := if glink z z then S z_barb else negb disc : nat.

Remark not_cross_edge_walkup : negb cross_edge -> forall u v,
 @g u = edge z -> @g v = node (face z) -> cedge u v.
Proof.
move=> Hznz u v Du Dv; case Hez: (z =d edge z).
  by case: u Du => [ez Hez'] Dez; rewrite -Dez /= (negbE Hez') in Hez.
  case/connectP: (etrans (Sedge g _ _) (fconnect1 _ z)).
move=> p0; case/shortenP=> [p Hp Up _ {p0}] Dz.
elim/last_ind: p Dz Up Hp => [|p z'] Dz; first by case/eqP: Hez.
rewrite last_add_last -cats1 -cat_adds uniq_cat path_cat /= !andbT orbF.
move=> Dz'; rewrite {z'}Dz' /setU1 eqd_sym Hez /= -uniq_adds.
rewrite {2}/eqdf (monic2F_eqd (Eedge g)) -Dv -Du.
move/andP=> [Up Hpz]; move/andP=> [Hp Ev].
case: {Hpz}(walkup_seq Hpz) => [p' Dp]; apply/connectP.
exists p'; last by rewrite Dp last_maps in Ev; exact (to_g_inj (eqP Ev)).
rewrite -(@path_maps g _ _ _ _ _ _ _ base_skip_edge); first by rewrite Dp in Hp.
simpl in Dp; rewrite -has_maps has_sym -belast_maps /= -Dp orbF -Dv.
apply/orP => [[Hpv|Hpnz]].
  by rewrite lastI (eqP Ev) -cats1 uniq_cat /= Hpv andbC in Up.
  case: (negP Hznz); apply: (connect_trans (fconnect1 edge z)).
rewrite -Du; exact (path_connect Hp (mem_belast Hpnz)).
Qed.

Remark disconnected_cross_edge : disconnected -> negb (glink z z) /\ cross_edge.
Proof.
move=> Hdz; apply: andP; apply/idPn => [Hgze].
have Huw: forall u w, node (@g u) = z -> face z = @g w -> connect clink u w.
  move=> u w Du Dw; case Hez: (z =d edge z).
    apply eq_connect0; apply to_g_inj; apply Inode.
    by rewrite -Dw (eqP Hez) Eedge.
  case Hnz: (z =d node z).
    by rewrite -{1}Du (inj_eqd (Inode g)) eqd_sym z_to_g in Hnz.
  case Hfz: (z =d face z); first by rewrite Dw z_to_g in Hfz.
  rewrite /glink /relU /setU /eqdf -!(eqd_sym z) Hez Hnz Hfz /= in Hgze.
  apply: (connect_trans _ (connect1 (clinkN _))).
  pose v := @g' (negbI Hez); apply connect_trans with v.
    rewrite Sclink; apply connect1; apply/clinkP; right.
    apply to_g_inj; apply Inode; rewrite /= /skip1 -(monic2F_eqd (Enode g)).
    by rewrite eqd_sym Hnz Eedge.
  rewrite clink_glink.
  apply: (connect_sub (fun _ _ H => connect1 (sub_relUl _ H))).
  apply (not_cross_edge_walkup Hgze); [ done | rewrite /= -Dw /skip1 ].
  by rewrite -(monic2F_eqd (Eedge g)) eqd_sym Hez.
rewrite /disconnected ltnNge leq_eqVlt ltnS leqn0 -z_barb_comp orbC in Hdz.
case/idP: Hdz {Hgze}; case Hbz: z_barb; [ done | apply/eqP ].
case/set0Pn: Hbz => [x]; move/andP=> [Hzx Hx]; set u := @g' Hx.
rewrite -(@eq_n_comp_r _ (closure clink (set2 u u))).
  by rewrite (n_comp_closure2 (Sclink walkupE)) connect0.
move=> v; apply/set0Pn/set0Pn; case=> [w]; move/andP=> [Hvw Dw].
  exists w; rewrite /set2 orbb in Dw.
  by rewrite /setI Hvw /preimage -((u =P w) Dw).
exists u; rewrite /setI /set2 orbb set11 andbT; apply: (connect_trans Hvw).
case/clinkP: Dw; case/clinkP: Hzx; move=> Dx Dw; auto.
- by apply eq_connect0; apply to_g_inj; apply Inode; rewrite -Dw.
- by rewrite Sclink; auto.
by apply eq_connect0; apply to_g_inj; rewrite -Dw.
Qed.

Let ae x := has (cedge x) (seq2 z (node z)).

Remark Hae : fclosed edge (setC ae).
Proof. by move=> x y; move/eqP=> <-; rewrite /setC /ae /= -!cedge1. Qed.

Remark adj_ae : fun_adjunction (@g) edge edge (setC ae).
Proof.
apply: (strict_adjunction (Sedge walkupE) Hae to_g_inj).
  apply/subsetP => x Haex.
  case Hx: (z =d x); last by exact (codom_f _ (@g' (negbI Hx))).
  by rewrite -(eqP Hx) /setC /ae /= connect0 in Haex.
move=> [x Hx] [y Hy]; move/negbE2=> Haex; apply: {y Hy}base_skip_edge.
rewrite /setC mem_seq2 /=; apply/orP=> [Dx]; case/orP: Haex.
rewrite /seq1 /=; case: Dx; move/eqP=> <- {x Hx}.
  by left; rewrite cedge1 Eface connect0.
by right; rewrite connect0.
Qed.

Lemma same_cskip_edge : forall u, negb (ae (@g u)) ->
  forall v, cedge u v = cedge (@g u) (@g v).
Proof. by case adj_ae; auto. Qed.

Lemma sub_cskip_edge : negb cross_edge -> forall u v,
  cedge (@g u) (@g v) -> cedge u v.
Proof.
move=> Hz u v Huv; case Hez: (z =d edge z).
  apply: (etrans (eq_fconnect (glink_fp_skip_edge _) _ _)).
    by apply/orP; left; rewrite eqd_sym in Hez.
  by rewrite fconnect_skip.
case/connectP: Huv => [p].
elim: {p}(S (size p)) {-2}p u (ltnSn (size p)) => [|n Hrec] //.
move=> [|y p] u /= Hn; first by move=> *; apply eq_connect0; apply to_g_inj.
 move/andP=> [Dy Hp] Ep; case Hy: (z =d y).
  case: p => [|ez p] /= in Hn Hp Ep |- *; first by rewrite Ep z_to_g in Hy.
  case/andP: Hp => [Dez Hp].
  have Eu: @g u = node (face z) by rewrite (eqP Hy) -(eqP Dy) Eedge.
  have Eu': @g (@g' (negbI Hez)) = edge z by done.
  rewrite -(same_cedge (not_cross_edge_walkup Hz Eu' Eu)).
  move: Hp Ep; rewrite -(eqP Dez) -(eqP Hy) -{1 2}Eu'.
  exact: Hrec (ltnW Hn).
apply: connect_trans (Hrec _ (@g' (negbI Hy)) Hn Hp Ep).
case Hfy: (z =d face y).
  have Eeu: @g (edge u) = edge z by rewrite /= /skip_edge1 Hez (eqP Dy) Hfy.
  have Hnfz: (negb (z =d node (face z))).
    by rewrite -(monic2F_eqd (Eedge g)) eqd_sym Hez.
  rewrite cedge1; pose u' := @g' Hnfz.
  apply: (connect_trans (@not_cross_edge_walkup _ _ u' _ _)); auto.
  apply: connect1; rewrite /eqdf /eqd /= /skip_edge1 Hez Eface set11.
  by rewrite {1 4}(eqP Hfy) Eface (inj_eqd (Iface g)) (eqd_sym y) Hy set11.
by apply connect1; rewrite /eqdf /eqd /= /skip_edge1 Hez (eqP Dy) Hfy Hy set11.
Qed.

Lemma cskip_edge_merge : negb cross_edge ->
  forall u v, ae (@g u) -> cedge u v = ae (@g v).
Proof.
move=> Hz u v Hu; apply/idP/idP => [Huv|].
  apply/idPn => [Hv]; case/idPn: Hu.
  rewrite Sedge (same_cskip_edge Hv) Sedge in Huv.
  exact (etrans (closed_connect Hae Huv) Hv).
move: Hu; rewrite /ae /= !orbF.
case Hez: (z =d (edge z)).
  have Hzz: fcycle edge (seq1 z) by rewrite /= /eqdf eqd_sym Hez.
  rewrite -!(Sedge g z) !(fconnect_cycle Hzz (setU11 _ _)) /= /setU1 !z_to_g.
  by move=> Hu Hv; apply (sub_cskip_edge Hz); rewrite (same_cedge Hu) Sedge.
have Hnfz := Hez; rewrite eqd_sym (monic2F_eqd (Eedge g)) in Hnfz.
pose uez := @g' (negbI Hez); pose unfz := @g' (negbI Hnfz).
have Henz := (@not_cross_edge_walkup Hz uez unfz (erefl _) (erefl _)).
rewrite cedge1r in Henz; have Eenz: @g (edge unfz) = edge (node z).
  rewrite /= /skip_edge1 Hez Eface set11.
  case: (z =P face z) => [Dfz|_] //; case/idP: Hz.
  by rewrite /cross_edge -{1}[z]Eface -Dfz Sedge fconnect1.
case/orP=> [Hu|Hu]; case/orP=> [Hv|Hv];
 try  by apply (sub_cskip_edge Hz); rewrite (same_cedge Hu) Sedge.
  apply: (connect_trans _ (connect_trans Henz _)); apply (sub_cskip_edge Hz).
    by rewrite /= -cedge1r.
  by rewrite Eenz -cedge1 Sedge.
rewrite Sedge in Henz.
apply: (connect_trans _ (connect_trans Henz _)); apply (sub_cskip_edge Hz).
  by rewrite Eenz -cedge1r.
by rewrite /= -cedge1 Sedge.
Qed.

Remark fcard_skip_edge :
  let Sez := if glink z z then S (z =d edge z) else double (negb cross_edge) in
  Sez + (fcard edge g') = S (fcard edge g).
Proof.
case Hgzz: (glink z z).
  congr S; rewrite -(fcard_skip (Iedge g)); NatCongr; apply: eq_fcard.
  exact (glink_fp_skip_edge Hgzz).
case: {Hgzz}(not_glink_fp (negbI Hgzz)) => [Hez Hnz Hfz].
have Hnfz := Hez; rewrite eqd_sym (monic2F_eqd (Eedge g)) in Hnfz.
pose unfz := @g' (negbI Hnfz); pose unz := @g' (negbI Hnz).
have Heg := Sedge g; have Heg' := (Sedge g').
rewrite (n_compC ae) (n_compC (preimage (@g) ae)).
rewrite (adjunction_n_comp _ Heg Heg' Hae adj_ae) -addSn !addnA; congr addn.
have Eae: ae =1 fclosure edge (set2 z (node z)).
  move=> x; rewrite /ae /= orbF; apply/orP/set0Pn; case.
  - by exists z; rewrite /setI /set2 set11 /= andbT.
  - by exists (node z); rewrite /setI /set2 set11 orbT andbT.
  move=> y; case/andP=> [Hxy].
  by case/orP; move/eqP=> Dy; rewrite -Dy in Hxy; auto.
rewrite (eq_n_comp_r Eae) (n_comp_closure2 Heg).
have Hag': preimage (@g) ae =1 fclosure edge (set2 unfz unz).
  move=> u; rewrite /preimage /ae /= orbF; apply/idP/set0Pn => [Hu|[v Hv]].
    have [y Huy Hy]: exists2 y, cedge (@g u) y & set2 (@g unfz) (@g unz) y.
      rewrite /set2 /=; case/orP: Hu.
        by exists (node (face z)); [ rewrite cedge1r Eface | rewrite set11 ].
      by exists (node z); last by rewrite set11 orbT.
    move/connectP: Huy Hy {Hu} => [p Hp <-] {y}.
    elim: p u Hp => [|y p Hrec] u /=; first by exists u; rewrite /setI connect0.
    move/andP=> [Dy Hp]; case Hex: (z =d edge (@g u)).
      exists u; rewrite /setI connect0 /set2 /eqd /= {1}(eqP Hex) Eedge.
      by rewrite /to_g set11.
    case Hfex: (z =d face (edge (@g u))).
      exists u; rewrite /setI connect0 /set2 /eqd /= {3}(eqP Hfex) Eedge.
      by rewrite /to_g set11 orbT.
    have Hu': setC1 z y by rewrite /setC1 -(eqP Dy) Hex.
    case/(Hrec (@g' Hu') Hp) {Hrec} => v; move/andP=> [Hu'v Dv].
    exists v; simpl in Dv; rewrite /setI Dv andbT.
    apply: (connect_trans (connect1 _) Hu'v).
    by rewrite /eqdf /eqd /= /skip_edge1 Hez -/to_g Hex Hfex.
  case/andP: Hv; move/connectP=> [p Hp <-] {v}.
  elim: p u Hp => [|v p Hrec] [x Hx] /=.
    rewrite {1}/set2 /eqd /=; clear; case/orP; move/eqP=> Dx.
      by rewrite -Dx cedge1 Eface connect0.
    by rewrite Dx connect0 orbT.
  move=> H Ep; case/andP: H; rewrite {1}/eqdf /eqd /= /skip_edge1 Hez.
  case Hex: (z =d edge x); first by do 2 clear; rewrite (eqP Hex) fconnect1.
  case Hfex: (z =d face (edge x)).
    by do 2 clear; rewrite (eqP Hfex) Eedge connect0 orbT.
  move=> Dex Hp; rewrite !(cedge1 x) (eqP Dex); exact (Hrec _ Hp Ep).
rewrite (eq_n_comp_r Hag') (n_comp_closure2 Heg') -/cross_edge.
case Hznz: cross_edge; rewrite /cross_edge in Hznz.
  rewrite -{1}[z]Eface -cedge1 in Hznz; case/connectP: Hznz => q.
  case/shortenP=> [[|z' p] Hp Up _ {q}] /= Dnfz.
    by rewrite (Inode _ Dnfz) set11 in Hfz.
  rewrite /= {1}/eqdf Eface in Hp; case/andP: Hp => Dz'.
  move/eqP: Dz' Up Dnfz => <- {z'} /=; case/and3P.
  move/norP=> [_ Hpnfz] Hpz Up Dnz Hp.
  case: (walkup_seq Hpz) => [[|uez p'] Dp]; simpl in Dp.
    by rewrite Dp in Dnz; case/eqP: (Hnz).
  rewrite Dp /= in Hp; move/andP: Hp => [Dez Hp].
  have Hunz: eqdf edge unz uez.
    by rewrite /eqdf /eqd /= -/to_g /skip_edge1 -(eqP Dez) Hez Enode !set11.
  have Dunz: unz = last uez p'.
    by apply: to_g_inj; rewrite -last_maps /= -Dnz Dp.
  have Hp': fcycle edge (Adds uez p').
    simpl in Dunz, Hunz, Dp; rewrite /= -cats1 path_cat -Dunz /= Hunz andbT.
    rewrite -(path_maps (d := g) base_skip_edge) //.
    rewrite -has_maps -belast_maps has_sym /= orbF.
    rewrite -Dnz Dp /=; apply/orP => [[Hp'nfz|Hp'nz]].
      case (negP Hpnfz); rewrite Dp; exact (mem_belast Hp'nfz).
    by rewrite Dp lastI -cats1 uniq_cat /= Hp'nz /= andbF in Up.
  rewrite Heg' (fconnect_cycle Hp'); last by rewrite Dunz mem_last.
  by rewrite Dp /= in Hpnfz; rewrite -(mem_maps to_g_inj) /= Hpnfz.
have Hw: cedge unfz unz; last by rewrite Hw.
rewrite Heg' cedge1; apply: (not_cross_edge_walkup (negbI Hznz)); last done.
by rewrite /= /skip_edge1 Hez Enode set11.
Qed.

Lemma base_clink_walkup :
  rel_base (@g) clink clink (seq2 (edge (node z)) (node z)).
Proof.
move=> [x Hx] [y Hy]; rewrite /setC mem_seq2 /=; move/norP=> [Hex Hfex].
rewrite /clink /relU /setU /eqdf !(monic2F_eqd (f_finv (Inode _))) /=.
rewrite {3 4}/eqd /= /skip1 -(monic2F_eqd (monicF_sym (Eface g))) (negbE Hex).
by case: (z =P node y) => [<-|_] //; rewrite !(eqd_sym x) (negbE Hfex) (negbE Hx).
Qed.

Lemma card_walkup : card g' = pred (card g).
Proof. exact (etrans (card_sub_dom _) (cardC1 z)). Qed.

Lemma card_S_walkup : card g = S (card g').
Proof. by rewrite card_walkup (cardD1 z). Qed.

Remark n_comp_glink_walkup :
  n_comp_z disconnected + n_comp glink g' = S (n_comp glink g).
Proof.
have Hsg := (Sclink g); have Hsg' := (Sclink g').
pose a := connect clink z.
have Ha: closed clink (setC a) by apply: setC_closed; apply: connect_closed.
have Haa: rel_adjunction (@g) clink clink (setC a).
  apply (strict_adjunction Hsg' Ha to_g_inj).
    apply/subsetP => [x Hax]; case Hx: (z =d x).
      by rewrite /setC /a -(eqP Hx) connect0 in Hax.
    exact (codom_f (@g) (@g' (negbI Hx))).
  move=> [x Hx] v; move/negbE2=> Hax; simpl in Hax; apply: {v}base_clink_walkup.
  rewrite /setC mem_seq2 /= {Hx}; apply/orP => Dx; case/idP: Hax.
  case: Dx; case/eqP=> <- {x}; rewrite /a Hsg.
    rewrite -{2}[z]Enode; apply connect1; apply clinkF.
  apply connect1; apply clinkN.
rewrite -2!(eq_n_comp (@clink_glink _)) (n_compC (preimage (@g) a)).
rewrite (n_compC a) (adjunction_n_comp _ Hsg Hsg' Ha Haa) !addnA -addSn.
congr addn; rewrite /a (n_comp_connect Hsg) -(eq_n_comp_r z_comp_preimage).
rewrite /n_comp_z; case Hdz: disconnected.
case: (disconnected_cross_edge Hdz) => [Hgzz _]; rewrite (negbE Hgzz).
case: (not_glink_fp Hgzz) => [_ Hfez Hfz].
  rewrite eqd_sym (monic2F_eqd (Enode g)) in Hfez.
  apply: eqP; rewrite /= add0n eqn_leq; apply/andP; split; last by exact Hdz.
  pose u := @g' (negbI Hfez); pose v := @g' (negbI Hfz).
  rewrite -(@eq_n_comp_r _ (closure clink (set2 u v))).
    by rewrite n_comp_closure2; case (connect clink u v).
  move=> w; rewrite /z_comp /closure !(disjoint_sym (connect clink w)).
  congr negb; apply: {w}eq_disjoint => w; apply/orP/clinkP.
    by move=> [Dw|Dw]; [ left | right ]; rewrite -((_ =P w) Dw) /= ?Eedge.
  rewrite /eqd /= -/to_g.
  by move=> [Dz|<-]; [ left; rewrite Dz | right ]; rewrite ?Enode set11.
move: (negbI Hdz); rewrite /disconnected -leqNgt leq_eqVlt ltnS leqn0.
rewrite -z_barb_comp orbC; case Hbz: z_barb.
have Hez: z =d edge z by rewrite z_barb_z in Hbz; case (andP Hbz).
rewrite {2}(eqP Hez) glinkE; rewrite z_barb_comp in Hbz.
  by rewrite (eqP Hbz).
by simpl; move/eqP=> ->; rewrite if_same.
Qed.

Remark genus_lhs_walkupE :
  double (n_comp_z disconnected) + genus_lhs g' = S (genus_lhs g).
Proof.
rewrite /genus_lhs card_walkup addnA -double_add n_comp_glink_walkup.
by rewrite (cardD1 z) addnCA.
Qed.

Remark genus_rhs_walkupE :
  double (n_comp_z cross_edge) + genus_rhs g' = S (genus_rhs g).
Proof.
rewrite /genus_rhs -(fcard_skip (Inode g)) -(fcard_skip (Iface g)).
rewrite -addSn -fcard_skip_edge addnC -!addnA; symmetry.
do 3 (rewrite addnC -!addnA; congr addn).
rewrite /n_comp_z /glink /relU /setU /eqdf -!(eqd_sym z) z_barb_z.
case Hnz: (z =d node z).
  rewrite -(eqd_sym (face z)) (monic2F_eqd (Eface g)) -(eqP Hnz).
  by case (z =d edge z).
case Hfz: (z =d face z); last by case (z =d edge z).
by rewrite -(eqd_sym (edge z)) (monic2F_eqd (Eedge g)) -(eqP Hfz) Hnz.
Qed.

Lemma genus_walkupE_eq : glink z z \/ negb cross_edge -> genus g' = genus g.
Proof.
rewrite {2}/genus -subSS -genus_lhs_walkupE -genus_rhs_walkupE /n_comp_z.
move=> [Hgzz|Hznz]; first by rewrite Hgzz subn_add2l.
case Hdz: disconnected; last by rewrite Hznz /= subn_add2l.
by case (negP Hznz); case: (disconnected_cross_edge Hdz).
Qed.

Lemma le_genus_walkup : genus g' <= genus g.
Proof.
rewrite {2}/genus -subSS -genus_lhs_walkupE -genus_rhs_walkupE /n_comp_z.
case Hgzz: (glink z z); first by rewrite subn_add2l; exact (leqnn _).
case Hdz: disconnected.
  case: (disconnected_cross_edge Hdz) => _ ->; rewrite subn_add2l; exact: leqnn.
case cross_edge; last by rewrite subn_add2l; exact: leqnn.
apply: half_leq; apply: leq_sub2r; apply leq_addl.
Qed.

Lemma planar_walkupE : planar g -> planar walkupE.
Proof. rewrite /planar -!leqn0; exact (leq_trans le_genus_walkup). Qed.

Lemma even_genus_walkup : even_genus walkupE -> even_genus g.
Proof.
move=> Elhs; apply: eq_add_S; rewrite /genus -subSS -genus_lhs_walkupE Elhs.
rewrite -addnS -genus_rhs_walkupE !addnA subn_add2r -double_add -double_sub.
rewrite half_double -double_add -(addnC (n_comp_z cross_edge)) leq_add_sub //.
apply: (leq_trans _ (leq_addr _ _)); rewrite /n_comp_z.
case (glink z z); first exact: leqnn.
case Hdz: disconnected; last by case cross_edge.
by case: (disconnected_cross_edge Hdz) => [_ Hznz]; rewrite Hznz.
Qed.

Definition skip_clink : rel g :=
  fun x y => (x =d skip1 node y) || (skip1 face x =d y).

Lemma skip_clink_walkup : forall x' p',
  path clink x' p' = path skip_clink (@g x') (maps (@g) p').
Proof.
move=> x' p'; elim: p' x' => [|y' p' Hrec] x' //=; rewrite {}Hrec.
by congr andb; congr orb; rewrite /eqdf (monic2F_eqd (f_finv (Inode walkupE))).
Qed.

Lemma skip_clinkf : forall x y, skip_clink x y -> negb (x =d node z) ->
 clink x y \/ face x = z /\ face z = y.
Proof.
move=> x y Hxy' Hxnz; case: {Hxy'}(orP Hxy'); rewrite /skip1.
  case (z =d node y); move=> Dx; first by rewrite Dx in Hxnz.
  by left; rewrite (eqP Dx) clinkN.
case: (z =P face x) => [Dfx|_] Dfy.
  by right; split; last by exact (eqP Dfy).
by left; rewrite -(eqP Dfy) clinkF.
Qed.

Remark splice_face_clink : forall x p,
 path skip_clink x p -> uniq (Adds x p) -> negb (belast x p (node z)) ->
 path clink x p
  \/ (exists2 p1, path clink x p1 /\ face (last x p1) = z
                & exists2 p2, path clink (face z) p2
                            & cat p1 (Adds (face z) p2) = p).
Proof.
move=> x p /=; elim: p x => [|y p Hrec] x /=; first by left.
move/andP=> [Hxy' Hp']; move/andP=> [Hpx Up]; move/norP=> [Hxnz Hpnz].
case: {Hxy' Hxnz}(skip_clinkf Hxy' Hxnz) => [Hxy|[Dfx Dfz]].
case: {Hrec Hpnz}(Hrec _ Hp' Up Hpnz); first by left; rewrite Hxy.
  move=> [p1 [Hp1 Ep1] [p2 Hp2 Dp]]; right; exists (Adds y p1).
    by split; first by rewrite /= Hxy.
  by exists p2; last by rewrite /= Dp.
right; exists (Seq0 g); [ by split | exists p; rewrite Dfz //= ].
elim: p y Hp' Hpx Hpnz {Hrec Dfz Up} => [|y2 p Hrec] y1 //=.
move/andP=> [Hy' Hp']; move/norP=> [Hy1x Hpx]; move/norP=> [Hy1nz Hpnz].
case: (skip_clinkf Hy' Hy1nz) => [Hy|[Hy _]]; first by rewrite Hy /=; auto.
by case/eqP: Hy1x; apply Iface; rewrite Hy.
Qed.

Lemma jordan_walkupE : jordan g -> jordan g'.
Proof.
move=> Hj [|u pw] //; apply/and3P; rewrite skip_clink_walkup.
have Einng := (finv_f (Inode g)).
set x := @g u; set p' := maps (@g) pw.
pose y := @g (finv node (last u pw)); pose p := Adds x p'.
move=> [Hynu Upw Hpw]; have Hpz: negb (p z).
  by apply/(mapsPx _ (Adds _ _) _) => [[v _ Hv]]; case/eqP: (z_to_g v).
have Up: uniq p by rewrite -(uniq_maps to_g_inj) in Upw.
have Hynx: mem2 p' y (skip1 node x).
  by rewrite -(mem2_maps to_g_inj) in Hynu.
have Ep: skip1 node y = last x p'.
  rewrite /p' /x last_maps; exact (congr1 (@g) (f_finv (Inode _) (last u pw))).
case Hxy: (x =d y); first by rewrite /p (eqP Hxy) /= (mem2l Hynx) in Up.
have Hzy: (z =d y) = false by apply: z_to_g.
clearbody p' x y; move: {pw Upw Hynu}Ep Hynx; rewrite /skip1.
case Hpnz: (negb (p (node z))).
  case: (z =d node y); first by move=> Dnz; rewrite /p Dnz mem_last in Hpnz.
  case: (z =d node x) => [|] Ep Hynx.
    by rewrite /p /= (setU1r x (mem2r Hynx)) in Hpnz.
  case: {Hpw}(splice_face_clink Hpw Up).
  + by apply/idP => [Hnz]; case/idP: Hpnz; apply: mem_belast.
  + by move=> Hp; case/and3P: (Hj p); split; rewrite // -Ep Einng.
  move=> [p1' [Hp1 Ep1] [p2' Hp2 Dp']].
  move Dp1: (Adds x p1') => p1; move Dp2: (Adds (face z) p2') => p2.
  case/and3P: (Hj (Adds x (cat p1' (Adds z p2)))); split.
  + rewrite -Dp' last_cat /= in Ep; rewrite -Dp' Dp2 in Hynx.
    by rewrite last_cat -{2}Dp2 /= -Ep Einng; apply mem2_splice1.
  + move: Hpz Up; rewrite /p -Dp' -!cat_adds Dp1 Dp2 !uniq_cat mem_cat /=.
    by move/norP=> [Hp1z Hp2z]; rewrite negb_orb Hp1z Hp2z.
  by rewrite path_cat Hp1 -Dp2 /= -{1}Ep1 !clinkF.
move: Hpnz Up Hpz Hpw; rewrite {}/p; move/idP; case/splitPl: p' / => [p' q Ep].
rewrite -cat_adds uniq_cat mem_cat path_cat last_cat; move Dp: (Adds x p') => p.
move/and3P=> [Up Upq Uq]; move/norP=> [Hpz Hqz].
case Hqnz: (q (node z)).
  by case/hasP: Upq; exists (node z); last by rewrite -Dp -Ep mem_last.
move/andP=> [Hpw Hqw]; rewrite -Dp in Up.
case: {Hpw}(splice_face_clink Hpw Up).
- by rewrite lastI Ep -cats1 uniq_cat /= orbF in Up; case/and3P: Up.
- rewrite Dp in Up; case Dq: {-3}q Hqw => [|fez q'].
    move=> _ Hp; rewrite Dq cats0 Ep /=.
    case: (z =P node y) => [Dz|_]; last by move=> *; case/eqP: Hzy; apply Inode.
    clear; rewrite {1}Dz (inj_eqd (Inode g)) eqd_sym Hxy.
    move=> Hynx; case/and3P: (Hj (Adds x (add_last p' z))); split.
    + by rewrite last_add_last Dz Einng -cats1 mem2_cat Hynx.
    + by rewrite -cats1 -cat_adds Dp uniq_cat Up /= orbF Hpz.
    by rewrite -cats1 path_cat Ep Hp /= clinkN.
  rewrite /= Ep; move/andP=> [Dfez Hqw] Hp.
  case Hzfez: (z =d fez); first by rewrite Dq (eqP Hzfez) /= setU11 in Hqz.
  case: (z =d node y) => [|] Eq; first by rewrite Dq Eq mem_last in Hqnz.
  rewrite Dq in Uq; case: {Hqw}(splice_face_clink Hqw Uq).
  + by apply/idP => H; case/idP: Hqnz; rewrite Dq mem_belast.
  + move=> Hq Hynx; rewrite -Dq in Uq; case Hzq: (clink z fez).
      case/and3P: (Hj (Adds x (cat p' (Adds z q)))); split.
      * rewrite last_cat {2}Dq /= -Eq Einng.
        case: (z =P node x) Hynx => [Dz|_] Hynx; last by apply mem2_splice1.
        rewrite (mem2r_cat Hqnz) in Hynx.
        by rewrite -Dz mem2_cat /= setU11 (mem2l Hynx) orbC.
      * by rewrite -cat_adds Dp uniq_cat Up /= negb_orb Upq Hpz Hqz.
      by rewrite path_cat Hp Dq /= Ep clinkN Hzq.
    case/orP: Dfez; rewrite /skip1.
      case: (z =P node fez) => [Dz|_] Dnz; first by rewrite Dz clinkN in Hzq.
      by rewrite (Inode g (eqP Dnz)) Dq /= setU11 in Hqz.
    case: (z =d face (node z)) => [|] Dfez.
      by rewrite -(eqP Dfez) clinkF in Hzq.
    case: (z =P node x) Hynx => [Dz|_] Hynx.
      case/and3P: (Hj (Adds z (Adds x (cat p' q)))); split.
      * by rewrite /= last_cat {2}Dq /= -Eq Einng mem2_adds Hxy.
      * rewrite -cat_adds Dp /= uniq_cat Up Upq mem_cat /setU negb_orb.
        by rewrite Hqz Hpz.
      rewrite Dq /= {1}Dz path_cat clinkN Hp Ep /=.
      by rewrite -{1}(eqP Dfez) clinkF.
    case/and3P: (Hj (Adds x (cat p' q))); split.
    * by rewrite last_cat {2}Dq /= -Eq Einng.
    * by rewrite -cat_adds Dp uniq_cat Up Upq.
    by rewrite path_cat Dq Hp Ep /= -{1}(eqP Dfez) clinkF.
  move=> [q1' [Hq1 Eq1] [q2' Hq2 Dq']].
  rewrite -Dq in Uq; case: q' / Dq' Dq Eq; rewrite last_cat /= -cat_adds.
  move Dq1: (Adds fez q1') => q1; move Dq2: (Adds (face z) q2') => q2 Dq Eq2.
  rewrite Dq mem_cat in Hqz; rewrite Dq uniq_cat in Uq.
  case/norP: Hqz => [Hq1z Hq2z]; case/and3P: Uq => [Uq1 Uq12 Uq2].
  rewrite Dq has_cat in Upq; case/norP: Upq => [Upq1 Upq2].
  case/orP: Dfez; rewrite Dq /skip1.
    case: (z =P node fez) {q Dq Hqnz} => [Dz|_] Dnz;
      last by rewrite (Inode g (eqP Dnz)) -Dq1 /= setU11 in Hq1z.
    case: (z =P node x) {Dnz} => [Dz'|_] Hynx.
      case/hasP: Upq1; exists fez; first by rewrite -Dq1 /= setU11.
      by rewrite Dz in Dz'; rewrite (Inode g Dz') -Dp /= setU11.
    case Hq1y: (q1 y).
      case/and3P: (Hj (Adds fez (cat q1' (Adds z q2)))); split.
      + rewrite last_cat -{2}Dq2 /= -Eq2 Einng -Dz.
        rewrite -Dq1 /= in Hq1y; case/orP: Hq1y.
        rewrite -(inj_eqd (Inode g)) Eq2 -Dz; move/eqP=> Eq2'.
        by rewrite Eq2' -Dq2 mem_last in Hq2z.
      + by move=> Hq1'y; rewrite mem2_cat Hq1'y /= setU11 /= orbT.
      + by rewrite -cat_adds Dq1 uniq_cat Uq1 /= negb_orb Hq1z Uq12 Hq2z.
      by rewrite path_cat Hq1 -Dq2 /= -{1}Eq1 !clinkF.
    case Hq1nx: (q1 (node x)).
      rewrite -Dq1 in Hq1nx; case/splitPl: {q1' Eq1}Hq1nx Dq1 Hq1 => [q3' q4 Eq3].
      rewrite -cat_adds; move Dq3: (Adds fez q3') => q3 Dq1.
      move: Uq12 Upq1 {Hq1y}(negbI Hq1y) Hq1z Hynx Uq1.
      rewrite -{q1}Dq1 has_sym !has_cat !mem_cat uniq_cat path_cat.
      move/norP=> [Uq23 _]; move/norP=> [Upq3 _]; move/norP=> [Hq3y _].
      move/norP=> [Hq3z _] Hynx; move/and3P=> [Uq3 Uq34 _]; move/andP=> [Hq3 _].
      case Hq423: (cat q4 q2 (last fez q3')).
        case (elimN (hasPx q3 (cat q4 q2))).
          by rewrite has_cat negb_orb Uq34 has_sym.
        by exists (last fez q3'); last by rewrite -Dq3 mem_last.
      rewrite -catA catA -Eq3 {q4 Hq423 Uq34}(mem2r_cat Hq423) in Hynx.
      case/and3P: (Hj (Adds fez (cat q3' (cat p (Adds z q2))))); split.
      + rewrite catA last_cat -{2}Dq2 /= -Eq2 Einng -Dz mem2_cat /=.
        apply/orP; right; move: (mem2l Hynx).
        rewrite !mem_cat /setU (negbE Hq3y) orbF orbC.
        by move=> Hpy; rewrite -Dp /= (setU1r x Hpy) setU11.
      + rewrite -cat_adds Dq3 !uniq_cat Uq3 Up has_cat /= !negb_orb Upq2.
        by rewrite !(has_sym q3) Upq3 Uq23 Hq3z Hpz Hq2z.
      by rewrite !path_cat Hq3 Eq3 -Dp -Dq2 /= Hp Ep !clinkN clinkF.
    case/and3P: (Hj (Adds x (cat p' (Adds z q2)))); split.
    + rewrite catA (mem2lr_splice Hq1y Hq1nx) in Hynx.
      by rewrite last_cat -{2}Dq2 /= -Eq2 Einng; apply mem2_splice1.
    + by rewrite -cat_adds Dp uniq_cat Up /= negb_orb Upq2 Hpz Hq2z.
    by rewrite path_cat Hp Ep -Dq2 /= clinkN clinkF.
  case: (z =P face (node z)) => [Dz|_] Dfnz Hynx.
    case/hasP: Upq1; exists (node z); last by rewrite -Ep -Dp mem_last.
    by rewrite Dz in Eq1; rewrite -(Iface g Eq1) -Dq1 mem_last.
  case/and3P: (Hj (Adds x (cat p' (cat q1 (Adds z q2))))); split.
  + rewrite catA last_cat -{2}Dq2 /= -Eq2 Einng.
    case: (z =P node x) Hynx => [Dz|_].
      rewrite -Dz -Dq (mem2r_cat Hqnz) mem2_cat /= setU11 orbC.
      by move=> Hpy; rewrite mem_cat /setU (mem2l Hpy).
    by rewrite catA; apply: mem2_splice1.
  + rewrite -cat_adds Dp !uniq_cat has_cat /= !negb_orb.
    by rewrite Up Upq1 Hpz Upq2 Uq1 Hq1z Uq12 Hq2z.
  by rewrite !path_cat Ep -Dq1 -Dq2 /= Hp Hq1 -{2}Eq1 -(eqP Dfnz) !clinkF.
move=> [p1' [Hp1 Ep1] [p2' Hp2 Dp']]; rewrite Dp in Up; rewrite Ep in Hqw.
case: p'/ Dp' Ep Dp; rewrite last_cat /= -cat_adds => Ep2.
move Dp1: (Adds x p1') => p1; move Dp2: (Adds (face z) p2') => p2 Dp.
rewrite -Dp uniq_cat in Up; case/and3P: Up => [Up1 Up12 Up2].
rewrite -Dp has_sym has_cat in Upq; case/norP: Upq => [Uqp1 Uqp2].
rewrite -Dp mem_cat in Hpz; case/norP: Hpz => [Hp1z Hp2z].
case Hp2nx: (setU1 z p2 (node x)).
  case/and3P: (Hj (Adds x (cat p1' (Adds z p2)))); split.
  - rewrite last_cat -{2}Dp2 /= Ep2 Einng mem2_cat mem2_adds set11 Hp2nx.
    by rewrite orbT.
  - by rewrite -cat_adds Dp1 uniq_cat /= negb_orb Up1 Hp1z Up12 Hp2z.
  by rewrite path_cat Hp1 -Dp2 /= -{1}Ep1 !clinkF.
case/norP: Hp2nx => [Hznx Hp2nx]; rewrite (negbE Hznx) Ep2.
case Dq: {1 2}q Hqw => [|fez q'] /=.
  rewrite Dq cats0 /=; case: (z =P node y) => [Dz|_] _;
    last by move=> Dy; case/eqP: Hzy; apply Inode.
  rewrite (mem2r_cat (negbE Hp2nx)); move=> _ Hynx.
  case/and3P: (Hj (Adds x (add_last p1' z))); split.
  - by rewrite last_add_last {2}Dz Einng -cats1 mem2_cat Hynx.
  - by rewrite -cats1 -cat_adds Dp1 uniq_cat /= Up1 orbF andbT.
  by rewrite -cats1 path_cat Hp1 /= -Ep1 clinkF.
case: (z =d (node y)); first by move=> _ Dnz; rewrite Dnz Dq mem_last in Hqnz.
move/andP=> [Dfez Hqw] Eq Hynx; have Uq' := Uq; rewrite Dq in Uq'.
case: {Hqw Uq'}(splice_face_clink Hqw Uq').
- by apply/idP => [Hnz]; case/idP: Hqnz; rewrite Dq mem_belast.
- case/orP: Dfez {Hqnz}; rewrite /skip1.
    case: (z =P node fez) => [Dz|_] Dnz;
      last by rewrite (Inode g (eqP Dnz)) Dq /= setU11 in Hqz.
    case Hp2y: (p2 y) {Dnz} => [|] Hq.
      case Hp1y: (p1' y) {Hp2nx}.
        by case/hasP: Up12; exists y; last by rewrite -Dp1 /= setU1r.
      rewrite -Dp2 in Hp2y.
      case/splitPl: {p2'}Hp2y Ep2 Dp2 Hp2 => [p3' p4' Ep3].
      rewrite last_cat -cat_adds lastI path_cat {}Ep3 cat_add_last.
      move: (belast (face z) p3') => p3; move Dp4: (Adds y p4') => p4 Ep4 Dp2.
      move/andP=> [_ {p3'} Hp4]; move: Up12 Uqp2 Up2 Hp2z.
      rewrite -Dp2 !has_cat uniq_cat mem_cat; move/norP=> [_ Up14].
      move/norP=> [_ Uqp4]; move/and3P=> [_ Up34 Up4]; move/norP=> [_ Hp4z].
      case Hp3y: (p3 y).
        by case/hasP: Up34; exists y; first by rewrite -Dp4 /= setU11.
      rewrite -Dp2 -catA (mem2l_cat Hp1y) -catA (mem2l_cat Hp3y) in Hynx.
      case/and3P: (Hj (Adds x (cat p1' (cat (Adds z q) p4)))); split.
      + rewrite !last_cat -{2}Dp4 /= Ep4 Einng mem2_cat mem2_adds set11.
        rewrite orbC /setU1 !orbA; apply/orP; right.
        by move: (mem2r Hynx); rewrite !mem_cat /setU orbC.
      + rewrite -cat_adds Dp1 uniq_cat Up1 /= uniq_cat has_cat Uq mem_cat.
        by rewrite /setU !negb_orb Hp1z Hqz Hp4z Uqp4 Up14 has_sym Uqp1.
      by rewrite !path_cat Hp1 Dq -Dp4 /= Hq -{1}Ep1 Dz -Eq !clinkN clinkF.
    rewrite (mem2lr_splice Hp2y (negbE Hp2nx)) in Hynx.
    case/and3P: (Hj (Adds x (cat p1' (Adds z q)))); split.
    + by rewrite last_cat {2}Dq /= -Eq Einng; apply mem2_splice1.
    + by rewrite -cat_adds Dp1 uniq_cat Up1 /= negb_orb Hp1z has_sym Uqp1 Hqz.
    by rewrite path_cat Hp1 Dq /= -{1}Ep1 clinkF Dz clinkN.
  case: (z =d face (node z)) => [|] Dfz Hq.
    case/hasP: Uqp2; exists fez; last by rewrite Dq /= setU11.
    by rewrite -(eqP Dfz) -Dp2 /= setU11.
  case/and3P: (Hj (Adds x (cat p1' (cat (Adds z p2) q)))); split.
  + by rewrite !last_cat {2}Dq /= -Eq Einng mem2_splice1 ?catA.
  + rewrite -cat_adds Dp1 uniq_cat Up1 /= has_cat uniq_cat Up2 mem_cat /setU.
    by rewrite !negb_orb Hp1z Up12 has_sym Uqp1 Hqz Hp2z has_sym Uqp2.
  by rewrite !path_cat Hp1 -Dp2 Dq /= Hp2 Hq -{1}Ep1 Ep2 -(eqP Dfz) !clinkF.
move=> [q1 _ [q2 _ Dq']]; case/hasP: Uqp2; exists (face z).
  by rewrite -Dp2 /= setU11.
by rewrite Dq -Dq' /= /setU1 mem_cat /setU /= setU11 !orbT.
Qed.

End Walkup.

Section WalkupAux.

Variables (g : hypermap) (z : g).

Definition walkupN : hypermap := permF (walkupE (z : permN g)).
Definition walkupF : hypermap := permN (walkupE (z : permF g)).

Lemma planar_walkupN : planar g -> planar walkupN.
Proof.
rewrite /walkupN /planar genus_permF -(genus_permN g); exact: planar_walkupE.
Qed.

Lemma planar_walkupF : planar g -> planar walkupF.
Proof.
rewrite /walkupF /planar genus_permN -(genus_permF g); exact: planar_walkupE.
Qed.

End WalkupAux.

Unset Implicit Arguments.
