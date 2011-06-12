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
Require Import jordan.

(* The geometrical interpretation of hypermaps, the definition of most of the *)
(* geometrical notions relevant to the statement and proof of the four color  *)
(* theorem :                                                                  *)
(*   - bridgeless and loopless maps.                                          *)
(*   - plain, precubic, cubic, quasicubic, and pentagonal maps.               *)
(*   - arities, simple paths, their bands and projections.                    *)
(*   - ring paths and adjacency.                                              *)
(* We also define a set of records that regroup various sets of geometrical   *)
(* properties of hypermaps, that are required at various points in the proof: *)
(*   - walkup jordan sew patch cube  no assumptions                           *)
(*   - snip                          planar                                   *)
(*   - revsnip                       planar, bridgeless, plain, connected     *)
(*   - proof induction               planar, bridgeless, plain, precubic (add *)
(*     (birkhoff contract embed)      cubic, pentagonal, connected later on)  *)
(*   - configuration (embed)         planar, bridgeless, plain, quasicubic,   *)
(*                                   connected, simple ring                   *)
(*   - kempe                         planar, plain, quasicubic, uniq ring     *)
(*   - quiz, quiztree                plain, cubic                             *)
(*   - quiz                          plain, quasicubic                        *)
(*   - part, redpart, hubcap         plain, cubic, pentagonal                 *)
(*   - discharge                     planar, plain, cubic, connected          *)
(* quiz and embed build and use an isomorphism from a configuration map to    *)
(* the coloring map, so they use two sets of assumptions.                     *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section BridgeAndLoopLess.

Variable g : hypermap.

Definition bridgelessb := set0b (fun x : g => cface x (edge x)).
Definition bridgeless : Prop := set0b (fun x : g => cface x (edge x)).

Lemma bridgeless_cface : bridgeless -> forall x : g, cface x (edge x) = false.
Proof. by move/set0P. Qed.

Definition loopless : Prop := set0b (fun x : g => cnode x (edge x)).

End BridgeAndLoopLess.

Lemma bridgeless_dual : forall g, bridgeless (dual g) = loopless g.
Proof.
move=> g; PropCongr; apply/set0P/set0P => /= Hg x.
  by rewrite Snode -(same_fconnect_finv (Inode g)) -{2}(finv_f (Iedge g) x) Hg.
by rewrite (same_fconnect_finv (Inode g)) Snode -{2}(f_finv (Iedge g) x) Hg.
Qed.

Lemma bridgeless_mirror : forall g, bridgeless (mirror g) = bridgeless g.
Proof.
move=> g; PropCongr; apply/set0P/set0P => [] /= Hg x.
  rewrite Sface -{2}[x]Eedge cface1 cface1r -(same_fconnect_finv (Iface g)).
  exact: Hg.
rewrite (same_fconnect_finv (Iface g)) Sface /comp -cface1 -{2}[x]Enode -cface1r.
exact: Hg.
Qed.

Section EqmBridgeLess.

Variables g g' : hypermap.
Hypothesis Eg' : g =m g'.

Lemma eqm_bridgeless : bridgeless g = bridgeless g'.
Proof.
PropCongr; case: g Eg' => [d e n f EgE] [e' n' f' Eg'E Ee _ Ef].
congr (_ =d 0); apply: eq_card => x.
by rewrite /= Ee; apply: eq_fconnect.
Qed.

Lemma eqm_loopless : loopless g = loopless g'.
Proof.
PropCongr; case: g Eg' => [d e n f EgE] [e' n' f' Eg'E Ee En _].
congr (_ =d 0); apply: eq_card => x.
by rewrite /= Ee; apply: eq_fconnect.
Qed.

End EqmBridgeLess.

(*   Since edge and node arity are fixed, face arity plays a central role    *)
(* in the theory, so we use a special `arity' syntax to refer to it.         *)

Notation "@ 'arity' g" := (@order g face)
  (at level 10, g at level 8, format "'@' 'arity'  g").
Notation arity := (@arity _).

Section FacePaths.

(* Arity lemmas, and the other face-centric notions: simple paths, their    *)
(* projection, ring band, and (outer) ring kernel.                          *)

Variables (n0 : nat) (g : hypermap).

Lemma arity_cface : forall x y : g, cface x y -> arity x = arity y.
Proof. by move=> x y Hxy; exact (eq_card (same_cface Hxy)). Qed.

Lemma arity_iter_face : forall n (x : g), arity (iter n face x) = arity x.
Proof. by move=> *; apply: arity_cface; rewrite Sface fconnect_iter. Qed.

Lemma arity_face : forall x : g, arity (face x) = arity x.
Proof. exact (arity_iter_face 1). Qed.

Lemma iter_face_arity : forall x : g, iter (arity x) face x = x.
Proof. apply: iter_order; exact (Iface g). Qed.

Lemma iter_face_subn : forall n (x : g), n <= arity x ->
  iter (arity x - n) face (iter n face x) = x.
Proof.
move=> n x Hn; rewrite -iter_addn addnC (leq_add_sub Hn); exact: iter_face_arity.
Qed.

Lemma arity_mirror : @arity (mirror g) =1 @arity g.
Proof. move=> x; apply: eq_card; exact (cface_mirror x). Qed.

Section SimplePaths.

Variables (e : rel g) (p : seq g).

Definition fband : set g := fun x => has (cface x) p.

Lemma ring_fband : subset p fband.
Proof.
by apply/subsetP => [x Hx]; apply/hasP; exists x; last by apply connect0.
Qed.

Lemma fbandF : fclosed face fband.
Proof.
apply: (intro_closed (Sface _)) => [x y Dy Hx]; apply/hasP.
by case/hasP: Hx => [z Hz Hxz]; exists z; last by rewrite -(eqP Dy) -cface1.
Qed.

(* kernel can be defined as the complement of band, since it is only used *)
(* when r is the outer ring of a configuration.                           *)

Definition kernel := setC fband.

Lemma kernel_off_ring : subset kernel (setC p).
Proof. rewrite -disjoint_subset disjoint_sym; exact ring_fband. Qed.

Lemma kernelF : fclosed face kernel.
Proof. apply: setC_closed; exact fbandF. Qed.

Definition fproj x := sub (froot face x) p (find (cface x) p).

Lemma fprojP : forall x, fband x -> p (fproj x) /\ cface x (fproj x).
Proof. by move=> x Hx; rewrite /fproj mem_sub ?sub_find // -has_find. Qed.

Lemma fproj_cface : forall x y, cface x y -> fproj x = fproj y.
Proof.
move=> x y Hxy; rewrite /fproj (rootP (Sface g) Hxy).
congr (@sub g); apply: eq_find; exact (same_cface Hxy).
Qed.

Definition simple := uniq (maps (froot face) p).

Lemma simple_uniq : simple -> uniq p.
Proof. move=> Up; exact (maps_uniq Up). Qed.

(* scycle is a coercion target. *)
Definition scycleb : bool := cycle e p && simple.
Definition scycle : Prop := cycle e p && simple.

Lemma scycle_cycle : scycle -> cycle e p.
Proof. by case/andP. Qed.

Lemma scycle_simple : scycle -> simple.
Proof. by case/andP. Qed.

Lemma scycle_uniq : scycle -> uniq p.
Proof. move/scycle_simple; exact simple_uniq. Qed.

Lemma scycle_ucycle : scycle -> ucycle e p.
Proof. by case/andP=> [Hp Up]; rewrite /ucycle Hp simple_uniq. Qed.

Coercion scycle_ucycle : scycle >-> paths.ucycle.

Lemma simple_fproj : simple -> forall x, p x -> fproj x = x.
Proof.
rewrite /simple /fproj; move=> Up x Hx; case/splitPr: Hx Up => [p1 p2].
rewrite maps_cat uniq_cat /=; case/and3P; clear; case/norP=> [Up1 _] _.
rewrite find_cat; case Hp1: (has (cface x) p1).
  case/mapsP: Up1; case/hasP: Hp1 => [y Hy Hxy]; exists y; auto.
  symmetry; exact (rootP (Sface g) Hxy).
by rewrite /= connect0 addn0 sub_cat /= ltnn subnn.
Qed.

Lemma scycle_fproj : scycle -> forall x, p x -> fproj x = x.
Proof. case/andP; clear; exact simple_fproj. Qed.

Lemma simple_cface : simple -> forall x y, cface x y -> p x -> p y -> x = y.
Proof.
move=> Up x y Hxy Hx Hy.
by rewrite -(simple_fproj Up Hx) (fproj_cface Hxy) simple_fproj.
Qed.

Lemma scycle_cface : scycle -> forall x y, cface x y -> p x -> p y -> x = y.
Proof. case/andP; clear; exact simple_cface. Qed.

Lemma simple_fcard_fband : simple -> fcard face fband = size p.
Proof.
move=> Up; rewrite -(size_maps (froot face) p) -(card_uniqP Up).
apply: eq_card => x; apply/andP/mapsP => [[Dx Hpx]|[y Hy <-]].
  case/hasP: Hpx => [y Hy Hxy]; exists y; first done.
  by rewrite -(rootP (Sface _) Hxy) (eqP Dx).
split; first by exact (roots_root (Sface g) y).
by apply/hasP; exists y; last by rewrite Sface connect_root.
Qed.

Lemma scycle_fcard_fband : scycle -> fcard face fband = size p.
Proof. case/andP; clear; exact simple_fcard_fband. Qed.

Lemma setI_cface_simple : forall x, simple -> card (setI (cface x) p) = fband x.
Proof.
move=> x Up; case Hx: (fband x).
  move/hasP: Hx => [y Hy Hxy].
  rewrite (cardD1 y) {1}/setI Hxy Hy; apply: eqP; apply/set0Pn.
  case=> z; move/and3P=> [Hyz Hxz Hz]; case/eqP: Hyz.
  by apply (simple_cface Up) => //; rewrite -(same_cface Hxy).
by apply: eq_card0 => y; apply/andP=> [] [Hxy Hy]; case/hasP: Hx; exists y.
Qed.

End SimplePaths.

Lemma fband_adds : forall x p y, fband (Adds x p) y = cface y x || fband p y.
Proof. done. Qed.

Lemma fband_seqn : forall x y, cface x y ->
  forall n, fband (seqn n x) =1 fband (seqn n y).
Proof.
move=> x y Hxy n z; elim: n => //= [n <-].
by rewrite !(Sface _ z) (same_cface Hxy).
Qed.

Fixpoint simple_rec (p : seq g) : bool :=
  if p is Adds x p' then negb (fband p' x) && simple_rec p' else true.

Lemma simple_recI : simple =1 simple_rec.
Proof.
rewrite /simple; elim=> //= [x p ->]; congr andb.
apply/mapsP/hasP => [[y Hy Dy]|[y Hy Hxy]]; exists y => //.
  by apply/(rootP (Sface g)).
exact (esym (rootP (Sface g) Hxy)).
Qed.

Lemma simple_adds : forall x p, simple (Adds x p) = negb (fband p x) && simple p.
Proof. by move=> *; rewrite !simple_recI. Qed.

Lemma fband_cat : forall p1 p2 x, fband (cat p1 p2) x = fband p1 x || fband p2 x.
Proof. move=> *; apply: has_cat. Qed.

Lemma fproj_adds : forall x p y,
  fproj (Adds x p) y = (if cface x y then x else fproj p y).
Proof. by move=> x p y; rewrite /fproj /= Sface; case (cface x y). Qed.

Lemma fproj_cat : forall p1 p2 x,
  fproj (cat p1 p2) x = fproj (if fband p1 x then p1 else p2) x.
Proof.
move=> p1 p2 x; elim: p1 => [|y p1 Hrec] //=; rewrite fproj_adds Hrec Sface.
case Hxy: (cface x y) => /=; first by rewrite fproj_adds Sface Hxy.
by case (fband p1 x); first by rewrite fproj_adds Sface Hxy.
Qed.

Lemma has_fband_sym : forall p1 p2, has (fband p1) p2 = has (fband p2) p1.
Proof.
by move=> p1 p2; apply/hasP/hasP => [] [x Hx]; (move/hasP=> [y Hy Hxy]);
  exists y=> //; apply/hasP; exists x=> //; rewrite Sface.
Qed.

Lemma simple_cat : forall p1 p2,
  simple (cat p1 p2) = and3b (simple p1) (negb (has (fband p1) p2)) (simple p2).
Proof.
move=> p1 p2; rewrite !simple_recI has_fband_sym.
elim: p1 => [|x p1 Hrec] //=.
by rewrite fband_cat Hrec !negb_orb -!andbA; repeat BoolCongr.
Qed.

Lemma simple_add_last : forall x p,
  simple (add_last p x) = negb (fband p x) && simple p.
Proof.
by move=> *; rewrite -cats1 simple_cat {2}/simple /= orbF andbT andbC.
Qed.

Lemma simple_catC : forall p1 p2, simple (cat p1 p2) = simple (cat p2 p1).
Proof. by move=> *; rewrite /simple !maps_cat uniq_catC. Qed.

Lemma simple_catCA : forall p1 p2 p3,
  simple (cat p1 (cat p2 p3)) = simple (cat p2 (cat p1 p3)).
Proof. by move=> *; rewrite /simple !maps_cat uniq_catCA. Qed.

Lemma fband_rot : forall p, fband (rot n0 p) =1 fband p.
Proof. move=> p x; apply: has_rot. Qed.

Lemma fproj_rot : forall p, simple p -> fproj (rot n0 p) =1 fproj p.
Proof.
move=> p Up x; case Hx: (fband (rot n0 p) x).
case/fprojP: Hx; rewrite mem_rot; move: (fproj (rot n0 p) x) => y Hy Hxy.
  by rewrite (fproj_cface p Hxy) simple_fproj.
have := Hx; rewrite fband_rot in Hx; move: Hx; rewrite /fband !has_find !ltnNge.
by move/idP=> Hx; move/idP=> Hx'; rewrite /fproj !sub_default.
Qed.

Lemma simple_rot : forall p, simple (rot n0 p) = simple p.
Proof. by move=> *; rewrite /simple maps_rot uniq_rot. Qed.

Lemma scycle_rot : forall e p, scycle e (rot n0 p) = scycle e p.
Proof. by move=> *; rewrite /scycle cycle_rot simple_rot. Qed.

Lemma simple_perm : forall p q,
  fband p =1 fband q -> size p = size q -> simple p = simple q.
Proof.
move=> p q Epq Hpq; apply: uniq_perm; last by rewrite !size_maps.
move=> x; apply/mapsP/mapsP; case=> y Hy <- {x}.
  have Hz: (fband q y) by rewrite -Epq; apply: (subsetP (ring_fband _)).
  by case/hasP: Hz => [z Hz Hyz]; exists z; last by rewrite (rootP (Sface g) Hyz).
have Hz: (fband p y) by rewrite Epq; apply: (subsetP (ring_fband _)).
by case/hasP: Hz => [z Hz Hyz]; exists z; last by rewrite (rootP (Sface g) Hyz).
Qed.

Lemma simple_rev : forall p, simple (rev p) = simple p.
Proof. by move=> *; rewrite /simple maps_rev uniq_rev. Qed.

Lemma fband_rev : forall p, fband (rev p) =1 fband p.
Proof. move=> p x; apply: {x}eq_has_r => y; exact: mem_rev. Qed.

End FacePaths.

Lemma simple_maps :  forall (g g' : hypermap) (h : g -> g'),
    (forall x y, cface (h x) (h y) = cface x y) ->
  forall p, simple (maps h p) = simple p.
Proof.
move=> g g' h HhF; elim=> [|x p Hrec] //.
rewrite maps_adds !simple_adds Hrec; congr andb; congr negb.
by elim: p {Hrec} => [|y p Hrec] //=; rewrite HhF Hrec.
Qed.

Notation "'sfcycle' f" := (scycle (eqdf f)) (at level 10, f at level 8).

Prenex Implicits fband kernel fproj simple scycle simple_rec.

(* Special geometries: plain maps (binary edges), cubic maps (ternary nodes) *)
(* precubic maps (at most ternary nodes), pentagonal maps (faces 5-ary, at   *)
(* least). The reduction to plain cubic maps will be established in cube.v.  *)
(* All these predicates take a set argument, as we also consider quasi-plain *)
(* /quasi-cubic maps, that are only plain/cubic on a subset of the darts.    *)

Section SpecialMaps.

Variable g : hypermap.

Definition plainb (a : set g) := subset a (order_set edge 2).
Definition plain : Prop := plainb g.

Lemma plainPx : forall a : set g,
 reflect (forall x, a x -> edge (edge x) = x /\ (edge x =d x) = false)
         (plainb a).
Proof.
move=> a; apply: (iffP subsetP) => Ha x Hx.
  split; first by rewrite -{2}(iter_order (Iedge g) x) (eqnP (Ha x Hx)).
  apply/idPn; move: (uniq_orbit edge x).
  by rewrite /orbit (eqnP (Ha x Hx)) /= andbT /setU1 orbF.
move: {Ha Hx}(Ha x Hx) => [De2x He1x].
apply/eqP; apply: (order_cycle (p := seq2 x (edge x)) _ _ _); try apply: setU11.
  by rewrite /= /eqdf De2x ?set11.
by rewrite /= /setU1 He1x.
Qed.

Lemma plain_eq : plain -> forall x : g, edge (edge x) = x.
Proof. by move/(plainPx _)=> HgE x; case (HgE x). Qed.

Lemma plain_eq' : plain -> forall x : g, node (face x) = edge x.
Proof. by move=> HgE x; rewrite -{2}[x]Eface plain_eq. Qed.

Lemma plain_neq : plain -> forall x : g, (edge x =d x) = false.
Proof. by move/(plainPx _)=> HgE x; case (HgE x). Qed.

Lemma plain_orbit : plain -> forall x : g, cedge x =1 seq2 x (edge x).
Proof.
move=> HgE x; move: (fconnect_orbit edge x).
by rewrite /orbit (eqnP (subsetA HgE x)).
Qed.

Definition cubicb (a : set g) := subset a (order_set node 3).
Definition cubic : Prop := cubicb g.
Definition precubic : Prop := subset g (fun x => order node x <= 3).

Lemma cubicPx : forall a : set g,
 reflect (forall x, a x -> node (node (node x)) = x /\ (node x =d x) = false)
         (cubicb a).
Proof.
move=> a; apply: (iffP subsetP) => Ha x Hx.
  split; first by rewrite -{2}(iter_order (Inode g) x) (eqnP (Ha x Hx)).
  apply/idPn; move: (uniq_orbit node x).
  by rewrite /orbit (eqnP (Ha x Hx)); case/andP; case/norP.
move: {Ha Hx}(Ha x Hx) => [Dn3x Hn1x].
apply/eqP; apply: (order_cycle (p := traject node x 3) _ _ _); try apply: setU11.
  by rewrite /= /eqdf Dn3x ?set11.
by rewrite /= /setU1 -{4}Dn3x !(inj_eqd (Inode g)) (eqd_sym x) Hn1x.
Qed.

Lemma cubic_eq : cubic -> forall x : g, node (node (node x)) = x.
Proof. by move/(cubicPx _)=> HgN x; case (HgN x). Qed.

Lemma cubic_eq' : cubic -> forall x : g, node (node x) = face (edge x).
Proof. by move=> HgN x; rewrite -{1}[x]Eedge cubic_eq. Qed.

Lemma cubic_neq : cubic -> forall x : g, (node x =d x) = false.
Proof. by move/(cubicPx _)=> HgN x; case (HgN x). Qed.

Lemma cubic_orbit : cubic -> forall x : g,
  cnode x =1 seq3 x (node x) (node (node x)).
Proof.
move=> HgN x; move: (fconnect_orbit node x).
by rewrite /orbit (eqnP (subsetA HgN x)).
Qed.

Lemma precubic_leq : precubic -> forall x : g, order node x <= 3.
Proof. by move/subsetA. Qed.

Lemma cubic_precubic : cubic -> precubic.
Proof. by move/subsetA=> HgN; apply/subsetP => x _; rewrite (eqnP (HgN x)). Qed.

Definition pentagonal : Prop := forall x : g, 4 < arity x.

(* Requirement for the four color theorem. *)
Record planar_bridgeless : Prop := PlanarBridgeless {
  planar_bridgeless_is_planar :> planar g;
  planar_bridgeless_is_bridgeless :> bridgeless g
}.

(* Required by quiz, quiztree, part. *)
Record plain_cubic : Prop := PlainCubic {
  plain_cubic_connected_is_plain :> plain;
  plain_cubic_connected_is_cubic :> cubic
}.

(* Required for special Euler formula. *)
Record plain_cubic_connected : Prop := PlainCubicConnected {
  plain_cubic_connected_base :> plain_cubic;
  plain_cubic_connected_is_connected :> connected g
}.

(* Required by discharge. *)
Record planar_plain_cubic_connected : Prop := PlanarPlainCubicConnected {
  planar_plain_cubic_connected_base :> plain_cubic_connected;
  planar_plain_cubic_connected_is_planar :> planar g
}.

(* Required by part, redpart, hubcap. *)
Record plain_cubic_pentagonal : Prop := PlainCubicPentagonal {
  plain_cubic_pentagonal_base :> plain_cubic;
  plain_cubic_pentagonal_is_pentagonal :> pentagonal
}.

(* Factored intermediate signature. *)
Record planar_bridgeless_plain : Prop := PlanarBridgelessPlain {
  planar_bridgeless_plain_base :> planar_bridgeless;
  planar_bridgeless_plain_is_plain :> plain
}.

(* Required by revsnip. *)
Record planar_bridgeless_plain_connected : Prop := PlanarBridgelessPlainConnected {
  planar_bridgeless_plain_connected_base :> planar_bridgeless_plain;
  planar_bridgeless_plain_connected_is_connected :> connected g
}.

(* Inductive assumption. *)
Record planar_bridgeless_plain_precubic : Prop := PlanarBridgelessPlainPrecubic {
  planar_bridgeless_plain_precubic_base :> planar_bridgeless_plain;
  planar_bridgeless_plain_precubic_is_precubic :> precubic
}.

Section QuasicubicMaps.

Variable r : seq g.

Definition quasicubic : Prop := cubicb (setC r).

Lemma quasicubic_eq : quasicubic -> forall x,
  setC r x -> node (node (node x)) = x.
Proof. by move/(cubicPx _)=> H x Hx; case (H x Hx). Qed.

(* Required by quiz. *)
Record plain_quasicubic : Prop := PlainQuasicubic {
  plain_quasicubic_is_plain :> plain;
  plain_quasicubic_is_quasicubic :> quasicubic
}.

(* Intermediate common base *)
Record ucycle_plain_quasicubic : Prop := UcyclePlainQuasicubic {
  ucycle_plain_quasicubic_base :> plain_quasicubic;
  ucycle_plain_quasicubic_is_ucycle :> ufcycle node r
}.

(* Required by kempe. *)
Record ucycle_planar_plain_quasicubic : Prop := UcyclePlanarPlainQuasicubic {
  ucycle_planar_plain_quasicubic_base :> ucycle_plain_quasicubic;
  ucycle_planar_plain_quasicubic_is_planar :> planar g
}.

(* Required by for special Euler formula *)
Record ucycle_plain_quasicubic_connected : Prop := UcyclePlainQuasicubicConnected {
  ucycle_plain_quasicubic_connected_base :> ucycle_plain_quasicubic;
  ucycle_plain_quasicubic_connected_is_connected :> connected g
}.

(* Required by embed and redpart. Two additional geometrical conditions *)
(* are also needed; these will be defined below, but will only be added *)
(* in reducible.v, along with reducibility.                             *)
Record scycle_planar_bridgeless_plain_quasicubic_connected : Prop :=
ScyclePlanarBridgelessPlainQuasicubicConnected {
  scycle_planar_bridgeless_plain_quasicubic_connected_base :>
    ucycle_plain_quasicubic_connected;
  scycle_planar_bridgeless_plain_quasicubic_connected_is_simple : simple r;
  scycle_planar_bridgeless_plain_quasicubic_connected_is_planar :> planar g;
  scycle_planar_bridgeless_plain_quasicubic_connected_is_bridgeless :> bridgeless g
}.

Lemma scycle_planar_bridgeless_plain_quasicubic_connected_is_scycle :
  scycle_planar_bridgeless_plain_quasicubic_connected -> sfcycle node r.
Proof. by do 3 case; clear; case/andP=> *; apply/andP; split. Qed.

Coercion scycle_planar_bridgeless_plain_quasicubic_connected_is_scycle :
 scycle_planar_bridgeless_plain_quasicubic_connected >-> scycle.

Definition scycle_planar_bridgeless_plain_quasicubic_connected_pbpc_base :
  scycle_planar_bridgeless_plain_quasicubic_connected
    -> planar_bridgeless_plain_connected.
by do 4 case; repeat split.
Defined.

Coercion scycle_planar_bridgeless_plain_quasicubic_connected_pbpc_base :
 scycle_planar_bridgeless_plain_quasicubic_connected
   >-> planar_bridgeless_plain_connected.

(* The special form of the Euler formula for plain quasicubic connected maps. *)

Lemma quasicubic_Euler : ucycle_plain_quasicubic_connected ->
  let exterior := negb (r =d seq0) in
  let nb_face := exterior + fcard face g in
  let ring_darts := double (size r) in
  planar g = (6 * nb_face =d card g + (ring_darts + 12)).
Proof.
do 2 case; move=> [HgE HgN]; move/andP=> [Hr Ur] Hcg exterior; PropCongr.
transitivity (6 * genus_lhs g =d 6 * genus_rhs g).
rewrite /planar even_genusP; move: (genus g) (genus_rhs g) => m m'.
  by rewrite /= -!addnA; repeat rewrite -?(addnCA m') !eqn_addl; case m.
set ne := fcard edge g; set nf := fcard face g; set sr := size r.
have Hne: card g = 2 * ne.
  by apply: eqP; rewrite (order_div_card (Iedge g) HgE) // set11.
have [nn Dnn Hnn]: exists2 nn, fcard node g = exterior + nn & card g = sr + 3 * nn.
  exists (fcard node (setC r)).
    rewrite (n_compC r) /exterior /sr; congr addn; case Dr: {2}r => [|x r'].
      by apply: eqP; apply/set0P => [x]; rewrite Dr /= /setI /= andbF.
    apply: etrans (n_comp_connect (Snode g) x); symmetry; apply: eq_n_comp_r.
    by apply: fconnect_cycle; rewrite // Dr /= setU11.
  have Ha: fclosed node (setC r).
    apply: setC_closed; apply: (intro_closed (Snode g)) => [x y Dy Hx].
    by rewrite -(fconnect_cycle Hr Hx) -(eqP Dy) fconnect1.
  rewrite -[sr](card_uniqP Ur) -(cardC r); congr addn; apply: eqP.
  by rewrite (order_div_card (Inode g) HgN) // set11.
rewrite /genus_lhs (eqnP Hcg) !double_mul2 muln1 muln_addr.
rewrite -{2}[6]/(1 + 2 + 3) !muln_addl mul1n {2}Hnn {2}Hne.
rewrite muln_addr !mulnA 3!addnA -addnA addnC -!addnA (addnC 12) -addnA eqd_sym.
by rewrite /genus_rhs -/ne -/nf Dnn -!addnA -!(addnCA nn) 2!muln_addr !eqn_addl.
Qed.

End QuasicubicMaps.

(* The special form of the Euler formula for plain cubic connected maps. *)

Lemma cubic_Euler : plain_cubic_connected ->
  planar g = (6 * fcard face g =d card g + 12).
Proof. by case; case=> *; rewrite (@quasicubic_Euler seq0); repeat split. Qed.

End SpecialMaps.

Notation plainP := (plainPx _).
Notation cubicP := (cubicPx _).

Section MirrorSpecials.

Variable g : hypermap.

Lemma plain_dual : plain (dual g) = plain g.
Proof.
PropCongr; apply: eq_subset_r => x.
by rewrite /order_set /= (order_finv (Iedge g)).
Qed.

Lemma plain_mirror : plain (mirror g) = plain g.
Proof.
PropCongr; apply/subsetP/subsetP => HgE x _.
  by rewrite /order_set -[x]Eedge -order_mirror_edge; apply: HgE.
by rewrite /order_set order_mirror_edge; apply: HgE.
Qed.

Lemma cubic_mirror : cubic (mirror g) = cubic g.
Proof.
PropCongr; apply: eq_subset_r => [x].
by rewrite /order_set /= (order_finv (Inode g)).
Qed.

Lemma precubic_mirror : precubic (mirror g) = precubic g.
Proof.
PropCongr; apply: eq_subset_r => [x].
by rewrite /order_set /= (order_finv (Inode g)).
Qed.

End MirrorSpecials.

Section Adj.

Variables (n0 : nat) (g : hypermap).

Definition rlink : rel g := fun x => cface (edge x).

Lemma rlinkE : forall x, rlink x (edge x).
Proof. move=> x; apply: connect0. Qed.

Lemma rlinkFr : forall y1 y2, cface y1 y2 -> forall x, rlink x y1 = rlink x y2.
Proof.
by move=> y1 y2 Hy12 x; rewrite /rlink !(Sface g (edge x)) (same_cface Hy12).
Qed.

Fixpoint srpath (x0 x : g) (p : seq g) {struct p} : bool :=
  if p is Adds y p' then
    and3b (cface (edge x) y) (all (fun z => negb (cface x z)) p') (srpath x0 y p')
  else cface (edge x) x0.

Definition srcycle r := if r is Adds x p then srpath x x p else true.

Lemma srcycleI : bridgeless g -> forall r, scycle rlink r = srcycle r.
Proof.
move=> Hbg [|x0 p] //; rewrite /scycle simple_recI /=; PropCongr.
elim: p {1 3 5}x0 => [|y p Hrec] x /=; first by rewrite !andbT.
 rewrite -{}Hrec -!andbA -/(rlink x y); case Hxy: (rlink x y) => //=.
BoolCongr; congr andb; rewrite Sface -(same_cface Hxy) Sface (set0P Hbg) /=.
by rewrite /fband -all_setC.
Qed.

Definition rlink_connected (a : set g) :=
  forall x y, a x -> a y ->
  exists2 p, path rlink (node (face x)) (add_last p y) & all a p.

Lemma simplify_rlink : forall x p, path rlink x p ->
 exists2 p', path rlink x p' /\ simple p'
          & and3 (last x p = last x p') ((p =d seq0) = (p' =d seq0)) (all p p').
Proof.
move=> x p; elim: {p}(S (size p)) x {-2}p (ltnSn (size p)) => // [n Hrec] x.
case=> [|y p] Hn Hp; first by exists (Seq0 g); split; rewrite // connect0.
rewrite /= ltnS in Hn Hp; case/andP: Hp => [Hxy Hp].
case Hpy: (fband p y).
case/fprojP: Hpy; move: (fproj p y) {Ep} => z Hpz Hyz.
  case/splitPr: Hpz Hp Hn => [p1 p2]; rewrite -cat_adds path_cat size_cat.
  move/andP=> [_ Hp2] Hn; case: {Hrec}(Hrec x (Adds z p2)) => //.
   by apply: leq_trans Hn; rewrite /= !ltnS leq_addl.
   by rewrite /= -(rlinkFr Hyz) Hxy; case/andP: Hp2.
  rewrite last_cat; move=> p' [Hp' Up'] [Ep' Ep'0 Hp2p']; exists p'; split; auto.
  by apply/allP => [t Ht]; rewrite mem_cat /setU orbC (allP Hp2p').
  case: {Hrec Hn Hp}(Hrec y p Hn Hp) => [p' [Hp' Up'] [Ep' _ Hpp']].
exists (Adds y p'); split; auto; try by rewrite /= Hxy.
  rewrite simple_adds Up' andbT; apply/hasP => [[z Hz Hyz]]; case/hasP: Hpy.
  by exists z; first by apply (allP Hpp').
apply/allP => [z]; rewrite /= /setU1; case: (y =d z) => //; apply: (allP Hpp').
Qed.

Definition adj : rel g := fun x y => has (fun x' => rlink x' y) (orbit face x).

Lemma adjPx : forall x y, reflect (exists2 z, cface x z & rlink z y) (adj x y).
Proof.
move=> x y; apply: (iffP hasP); case=> z Hxz Hyz;
  by exists z; auto; move: Hxz; rewrite fconnect_orbit.
Qed.

Notation adjP := (adjPx _ _).

Lemma rlink_adj : forall x y, rlink x y -> adj x y.
Proof. by move=> x *; apply/adjP; exists x; first by apply connect0. Qed.

Lemma adjE : forall x, adj x (edge x).
Proof. move=> x; apply rlink_adj; apply rlinkE. Qed.

Lemma adjF : forall x1 x2, cface x1 x2 -> adj x1 =1 adj x2.
Proof.
move=> x1 x2 Hx12 y; apply: {y}eq_has_r => y.
by rewrite -!fconnect_orbit (same_cface Hx12).
Qed.

Lemma adjFr : forall y1 y2, cface y1 y2 -> forall x, adj x y1 = adj x y2.
Proof.
move=> y1 y2 Hy12 x; apply: {x}eq_has => x.
by rewrite /rlink !(Sface g (edge x)) (same_cface Hy12).
Qed.

Lemma adjF1 : forall x, adj x =1 adj (face x).
Proof. move=> x y; apply adjF; apply fconnect1. Qed.

Lemma adjF1r : forall x y, adj x y = adj x (face y).
Proof. move=> x y; apply adjFr; apply fconnect1. Qed.

Lemma adjN : forall x, adj (node x) x.
Proof. by move=> x; rewrite -{2}[x]Enode -adjF1r adjE. Qed.

Lemma Sadj : plain g -> forall x y, adj x y = adj y x.
Proof.
move=> HgE x y; apply/adjP/adjP => [[z Hxz Hzy]|[z Hyz Hzx]];
 by exists (edge z); rewrite /rlink Sface ?plain_eq.
Qed.

Lemma no_adj_adj : forall x y1, negb (adj x y1) ->
 forall y2, adj x y2 -> cface y1 y2 = false.
Proof.
move=> x y1 Hxy1 y2 Hxy2; apply/idP => [Hy12]; case/idP: Hxy1.
by rewrite (adjFr Hy12).
Qed.

Lemma adj_no_cface : bridgeless g -> forall x y, adj x y -> cface x y = false.
Proof.
move=> Hbg x y; move/adjP=> [z Hxz Hzy].
by rewrite (same_cface Hxz) Sface -(same_cface Hzy) Sface (set0P Hbg).
Qed.

Definition chordless (r : seq g) :=
  subset r (fun x => disjoint (adj x) (setD1 (setD1 r (prev r x)) (next r x))).

Lemma chordless_rot : forall r, uniq r -> chordless (rot n0 r) = chordless r.
Proof.
move=> r Ur; rewrite /chordless (eq_subset (mem_rot n0 r)).
apply: eq_subset_r => [x]; rewrite (next_rot n0 Ur) (prev_rot n0 Ur).
rewrite !(disjoint_sym (adj x)); apply: eq_disjoint => [y].
by rewrite /setD1 mem_rot.
Qed.

(* Edge closure of a sequence, in a plain graph; used mainly for contracts.  *)

Fixpoint insertE (p : seq g) : seq g :=
  if p is Adds x p' then Adds x (Adds (edge x) (insertE p')) else seq0.

Lemma insertE_seqb : forall (b : bool) x,
  insertE (seqn b x) = cat (seqn b x) (seqn b (edge x)).
Proof. by case. Qed.

Lemma size_insertE : forall p, size (insertE p) = double (size p).
Proof. by elim=> //= [x p1 Hrec]; do 2 congr S. Qed.

Lemma insertE_cat : forall p1 p2,
  insertE (cat p1 p2) = cat (insertE p1) (insertE p2).
Proof. by move=> p1 p2; elim: p1 => //= [x p1 Hrec]; do 2 congr Adds. Qed.

Lemma mem_insertE : plain g -> forall p x, insertE p x = has (cedge x) p.
Proof.
move=> HgE p x; elim: p => //= [y p <-].
by rewrite Sedge (plain_orbit HgE) /= /setU1 -!orbA.
Qed.

Lemma insertE_rot : forall p, insertE (rot n0 p) = rot (double n0) (insertE p).
Proof.
move=> p; case: (ltnP n0 (size p)) => Hn0.
  rewrite -{2}(cat_take_drop n0 p) {1}/rot !insertE_cat -rot_size_cat.
  by rewrite size_insertE (size_takel (ltnW Hn0)).
by rewrite !rot_oversize // size_insertE leq_double.
Qed.

End Adj.

Prenex Implicits plainb cubicb rlink adj insertE quasicubic chordless.

Notation adjP := (adjPx _ _).

Unset Implicit Arguments.