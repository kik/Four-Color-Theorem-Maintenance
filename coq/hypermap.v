(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype path fingraph.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* A (finite) hypermap is just a triplet of functions over a finite set that *)
(* are mutually inverse -their composite is the identity. This is equivalent *)
(* to an arbitrary pair of permutations, but the three function presentation *)
(* has better symmetries. In particular, the generalizations of the Euler    *)
(* and genus formulae to hypermaps are completely symmetric. The Jordan      *)
(* characterization of planarity also has a nice hypermap formulation, but   *)
(* it is not as symmetrical (it requires singling out two of the three       *)
(* functions). Indeed, while it is relatively straightforward to show that   *)
(* swapping the two functions yields an equivalent definition (see below),   *)
(* is not at all obvious that substituting the third function also gives an  *)
(* equivalent definition; we will in fact only obtain this as a corollary of *)
(* the equivalence of the Jordan property with the Euler, in file jordan.v.  *)
(*    Although we conspicuously call the three functions edge, node, and     *)
(* face, we only give symmetrical definitions in this file. In particular,   *)
(* all the derived map constructions given here are symmetrical, and apply   *)
(* to arbitrary maps. The individual geometrical interpretation of these     *)
(* functions will only be introduced in file colormap.v.                     *)
(*    The precise triangular identity forces us to make several subtle       *)
(* choices in some of our definitions, that are easily overlooked in the     *)
(* more traditional relational/simplicial fomalization of geometry (e.g.,    *)
(* the inverion of funtions in the defition of the Jordan property and the   *)
(* dual graph. This extra attention to detail pays off handsomely in the     *)
(* rest of the devellopment, where we can establish many geometrical         *)
(* using only rewriting with the basic triangular identity and its           *)
(* permutations.                                                             *)
(*   Properties on maps, such as connectedness and planarity defined here,   *)
(* are usually defined as boolean predicates, so that we can state           *)
(* equivalence lemmas (e.g., the map obtained by sewing up two submaps along *)
(* their outer rings is planar iff the two submaps are). However we also     *)
(* need to define explicit shorthand for the equivalent Prop statement,      *)
(* because the coercion of a bool to Prop is not a good coercion target      *)
(* (all such assumptions are in the class is_true!).                         *)

Notation "'cancel3' f g h" := (cancel f (fun x => g (h x)))
  (at level 10, f, g, h at level 8).

Notation "@ 'cancel3' d f g h" :=
  (cancel (rT := d) (aT := d) f (fun x : d => g (h x : d)))
  (at level 10, d, f, g, h at level 8, format "'@' 'cancel3'  d  f  g  h").

Record hypermap : Type := Hypermap {
  dart :> finType;
  edge : dart -> dart;
  node : dart -> dart;
  face : dart -> dart;
  Eedge : cancel3 edge node face
}.

Implicit Arguments Eedge [].

Prenex Implicits edge node face.

Notation cedge := (fconnect edge).
Notation cnode := (fconnect node).
Notation cface := (fconnect face).

Section FiniteMap.

Variable g : hypermap.

Lemma Eface : @cancel3 g face edge node.
Proof. exact (canF_sym (Eedge g)). Qed.

Lemma Enode : @cancel3 g node face edge.
Proof. exact (canF_sym Eface). Qed.

Lemma Iedge : @injective g g edge. Proof. exact (can_inj (Eedge g)). Qed.
Lemma Inode : @injective g g node. Proof. exact (can_inj Enode). Qed.
Lemma Iface : @injective g g face. Proof. exact (can_inj Eface). Qed.

Lemma Sedge : forall x y : g, cedge x y = cedge y x.
Proof. exact (fconnect_sym Iedge). Qed.
Lemma Snode : forall x y : g, cnode x y = cnode y x.
Proof. exact (fconnect_sym Inode). Qed.
Lemma Sface : forall x y : g, cface x y = cface y x.
Proof. exact (fconnect_sym Iface). Qed.

Lemma same_cedge : forall x y : g, cedge x y -> cedge x =1 cedge y.
Proof. exact (same_connect Sedge). Qed.
Lemma same_cnode : forall x y : g, cnode x y -> cnode x =1 cnode y.
Proof. exact (same_connect Snode). Qed.
Lemma same_cface : forall x y : g, cface x y -> cface x =1 cface y.
Proof. exact (same_connect Sface). Qed.

Lemma cedge1 : forall x : g, cedge x =1 cedge (edge x).
Proof. exact (same_fconnect1 Iedge). Qed.
Lemma cedge1r : forall y x : g, cedge x y = cedge x (edge y).
Proof. exact (fun y x => same_fconnect1_r Iedge x y). Qed.

Lemma cnode1 : forall x : g, cnode x =1 cnode (node x).
Proof. exact (same_fconnect1 Inode). Qed.
Lemma cnode1r : forall y x : g, cnode x y = cnode x (node y).
Proof. exact (fun y x => same_fconnect1_r Inode x y). Qed.

Lemma cface1 : forall x : g, cface x =1 cface (face x).
Proof. exact (same_fconnect1 Iface). Qed.
Lemma cface1r : forall y x : g, cface x y = cface x (face y).
Proof. exact (fun y x => same_fconnect1_r Iface x y). Qed.

End FiniteMap.

Implicit Arguments Enode [].
Implicit Arguments Eface [].
Implicit Arguments Iedge [].
Implicit Arguments Inode [].
Implicit Arguments Iface [].
Implicit Arguments Sedge [].
Implicit Arguments Snode [].
Implicit Arguments Sface [].

Section Components.

Variable g : hypermap.

Definition glink : rel g := relU (frel edge) (relU (frel node) (frel face)).

Lemma glinkE : forall x : g, glink x (edge x).
Proof. by move=> *; rewrite /glink /relU /predU /frel /= eqxx. Qed.

Lemma glinkN : forall x : g, glink x (node x).
Proof. by move=> *; rewrite /glink /relU /predU /frel /= eqxx !orbT. Qed.

Lemma glinkF : forall x : g, glink x (face x).
Proof. by move=> *; rewrite /glink /relU /predU /frel /= eqxx !orbT. Qed.

Lemma Sglink : connect_sym glink.
Proof.
apply: relU_sym; first by exact (Sedge _).
apply: relU_sym; [ exact (Snode _) | exact (Sface _) ].
Qed.

Definition connectedb : bool := n_comp glink g == 1.
Definition connected : Prop := n_comp glink g == 1.

End Components.

Implicit Arguments Sglink [].

Prenex Implicits glink.

Notation gcomp := (connect glink).

Section Genus.

Variable g : hypermap.

Definition genus_lhs := double (n_comp glink g) + #|g|.

Definition genus_rhs := fcard edge g + (fcard node g + fcard face g).

Definition genus := half (genus_lhs - genus_rhs).

Definition even_genus : Prop := genus_lhs = double genus + genus_rhs.

Definition planarb : bool := genus == 0.
Definition planar : Prop := genus == 0.

End Genus.

Section Jordan.

Variable g : hypermap.

Definition clink : rel g := relU (frel (finv node)) (frel face).

Lemma clinkPx : forall x y, reflect (x = node y \/ face x = y) (clink x y).
Proof.
move=> x y; apply: (iffP orP); rewrite /frel.
  case; move/eqP=> <-; rewrite ?(f_finv (Inode g)); auto.
case=> /= ->; rewrite ?(finv_f (Inode g)) eq_refl; auto.
Qed.

Notation clinkP := (clinkPx _ _).

Lemma clinkN : forall x, clink (node x) x.
Proof. move=> x; apply/clinkP; auto. Qed.

Lemma clinkF : forall x, clink x (face x).
Proof. move=> x; apply/clinkP; auto. Qed.

Lemma Sclink : connect_sym clink.
Proof.
apply: relU_sym; [ exact (fconnect_sym (finv_inj (Inode _))) | apply: Sface ].
Qed.

Lemma clink_glink : connect clink =2 gcomp.
Proof.
move=> x; apply: subset_eqP; apply/andP.
split; apply/subsetP; move: x; apply: connect_sub => [x y Hy].
  case/clinkP: Hy => [Hy|Hy].
    rewrite Sglink Hy; exact (connect1 (glinkN _)).
  rewrite -Hy; exact (connect1 (glinkF _)).
case/predU1P: Hy => [Dy|Hy].
  rewrite -[x]Eedge Dy; apply: (connect_trans (connect1 (clinkN _))).
  rewrite Sclink; exact (connect1 (clinkF _)).
case/orP: Hy; case/eqP=> <-; first by rewrite Sclink; exact (connect1 (clinkN _)).
exact (connect1 (clinkF _)).
Qed.

Lemma connected_clink : connected g -> forall x y : g,
  exists2 p, path clink x p & y = last x p.
Proof.
move=> Hcg x y; apply: connectP; rewrite clink_glink.
apply/(rootP (Sglink _)); set rx := root glink x; set ry := root glink y.
rewrite /connected /n_comp (cardD1 rx) (cardD1 ry) in Hcg.
rewrite /predI /predD1 /= !inE {1}/rx {2}/ry !(roots_root (Sglink g)) /predT andbT in Hcg.
by case: (ry =P rx) Hcg.
Qed.

Definition moebius p :=
  if p is cons x p' then
    [&& (mem2 p' (finv node (last x p')) (node x)), (uniq p) & (path clink x p')]
  else false.

Definition jordan := forall p, moebius p = false.

Lemma jordan_face : jordan -> forall x p,
 [&& (mem2 p (face (last x p)) (finv face x)),
     (uniq (cons x p))
   & (path clink x p)] = false.
Proof.
move=> Hj x p; apply/and3P; move Dy: (last x p) => y [Hxy Up Hp].
case/splitP2r: p / Hxy Up Hp Dy => [p1' p23 Hx].
rewrite -cat_cons cat_uniq last_cat path_cat; set p1 := cons x p1'.
move/and3P=> [Up1 Up123 Up23] /=; move/and3P=> [Hp1 Hfy Hp23] Dy.
case/clinkP: Hfy => [Dnfy|Hfy];
 last by case/hasP: Up123;
   exists y; [ rewrite -{1}Dy | rewrite -(Iface _ _ _ Hfy) ]; apply: mem_last.
case/splitPl: p23 / Hx Up123 Up23 Hp23 Dy => [p2' p3 Dx].
rewrite -cat_cons has_cat cat_uniq; set p2 := cons (face y) p2'.
move/norP=> [Up12 Up13]; move/and3P=> [Up2 Up23 Up3].
rewrite path_cat last_cat (Dx); case Dp3: p3 => [|feenx p3'] /=.
  by move=> _ Dy; rewrite /p1 /p2 -Dy /= (f_finv (Iface g)) inE eqxx in Up12.
move/and3P=> [Hp2 Hx Hp3] Dy; case/clinkP: Hx => [Dfeenx|Hfx];
  last by rewrite /p1 Dp3 -Hfx /= (f_finv (Iface g)) inE eqxx in Up13.
case/and3P: (Hj (cons feenx (cat p3' (cat p2 p1)))); split.
- rewrite !last_cat Dy /= Dnfy (finv_f (Inode g)) mem2_cat mem2_cons eqxx.
  by rewrite -Dfeenx /= -in_cons -cat_cons mem_cat /predU -Dx mem_last /= orbT.
- rewrite -cat_cons -Dp3 !cat_uniq has_cat negb_orb.
  by rewrite Up3 has_sym Up23 has_sym Up13 has_sym Up12 Up2.
rewrite !path_cat Dy /(p1) /(p2) /= Dx.
by rewrite -{2}(f_finv (Iface g) x) !clinkF Hp3 Hp2.
Qed.

End Jordan.

Prenex Implicits clink moebius.

Notation clinkP := (clinkPx _ _).

Implicit Arguments Sclink [].

Section DerivedMaps.

Variable g : hypermap.

(* Left permutation (edge -> node) *)

Definition permN := Hypermap (Enode g : cancel3 node face edge).

Remark gcomp_permN : (gcomp : rel permN) =2 (gcomp : rel g).
Proof. by apply: eq_connect => [x y]; rewrite /glink /relU /predU /= orbA orbC. Qed.

Lemma connected_permN : connected permN = connected g.
Proof. by rewrite /connected (eq_n_comp gcomp_permN). Qed.

Lemma genus_permN : genus permN = genus g.
Proof.
by rewrite /genus /genus_rhs /= addnA addnC /genus_lhs (eq_n_comp gcomp_permN).
Qed.

Lemma planar_permN : planar permN = planar g.
Proof. by rewrite /planar genus_permN. Qed.

(* Right permutation (edge -> face) *)

Definition permF := Hypermap (Eface g : cancel3 face edge node).

Remark gcomp_permF : (gcomp : rel permF) =2 (gcomp : rel g).
Proof. by apply: eq_connect => [x y]; rewrite /glink /relU /predU /= orbC orbA. Qed.

Lemma connected_permF : connected permF = connected g.
Proof. by rewrite /connected (eq_n_comp gcomp_permF). Qed.

Lemma genus_permF : genus permF = genus g.
Proof.
by rewrite /genus /genus_rhs /= addnC addnA /genus_lhs (eq_n_comp gcomp_permF).
Qed.

Lemma planar_permF : planar permF = planar g.
Proof. by rewrite /planar genus_permF. Qed.

Remark hmap_dualP : @cancel3 g (finv edge) (finv face) (finv node).
Proof.
move=> x; rewrite -{1}[x]Eface (finv_f (Iedge g)) (finv_f (Inode g)).
exact (finv_f (Iface g) x).
Qed.

(* Dual: invert all functions, and transpose node and face *)

Definition dual : hypermap := Hypermap hmap_dualP.

Remark gcomp_dual : (gcomp : rel dual) =2 (gcomp : rel g).
Proof.
move=> x y; rewrite -!clink_glink; apply: {x y}eq_connect => x y.
by rewrite /clink /relU /predU /frel /= (finv_inv (Iface g)) orbC.
Qed.

Lemma connected_dual : connected dual = connected g.
Proof. by rewrite /connected (eq_n_comp gcomp_dual). Qed.

Lemma genus_dual : genus dual = genus g.
Proof.
rewrite {1}/genus /genus_rhs /= addnCA addnC -addnA /genus_lhs.
rewrite (eq_n_comp gcomp_dual) (fcard_finv (Iedge g)).
by rewrite (fcard_finv (Inode g)) (fcard_finv (Iface g)).
Qed.

Lemma planar_dual : planar dual = planar g.
Proof. by rewrite /planar genus_dual. Qed.

(* Mirror: invert node and face in place, garble edge *)

Remark hmap_mirrorP : @cancel3 g (comp face node) (finv node) (finv face).
Proof.
move=> x; rewrite /comp (finv_f (Iface g)); exact (finv_f (Inode g) x).
Qed.

Definition mirror : hypermap := Hypermap hmap_mirrorP.

Lemma cnode_mirror : (cnode : rel mirror) =2 (cnode : rel g).
Proof. exact (same_fconnect_finv (Inode g)). Qed.

Lemma cface_mirror : (cface : rel mirror) =2 (cface : rel g).
Proof. exact (same_fconnect_finv (Iface g)). Qed.

Remark mirror_edge_adj : @fun_adjunction mirror g face edge (finv edge) g.
Proof.
apply: strict_adjunction=> //; try apply: Iface; try exact (Sedge dual).
  by apply/subsetP => [x _]; rewrite -(Enode g x); apply: codom_f.
move=> x y _ /=.
by rewrite /frel /comp (inj_eq (Iface g)) (finv_eq_can (Eedge g)).
Qed.

Lemma order_mirror_edge : forall x : g, @order mirror edge x = order edge (node x).
Proof.
move=> x; move: mirror_edge_adj => [_ De'].
apply: (etrans _ (card_image (Iface g) _)); apply: eq_card => [y].
rewrite /in_mem /=. rewrite -[connect _ _ _]/(connect (frel (@edge mirror)) x y).
rewrite cedge1 {2}/edge {4}/mirror /comp -(Enode g y) /in_mem /= (image_f _ (Iface g)).
by rewrite -De' // (same_fconnect_finv (Iedge g)).
Qed.

Lemma gcomp_mirror : (gcomp : rel mirror) =2 (gcomp : rel g).
Proof.
move=> x y; rewrite -!clink_glink (same_connect_rev (Sclink g)).
apply: {x y}eq_connect => [x y]; rewrite /clink /relU /predU /frel /=.
rewrite (canF_eq (f_finv (finv_inj (Inode g)))) eq_sym; congr orb.
by rewrite (canF_eq (f_finv (Iface g))) eq_sym.
Qed.

Lemma connected_mirror : connected mirror = connected g.
Proof. by rewrite /connected (eq_n_comp gcomp_mirror). Qed.

Lemma genus_mirror : genus mirror = genus g.
Proof.
rewrite {1}/genus /genus_rhs /genus_lhs (eq_n_comp gcomp_mirror).
have <-: fcard edge g = fcard edge mirror.
  have Ea := adjunction_n_comp _ (Sedge mirror) (Sedge dual) _ mirror_edge_adj.
  symmetry; apply: (etrans (Ea _)); first done.
  apply: eq_n_comp; exact (same_fconnect_finv (Iedge g)).
by rewrite (eq_n_comp cnode_mirror) (eq_n_comp cface_mirror).
Qed.

Lemma planar_mirror : planar mirror = planar g.
Proof. by rewrite /planar genus_mirror. Qed.

End DerivedMaps.

Section EqualHypermap.

Variable g : hypermap.

Inductive eqm : hypermap -> Prop :=
    EqHypermap : forall (e n f : g -> g) (Eenf : cancel3 e n f),
      edge =1 e -> node =1 n -> face =1 f -> eqm (Hypermap Eenf).

Variable g' : hypermap.
Hypothesis Hg' : eqm g'.

Remark eqm_gcomp : n_comp glink g = n_comp glink g'.
Proof.
case: Hg' => [e n f Eenf Ee En Ef]; apply: eq_n_comp.
by apply: eq_connect => [x y]; rewrite {1}/glink /relU /predU /frel /= Ee En Ef.
Qed.

Lemma eqm_connected : connected g = connected g'.
Proof. by rewrite {2}/connected -eqm_gcomp. Qed.

Lemma eqm_genus : genus g = genus g'.
Proof.
rewrite {2}/genus /genus_lhs -eqm_gcomp; case: Hg' => [e n f Eenf Ee En Ef].
by rewrite /genus_rhs /= -(eq_fcard Ee) -(eq_fcard En) -(eq_fcard Ef).
Qed.

Lemma eqm_planar : planar g = planar g'.
Proof. by rewrite {2}/planar -eqm_genus. Qed.

End EqualHypermap.

Notation "x '=m' y" := (eqm x y) (at level 70, no associativity).

Lemma eqm_sym : forall g g', g =m g' -> g' =m g.
Proof. move=> [d e n f Eg] _ [] *; apply: EqHypermap => x; auto. Qed.

Lemma dual_inv : forall g, dual (dual g) =m g.
Proof.
move=> g; case: g (Iedge g) (Inode g) (Iface g) => [d e n f Eenf] /= *.
by rewrite /dual /=; apply: EqHypermap; apply: finv_inv.
Qed.

Lemma mirror_inv : forall g, mirror (mirror g) =m g.
Proof.
move=> g; case: g (Inode g) (Iface g) => [d e n f Eeg] /= Ing Ifg.
rewrite /dual /=; apply: EqHypermap; try by apply: finv_inv.
by move=> x; rewrite -{1}[x]Eeg /= /comp !finv_f.
Qed.

Unset Implicit Arguments.