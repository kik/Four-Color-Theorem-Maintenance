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
Require Import hypermap.
Require Import geometry.
Require Import color.
Require Import coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Reduction to cubic maps; since this is not the inductive case, we can    *)
(* construct a larger map (indeed, we split each dart in 6!).               *)

Section Cube.

Variable g : hypermap.

Inductive cube_tag : Set := CTn | CTen | CTf | CTnf | CTe | CTfe.

Definition cube_tag_eq o o' :=
  match o, o' with
  | CTn, CTn => true
  | CTen, CTen => true
  | CTf, CTf => true
  | CTnf, CTnf => true
  | CTe, CTe => true
  | CTfe, CTfe => true
  | _, _ => false
  end.

Definition cube_tagData : dataSet.
apply (@DataSet _ cube_tag_eq); abstract by do 2 case; constructor.
Defined.

Canonical Structure cube_tagData.

Definition cube_tagSet : finSet.
apply (@FinSet _ (Seq CTn CTen CTf CTnf CTe CTfe)); abstract by case.
Defined.

Canonical Structure cube_tagSet.

Definition cube_dart := prodFin cube_tagSet g.

Let tsI : cube_tag -> g -> cube_dart := @proddI _ _.
Let tsE (u : cube_dart) : g := proddE2 u.

Definition cube_edge (u : cube_dart) :=
  let: proddI o x := u in
  match o with
  | CTen => tsI CTnf (edge x)
  | CTf  => tsI CTe  (node (face x))
  | CTnf => tsI CTen (node (face x))
  | CTe  => tsI CTf  (edge x)
  | CTfe => tsI CTn  x
  | CTn  => tsI CTfe x
  end.

Definition cube_node (u : cube_dart) :=
  let: proddI o x := u in
  match o with
  | CTn  => tsI CTen (node x)
  | CTen => tsI CTfe x
  | CTf  => tsI CTnf (edge x)
  | CTnf => tsI CTe  (node (face x))
  | CTe  => tsI CTf  x
  | CTfe => tsI CTn  (face (edge x))
  end.

Definition cube_face (u : cube_dart) :=
  let: proddI o x := u in
  match o with
  | CTn  => tsI CTen x
  | CTen => tsI CTf  x
  | CTf  => tsI CTnf x
  | CTnf => tsI CTn  (face x)
  | CTe  => tsI CTe  (edge x)
  | CTfe => tsI CTfe (node x)
  end.

Remark cube_monic3 : monic3 cube_edge cube_node cube_face.
Proof. by do 2 case; move=> x; rewrite /= ?Eface ?Eedge ?Enode. Qed.

Let cmap := Hypermap cube_monic3.

Definition cube := locked cmap.

Lemma plain_cube : plain cube.
Proof.
unlock cube; apply/plainP => u _.
by case: u; case; split; rewrite //= ?Eedge ?Eface ?Enode.
Qed.

Lemma cubic_cube : cubic cube.
Proof.
unlock cube; apply/cubicP => u _.
by case: u; case; split; rewrite //= ?Eedge ?Eface ?Enode.
Qed.

Let ate : set cmap := fun u => proddE1 u =d CTe.
Let atn : set cmap := fun u => proddE1 u =d CTfe.
Let atf : set cmap := setC (setU ate atn).

Let cf : rel cmap := eqdf cube_face.

Remark Cube_Hcf : connect_sym cf. Proof. exact (Sface cmap). Qed.
Notation Hcf := Cube_Hcf.

Remark Cube_Hate : closed cf ate.
Proof.
by apply: (intro_closed Hcf) => [[o x] v Dv]; rewrite -((_ =P v) Dv); case o.
Qed.
Notation Hate := Cube_Hate.

Remark Cube_Hatn : closed cf atn.
Proof.
by apply: (intro_closed Hcf) => [[o x] v Dv]; rewrite -((_ =P v) Dv); case o.
Qed.
Notation Hatn := Cube_Hatn.

Remark Cube_Hatf : closed cf atf.
Proof. by move=> u v Huv; rewrite /atf /setC /setU (Hate Huv) (Hatn Huv). Qed.
Notation Hatf := Cube_Hatf.

Remark Cube_Hcfe : fun_adjunction (tsI CTe) cube_face edge ate.
Proof.
apply: (strict_adjunction (Sedge g) Hate) => // [x y [Dx]|] //.
apply/subsetP => [[o x]]; rewrite /ate /=; move/eqP=> ->; exact (codom_f _ x).
Qed.
Notation Hcfe := Cube_Hcfe.

Remark Cube_Hcfn : fun_adjunction (tsI CTfe) cube_face node atn.
Proof.
apply: (strict_adjunction (Snode g) Hatn) => // [x y [Dx]|] //.
apply/subsetP => [[o x]]; rewrite /atn /=; move/eqP=> ->; exact (codom_f _ x).
Qed.
Notation Hcfn := Cube_Hcfn.

Remark Cube_Hcff : fun_adjunction (tsI CTnf) cube_face face atf.
Proof.
apply: (intro_adjunction (Sface g) Hatf (fun x _ => tsE x)) => [[o x] Hox|x].
  rewrite /sumfin_subdom in x Hox |- *; split.
    case: o Hox => // _; do 4 rewrite ?connect0 // (@cface1 cmap).
  move=> v _ Dv; rewrite -{v Dv}((_ =P v) Dv) /=.
  case: o Hox => // _; first [exact: connect0 | exact: fconnect1].
split; first exact: connect0.
move=> y; move/eqP=> <- {y}; rewrite 3!(@cface1 cmap); exact: fconnect1.
Qed.
Notation Hcff := Cube_Hcff.

Lemma genus_cube : genus cube = genus g.
Proof.
move: plain_cube cubic_cube; unlock cube => HcgE HcgN.
have HcD: card cmap = 6 * card g by apply: (etrans (card_prod_dom _ _)).
have HcE: fcard edge cmap = 3 * card g.
  by apply: eqP; rewrite -(order_div_card (Iedge _) HcgE) // mulnA; apply/eqP.
have HcN: fcard node cmap = 2 * card g.
  by apply: eqP; rewrite -(order_div_card (Inode _) HcgN) // mulnA; apply/eqP.
have HcFE: fcard edge g = n_comp cf ate.
  by apply: etrans (esym (adjunction_n_comp _ Hcf (Sedge g) Hate Hcfe)).
have HcFN: fcard node g = n_comp cf atn.
  by apply: etrans (esym (adjunction_n_comp _ Hcf (Snode g) Hatn Hcfn)).
have HcFF: fcard face g = n_comp cf atf.
  by apply: etrans (esym (adjunction_n_comp _ Hcf (Sface g) Hatf Hcff)).
have HcF: fcard face cmap = genus_rhs g.
  rewrite /n_comp /genus_rhs HcFE -(cardIC ate); congr addn.
    by apply: eq_card => u; rewrite /setI -andbA.
  rewrite -(cardIC atn) HcFN HcFF; congr addn.
    by apply: eq_card => u; rewrite /setI -!andbA; case: u; case.
  by apply: eq_card => u; rewrite /setI /atf /setU /setC negb_orb -!andbA.
have HcG: n_comp glink cmap = n_comp glink g.
  move: (Sclink g) (Sclink cmap) => Sg Scg.
  rewrite -!(eq_n_comp (@clink_glink _)).
  have Hg0 := connect0 glink.
  have Hg1e := fun g' u => @connect1 (dart g') _ _ _ (@glinkE g' u).
  have Hg1n := fun g' u => @connect1 (dart g') _ _ _ (@glinkN g' u).
  have Hg1f := fun g' u => @connect1 (dart g') _ _ _ (@glinkF g' u).
  have Ha: closed clink cmap by done.
  apply: (adjunction_n_comp (tsI CTnf) Scg Sg Ha).
  apply: (intro_adjunction Sg Ha (fun x _ => tsE x)) => [u _|x _].
    split.
      case: u => [o x] /=.
      pose cgx := gcomp (tsI _ x : cmap) (tsI CTnf x).
      have Hxe: cgx CTe by exact: connect_trans (Hg1n _ _) (Hg1f _ _).
      have Hxnf: cgx CTfe.
        apply: (connect_trans (Hg1e _ _)).
        do 2 apply: (connect_trans (Hg1f _ _)); exact: Hg1f.
      rewrite (@clink_glink cmap); case: o => //;
       do 4 first [ apply: Hg0 | apply: (connect_trans (Hg1f _ _)) ].
    move=> v _; rewrite clink_glink; case/clinkP=> [Du|Dv].
      rewrite {u}Du Sglink; case: v; case=> //= x.
        exact (connect_trans (Hg1f _ _) (Hg1n _ _)).
      exact (connect_trans (Hg1e _ _) (Hg1f _ _)).
    by rewrite -{v}Dv; case: u; case=> x /=.
  split; first by apply: connect0.
  move=> y; rewrite (@clink_glink cmap); case/clinkP=> [Dx|Dy].
    apply connect_trans with (tsI CTn y).
      rewrite Sglink Dx; apply: (connect_trans (Hg1n cmap _)) => /=.
      exact (connect_trans (Hg1f cmap _) (Hg1f cmap _)).
    do 2 apply: (connect_trans (Hg1f cmap _)); apply: Hg1f.
  by rewrite -Dy; do 4 apply: (connect_trans (Hg1f cmap _)).
rewrite {1}/genus /genus_lhs /genus_rhs HcD HcE HcN HcF HcG /= addn0.
by rewrite addnC -!addnA !subn_add2l addnC.
Qed.

Lemma planar_cube : planar cube = planar g.
Proof. PropCongr; congr (_ =d 0); exact genus_cube. Qed.

Lemma cube_colorable : four_colorable cube -> four_colorable g.
Proof.
unlock cube; move=> [k [HkE HkF]]; exists (fun x => k (tsI CTnf x)); split.
 move=> x; apply/eqcP => [Hkx]; case/eqcP: (HkE (tsI CTnf (edge x))) => /=.
  by symmetry; do 2 apply: etrans (eqcP (HkF _)) => /=; rewrite Eedge.
by move=> x; apply/eqcP; do 4 apply: etrans (eqcP (HkF _)) => /=.
Qed.

Lemma bridgeless_cube : bridgeless cube = bridgeless g.
Proof.
case: (Hcff) => [_ Ecff].
unlock cube; PropCongr; apply/set0P/set0P => [Htg x|Hg u].
  apply/idP => [Hgx]; case/idP: {Htg}(Htg (tsI CTen x)) => /=.
  do 2 apply: (connect_trans (fconnect1 cube_face _)) => /=.
  by rewrite Ecff in Hgx.
apply/idP => Hgu; case: u Hgu (closed_connect Hatf Hgu); case=> //= x Hgu.
  case/idP: {Hg}(Hg x); rewrite Ecff //.
  apply: connect_trans Hgu; rewrite (Sface cmap).
  exact: connect_trans (fconnect1 _ _) (fconnect1 _ _).
case/idP: {Hg}(Hg (node (face x))).
rewrite Sface Eface Ecff //; apply: connect_trans Hgu _.
exact (connect_trans (fconnect1 _ _) (fconnect1 _ _)).
Qed.

End Cube.

Set Strict Implicit.
Unset Implicit Arguments.

