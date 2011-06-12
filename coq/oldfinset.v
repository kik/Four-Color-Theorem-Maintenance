(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*   A small theory of data sets of finite cardinal, based on sequences.     *)
(* A finite data set is a data set plus a duplicate-free sequence of all its *)
(* elements. This is equivalent to requiring only a list, and we do give a   *)
(* construction of a finSet from a list, but it is preferable to specify the *)
(* structure of the dataset in general.                                      *)

Record finSet : Type := FinSet {
  element :> dataSet;
  enum : seq element;
  count_set1_enum : forall x, count (set1 x) enum = 1
}.

Section SeqFinSet.

Variables (d : dataSet) (e : seq d).

Let d' : dataSet := subData e.

Fixpoint subd_enum (s : seq d) : seq d' :=
  if s is Adds x s' then
    let s'' := subd_enum s' in
    if subdIopt e x is Some u then
      if s'' u then s'' else Adds u s''
    else s''
  else seq0.

Lemma subd_enumP : forall u, count (set1 u) (subd_enum e) = 1.
Proof.
move=> [x Hx]; rewrite /eqd /= -[1]/(true : nat) -Hx.
have: forall y, e y -> e y by done.
elim: {1 5 6}e => [|y s Hrec] //=.
case: subdIoptP => [u _ Du|Hy] Hs; last by case/idP: Hy; apply Hs; rewrite setU11.
have Hs' := Hs _ (setU1r _ _).
rewrite (fun_if (@count d' _)) /= (Hrec Hs') /eqd /= (Du) eqd_sym /setU1.
case: (y =P x) => [Dy|_]; last by rewrite /= add0n if_same.
by rewrite -has_set1 has_count /eqd /= Du Dy (Hrec Hs'); case (s x).
Qed.

Definition SeqFinSet := FinSet subd_enumP.

End SeqFinSet.

Lemma boolEnumP : forall b, count (set1 b) (seq2 true false) = 1.
Proof. by move=> [|]. Qed.

Canonical Structure boolEnum := FinSet boolEnumP.

Section FiniteSet.

Variable d : finSet.

Lemma mem_enum : enum d =1 d.
Proof. by move=> x; rewrite -has_set1 has_count count_set1_enum. Qed.

Lemma filter_enum : forall a : set d, filter a (enum d) =1 a.
Proof. by move=> a x; rewrite mem_filter /setI andbC mem_enum. Qed.

Lemma uniq_enum : uniq (enum d).
Proof.
have: forall x, count (set1 x) (enum d) <= 1.
  by move=> x; rewrite count_set1_enum.
elim: (enum d) => [|x s Hrec] Hs //=; apply/andP; split.
  rewrite -has_set1 has_count -ltnNge /=.
  by apply: leq_trans (Hs x); rewrite /= set11 leqnn.
by apply: Hrec => [y]; apply: leq_trans (Hs y); rewrite /= leq_addl.
Qed.

Section Pick.

Variable a : set d.

Inductive pick_spec : option d -> Set :=
  | Pick : forall x, a x -> pick_spec (Some x)
  | Nopick : a =1 set0 -> pick_spec None.

Definition pick : option d :=
  if filter a (enum d) is Adds x _ then Some x else None.

Lemma pickP : pick_spec pick.
Proof.
rewrite /pick; case: (filter a (enum d)) (filter_enum a) => [|x s] Ha.
  by right; apply: fsym.
by left; rewrite -Ha /= setU11.
Qed.

End Pick.

Lemma eq_pick : forall a b, a =1 b -> pick a = pick b.
Proof. move=> a *; symmetry; rewrite /pick -(@eq_filter _ a); auto. Qed.

Opaque pick.

Section Cardinal.

Definition card a := count a (enum d).

Lemma eq_card : forall a b, a =1 b -> card a = card b.
Proof. move=> a b Eab; apply: (eq_count Eab). Qed.

Lemma card0 : card set0 = 0. Proof. apply: count_set0. Qed.

Lemma cardA : card d = size (enum d). Proof. apply: count_setA. Qed.

Lemma card1 : forall x, card (set1 x) = 1.
Proof. move=> x; apply: count_set1_enum. Qed.

Lemma cardUI : forall a b, card (setU a b) + card (setI a b) = card a + card b.
Proof. move=> a b; apply: count_setUI. Qed.

Lemma cardIC : forall b a, card (setI a b) + card (setI a (setC b)) = card a.
Proof.
by move=> b a; apply: etrans _ (add0n _); rewrite -cardUI addnC -card0;
   congr (_ + _); apply: eq_card => x; rewrite /setI /setU /setC;
   case (a x); case (b x).
Qed.

Lemma cardC : forall a, card a + card (setC a) = card d.
Proof. move=> a; apply: etrans (esym cardA); exact: count_setC. Qed.

Lemma cardU1 : forall x a, card (setU1 x a) = negb (a x) + card a.
Proof.
move=> x a; apply: addn_injr (etrans (cardUI _ _) _); symmetry.
rewrite addnC addnA; congr addn; rewrite -(@eq_card (filter a (seq1 x))).
  simpl; case: (a x); last by rewrite /= card0 card1.
  by rewrite addnC; apply: eq_card => y; exact: mem_seq1.
by move=> y; rewrite mem_filter /setI mem_seq1 andbC.
Qed.

Lemma card2 : forall x y, card (set2 x y) = S (negb (x =d y)).
Proof.
move=> x y /=; apply: (etrans (cardU1 x (eqd y))).
by rewrite card1 addn1 eqd_sym.
Qed.

Lemma cardC1 : forall x, card (setC1 x) = pred (card d).
Proof. by move=> x; rewrite -(cardC (eqd x)) card1. Qed.

Lemma cardD1 : forall x a, card a = a x + card (setD1 a x).
Proof.
move=> x a; rewrite addnC; apply: (addn_injr (etrans (cardC a) _)).
rewrite -addnA (negb_intro (a x)) -[negb (a x)]/(setC a x) -cardU1.
symmetry; apply: etrans (congr1 (addn _) _) (cardC _).
by apply: eq_card => y; rewrite /setC /setU1 /setD1 negb_andb negb_elim.
Qed.

Lemma max_card : forall a, card a <= card d.
Proof. move=> a; rewrite -(cardC a); apply: leq_addr. Qed.

Lemma card_size : forall s : seq d, card s <= size s.
Proof.
elim=> [|x s Hrec] /=; first by rewrite card0.
by rewrite cardU1; case (s x); first exact (leqW Hrec).
Qed.

Lemma card_uniqPx : forall s : seq d, reflect (card s = size s) (uniq s).
Proof.
move=> s; elim: s => [|x s Hrec]; first by left; exact card0.
rewrite /= cardU1 /addn; case (s x); simpl.
  by right; move=> H; move: (card_size s); rewrite H ltnn.
by apply: (iffP Hrec) => [<-| [<-]].
Qed.

End Cardinal.

Definition set0b a := card a =d 0.
Definition disjoint a b := set0b (setI a b).
Definition subset a b := disjoint a (setC b).

Lemma card0_eq : forall a, card a = 0 -> a =1 set0.
Proof. by move=> a Ha x; apply/idP => [Hx]; rewrite (cardD1 x) Hx in Ha. Qed.

Lemma eq_card0 : forall a, a =1 set0 -> card a = 0.
Proof. by move=> a Da; rewrite (eq_card Da) card0. Qed.

Lemma set0Px : forall a, reflect (a =1 set0) (set0b a).
Proof. move=> a; apply: (iffP eqP); [apply: card0_eq | apply: eq_card0]. Qed.

Lemma set0Pnx : forall a : set d, reflect (exists x, a x) (negb (set0b a)).
Proof.
move=> a; case: (set0Px a) => [Ha|Hna]; constructor.
  by move=> [x Hx]; case/idP: (Ha x).
by case: (pickP a) => [x Hx|Ha]; [ exists x | case (Hna Ha) ].
Qed.

Lemma subsetPx : forall a b, reflect (sub_set a b) (subset a b).
Proof.
move=> a b; rewrite /subset /disjoint /setI /setC.
apply: (iffP (set0Px _)).
  by move=> Hab x Ha; apply negbEf; rewrite -(Hab x) Ha.
by move=> Hab x; case Ha: (a x); try rewrite (Hab _ Ha).
Qed.

Lemma subset_leq_card : forall a b, subset a b -> card a <= card b.
Proof.
move=> a b; move/(set0Px _)=> Hab.
rewrite -(leq_add2l (card (setC b))) 2!(addnC (card (setC b))).
rewrite -cardUI (eq_card Hab) card0 addn0 cardC; apply max_card.
Qed.

Lemma subset_refl : forall a, subset a a.
Proof. by move=> a; apply/(subsetPx _ _); move. Qed.

Lemma eq_subset : forall a a', a =1 a' -> subset a =1 subset a'.
Proof.
by move=> a a' Eaa' b; congr eqn; apply: eq_card => x; rewrite /setI Eaa'.
Qed.

Lemma eq_subset_r : forall b b', b =1 b' -> forall a, subset a b = subset a b'.
Proof.
by move=> b b' Ebb' a; congr eqn; apply: eq_card => x; rewrite /setI /setC Ebb'.
Qed.

Lemma subset_setA : forall a, subset a d.
Proof. by move=> a; apply/(subsetPx _ _). Qed.

Lemma subsetA : forall a, subset d a -> forall x, a x.
Proof. move=> a; move/subsetPx=> Ha x; auto. Qed.

Lemma subset_eqPx : forall a b, reflect (a =1 b) (subset a b && subset b a).
Proof.
move=> a b; apply: (iffP andP) => [[Hab Hba] x|Eab].
  by apply/idP/idP; apply: subsetPx.
by rewrite (eq_subset_r Eab) (eq_subset Eab) subset_refl.
Qed.

Lemma subset_cardP : forall a b, card a = card b -> reflect (a =1 b) (subset a b).
Proof.
move=> a b Ecab; case Hab: (subset a b) (subset_eqPx a b); simpl; auto.
case: (subsetPx b a) => [H|[]] // x Hbx; apply/idPn => Hax.
case/idP: (ltnn (card a)); rewrite {2}Ecab (cardD1 x b) Hbx /setD1.
apply: subset_leq_card; apply/(subsetPx _ _) => y Hy; rewrite andbC.
by rewrite (subsetPx _ _ Hab _ Hy); apply/eqP => Dx; rewrite Dx Hy in Hax.
Qed.

Lemma subset_trans : forall a b c, subset a b -> subset b c -> subset a c.
Proof.
move=> a b c; move/subsetPx=> Hab; move/subsetPx=> Hbc.
apply/(subsetPx _ _) => x Hx; auto.
Qed.

Lemma subset_all : forall (s : seq d) a, subset s a = all a s.
Proof. by move=> s a; exact (sameP (subsetPx _ _) allP). Qed.

Lemma disjoint_sym : forall a b, disjoint a b = disjoint b a.
Proof. by move=> a b; congr eqn; apply: eq_card => x; apply: andbC. Qed.

Lemma eq_disjoint : forall a a', a =1 a' -> disjoint a =1 disjoint a'.
Proof. by move=> a a' Ea b; congr eqn; apply: eq_card => x; congr andb. Qed.

Lemma disjoint_subset : forall a b, disjoint a b = subset a (setC b).
Proof.
move=> a b; rewrite /subset; rewrite 2!(disjoint_sym a).
by apply: eq_disjoint => x; rewrite /setC negb_elim.
Qed.

Lemma disjoint_trans : forall a b c, subset a b -> disjoint b c -> disjoint a c.
Proof. move=> a b c; rewrite 2!disjoint_subset; apply subset_trans. Qed.

Lemma disjoint0 : forall a, disjoint set0 a.
Proof. by move=> a; apply/(set0Px _). Qed.

Lemma disjoint1 : forall x a, disjoint (set1 x) a = negb (a x).
Proof.
move=> x a; apply negb_sym; apply: (sameP _ (set0Pnx (setI (set1 x) a))).
rewrite /setI; apply introP; move=> Hx; first by exists x; rewrite eqd_refl.
by case=> y; case/andP=> [Dx Hy]; case: (negP Hx); rewrite (eqP Dx).
Qed.

Lemma disjointU : forall a a' b,
  disjoint (setU a a') b = disjoint a b && disjoint a' b.
Proof.
move=> a a' b; rewrite /disjoint; case: (set0Px (setI a b)) => [Hb|Hb] /=.
congr eqn; apply: eq_card => x; move: {Hb}(Hb x); rewrite /setI /setU.
  by case (b x); [ rewrite andbT; move -> | rewrite !andbF ].
apply/(set0Px _) => [Ha]; case: Hb => x; apply/nandP.
case/nandP: {Ha}(Ha x); auto; case/norP; auto.
Qed.

Lemma disjointU1 : forall x a b,
  disjoint (setU1 x a) b = negb (b x) && disjoint a b.
Proof.
by move=> x a b; rewrite -(@eq_disjoint (setU (set1 x) a)) ?disjointU ?disjoint1.
Qed.

Lemma disjoint_has : forall (s : seq d) a, disjoint s a = negb (has a s).
Proof.
move=> s a; rewrite has_count -(eq_count (filter_enum a)) -has_count has_sym.
by rewrite has_count count_filter -filter_setI -count_filter -leqNgt leqn0.
Qed.

Lemma disjoint_cat : forall s1 s2 a,
  disjoint (cat s1 s2) a = disjoint s1 a && disjoint s2 a.
Proof. by move=> *; rewrite !disjoint_has has_cat negb_orb. Qed.

End FiniteSet.

Notation card_uniqP := (card_uniqPx _).
Notation subsetP := (subsetPx _ _).
Notation set0P := (set0Px _).
Notation set0Pn := (set0Pnx _).
Notation subset_eqP := (subset_eqPx _ _).

Prenex Implicits card set0b pick subset disjoint.

Section FunImage.

Variables (d : finSet) (d' : dataSet) (f : d -> d').

Definition codom : set d' := fun x' => negb (set0b (preimage f (set1 x'))).

Remark Hiinv : forall x', codom x' -> {x : d | x' =d f x}.
Proof.
move=> x' Hx'; pose a := x' =d f _.
case: (pickP a) => [x Dx | Hnx']; first by exists x.
by rewrite /codom /preimage -/a (introT set0P Hnx') in Hx'.
Qed.

Definition iinv x' (Hx' : codom x') := let (x, _) := Hiinv Hx' in x.

Lemma codom_f : forall x, codom (f x).
Proof. move=> x; apply/set0Pn; exists x; apply: set11. Qed.

Lemma f_iinv : forall x' (Hx' : codom x'), f (iinv Hx') = x'.
Proof.
by move=> x' Hx'; rewrite /iinv; case: (Hiinv Hx') => [x]; case/eqP.
Qed.

Hypothesis Hf : injective f.

Lemma iinv_f : forall x (Hfx : codom (f x)), iinv Hfx = x.
Proof. move=> x Hfx; apply Hf; apply f_iinv. Qed.

Lemma preimage_iinv : forall a' x' (Hx' : codom x'),
  preimage f a' (iinv Hx') = a' x'.
Proof. by move=> *; rewrite /preimage f_iinv. Qed.

Section Image.

Variable a : set d.

Definition image : set d' := fun x' => negb (disjoint (preimage f (set1 x')) a).

(* This first lemma does not depend on Hf : (injective f). *)
Lemma image_codom : forall x', image x' -> codom x'.
Proof.
move=> x'; case/set0Pn=> x; case/andP; move/eqP=> Dx _; rewrite Dx.
apply codom_f.
Qed.

Lemma image_f : forall x, image (f x) = a x.
Proof.
move=> x; apply/set0Pn/idP => [[y Hy]|Hx].
  by case/andP: Hy => [Dx Hy]; rewrite (Hf (eqP Dx)).
by exists x; rewrite /setI /preimage eqd_refl.
Qed.

Lemma image_iinv : forall x' (Hx' : codom x'), image x' = a (iinv Hx').
Proof. by move=> x' Hx'; rewrite -image_f f_iinv. Qed.

Lemma pre_image : preimage f image =1 a.
Proof. by move=> x; rewrite /preimage image_f. Qed.

End Image.

Lemma image_pre : forall a', image (preimage f a') =1 setI a' codom.
Proof.
move=> a' x'; rewrite /setI andbC; case Hx': (codom x'); simpl.
  by rewrite -(f_iinv Hx') image_f /preimage f_iinv.
apply/idPn => [Hax']; case/idPn: Hx'; exact (image_codom Hax').
Qed.

Fixpoint preimage_seq (s : seq d') : seq d :=
  if s is Adds x s' then
    (if pick (preimage f (set1 x)) is Some y then Adds y else id) (preimage_seq s')
  else seq0.

Lemma maps_preimage : forall s : seq d',
  sub_set s codom -> maps f (preimage_seq s) = s.
Proof.
elim=> [|x s Hrec] //=; case: pickP => [y Dy|Hs'] Hs.
  rewrite /= (eqP Dy) Hrec // => z Hz; apply Hs; exact: setU1r.
by case/set0P: (Hs x (setU11 _ _)).
Qed.

End FunImage.

Prenex Implicits codom iinv image.

Section Ordinal.

Variable n : nat.

Let ordp : set natData := fun m => m < n.

Definition ordData := subData ordp.

Fixpoint iota (m : nat) : seq ordData :=
  if m is S m' then
    if subdIopt ordp m' is Some u then add_last (iota m') u else iota m'
  else seq0.

Lemma iota_ltn : forall m u, iota m u = (subdE u < m).
Proof.
move=> m u; elim: m => [|m Hrec] //=; rewrite /= ltnS leq_eqVlt -Hrec.
case: (subdIoptP ordp m) => [v Hm Dv|Hm].
  by rewrite /= mem_add_last /= /setU1 eqd_sym /eqd /= Dv.
by case: (subdE u =P m) => [Dm|_]; first by case (negP Hm); case Dm; case u.
Qed.

Lemma iotaP : forall u, count (set1 u) (iota n) = 1.
Proof.
move=> [p Hp]; rewrite /eqd /= -/(true : nat) -{}Hp {3}/ordp.
elim: {1 3 4}n (leqnn n) => [|m Hrec] Hm //=; rewrite ltnS.
case: (subdIoptP ordp m) => [v _ Dv|Hm']; last by rewrite /ordp Hm in Hm'.
rewrite -cats1 count_cat (Hrec (ltnW Hm)) /seq1 /= Dv.
by rewrite ltn_neqAle leq_eqVlt; case (eqd p m).
Qed.

Definition ordinal := FinSet iotaP.

Lemma ordinal_ltn : forall x : ordinal, subdE x < n.
Proof. by case. Qed.

Lemma card_ordinal : card ordinal = n.
Proof.
rewrite cardA /=; elim: {-2}n (leqnn n) => [|m Hrec] Hm //=.
case: (subdIoptP ordp m) => [v _ _|Hm']; last by rewrite /ordp Hm in Hm'.
exact (etrans (size_add_last _ v) (congr1 S (Hrec (ltnW Hm)))).
Qed.

Definition make_ord : forall m, m < n -> ordinal := @subdI _ ordp.

End Ordinal.

Section SubFinSet.

Variables (d : finSet) (a : set d).

Fixpoint fsub_enum (s : seq d) : seq (subData a) :=
  if s is Adds x s' then
    (if subdIopt a x is Some u then Adds u else id) (fsub_enum s')
  else seq0.

Lemma fsub_enumP : forall u, count (set1 u) (fsub_enum (enum d)) = 1.
Proof.
move=> [x Hx]; rewrite /eqd /= -(count_set1_enum x).
elim: (enum d) => [|y s Hrec] //=; rewrite -{}Hrec.
case: (subdIoptP a y) => [u Hy Du|Hy]; first by rewrite /= Du.
by case: (x =P y) => [Dx|_] //; rewrite -Dx Hx in Hy.
Qed.

Definition subFin := FinSet fsub_enumP.

Lemma card_sub_dom : @card subFin (subData a) = card a.
Proof.
apply: (etrans (cardA _)); rewrite /card /=.
elim: (enum d) => [|x s Hrec] //=.
by case: (subdIoptP a x) => [u Hx _|Hx]; rewrite ?(Hx) /= -Hrec // ?(negbE Hx).
Qed.

End SubFinSet.

Section ProdFinSet.

Variable d1 d2 : finSet.

Notation pd := (prodData d1 d2) (only parsing).

Definition fprod_enum :=
  foldr (fun x1 => cat (maps (proddI x1) (enum d2))) seq0 (enum d1).

Lemma fprod_enumP : forall u, count (set1 u) fprod_enum = 1.
Proof.
move=> [x1 x2]; rewrite -[1]/(d1 x1 : nat) -mem_enum /fprod_enum.
elim: (enum d1) (uniq_enum d1) => [|y1 s1 Hrec] //=; move/andP=> [Hy1 Hs1].
rewrite count_cat {Hrec Hs1}(Hrec Hs1) count_maps /setU1 /comp.
case Hx1: (y1 =d x1) => /=.
  rewrite (eqP Hx1) in Hy1; rewrite (negbE Hy1) (eqP Hx1) /= addn0 -(card1 x2).
  by apply: eq_count => y2; rewrite {1}/eqd /= set11.
rewrite addnC -{2}(addn0 (s1 x1)) -(card0 d2); congr addn.
by apply: eq_count => y; rewrite eqd_sym /eqd /= Hx1.
Qed.

Definition prodFin := FinSet fprod_enumP.

Lemma card_prod_dom : @card prodFin (prodData d1 d2) = card d1 * card d2.
Proof.
apply: (etrans (cardA _)); rewrite /= /fprod_enum !cardA.
by elim: (enum d1) => [|x1 s1 Hrec] //=; rewrite size_cat {}Hrec size_maps.
Qed.

End ProdFinSet.

Section SumFinSet.

Variables (I : finSet) (d : I -> finSet).

Definition sumfin_subdom i : dataSet := d i.
Let fsd : dataSet := sumData sumfin_subdom.

Fixpoint fsum_enum (si : seq I) : seq fsd :=
  if si is Adds i si' then
    cat (maps (fun x => sumdI x : fsd) (enum (d i))) (fsum_enum si')
  else seq0.

Lemma fsum_enumP : forall u, count (set1 u) (fsum_enum (enum I)) = 1.
Proof.
move=> [i x]; rewrite -[1]/(I i : nat) -mem_enum.
elim: (enum I) (uniq_enum I) => [|j s Hrec] //=; case/andP=> [Hj Hs].
rewrite count_cat {Hrec Hs}(Hrec Hs).
rewrite count_filter filter_maps size_maps /= /setU1 -count_filter.
case Hi: (j =d i); rewrite /= /comp.
  rewrite (eqP Hi) in Hj; rewrite (negbE Hj) (eqP Hi) /= addn0 -(card1 x).
  apply: eq_count => y; exact (sumd_eqdr x y).
rewrite addnC -{2}(addn0 (s i)) -(card0 (d j)); congr addn.
apply: eq_count => y; rewrite eqd_sym.
apply/idP => Hy; case/idP: Hi; exact (sumd_eqdl Hy).
Qed.

Definition sumFin := FinSet fsum_enumP.

Lemma card_sum_dom :
  @card sumFin fsd = foldr (fun i => addn (card (d i))) 0 (enum I).
Proof.
apply: (etrans (cardA _)); simpl; elim: (enum I) => [|i s Hrec] //=.
by rewrite /= -Hrec size_cat size_maps Hrec cardA.
Qed.

End SumFinSet.

Section IsoCard.

Lemma monic_card_leq :  forall (d d' : finSet) (f : d -> d') (g : d' -> d),
  monic f g -> card d <= card d'.
Proof.
move=> d d' f g Hfg; rewrite (cardA d') -(size_maps g).
apply: (leq_trans (subset_leq_card _) (card_size _)).
by apply/subsetP => [x _]; apply/mapsP; exists (f x); rewrite ?mem_enum.
Qed.

Lemma iso_eq_card_dom : forall d d' : finSet,
  (exists f : d -> d', iso f) -> card d = card d'.
Proof.
move=> d d' [f [g Hfg Hgf]]; apply: eqP.
by rewrite eqn_leq (monic_card_leq Hfg) (monic_card_leq Hgf).
Qed.

Lemma eq_datum_card : forall d d' : finSet, d = d' :> Set -> card d = card d'.
Proof.
move=> d [[d' eqd' eqd'P] ed' Hed'] Hdd'; simpl in Hdd'.
case: d' / Hdd' in eqd' eqd'P ed' Hed' |- *.
by apply iso_eq_card_dom; do 2 exists (@id d).
Qed.

Lemma iso_eq_card : forall (d d' : finSet) (a : set d) (a' : set d'),
 (exists f : @subd _ a -> @subd _ a', iso f) -> card a = card a'.
Proof.
move=> d d' a a' Haa'; rewrite -(card_sub_dom a) -(card_sub_dom a').
by apply: iso_eq_card_dom.
Qed.

Definition eq_dom_size d1 d2 := size (enum d1) = size (enum d2).

Definition assoc_findom : forall d1 d2, eq_dom_size d1 d2 -> d1 -> d2.
move=> d1 d2 E12 x1; apply (fun y2 => sub y2 (enum d2) (index x1 (enum d1))).
abstract by move: E12; rewrite /eq_dom_size; case: (enum d2) => //;
           case: (enum d1) (mem_enum x1).
Defined.

Lemma assoc_findom_monic : forall d1 d2,
 forall (E12 : eq_dom_size d1 d2) (E21 : eq_dom_size d2 d1),
 monic (assoc_findom E12) (assoc_findom E21).
Proof.
rewrite /eq_dom_size; move=> d1 d2 E12 E21 x.
set y := assoc_findom E12 x; rewrite /assoc_findom {2}/y /assoc_findom.
by rewrite index_uniq ?sub_index ?uniq_enum ?E21 ?index_mem ?mem_enum.
Qed.

Lemma eq_card_iso_dom : forall d1 d2 : finSet,
  card d1 = card d2 -> {f : d1 -> d2 &  {g : d2 -> d1 | monic f g &  monic g f}}.
Proof.
move=> d d'; rewrite !cardA; move=> E12; have E21 := esym E12.
exists (assoc_findom E12); exists (assoc_findom E21); apply assoc_findom_monic.
Qed.

Lemma eq_card_iso : forall (d d' : finSet) (a : set d) (a' : set d'),
 let da := @subd d a in let da' := @subd d' a' in
 card a = card a' -> {f : da -> da' &  {g : da' -> da | monic f g &  monic g f}}.
Proof.
move=> d d' a a' /= Haa'; apply: eq_card_iso_dom (subFin a) (subFin a') _.
by rewrite /= !card_sub_dom.
Qed.

End IsoCard.

Section CardFunImage.

Variables (d d' : finSet) (f : d -> d').

Lemma leq_image_card : forall a, card (image f a) <= card a.
Proof.
move=> a; set p := filter a (enum d).
have Up: (uniq p) by apply: uniq_filter; apply uniq_enum.
rewrite -(eq_card (filter_enum a)) -/p (card_uniqP Up) -(size_maps f).
apply: (leq_trans (subset_leq_card _) (card_size _)); apply/subsetP => u.
case/set0Pn=> x; case/andP; move/eqP=> Du Hx.
by apply/mapsP; exists x; first by rewrite /p filter_enum.
Qed.

Hypothesis Hf : injective f.

Lemma card_image : forall a, card (image f a) = card a.
Proof.
move=> a; apply iso_eq_card.
have Hf1: forall w : @subd _ (image f a), a (iinv (image_codom (subd_mem w))).
  by move=> [x' Hx']; rewrite -image_iinv.
have Hf2: forall w : @subd _ a, image f a (f (subdE w)).
  by move=> [x Hx]; rewrite image_f.
exists (fun w => @subdI d _ _ (Hf1 w)); exists (fun w => @subdI d' _ _ (Hf2 w)).
  by move=> [x Hx]; apply: subdE_inj; rewrite /= f_iinv.
by move=> [x Hx]; apply: subdE_inj; rewrite /= iinv_f.
Qed.

Lemma card_codom : card (codom f) = card d.
Proof.
apply: etrans (card_image d); apply: eq_card => x'.
apply/idPn/idP; last exact: image_codom.
by move=> Hx; rewrite -(f_iinv Hx) image_f.
Qed.

Lemma card_preimage : forall a', card (preimage f a') = card (setI (codom f) a').
Proof.
move=> a'; apply: etrans (esym (card_image _)) (eq_card _) => x'.
by rewrite (image_pre Hf) /setI andbC.
Qed.

End CardFunImage.

Unset Implicit Arguments.

