(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Generic definitions and lemmas for datatypes with reflected (decidable) *)
(* equality. The structure includes the actual boolean predicate, not just *)
(* the decision procedure. A canonical structure for the booleans is given *)
(* here, and one will be provided for the integers in natprop.v.           *)
(*   Congruence properties of injective functions wrt reflected equality   *)
(* are established.                                                        *)
(*   Basic definitions are also given for sets and relations (i.e., unary  *)
(* and binary boolean predicates); however, the boolean algebra is NOT     *)
(* lifted to sets.                                                         *)
(*   The main technical result is the construction of the subdomain        *)
(* associated with a set.                                                  *)
(*   Syntactic sugar is provided for the equality predicate and its        *)
(* reflection property.                                                    *)
(*   We also provide a "dirty trick" to compensate for the fact that the   *)
(* Coq typechecker will not look up the canonical structure when pressed   *)
(* for the actual structure; a projection data will do the coercion.       *)

Definition reflect_eq (d : Set) (eq_d : d -> d -> bool) : Set :=
  forall x y : d, reflect (x = y) (eq_d x y).

Structure dataSet : Type := DataSet
  {datum :> Set;
   eqdata : datum -> datum -> bool;
   eqdataP : reflect_eq eqdata}.

Definition data (d : dataSet) (u : option d) : dataSet :=
  if u is None then d else d.

Implicit Arguments data [].

Notation "'data' t" := (data _ (None t)) (at level 10, t at level 9).

Definition eqd := nosimpl eqdata.

Lemma eqd_data : eqd = eqdata. Proof. done. Qed.

Notation "x '=d' y" := (eqd x y) (at level 70, no associativity).

Lemma eqPx : forall (d : dataSet) (x y : d), reflect (x = y) (x =d y).
Proof. exact eqdataP. Qed.

Notation "x '=P' y" := (eqPx x y) (at level 70, no associativity).

Notation eqP := (_ =P _).

Lemma eqd_refl : forall (d : dataSet) (x : d), x =d x.
Proof. by move=> *; apply/eqP. Qed.

Lemma eqd_sym : forall (d : dataSet) (x y : d), (x =d y) = (y =d x).
Proof. by move=> *; apply/eqP/eqP. Qed.

(* A short proof of the K axiom (proof-irrelevance for x = x) on dataSets. *)

Theorem eqP_K : forall (d : dataSet) (x : d) (Ex : x = x), Ex = erefl x.
Proof.
move=> d x Exx.
have Er: forall E, eq_ind x (fun y => y = x) E x E = erefl x.
  by case: {2 3 4 6 7 8}x /.
case (Er (if x =P x is Reflect_true E then E else Exx)).
case: {2 4 6 8 10 12 14 16}x / {-3}Exx; case: (x =P x) => [E|[]]; auto.
Qed.

Lemma data_eqT : forall (d : dataSet) (x y : d) (E E' : x = y), E = E'.
Proof. by move=> d x y; case: y / => E; rewrite eqP_K. Qed.

(* Comparison for booleans. *)

Lemma eqbPx : reflect_eq eqb.
Proof. by do 2 case; constructor. Qed.

Notation eqbP := (eqbPx _ _).

Canonical Structure boolData := DataSet eqbPx.

Lemma eqbE : eqb = @eqd _. Proof. done. Qed.

Lemma bool_eqT : forall (x y : bool) (E E' : x = y), E = E'.
Proof. apply: data_eqT. Qed.

(* Subsets and relations, defined by their characteristic functions.       *)

Section DataSubset.

Variable d : dataSet.

Definition set : Set := d -> bool.
Definition rel : Set := d -> set.

Definition sub_set (a a' : set) : Prop := forall x : d, a x -> a' x.
Definition sub_rel (e e' : rel) : Prop := forall x y : d, e x y -> e' x y.

Notation set1 := (@eqd d) (only parsing).
Definition set2 (x1 x2 : d) : set := fun y => (x1 =d y) || (x2 =d y).
Definition set3 (x1 x2 x3 : d) : set :=
  fun y => (x1 =d y) || ((x2 =d y) || (x3 =d y)).
Definition set4 (x1 x2 x3 x4 : d) : set :=
  fun y => (x1 =d y) || ((x2 =d y) || ((x3 =d y) || (x4 =d y))).
Definition setU (a b : set) : set := fun x => a x || b x.
Definition setU1 (x : d) (a : set) : set := fun y => (x =d y) || a y.
Definition setI (a b : set) : set := fun x => a x && b x.
Definition setC (a : set) : set := fun x => negb (a x).
Definition setC1 (x : d) : set := fun y => negb (x =d y).
Definition setD (a b : set) : set := fun x => negb (b x) && a x.
Definition setD1 (a : set) (x : d) : set := fun y => negb (x =d y) && a y.

Definition eqdf (f : d -> d) : rel := fun x => eqd (f x).
Definition relU (e e' : rel) : rel := fun x => setU (e x) (e' x).

Lemma set11 : forall x : d, set1 x x. Proof. apply: eqd_refl. Qed.

Lemma setU11 : forall x a, setU1 x a x.
Proof. by move=> *; rewrite /setU1 set11. Qed.

Lemma setU1r : forall x a, sub_set a (setU1 x a).
Proof. by move=> x a y Hy; rewrite /setU1 Hy orbT. Qed.

Lemma setU1Px : forall x (a : set) y, reflect (x = y \/ a y) (setU1 x a y).
Proof.
by move=> x a y; apply: (iffP orP); case; auto; left; [ apply: eqP | apply/eqP ].
Qed.

Lemma setC11 : forall x, setC1 x x = false.
Proof. by move=> *; rewrite /setC1 set11. Qed.

Lemma setD11 : forall x a, setD1 a x x = false.
Proof. by move=> *; rewrite /setD1 set11. Qed.

Lemma set21 : forall x1 x2, set2 x1 x2 x1.
Proof. by move=> *; rewrite /set2 set11. Qed.

Lemma set22 : forall x1 x2, set2 x1 x2 x2.
Proof. by move=> *; rewrite /set2 set11 orbT. Qed.

Lemma set31 : forall x1 x2 x3, set3 x1 x2 x3 x1.
Proof. by move=> *; rewrite /set3 set11. Qed.

Lemma set32 : forall x1 x2 x3, set3 x1 x2 x3 x2.
Proof. by move=> *; rewrite /set3 set11 !orbT . Qed.

Lemma set33 : forall x1 x2 x3, set3 x1 x2 x3 x3.
Proof. by move=> *; rewrite /set3 set11 !orbT. Qed.

Lemma sub_relUl : forall e e', sub_rel e (relU e e').
Proof. by move=> e e' x y Hxy; rewrite /relU /setU Hxy. Qed.

Lemma sub_relUr : forall e e', sub_rel e' (relU e e').
Proof. by move=> e e' x y Hxy; rewrite /relU /setU Hxy orbT. Qed.

End DataSubset.

Notation set0 := (fun _ : datum _ => false).
Notation set1 := (@eqd _) (only parsing).
Notation setU1P := (setU1Px _ _ _).

Coercion setA (d : dataSet) : set d := fun x : d => true.

Identity Coercion membership : set >-> Funclass.

Prenex Implicits eqdf set2 set3 set4 setU setU1 setD setD1 setI setC setC1.

(* Lemmas for reflected equality and endo functions.   *)

Section DataSetFun.

Lemma inj_eqd : forall (d d' : dataSet) (h : d -> d'),
  injective h -> forall x y, (h x =d h y) = (x =d y).
Proof. by move=> d d' h *; apply/eqP/eqP => *; [ auto | congr h ]. Qed.

Variables (d : dataSet) (f g : d -> d).

Lemma monic_eqd : monic f g -> forall x y, (f x =d f y) = (x =d y).
Proof. move/monic_inj; exact: inj_eqd. Qed.

Lemma iso_eqd : iso f -> forall x y, (f x =d f y) = (x =d y).
Proof. move/iso_inj; apply: inj_eqd. Qed.

Lemma monic2_eqd : monic f g -> monic g f -> forall x y, (f x =d y) = (x =d g y).
Proof. by move=> Ef Eg x y; rewrite -{1}[y]Eg; exact: monic_eqd. Qed.

Variable d' : dataSet.

Definition preimage k (a : set d') : set d := fun x => a (k x).

(* The invariant of an function f wrt a projection k is the set of points that *)
(* have the same projection as their image. We use this mainly with k a        *)
(* coloring function (in fact "coloring" a map is defined using "invariant").  *)

Definition invariant (k : d -> d') : set d := fun x => (k (f x) =d k x).

Lemma invariant_comp : forall h k, sub_set (invariant k) (invariant (comp h k)).
Proof. by move=> h k x Dkfx; rewrite /comp /invariant (eqP Dkfx) set11. Qed.

Lemma invariant_inj : forall h, injective h -> 
  forall k, invariant (comp h k) =1 invariant k.
Proof. move=> h Hh k x; exact: (inj_eqd Hh). Qed.

End DataSetFun.

Prenex Implicits preimage.

(* Various dataset constructions (however, we tend to roll out our own, in *)
(* order to retain control over the equality predicate).                   *)

Section ComparableDataSet.

Variable d : Set.

Definition comparable : Set := forall x y : d, {x = y} + {x <> y}.

Hypothesis Hdec : forall x y : d, {x = y} + {x <> y}.

Definition compareb x y := if Hdec x y is left _ then true else false.

Lemma compareP : reflect_eq compareb.
Proof. by move=> x y; rewrite /compareb; case (Hdec x y); constructor. Qed.

Definition compareData : dataSet := DataSet compareP.

End ComparableDataSet.

Lemma comparable_data : forall d : dataSet, comparable d.
Proof. by move=> d x y; case (x =P y); auto. Qed.

Section SubDataSet.

Variables (d : dataSet) (a : set d).

Record subd : Set := subdI {subdE : d; subd_mem : a subdE}.

Lemma subd_eqPx : reflect_eq (fun u v => subdE u =d subdE v).
Proof.
move=> [x Hx] [y Hy]; apply: (iffP eqP) => Hxy; last by congr subdE.
by simpl in Hxy; rewrite -Hxy in Hy |- *; rewrite (bool_eqT Hy Hx).
Qed.

Canonical Structure subData : dataSet := DataSet subd_eqPx.

Lemma subd_eqd : forall u v : subData, (u =d v) = (subdE u =d subdE v).
Proof. done. Qed.

Lemma subdE_inj : injective subdE.
Proof. move=> u v; move/(introT eqP); rewrite -subd_eqd; exact eqP. Qed.

Definition subdIopt x :=
  if idPx (a x) is Reflect_true Hx then Some (subdI Hx) else None.

Inductive subdI_spec (x : d) : option subData -> Set :=
  | Some_subd : forall u : subData, a x -> subdE u = x -> subdI_spec x (Some u)
  | None_subd : negb (a x) -> subdI_spec x None.

Lemma subdIoptP : forall x, subdI_spec x (subdIopt x).
Proof.
move=> x; rewrite /subdIopt; case: {2}(a x) / (idPx (a x)); first by left.
by move/(introT negP)=> Hx; right.
Qed.

End SubDataSet.

Notation subd_eqP := (subd_eqPx _ _).

Section ProdDataSet.

Variable d1 d2 : dataSet.

Record prodd : Set := proddI {proddE1 : d1; proddE2 : d2}.

Definition prodd_eqd (u v : prodd) : bool :=
  let (x1, x2) := u in let (y1, y2) := v in (x1 =d y1) && (x2 =d y2).

Lemma prodd_eqPx : reflect_eq prodd_eqd.
Proof.
move=> [x1 x2] [y1 y2] /=; apply: (iffP idP) => [|[<- <-]]; last by rewrite !set11.
by case/andP; do 2 move/eqP=> <-.
Qed.

Canonical Structure prodData := DataSet prodd_eqPx.

Lemma prodd_eqE : prodd_eqd = set1. Proof. done. Qed.

Lemma prodd_eqdl : forall u v : prodData, u =d v -> proddE1 u =d proddE1 v.
Proof. by move=> [x1 x2] [y1 y2]; case/andP. Qed.

Lemma prodd_eqdr : forall u v : prodData, u =d v -> proddE2 u =d proddE2 v.
Proof. by move=> [x1 x2] [y1 y2]; case/andP. Qed.

End ProdDataSet.

Notation prodd_eqP := (prodd_eqPx _ _).

Section SumDataSet.

Variables (I : dataSet) (d : I -> dataSet).

Record sumd : Set := sumdI {sumdE1 : I; sumdE2 : d sumdE1}.

Let sumdE3 (u v : sumd) : d (sumdE1 u) :=
  if sumdE1 u =P sumdE1 v is Reflect_true Huv then eq_rec_r d (sumdE2 v) Huv else
  sumdE2 u.

Remark sumdE3I : forall i (x y : d i), sumdE3 (sumdI x) (sumdI y) = y.
Proof.
move=> i x y; rewrite /sumdE3 /=; case: (i =P i) => [Hii|[]]; auto.
by rewrite (eqP_K Hii).
Qed.

Definition sumd_eqd u v := (sumdE1 u =d sumdE1 v) && (sumdE2 u =d sumdE3 u v).

Lemma sumd_eqPx : reflect_eq sumd_eqd.
Proof.
move=> [i x] [j y]; rewrite /sumd_eqd /=.
case: (i =P j) y => [<-|Hij] y; last by right; move=> [Dx].
by apply: (iffP eqP) => [Dx|<-]; try rewrite Dx; rewrite sumdE3I.
Qed.

Canonical Structure sumData := DataSet sumd_eqPx.

Lemma sumd_eqE : sumd_eqd = set1. Proof. done. Qed.

Lemma sumd_eqdl : forall u v : sumData, u =d v -> sumdE1 u =d sumdE1 v.
Proof.
by move=> [i x] [j y]; rewrite {1}/eqd /= /sumd_eqd /=; case (eqd i j).
Qed.

Lemma sumd_eqdr : forall i (x y : d i), (sumdI x =d sumdI y) = (x =d y).
Proof.
move=> i x y; rewrite {1}/eqd /= /sumd_eqd /= eqd_refl; congr eqd; apply: sumdE3I.
Qed.

End SumDataSet.

Notation sumd_eqP := (sumd_eqPx _ _).

Prenex Implicits subd sumd.

Unset Implicit Arguments.