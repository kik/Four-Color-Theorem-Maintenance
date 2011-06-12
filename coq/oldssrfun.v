(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

(* Basic constructions for intuitionistic functions : extensional equality   *)
(* composition, override, update, inverse, and iteration, with some their    *)
(* identities, and reflected equalities.                                     *)

(* Shorthand for some basic equality lemmas lemmas. *)

Definition erefl := refl_equal.
Definition esym := sym_eq.
Definition nesym := sym_not_eq.
Definition etrans := trans_eq.
Definition congr1 := f_equal.
Definition congr2 := f_equal2.
(* Force at least one implicit when used as a view. *)
Prenex Implicits esym nesym.

(* Extensional equality, for unary and binary functions, including syntactic *)
(* sugar.                                                                    *)

Section ExtensionalEquality.

Variables A B C : Type.

Definition eqfun (f g : B -> A) : Prop := forall x, f x = g x.

Definition eqrel (f g : C -> B -> A) : Prop := forall x y, f x y = g x y.

Lemma frefl : forall f, eqfun f f. Proof. split. Qed.
Lemma fsym : forall f g, eqfun f g -> eqfun g f. Proof. move=> f g H x; auto. Qed.
Lemma rrefl : forall f, eqrel f f. Proof. split. Qed.

End ExtensionalEquality.

Notation "f1 '=1' f2" := (eqfun f1 f2) (at level 70, no associativity).
Notation "f1 '=2' f2" := (eqrel f1 f2) (at level 70, no associativity).

Section Composition.

Variables A B C : Type.

Definition id (x : A) := x.

Definition comp (f : B -> A) (g : C -> B) x := f (g x).

Lemma eq_comp : forall f f' g g', f =1 f' -> g =1 g' -> comp f g =1 comp f' g'.
Proof. by move=> f f' g g' Ef Eg x; rewrite /comp Eg Ef. Qed.

End Composition.

Prenex Implicits id.

(* Simple iteration (`for' loops!), indexed and unindexed.                  *)

Section Iteration.

Variable A : Type.

Definition iter_n n f x :=
  let fix loop (m : nat) : A := if m is S i then f i (loop i) else x in loop n.

Definition iter n f x :=
  let fix loop (m : nat) : A := if m is S i then f (loop i) else x in loop n.

Lemma iter_f : forall n f x, iter n f (f x) = iter (S n) f x.
Proof. by move=> n f x; elim: n => [|n Hrec] //; congr f. Qed.

Lemma f_iter : forall n f x, f (iter n f x) = iter (S n) f x.
Proof. done. Qed.

Lemma eq_iter : forall f f', f =1 f' -> forall n, iter n f =1 iter n f'.
Proof. by move=> f f' Ef n; elim: n => [|n Hrec] x //=; rewrite Ef Hrec. Qed.

Lemma eq_iter_n : forall f f', f =2 f' -> forall n, iter_n n f =1 iter_n n f'.
Proof. by move=> f f' Ef; elim=> [|n Hrec] x //=; rewrite Ef Hrec. Qed.

End Iteration.

(* In an intuitionistic setting, we have two degrees of injectivity. The     *)
(* weaker one gives only simplification, and the strong one provides a left  *)
(* inverse (we show in `finset' that they coincide for finite types).        *)
(* (The definition could be further weakened if equality on A is not         *)
(* decidable, to ~ x = y -> ~ (f x) = (f y), but this doesn't seem useful.)  *)

Section Injections.

Variables (A B : Type) (f : B -> A) (g : A -> B).

Definition injective : Prop := forall x x' : B, f x = f x' -> x = x'.

Definition monic : Prop := forall x, g (f x) = x.
Hypothesis Hf : monic.

Lemma monic_move : forall x y, f x = y -> x = g y.
Proof. by move=> x y <-. Qed.

Lemma monic_inj : injective.
Proof. by move=> x y Ef; rewrite (monic_move Ef). Qed.

End Injections.

Section InjectionsTheory.

Variables (A B C : Type) (f f' : B -> A) (g g' : A -> B) (h : C -> B) (k : B -> C).
Hypotheses (Hf : injective f) (Hfg : monic f g) (Hg : injective g).
Hypotheses (Hh : injective h) (Hhk : monic h k).

Lemma inj_monic_sym : monic g f. Proof. by move=> x; apply: Hg. Qed.

Lemma inj_comp : injective (comp f h). Proof. move=> x y; move/Hf; apply: Hh. Qed.

Lemma monic_comp : monic (comp f h) (comp k g).
Proof. by move=> x; rewrite /comp Hfg Hhk. Qed.

Lemma eq_injective : f =1 f' -> injective f'.
Proof. move=> Ef x y; rewrite -2!Ef; apply Hf. Qed.

Lemma eq_monic : f =1 f' -> g =1 g' -> monic f' g'.
Proof. by move=> Ef Eg x; rewrite -Ef -Eg. Qed.

Lemma inj_monic_eq : monic f' g -> f =1 f'.
Proof. by move=> Hf'g x; apply: Hg; transitivity x. Qed.

End InjectionsTheory.

Section Isos.

Variables (A B : Type) (f : B -> A).

Definition iso : Prop := exists2 g, monic f g & monic g f.

Hypothesis Hf : iso.

Lemma iso_inj : injective f.
Proof. by case: Hf => [h Ef _]; apply: monic_inj Ef. Qed.

Lemma monic_iso_sym : forall g, monic g f -> monic f g.
Proof. move=> g Eg; apply: inj_monic_sym Eg iso_inj. Qed.

Lemma iso_monic_sym : forall g, monic f g -> monic g f.
Proof. by move=> g Eg x; case: Hf => [h _ Eh]; case (Eh x); congr f. Qed.

Lemma iso_monic_eq : forall g g', monic f g -> monic f g' -> g =1 g'.
Proof.
move=> g g' Eg Eg'; apply: (inj_monic_eq _ iso_inj); apply iso_monic_sym; auto.
Qed.

End Isos.

Section IsosTheory.

Variables (A B C : Type) (f : B -> A) (g : C -> B).

Lemma eq_iso : iso f -> forall f', f =1 f' -> iso f'.
Proof.
move=> [h Ef Eh] f' Eff'.
by exists h; [ apply: (eq_monic Ef) | apply: (eq_monic Eh) ]; auto.
Qed.

Lemma iso_comp : iso f -> iso g -> iso (comp f g).
Proof.
move=> [h Ef Eh] [k Eg Ek]; exists (comp k h); apply monic_comp; auto.
Qed.

Lemma iso_monic_iso : iso f -> forall h, monic f h -> iso h.
Proof. by move=> Hf; exists f; first by apply iso_monic_sym. Qed.

End IsosTheory.

Unset Implicit Arguments.








