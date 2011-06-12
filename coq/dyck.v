(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ``Dyck numbers'', i.e., the number of balanced bracket words of length n. *)
(* (In fact, we define generalized Dyck numbers, that allow for m-1 extra    *)
(* closing brackets.) Dyck numbers are the only link between the initial     *)
(* color and (chromo)gram trees.                                             *)

Fixpoint gen_dyck (m n : nat) {struct n} : nat :=
  match n, m with
  | O, S O => 1
  | S n', S m' => gen_dyck (S m) n' + gen_dyck m' n'
  | _, _ => 0
  end.

Definition dyck : nat -> nat := gen_dyck 1.

Lemma gen_dyck_max : forall m n, S n < m -> gen_dyck m n = 0.
Proof.
move=> m n; elim: n m => [|n Hrec] [|m] //; first by case m.
move=> Hm; rewrite /= !Hrec //; exact (leq_trans (leq_addl 2 n) Hm).
Qed.

Lemma gen_dyck_all_close : forall m, gen_dyck (S m) m = 1.
Proof.
elim=> [|m Hrec] //=; rewrite Hrec gen_dyck_max //; exact (leqnSn m).
Qed.

Lemma even_dyck_pos : forall n, 0 < dyck (double n).
Proof.
move=> n; rewrite /dyck -(addn0 (double n)).
elim: n {-1}0 => [|n Hrec] m; first by rewrite gen_dyck_all_close.
rewrite doubleS addSnnS addSn; exact (leq_trans (Hrec _) (leq_addr _ _)).
Qed.

Unset Implicit Arguments.