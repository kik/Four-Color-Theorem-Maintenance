(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.

Module SsrSyntax.

(* Declare Ssr keywords: 'is' 'by' '//' '/=' and '//='.                     *)
(* We also declare the parsing level 8, as a workaround for a notation      *)
(* grammar factoring problem. Arguments of application-style notations      *)
(* (at level 10) should be declared at level 8 rather than 9 or the camlp4  *)
(* grammar will not factor properly.                                        *)

Reserved Notation "'(*' x 'is' y 'by' '//' '/=' '//='" (at level 8).

Delimit Scope boolean_if_scope with BOOL_IF.
Delimit Scope general_if_scope with GEN_IF.

(* Make the general "if" into a notation, so that we can override it below *)
Notation "'if' c 'then' v1 'else' v2" :=
         (if c then v1 else v2)
         (at level 200, c, v1, v2 at level 200) : general_if_scope.

Notation "'if' c 'as' x 'return' t 'then' v1 'else' v2" :=
         (if c as x return t then v1 else v2)
         (at level 200, c, t, v1, v2 at level 200, x ident) : general_if_scope.

Open Scope general_if_scope.

(* Force boolean interpretation of simple if expressions.                  *)
(* The Coq printer doesn't recognize notations that contain a 'match', so  *)
(* these notations are, in effect, "only parsing".                         *)
Notation "'if' c 'then' v1 'else' v2" :=
         (if c%bool is true then v1 else v2)
         : boolean_if_scope.

(* The (fun x => t) is a workaround for a scoping bug in Coq v8.0 notation *)
(* expansion; fortunately it's beta-expanded by the "match" compiler, so   *)
(* it will only show up as an alpha-conversion of the "as" variable.       *)
Notation "'if' c 'as' x 'return' t 'then' v1 'else' v2" :=
         (match c%bool as b return (fun x => t) b with true => v1 | _ => v2 end)
         : boolean_if_scope.

End SsrSyntax.

Export SsrSyntax.

Open Scope boolean_if_scope.

Definition protect_term (A : Type) (x : A) : A := x.

Lemma eq_protect_rect : forall A x (P : A -> Type),
  protect_term P x -> forall y, x = y -> P y.
Proof. move=> A x P Hx y <-; exact Hx. Qed.

(** Term tagging (user-level).                                              *)
(* We provide two strengths of term tagging :                               *)
(*  - (nosimpl t) simplifies to t EXCEPT in a definition; more precisely,   *)
(*    given Definition foo := (nosimpl bar), foo (or (foo t')) will NOT be  *)
(*    expanded by the simpl tactic unless it is in a forcing context (e.g., *)
(*    in match foo t' with ... end, foo t' will be reduced if this allows   *)
(*    match to be reduced. Note that nosimpl bar is simply notation for     *)
(*    a term that beta-iota reduces to bar; hence unfold foo will replace   *)
(*    foo by bar, and fold foo will replace bar by foo. A final warning:    *)
(*    nosimpl only works if no reduction is apparent in t; in particular    *)
(*    Definition foo x := nosimpl t. will usually not work.                 *)
(*  - (locked t) is provably equal to t, but is not convertible to t; it    *)
(*    provides support for abstract data types, and selective rewriting.    *)
(*    The equation t == (locked t) is provided as a lemma, but it should    *)
(*    only be used for selective rewriting (see below). For ADTs, the       *)
(*    unlock tactic should be used to remove locking.                       *)

Notation "'nosimpl' t" := (let: tt := tt in t) (at level 10, t at level 8).

Lemma master_key : unit. Proof. exact tt. Qed.

Definition locked A := let: tt := master_key in fun x : A => x.

Lemma lock : forall A x, x = locked x :> A. Proof. unlock; split. Qed.

(* Needed for locked predicates, in particular for dataSet. *)
Lemma not_locked_false_eq_true : locked false <> true.
Proof. unlock; discriminate. Qed.

(* The basic closing tactic "done".                                       *)
Ltac done :=
  trivial; hnf; intros; solve
   [ trivial
   | contradiction
   | discriminate
   | repeat split
   | case not_locked_false_eq_true; assumption
   | apply: sym_equal; trivial ].

(* The internal lemmas for the have tactics.                                *)
Definition ssr_have Plemma Pgoal (step : Plemma) rest : Pgoal := rest step.
Implicit Arguments ssr_have [Pgoal].

Definition ssr_suffice Plemma Pgoal step (rest : Plemma) : Pgoal := step rest.
Implicit Arguments ssr_suffice [Pgoal].

(* Internal  N-ary congruence lemma for the congr tactic *)

Fixpoint nary_congruence_statement (n : nat)
         : (forall B, (B -> B -> Prop) -> Prop) -> Prop :=
  match n with
  | O => fun k => forall B, k B (fun x1 x2 : B => x1 = x2)
  | S n' =>
    let k' A B e (f1 f2 : A -> B) :=
      forall x1 x2, x1 = x2 -> (e (f1 x1) (f2 x2) : Prop) in
    fun k => forall A, nary_congruence_statement n' (fun B e => k _ (k' A B e))
  end.

Lemma nary_congruence : forall n : nat,
 let k B e := forall y : B, (e y y : Prop) in nary_congruence_statement n k.
Proof.
move=> n k; have: k _ _ := _; rewrite {1}/k.
elim: n k  => [|n Hrec] k Hk /= A; auto.
by apply: Hrec => B e He; apply: Hk => f x1 x2 <-.
Qed.

(* Coercion bool >-> Prop and reflection predicate.                    *)

Coercion is_true b := b = true.

Ltac FoldIsTrue := match goal with |- (?X1 = true) => change (is_true X1) end.

Lemma prop_congr : forall b b' : bool, b = b' -> b = b' :> Prop.
Proof. by move=> b b' ->. Qed.

Ltac PropCongr := apply: prop_congr.

(* View lemmas that don't use reflection.                       *)
Section ViewLemmas.

Variables (b : bool) (P Q : Prop).

Lemma if_negE_Prop : (if b then Q else P) -> if negb b then P else Q.
Proof. by case b. Qed.

Lemma if_negI_Prop : (if negb b then P else Q) -> if b then Q else P.
Proof. by case b. Qed.

Lemma iff_l2r : (P <-> Q) -> P -> Q. Proof. by case. Qed.
Lemma iff_r2l : (P <-> Q) -> Q -> P. Proof. by case. Qed.

End ViewLemmas.

(* Lemmas for done. *)
Lemma is_true_true : true. Proof. done. Qed.
Lemma not_is_true_false : ~ false. Proof. done. Qed.
Lemma is_true_locked_true : locked true. Proof. by unlock. Qed.
Lemma not_is_true_locked_false : ~ locked false. Proof. done. Qed.
Hint Resolve is_true_true is_true_locked_true.
Hint Resolve not_is_true_false not_is_true_locked_false.

(* The reflection predicate.                                          *)

Inductive reflect (P : Prop) : bool -> Set :=
  | Reflect_true : P -> reflect P true
  | Reflect_false : ~ P -> reflect P false.

(* Core (internal) reflection lemmas, used for the three kinds of views. *)

Section ReflectCore.

Variables (P Q : Prop) (b c : bool).

Hypothesis Hb : reflect P b.

Lemma introNTF : (if c then ~ P else P) -> negb b = c.
Proof. case c; case Hb; tauto. Qed.

Lemma introTF : (if c then P else ~ P) -> b = c.
Proof. case c; case Hb; tauto. Qed.

Lemma elimNTF : negb b = c -> if c then ~ P else P.
Proof. by move <-; case Hb. Qed.

Lemma elimTF : b = c -> if c then P else ~ P.
Proof. by move <-; case Hb. Qed.

Lemma equivPif : (Q -> P) -> (P -> Q) -> if b then Q else ~ Q.
Proof. case Hb; tauto. Qed.

Lemma equivPifn : Q \/ P -> ~ (Q /\ P) -> if b then ~ Q else Q.
Proof. case Hb; tauto. Qed.

End ReflectCore.

(* Internal negated reflection lemmas *)
Section ReflectNegCore.

Variables (P : Prop) (b c : bool).
Hypothesis Hb : reflect P (negb b).

Lemma introTFn : (if c then ~ P else P) -> b = c.
Proof. by move/(introNTF Hb) => <-; case b. Qed.

Lemma elimTFn : b = c -> if c then ~ P else P.
Proof. by move <-; apply: (elimNTF Hb); case b. Qed.

End ReflectNegCore.

(* User-oriented reflection lemmas *)
(* We still can't use the view feature here, because the ML implementation *)
(* of views refers to this file.                                           *)
Section Reflect.

Variables (P Q : Prop) (b b' c : bool).
Hypotheses (Hb : reflect P b) (Hb' : reflect P (negb b')).

Lemma introT  : P -> b.              Proof. exact: introTF true _. Qed.
Lemma introF  : ~P -> b = false.     Proof. exact: introTF false _. Qed.
Lemma introN  : ~P -> negb b.        Proof. exact: introNTF true _. Qed.
Lemma introNf : P -> negb b = false. Proof. exact: introNTF false _. Qed.
Lemma introTn  : ~P -> b'.           Proof. exact: introTFn true _. Qed.
Lemma introFn  : P -> b' = false.    Proof. exact: introTFn false _. Qed.

Lemma elimT  : b -> P.               Proof. exact: elimTF true _. Qed.
Lemma elimF  : b = false -> ~P.      Proof. exact: elimTF false _. Qed.
Lemma elimN  : negb b -> ~P.         Proof. exact: elimNTF true _. Qed.
Lemma elimNf : negb b = false -> P.  Proof. exact: elimNTF false _. Qed.
Lemma elimTn  : b' -> ~P.            Proof. exact: elimTFn true _. Qed.
Lemma elimFn  : b' = false -> P.     Proof. exact: elimTFn false _. Qed.

Lemma introP : (b -> Q) -> (negb b -> ~ Q) -> reflect Q b.
Proof. case b; constructor; auto. Qed.

Lemma iffP : (P -> Q) -> (Q -> P) -> reflect Q b.
Proof. case: {b' Hb'}Hb; constructor; tauto. Qed.

Lemma appP : reflect Q b -> P -> Q.
Proof. by move=> HbQ; move/introT; case: HbQ. Qed.

Lemma sameP : reflect P c -> b = c.
Proof. case; [exact: introT | exact: introF]. Qed.

Lemma equivP : reflect Q c -> (P -> Q) -> (Q -> P) -> b = c.
Proof. case; case Hb; tauto. Qed.

Lemma equivNP : reflect Q c -> P \/ Q -> ~ (P /\ Q) -> negb b = c.
Proof. case; case Hb; tauto. Qed.

Lemma decP : {P} + {~ P}.
Proof. case Hb; auto. Qed.

End Reflect.

(* Allow to apply directly a reflection lemma to a boolean assertion.  *)
Coercion elimT : reflect >-> Funclass.

Unset Implicit Arguments.

