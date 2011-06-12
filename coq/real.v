(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(* Definitions for generic reals -- no prerequisites, no syntax extensions. *)
(* The definition has three parts: we define separately the structure       *)
(* (carrier + operations), the axioms (for a complete totally ordered       *)
(* field); a model is then a structure + axioms record. We also define      *)
(* (mono)morphisms between structures here, for completeness, although it   *)
(* won't be used in "normal" developments on the reals: it's used to        *)
(* show the categorical uniqueness of the real model. We also construct one *)
(* such model, using the (classical) Dedekind construction.                 *)
(*   We axiomatize the reals as a setoid, so that we do not need to rely on *)
(* (strong) extensionality axioms in the construction. The downside of this *)
(* is that real equality (defined as "eqr" below) is not the Leibnitz       *)
(* equality, so we need to use the much less convenient setoid rewriting    *)
(* for equational reasoning. Note that the real axioms we take imply that   *)
(* the arithmetic operations are extensional with respect to eqr -- except  *)
(* taking the inverse of 0. The latter is a problem because it precludes    *)
(* setoid rewriting in denominators -- it might be worth setting 1/0 = 0 to *)
(* just to elude this problem.                                              *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Record real_structure : Type := RealStructure {
   real_carrier : Type;
   leqr : real_carrier -> real_carrier -> Prop;
   supr : (real_carrier -> Prop) -> real_carrier;
   addr : real_carrier -> real_carrier -> real_carrier;
   real0 : real_carrier;
   oppr : real_carrier -> real_carrier;
   mulr : real_carrier -> real_carrier -> real_carrier;
   real1 : real_carrier;
   invr : real_carrier -> real_carrier
}.

Coercion real_carrier : real_structure >-> Sortclass.

Section BasicRealOperations.

(* A few basic derived operations and relations, used in the real axioms. *)
(* The injection from N to R is used to define the semantics of literals  *)
(* in the abstract syntax.                                                *)

Variable R : real_structure.

Definition eqr (x1 x2 : R) := leqr x1 x2 /\ leqr x2 x1.

Definition hasr (E : R -> Prop) := exists x, E x.

Definition ubr (E : R -> Prop) (y : R) : Prop := forall x, E x -> leqr x y.

Definition has_supr (E : R -> Prop) : Prop := hasr E /\ hasr (ubr E).

Definition boundedr (x : R) (E : R -> Prop) := exists2 y, E y & leqr x y.

Fixpoint addnr (n : nat) (x : R) {struct n} : R :=
  match n with S n' => addnr n' (addr (real1 R) x) | O => x end.

Definition natr (n : nat) : R :=
  match n with S n' => addnr n' (real1 R) | O => real0 R end.

End BasicRealOperations.

Notation ltr := (fun x1 x2 => ~ leqr x2 x1).
Notation neqr := (fun x1 x2 => ~ eqr x1 x2).

(* This presentation of the reals is intrinsically classical; the axioms    *)
(* below imply the excluded middle (the least upper bound totality axiom is *)
(* somewhat contrived in order to achieve this). The supremum axioms also   *)
(* imply that the ordering is total.                                        *)
(* Conversely, the usual Dedekind cut construction produces a real model,   *)
(* assuming only the excluded middle; in that case we make the assumption   *)
(* explicit, using the definition below.                                    *)
(*   To summarize, we have                                                  *)
(*     Theorem dedekind_reals : excluded_middle -> real_model.              *)
(*     Lemma reals_classic : real_model -> excluded_middle.                 *)

Definition excluded_middle := forall P : Prop, P \/ ~ P.

Record real_axioms (R : real_structure) : Prop := RealAxioms {
  leqr_reflexivity :
    forall x : R, leqr x x;
  leqr_transitivity :
    forall x1 x2 x3 : R, leqr x1 x2 -> leqr x2 x3 -> leqr x1 x3;
  supr_upper_bound :
    forall E : R -> Prop, has_supr E -> ubr E (supr E);
  supr_totality :
    forall (x : R) (E : R -> Prop), has_supr E -> boundedr x E \/ leqr (supr E) x;
  addr_monotony :
    forall x1 x2 x3 : R, leqr x2 x3 -> leqr (addr x1 x2) (addr x1 x3);
  addr_commutativity :
    forall x1 x2 : R, eqr (addr x1 x2) (addr x2 x1);
  addr_associativity :
    forall x1 x2 x3 : R, eqr (addr x1 (addr x2 x3)) (addr (addr x1 x2) x3);
  addr_neutral_left :
    forall x : R, eqr (addr (real0 R) x) x;
  addr_inverse_right :
    forall x : R, eqr (addr x (oppr x)) (real0 R);
  mulr_monotony :
    forall x1 x2 x3 : R,
    leqr (real0 R) x1 -> leqr x2 x3 -> leqr (mulr x1 x2) (mulr x1 x3);
  mulr_commutativity :
    forall x1 x2 : R, eqr (mulr x1 x2) (mulr x2 x1);
  mulr_associativity :
    forall x1 x2 x3 : R, eqr (mulr x1 (mulr x2 x3)) (mulr (mulr x1 x2) x3);
  mulr_addr_distributivity_right :
    forall x1 x2 x3 : R,
    eqr (mulr x1 (addr x2 x3)) (addr (mulr x1 x2) (mulr x1 x3));
  mulr_neutral_left :
    forall x : R, eqr (mulr (real1 R) x) x;
  mulr_inverse_right :
    forall x : R, neqr x (real0 R) -> eqr (mulr x (invr x)) (real1 R);
  mulr_neutral_nonzero :
    neqr (real1 R) (real0 R)
}.

Record real_model : Type := RealModel {
  real_model_structure :> real_structure;
  real_model_axioms :> real_axioms real_model_structure
}.

Section RealStructureMorphismDefinition.

Variable R R' : real_structure.

(* (Strict) image of an arbitrary set of reals. *)

Definition imager (phi : R -> R') (E : R -> Prop) (x' : R') :=
  exists2 x, phi x = x' & E x.

(* We use monomorphisms, so we can lift real axioms in R' back to R. *)

Record real_structure_morphism (phi : R -> R') : Prop := RealStructureMorphism {
  morphr_leq :
    forall x1 x2 : R, leqr (phi x1) (phi x2) <-> leqr x1 x2;
  morphr_sup :
    forall E : R -> Prop, has_supr E -> eqr (phi (supr E)) (supr (imager phi E));
  morphr_add :
    forall x1 x2 : R, eqr (phi (addr x1 x2)) (addr (phi x1) (phi x2));
  morphr_0 :
    eqr (phi (real0 R)) (real0 R');
  morphr_opp :
    forall x : R, eqr (phi (oppr x)) (oppr (phi x));
  morphr_mul :
    forall x1 x2 : R, eqr (phi (mulr x1 x2)) (mulr (phi x1) (phi x2));
  morphr_1 :
    eqr (phi (real1 R)) (real1 R');
  morphr_inv :
    forall x : R, neqr x (real0 R) -> eqr (phi (invr x)) (invr (phi x))
}.

End RealStructureMorphismDefinition.

Set Strict Implicit.
Unset Implicit Arguments.