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
Require Import color.
Require Import geometry.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*    These "parts" are patterns for performing local matching on graphs. *)
(* Specifically, a part specifies ranges of arities for darts in the      *)
(* second neighborhood of some match anchor x, using the "prange" type    *)
(* below to specify ranges.                                               *)
(*   A part is broken into a sequence of subparts, with each subpart      *)
(* specifying arities in successive sectors around the "hub" x, following *)
(* a counterclockwise order. Each subpart comprises a "spoke" (darts      *)
(* immediately adjacent to x; the spoke of the first sector is the face   *)
(* orbit of (edge x)), a "hat" (non-hub darts adjacent to this spoke and  *)
(* the previous spoke; (edge (face (face (edge x)))) is in the hat of the *)
(* first spoke), and "fans" (other darts adjacent to the spoke, listed    *)
(* counterclockwise). This is a partition; the hat of the next spoke is   *)
(* not a fan of the current one.                                          *)
(*   A part fits a dart x when all its subparts fit x, (face x), etc,     *)
(* respectively; it fits exactly when, in addition, its length is equal   *)
(* to the arity of x.                                                     *)
(*   Because parts are created and traversed in the inner loop of the     *)
(* unavoidability checks their representation is somewhat optimised. The  *)
(* list structure is merged into the record structure, and there are four *)
(* different kinds of parts, according to the number of (known) fans. The *)
(* spoke arity is always fixed when there are known fans (e.g., if there  *)
(* are two known fans, the spoke is a heptagon). The converse isn't true, *)
(* in fact we never use the explicit fan form when there are no           *)
(* nontrivial fan constraints (this simplifies the converse part          *)
(* computation, but isn't strictly necessary for correctness).            *)
(*   Parts are used throughout the unavoidability check: to specify the   *)
(* arity discharging procedure and its rules, to enumerate all possible   *)
(* second neighborhoods, to check for the presence of a reducible         *)
(* configuration. If x fits p, we check whether a discharge rule applies  *)
(* to x by comparing p to the part r of the rule; we force the            *)
(* application of the rule by intersecting p with r (function meet_part   *)
(* below); we check whether a reducible map appears near x by applying    *)
(* its quiz to the part ranges in p (file redpart).                       *)
(*   This file contains the formal definition of "fit", and the basic     *)
(* operations on parts :                                                  *)
(*    - size_part, cat_part, take_part, drop_part, rot_part, catrev_part, *)
(*      rev_part : list operations.                                       *)
(*    - mirror_part : reflection along the first spoke (similar, but not  *)
(*      identical to rev_part).                                           *)
(*    - converse_part : reflection across the first spoke.                *)
(*    - split_part : restricting a specific range in the part.            *)
(* The converse_part operation is only used to compute converse discharge *)
(* rules, and is (safely) approximate : upon reflection, some ranges      *)
(* may fall outside the second neighborhood. This never happens with the  *)
(* parts given in discharge.v; in fact, we've somewhat tailored the       *)
(* function to that data; there are a few other cases where it over       *)
(* approximates because such cases don't arise with our data.             *)
(*   Some of the internal accessors/updators defined here are also used   *)
(* in redpart.v to implement zipped parts.                                *)

(* PrMN stands for the range M..N; N=9 actually means infinity, e.g, Pr59 *)
(* means any arity greater than or equal to 5, that is any arity in a     *)
(* pentagonal map.                                                        *)
Inductive prange : Set :=
  | Pr55 | Pr66 | Pr77 | Pr88 | Pr99
  | Pr56 | Pr67 | Pr78 | Pr89
  | Pr57 | Pr68 | Pr79
  | Pr58 | Pr69
  | Pr59.

Inductive part : Set :=
  | Pnil
  | Pcons (spk hat : prange) (p' : part)
  | Pcons6 (hat fan1 : prange) (p' : part)
  | Pcons7 (hat fan1 fan2 : prange) (p' : part)
  | Pcons8 (hat fan1 fan2 fan3 : prange) (p' : part).

Lemma prangeDataP : comparable prange.
Proof. rewrite /comparable. decide equality. Qed.
Lemma partDataP : comparable part.
Proof. rewrite /comparable. decide equality; apply prangeDataP. Qed.
Definition partData : dataSet := Eval compute in compareData partDataP.
Canonical Structure partData.

Inductive subpart_loc : Set := Pspoke | Phat | Pfan1 | Pfan2 | Pfan3.

Module PartSyntax.

Notation "5" := 5 : nat_scope.
Notation "6" := 6 : nat_scope.
Notation "7" := 7 : nat_scope.
Notation "8" := 8 : nat_scope.

Notation "5" := Pr55 : prange_scope.
Notation "6" := Pr66 : prange_scope.
Notation "7" := Pr77 : prange_scope.
Notation "8" := Pr88 : prange_scope.

Notation "*" := Pr59 (at level 0) : prange_scope.
Notation "6 +" := Pr69 (at level 0, format "6 +") : prange_scope.
Notation "7 +" := Pr79 (at level 0, format "7 +") : prange_scope.
Notation "8 +" := Pr89 (at level 0, format "8 +") : prange_scope.
Notation "9 +" := Pr99 (at level 0, format "9 +") : prange_scope.

Notation "6 -" := Pr56 (at level 0, format "6 -") : prange_scope.
Notation "7 -" := Pr57 (at level 0, format "7 -") : prange_scope.
Notation "8 -" := Pr58 (at level 0, format "8 -") : prange_scope.

Notation "6 : 7" := Pr67 (at level 0, format "6 : 7") : prange_scope.
Notation "6 : 8" := Pr68 (at level 0, format "6 : 8") : prange_scope.
Notation "7 : 8" := Pr78 (at level 0, format "7 : 8") : prange_scope.

Bind Scope part_scope with part.
Arguments Scope Pcons [prange_scope prange_scope part_scope].
Arguments Scope Pcons6 [prange_scope prange_scope part_scope].
Arguments Scope Pcons7 [prange_scope prange_scope prange_scope part_scope].
Arguments Scope Pcons8 [prange_scope prange_scope prange_scope prange_scope
                        part_scope].

Definition Part (p : part) := p.

Notation "'[]'" := Pnil (at level 8) : part_scope.
Notation "[ h ] s p" := (Pcons s h p)
  (at level 8, s, h at level 0, p at level 9,
   format "[ h ]  s  p") : part_scope.
Notation "'[]' s p" := (Pcons s Pr59 p)
  (at level 8, s at level 0, p at level 9,
   format "[]  s  p") : part_scope.
Notation "[ h f1 ] 6 p" := (Pcons6 h f1 p)
  (at level 8, h, f1 at level 0, p at level 9,
   format "[ h  f1 ]  6  p") : part_scope.
Notation "[ h f1 f2 ] 7 p" := (Pcons7 h f1 f2 p)
  (at level 8, h, f1, f2 at level 0, p at level 9,
   format "[ h f1 f2 ]  7  p") : part_scope.
Notation "[ h f1 f2 f3 ] 8 p" := (Pcons8  h f1 f2 f3 p)
  (at level 8, h, f1, f2, f3 at level 0, p at level 9,
   format "[ h f1 f2 f3 ]  8  p") : part_scope.

End PartSyntax.

Module SublocSyntax.

Definition s := Pspoke.
Definition h := Phat.
Definition f1 := Pfan1.
Definition f2 := Pfan2.
Definition f3 := Pfan3.

End SublocSyntax.

(* Shorthand for making (mostly) empty parts.                                 *)

Definition pcons_s s := Pcons s Pr59.

Definition pcons_ n := iter n (Pcons Pr59 Pr59) Pnil.

(* Range semantics.                                                           *)

Definition mem_range r :=
  match r with
  | Pr55 => set1 5
  | Pr66 => set1 6
  | Pr77 => set1 7
  | Pr88 => set1 8
  | Pr56 => set2 5 6
  | Pr67 => set2 6 7
  | Pr78 => set2 7 8
  | Pr57 => set3 5 6 7
  | Pr68 => set3 6 7 8
  | Pr58 => set4 5 6 7 8
  | Pr59 => leq 5
  | Pr69 => leq 6
  | Pr79 => leq 7
  | Pr89 => leq 8
  | Pr99 => leq 9
  end.

Coercion mem_range : prange >-> Funclass.

(* Part/range comparison results; Pstraddle covers all the remaining cases,  *)
(* including when the left hand side stricly contains the right hand side.   *)
(* We use the result of a comparison by applying it to a "fit" predicate.    *)

Inductive part_rel : Set := Pdisjoint | Pstraddle | Psubset.

Definition apply_part_rel pr b :=
  match pr with
  | Pdisjoint => false
  | Psubset => true
  | _ => b
  end.

Coercion apply_part_rel : part_rel >-> Funclass.

Definition notPsubset c := if c is Psubset then Pstraddle else c.

Definition meet_prel c c' :=
  match c with
  | Pdisjoint => c
  | Psubset => c'
  | Pstraddle => notPsubset c'
  end.

(* Range comparison and meet.                                                 *)

Definition cmp_range r r' :=
  match r', r with
  | Pr59, _    => Psubset
  | _ ,   Pr59 => Pstraddle
  | Pr69, Pr55 => Pdisjoint
  | Pr69, Pr56 => Pstraddle
  | Pr69, Pr57 => Pstraddle
  | Pr69, Pr58 => Pstraddle
  | Pr69, _    => Psubset
  | Pr55, Pr69 => Pdisjoint
  | _,    Pr69 => Pstraddle
  | Pr58, Pr99 => Pdisjoint
  | Pr58, Pr89 => Pstraddle
  | Pr58, Pr79 => Pstraddle
  | Pr58, _    => Psubset
  | Pr99, Pr58 => Pdisjoint
  | _,    Pr58 => Pstraddle
  | Pr55, Pr55 => Psubset
  | Pr55, Pr56 => Pstraddle
  | Pr55, Pr57 => Pstraddle
  | Pr55, _    => Pdisjoint
  | Pr56, Pr55 => Psubset
  | Pr57, Pr55 => Psubset
  | _,    Pr55 => Pdisjoint
  | Pr99, Pr99 => Psubset
  | Pr99, Pr89 => Pstraddle
  | Pr99, Pr79 => Pstraddle
  | Pr99, _    => Pdisjoint
  | Pr89, Pr99 => Psubset
  | Pr79, Pr99 => Psubset
  | _,    Pr99 => Pdisjoint
  | Pr66, Pr66 => Psubset
  | Pr66, Pr56 => Pstraddle
  | Pr66, Pr57 => Pstraddle
  | Pr66, Pr67 => Pstraddle
  | Pr66, Pr68 => Pstraddle
  | Pr66, _    => Pdisjoint
  | Pr56, Pr66 => Psubset
  | Pr57, Pr66 => Psubset
  | Pr67, Pr66 => Psubset
  | Pr68, Pr66 => Psubset
  | _,    Pr66 => Pdisjoint
  | Pr88, Pr88 => Psubset
  | Pr88, Pr89 => Pstraddle
  | Pr88, Pr79 => Pstraddle
  | Pr88, Pr78 => Pstraddle
  | Pr88, Pr68 => Pstraddle
  | Pr88, _    => Pdisjoint
  | Pr89, Pr88 => Psubset
  | Pr79, Pr88 => Psubset
  | Pr78, Pr88 => Psubset
  | Pr68, Pr88 => Psubset
  | _,    Pr88 => Pdisjoint
  | Pr77, Pr77 => Psubset
  | Pr77, Pr56 => Pdisjoint
  | Pr77, Pr89 => Pdisjoint
  | Pr77, _    => Pstraddle
  | Pr56, Pr77 => Pdisjoint
  | Pr89, Pr77 => Pdisjoint
  | _,    Pr77 => Psubset
  | Pr68, Pr68 => Psubset
  | Pr68, Pr67 => Psubset
  | Pr68, Pr78 => Psubset
  | Pr68, _    => Pstraddle
  | _,    Pr68 => Pstraddle
  | Pr67, Pr67 => Psubset
  | Pr67, Pr89 => Pdisjoint
  | Pr67, _    => Pstraddle
  | Pr57, Pr67 => Psubset
  | Pr89, Pr67 => Pdisjoint
  | _,    Pr67 => Pstraddle
  | Pr78, Pr78 => Psubset
  | Pr78, Pr56 => Pdisjoint
  | Pr78, _    => Pstraddle
  | Pr79, Pr78 => Psubset
  | Pr56, Pr78 => Pdisjoint
  | _,    Pr78 => Pstraddle
  | Pr89, Pr56 => Pdisjoint
  | Pr79, Pr56 => Pdisjoint
  | _,    Pr56 => Psubset
  | Pr56, Pr57 => Pstraddle
  | Pr56, _    => Pdisjoint
  | Pr57, Pr89 => Pdisjoint
  | _,    Pr89 => Psubset
  | Pr89, Pr79 => Pstraddle
  | Pr89, _    => Pdisjoint
  | Pr57, Pr57 => Psubset
  | Pr79, Pr79 => Psubset
  | _,    _    => Pstraddle
  end.

Definition meet_range r r' :=
  match r', r with
  | Pr56, Pr67 => Pr66
  | Pr56, Pr68 => Pr66
  | Pr56, Pr69 => Pr66
  | Pr67, Pr56 => Pr66
  | Pr68, Pr56 => Pr66
  | Pr69, Pr56 => Pr66
  | Pr57, Pr78 => Pr77
  | Pr57, Pr79 => Pr77
  | Pr67, Pr78 => Pr77
  | Pr67, Pr79 => Pr77
  | Pr78, Pr57 => Pr77
  | Pr79, Pr57 => Pr77
  | Pr78, Pr67 => Pr77
  | Pr79, Pr67 => Pr77
  | Pr89, Pr58 => Pr88
  | Pr89, Pr68 => Pr88
  | Pr89, Pr78 => Pr88
  | Pr58, Pr89 => Pr88
  | Pr68, Pr89 => Pr88
  | Pr78, Pr89 => Pr88
  | Pr57, Pr68 => Pr67
  | Pr57, Pr69 => Pr67
  | Pr68, Pr57 => Pr67
  | Pr69, Pr57 => Pr67
  | Pr79, Pr58 => Pr78
  | Pr79, Pr68 => Pr78
  | Pr58, Pr79 => Pr78
  | Pr68, Pr79 => Pr78
  | Pr58, Pr69 => Pr68
  | Pr69, Pr58 => Pr68
  | Pr59, _    => r
  | _,    Pr59 => r'
  | Pr58, _    => r
  | Pr69, _    => r
  | _,    Pr58 => r'
  | _,    Pr69 => r'
  | Pr57, _    => r
  | Pr68, _    => r
  | Pr79, _    => r
  | _,    Pr57 => r'
  | _,    Pr68 => r'
  | _,    Pr79 => r'
  | Pr56, _    => r
  | Pr67, _    => r
  | Pr78, _    => r
  | Pr89, _    => r
  | _,    Pr56 => r'
  | _,    Pr67 => r'
  | _,    Pr78 => r'
  | _,    _    => r'
  end.

Lemma mem_cmp_range : forall (r : prange) n, r n ->
  forall r' : prange, r' n = cmp_range r r' (r' n).
Proof.
by move=> r; move=> [|[|[|[|[|[|[|[|[|n]]]]]]]]]; case: r => // _; case.
Qed.

Lemma mem_meet_range : forall (r r' : prange) n, r n -> r' n -> meet_range r r' n.
Proof.
by move=> r r' [|[|[|[|[|[|[|[|[|n]]]]]]]]]; case: r => // _; case r'.
Qed.

(* List-like operations on parts. Most also have a geometric meaning, exept   *)
(* "rev_part", which is just a subroutine for the implementation of zipped    *)
(* parts in redpart.v.                                                        *)

Fixpoint size_part (p : part) : nat :=
  match p with
  | Pnil              => 0
  | Pcons _ _ p'      => S (size_part p')
  | Pcons6 _ _ p'     => S (size_part p')
  | Pcons7 _ _ _ p'   => S (size_part p')
  | Pcons8 _ _ _ _ p' => S (size_part p')
  end.

Fixpoint drop_part (n : nat) (p : part) {struct n} : part :=
  match n, p with
  | S n', Pcons _ _ p'      => drop_part n' p'
  | S n', Pcons6 _ _ p'     => drop_part n' p'
  | S n', Pcons7 _ _ _  p'  => drop_part n' p'
  | S n', Pcons8 _ _ _ _ p' => drop_part n' p'
  | _,    _                 => p
  end.

Fixpoint take_part (n : nat) (p : part) {struct n} : part :=
  match n, p with
  | S n', Pcons s h p'         => Pcons s h (take_part n' p')
  | S n', Pcons6 h f1 p'       => Pcons6 h f1 (take_part n' p')
  | S n', Pcons7 h f1 f2 p'    => Pcons7 h f1 f2 (take_part n' p')
  | S n', Pcons8 h f1 f2 f3 p' => Pcons8 h f1 f2 f3 (take_part n' p')
  | _,    _                    => Pnil
  end.

Fixpoint cat_part (p q : part) {struct p} : part :=
  match p with
  | Pcons s h p'         => Pcons s h (cat_part p' q)
  | Pcons6 h f1 p'       => Pcons6 h f1 (cat_part p' q)
  | Pcons7 h f1 f2 p'    => Pcons7 h f1 f2 (cat_part p' q)
  | Pcons8 h f1 f2 f3 p' => Pcons8 h f1 f2 f3 (cat_part p' q)
  | Pnil                 => q
  end.

Definition rot_part n p := cat_part (drop_part n p) (take_part n p).

Lemma size_cat_part : forall p1 p2,
 size_part (cat_part p1 p2) = size_part p1 + size_part p2.
Proof. by move=> p1 p2; elim: p1 => //= *; congr S. Qed.

Lemma size_drop_part : forall n p,
  size_part (drop_part n p) = size_part p - n.
Proof. by move=> n; elim: n => [|n Hrec] p; case p. Qed.

Lemma cat_take_drop_part : forall n p,
  cat_part (take_part n p) (drop_part n p) = p.
Proof. by elim=> [|n Hrec]; case=> //= *; rewrite Hrec. Qed.

Lemma size_rot_part : forall n p, size_part (rot_part n p) = size_part p.
Proof.
by move=> n p; rewrite -{2}(cat_take_drop_part n p) /rot_part !size_cat_part addnC.
Qed.

Fixpoint catrev_part (p1 p2 : part) {struct p1} : part :=
  match p1 with
  | Pnil                  => p2
  | Pcons s h p1'         => catrev_part p1' (Pcons s h p2)
  | Pcons6 h f1 p1'       => catrev_part p1' (Pcons6 h f1 p2)
  | Pcons7 h f1 f2 p1'    => catrev_part p1' (Pcons7 h f1 f2 p2)
  | Pcons8 h f1 f2 f3 p1' => catrev_part p1' (Pcons8 h f1 f2 f3 p2)
  end.

Definition rev_part p := catrev_part p Pnil.

Lemma catrev_part_eq : forall p1 p2, catrev_part p1 p2 = cat_part (rev_part p1) p2.
Proof.
move=> p1 p2; rewrite /rev_part -{1}[p2]/(cat_part Pnil p2); move: p1 Pnil p2.
elim=> [|s h p1 Hrec|h f1 p1 Hrec|h f1 f2 p1 Hrec|h f1 f2 f3 p1 Hrec] p2 p3 //=;
  by rewrite -Hrec.
Qed.

Lemma size_rev_part : forall p, size_part (rev_part p) = size_part p.
Proof.
move=> p; rewrite /rev_part -[size_part p]addn0 -[0]/(size_part Pnil).
elim: p Pnil => //= [s h p Hrec|h f1 p Hrec|h f1 f2 p Hrec|h f1 f2 f3 p Hrec] p';
  by rewrite addSnnS Hrec.
Qed.

Lemma rev_rev_part : forall p, rev_part (rev_part p) = p.
Proof.
move=> p; rewrite {2}/rev_part -{2}[p]/(catrev_part Pnil p); move: p Pnil.
by elim=> //= [s h p Hrec|h f1 p Hrec|h f1 f2 p Hrec|h f1 f2 f3 p Hrec] p';
  rewrite Hrec.
Qed.

(* Accessors; except for "next_hat", they assume the part is not nil.         *)
(* The accessors are mostly used for zipped parts, where we also need to      *)
(* access the fans in clockwise order, so we have both "r" (counterclockwise) *)
(* and "l" (clockwise) versions of the fan accessors. We don't provide update *)
(* functions because both here (for split_part) and in redpart, update is     *)
(* bundeled with another operation.                                           *)

Definition get_spoke p :=
  match p with
  | Pcons s _ _      => s
  | Pcons6 _ _ _     => Pr66
  | Pcons7 _ _ _ _   => Pr77
  | Pcons8 _ _ _ _ _ => Pr88
  | _                => Pr59
  end.

Definition next_hat h0 p :=
  match p with
  | Pnil             => h0
  | Pcons _ h _      => h
  | Pcons6 h _ _     => h
  | Pcons7 h _ _ _   => h
  | Pcons8 h _ _ _ _ => h
  end.

Definition get_hat := Eval compute in next_hat Pr59.

Definition get_fan1r p :=
  match p with
  | Pcons6 _ f1 _     => f1
  | Pcons7 _ f1 _ _   => f1
  | Pcons8 _ f1 _ _ _ => f1
  | _               => Pr59
  end.

Definition get_fan2r p :=
  match p with
  | Pcons7 _ _ f2 _   => f2
  | Pcons8 _ _ f2 _ _ => f2
  | _               => Pr59
  end.

Definition get_fan3r p :=
  match p with
  | Pcons8 _ _ _ f3 _ => f3
  | _               => Pr59
  end.

Definition get_fan1l p :=
  match p with
  | Pcons6 _ f1 _     => f1
  | Pcons7 _ _ f2 _   => f2
  | Pcons8 _ _ _ f3 _ => f3
  | _               => Pr59
  end.

Definition get_fan2l p :=
  match p with
  | Pcons7 _ f1 _ _   => f1
  | Pcons8 _ _ f2 _ _ => f2
  | _               => Pr59
  end.

Definition get_fan3l p :=
  match p with
  | Pcons8 _ f1 _ _ _ => f1
  | _               => Pr59
  end.

(* Mirror image : reflection ACROSS the first spoke (exchanges second  *)
(* and last spoke).                                                    *)

Fixpoint mirror_part_rec (h0 : prange) (rp p : part) {struct p} : part :=
  match p with
  | Pnil =>
    rp
  | Pcons s _ p' =>
    mirror_part_rec h0 (Pcons s (next_hat h0 p') rp) p'
  | Pcons6 _ f1 p'       =>
    mirror_part_rec h0 (Pcons6 (next_hat h0 p') f1 rp) p'
  | Pcons7 _ f1 f2 p'    =>
    mirror_part_rec h0 (Pcons7 (next_hat h0 p') f2 f1 rp) p'
  | Pcons8 _ f1 f2 f3 p' =>
    mirror_part_rec h0 (Pcons8 (next_hat h0 p') f3 f2 f1 rp) p'
  end.

Definition mirror_part p := mirror_part_rec (get_hat p) Pnil p.

Lemma size_mirror_part : forall p, size_part (mirror_part p) = size_part p.
Proof.
move=> p; rewrite /mirror_part -[size_part p]/(size_part Pnil + size_part p).
elim: p Pnil (get_hat p)
         => [|s h p Hrec|h f1 p Hrec|h f1 f2 p Hrec|h f1 f2 f3 p Hrec] q h0;
  by rewrite /= ?addn0 ?addnS ?Hrec.
Qed.

Lemma mirror_mirror_part : forall p, mirror_part (mirror_part p) = p.
Proof.
move=> p; rewrite {2}/mirror_part; move Dh0: (get_hat p) => h0.
have Eh0: next_hat (if p is Pnil then Pr59 else h0) Pnil = next_hat h0 p.
  by rewrite -Dh0; case p.
transitivity (mirror_part_rec h0 p Pnil); last done.
elim: p {Dh0}Pnil Eh0
  => [|s h p Hrec|h f1 p Hrec|h f1 f2 p Hrec|h f1 f2 f3 p Hrec] q /= Eh0;
  by rewrite ?Hrec // /mirror_part /= ?Eh0 // -Eh0.
Qed.

(* Converse part: reflection ALONG the first spoke (exchanges hub and first *)
(* spoke).                                                                  *)

Definition conv_part12 p4 :=
  match p4 with
  | Pcons s2 s1 (Pcons h23 f2 _) =>
     match f2, s2 with
     | Pr59, _ => (h23, fun q => pcons_s s1 (pcons_s s2 q))
     | _, Pr55 => (h23, fun q => pcons_s s1 (Pcons Pr55 f2 q))
     | _, Pr66 => (h23, fun q => pcons_s s1 (Pcons6 Pr59 f2 q))
     | _, Pr77 => (h23, fun q => pcons_s s1 (Pcons7 Pr59 Pr59 f2 q))
     | _, _    => (Pr59, fun _ => Pnil)
     end
  | Pcons6 s1 h12 (Pcons h23 f21 _) =>
    (h23, fun q => pcons_s s1 (Pcons6 h12 f21 q))
  | Pcons7 s1 h12 f21 (Pcons h23 f22 _) =>
    (h23, fun q => pcons_s s1 (Pcons7 h12 f21 f22 q))
  | _ =>
   (Pr59, fun _ => Pnil)
  end.

Definition conv_part3 h23 p6 :=
  match p6 with
  | Pnil =>
    Pcons Pr55 h23
  | Pcons _ _ Pnil =>
    Pcons Pr66 h23
  | Pcons f31 _ (Pcons f32 _ Pnil) =>
    match f31, f32 with
    | Pr59, Pr59 => Pcons Pr77 h23
    | _,    _    => Pcons7 h23 f31 f32
    end
  | Pcons f31 _ (Pcons f32 _ (Pcons f33 _ Pnil)) =>
    Pcons8 h23 f31 f32 f33
  | _ =>
    fun _ => Pnil
  end.

Definition conv_part4 p1 :=
  match p1 with
  | Pcons h34 _ (Pcons s4 f41 _) =>
    match f41, s4 with
    | Pr59, _ => (Pr59, Pcons s4 h34)
    | _, Pr55 => (f41,  Pcons Pr55 h34)
    | _, Pr66 => (Pr59, Pcons6 h34 f41)
    | _, Pr77 => (Pr59, Pcons7 h34 f41 Pr59)
    | _, _    => (Pr59, fun _ => Pnil)
    end
  | Pcons h34 _ (Pcons6 f41 h45 _) =>
    (h45, Pcons6 h34 f41)
  | Pcons h34 _ (Pcons7 f41 f42 h45 _) =>
    (h45, Pcons7 h34 f41 f42)
  | _ =>
    (Pr59,  fun _ => Pnil)
  end.

Definition conv_part5 h45 p3 :=
  match p3 with
  | Pcons u s5 _      => (u,    Pcons s5 h45 Pnil)
  | Pcons7 s5 s6 s7 _ => (Pr77, Pcons s5 h45 (pcons_s s6 (pcons_s s7 Pnil)))
  | _                 => (Pr59, Pnil)
  end.

Definition converse_part p1 :=
  let (h45, q4) := conv_part4 p1 in
  let (u, q5) := conv_part5 h45 (drop_part 2 p1) in
  let (h23, q12) := conv_part12 (drop_part 3 p1) in
  let q3 := conv_part3 h23 (drop_part 5 p1) in
  (u, q12 (q3 (q4 q5))).

(* Part (and range) splitting with respect to a condition, that is a quadruple *)
(* part location i, spoke index j, arity value k, and a boolean lo, true if we *)
(* want to restrict the range at i[j] to arities lower than or equal to k, and *)
(* false if we want the arities greater than k. A split is "good" if it is     *)
(* nontrivial (k is in the range) and definite (if i is a fan location, the    *)
(* spoke below it has a definite arity that is large enough).                  *)

Definition prange_lo k :=
  match k with
  | 5 => Pr55
  | 6 => Pr56
  | 7 => Pr57
  | 8 => Pr58
  | _ => Pr59
  end.

Definition prange_hi k :=
  match k with
  | 5 => Pr69
  | 6 => Pr79
  | 7 => Pr89
  | 8 => Pr99
  | _ => Pr59
  end.

Definition good_rsplit k r :=
  if cmp_range r (prange_lo k) is Pstraddle then true else false.

Definition split_range k (lo : bool) r :=
  meet_range ((if lo then prange_lo else prange_hi) k) r.

Lemma fit_split_range : forall k r, good_rsplit k r ->
  forall lo a, split_range k lo r a = (lo +b (k < a)) && r a.
Proof. move=> k [] Hk [] a; move: k a Hk; repeat case=> //. Qed.

Definition good_split i j k p :=
  match i, drop_part j p with
  | Pspoke, Pcons s _ _       => good_rsplit k s
  | Phat,   Pcons s h _       => good_rsplit k h
  | Phat,   Pcons6 h _ _      => good_rsplit k h
  | Phat,   Pcons7 h _ _ _    => good_rsplit k h
  | Phat,   Pcons8 h _ _ _ _  => good_rsplit k h
  | Pfan1,  Pcons6 _ f1 _     => good_rsplit k f1
  | Pfan1,  Pcons Pr66 _ _    => good_rsplit k Pr59
  | Pfan1,  Pcons7 _ f1 _ _   => good_rsplit k f1
  | Pfan1,  Pcons Pr77 _ _    => good_rsplit k Pr59
  | Pfan1,  Pcons8 _ f1 _ _ _ => good_rsplit k f1
  | Pfan1,  Pcons Pr88 _ _    => good_rsplit k Pr59
  | Pfan2,  Pcons7 _ _ f2 _   => good_rsplit k f2
  | Pfan2,  Pcons Pr77 _ _    => good_rsplit k Pr59
  | Pfan2,  Pcons8 _ _ f2 _ _ => good_rsplit k f2
  | Pfan2,  Pcons Pr88 _ _    => good_rsplit k Pr59
  | Pfan3,  Pcons8 _ _ _ f3 _ => good_rsplit k f3
  | Pfan3,  Pcons Pr88 _ _    => good_rsplit k Pr59
  | _,       _                => false
  end.

Definition split_part i j k lo p :=
  let p1 := take_part j p in
  let p2 := drop_part j p in
  let mkp df r p' := cat_part p1 (df (split_range k lo r) p') in
  match i, p2 with
  | Pspoke, Pcons s h p'         => mkp (fun r => Pcons r h) s p'
  | Phat,   Pcons s h p'         => mkp (fun r => Pcons s r) h p'
  | Phat,   Pcons6 h f1 p'       => mkp (fun r => Pcons6 r f1) h p'
  | Phat,   Pcons7 h f1 f2 p'    => mkp (fun r => Pcons7 r f1 f2) h p'
  | Phat,   Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 r f1 f2 f3) h p'
  | Pfan1,  Pcons6 h f1 p'       => mkp (fun r => Pcons6 h r) f1 p'
  | Pfan1,  Pcons Pr66 h p'      => mkp (fun r => Pcons6 h r) Pr59 p'
  | Pfan1,  Pcons7 h f1 f2 p'    => mkp (fun r => Pcons7 h r f2) f1 p'
  | Pfan1,  Pcons Pr77 h p'      => mkp (fun r => Pcons7 h r Pr59) Pr59 p'
  | Pfan1,  Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 h r f2 f3) f1 p'
  | Pfan1,  Pcons Pr88 h p'      => mkp (fun r => Pcons8 h r Pr59 Pr59) Pr59 p'
  | Pfan2,  Pcons7 h f1 f2 p'    => mkp (fun r => Pcons7 h f1 r) f2 p'
  | Pfan2,  Pcons Pr77 h p'      => mkp (fun r => Pcons7 h Pr59 r) Pr59 p'
  | Pfan2,  Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 h f1 r f3) f2 p'
  | Pfan2,  Pcons Pr88 h p'      => mkp (fun r => Pcons8 h Pr59 r Pr59) Pr59 p'
  | Pfan3,  Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 h f1 f2 r) f3 p'
  | Pfan3,  Pcons Pr88 h p'      => mkp (fun r => Pcons8 h Pr59 Pr59 r) Pr59 p'
  | _,      _                    => p
  end.

Lemma size_split_part : forall i j k lo p,
  size_part (split_part i j k lo p) = size_part p.
Proof.
move=> i j k lo p.
move: (size_rot_part j p); rewrite /rot_part size_cat_part addnC.
case: i => //=; case: (drop_part j p) => [|s h|h f1|h f1 f2|h f1 f2 f3] //= p';
  by try case s; rewrite //= ?size_cat_part.
Qed.

(* Part comparison and intersection; note that the intersection is slightly *)
(* asymmetric, in that it will truncate the second argument.                *)

Fixpoint cmp_part (p q : part) {struct q} : part_rel :=
  match q, p with
  | Pcons sq hq q',           Pcons sp hp p' =>
      meet_prel (cmp_range sp sq)
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons sq hq q',           Pcons6 hp _ p' =>
      meet_prel (cmp_range Pr66 sq)
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons sq hq q',           Pcons7 hp _ _ p' =>
      meet_prel (cmp_range Pr77 sq)
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons sq hq q',           Pcons8 hp _ _ _ p' =>
      meet_prel (cmp_range Pr88 sq)
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons6 hq _ q',           Pcons sp hp p' =>
      meet_prel (notPsubset (cmp_range sp Pr66))
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons7 hq _ _ q',         Pcons sp hp p' =>
      meet_prel (notPsubset (cmp_range sp Pr77))
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons8 hq _ _ _ q',       Pcons sp hp p' =>
      meet_prel (notPsubset (cmp_range sp Pr88))
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons6 hq f1q q',         Pcons6 hp f1p p' =>
      meet_prel (cmp_range hp hq)
     (meet_prel (cmp_range f1p f1q)
                (cmp_part p' q'))
  | Pcons7 hq f1q f2q q',     Pcons7 hp f1p f2p p' =>
      meet_prel (cmp_range hp hq)
     (meet_prel (cmp_range f1p f1q)
     (meet_prel (cmp_range f2p f2q)
                (cmp_part p' q')))
  | Pcons8 hq f1q f2q f3q q', Pcons8 hp f1p f2p f3p p' =>
      meet_prel (cmp_range hp hq)
     (meet_prel (cmp_range f1p f1q)
     (meet_prel (cmp_range f2p f2q)
     (meet_prel (cmp_range f3p f3q)
                (cmp_part p' q'))))
  | Pnil,                    _ =>
     Psubset
  | _,                      Pnil =>
     Pstraddle
  | _,                      _ =>
     Pdisjoint
  end.

Fixpoint meet_part (p q : part) {struct q} : part :=
  match q, p with
  | Pcons sq hq q',            Pcons sp hp p' =>
    Pcons (meet_range sp sq) (meet_range hp hq) (meet_part p' q')
  | Pcons sq hq q',            Pcons6 hp f1 p' =>
    Pcons6 (meet_range hp hq) f1 (meet_part p' q')
  | Pcons sq hq q',            Pcons7 hp f1 f2 p' =>
    Pcons7 (meet_range hp hq) f1 f2 (meet_part p' q')
  | Pcons sq hq q',            Pcons8 hp f1 f2 f3 p' =>
    Pcons8 (meet_range hp hq) f1 f2 f3 (meet_part p' q')
  | Pcons6 hq f1 q',          Pcons sp hp p' =>
    Pcons6 (meet_range hp hq) f1 (meet_part p' q')
  | Pcons7 hq f1 f2 q',       Pcons sp hp p' =>
    Pcons7 (meet_range hp hq) f1 f2 (meet_part p' q')
  | Pcons8 hq f1 f2 f3 q',    Pcons sp hp p' =>
    Pcons8 (meet_range hp hq) f1 f2 f3 (meet_part p' q')
  | Pcons6 hq f1q q',         Pcons6 hp f1p p' =>
    Pcons6 (meet_range hp hq) (meet_range f1p f1q) (meet_part p' q')
  | Pcons7 hq f1q f2q q',     Pcons7 hp f1p f2p p' =>
    Pcons7 (meet_range hp hq) (meet_range f1p f1q) (meet_range f2p f2q) 
           (meet_part p' q')
  | Pcons8 hq f1q f2q f3q q', Pcons8 hp f1p f2p f3p p' =>
    Pcons8 (meet_range hp hq) (meet_range f1p f1q) (meet_range f2p f2q)
           (meet_range f3p f3q) (meet_part p' q')
  | _,                      _ =>
    p
  end.

Lemma size_meet_part : forall p q, size_part (meet_part p q) = size_part p.
Proof.
move=> p q; move Dn: (size_part q) => n.
by elim: n p q {Dn}(introT eqP Dn) => [|n Hrec] p; case=> //;
   case: p => //= *; rewrite Hrec.
Qed.

(* Part semantics : matching maps. *)

Definition subpart_loc_move i g x :=
  match i with
  | Pspoke => @edge g x
  | Phat   => edge (iter 2 face (edge x))
  | Pfan1  => edge (iter 3 face (edge x))
  | Pfan2  => edge (iter 4 face (edge x))
  | Pfan3  => edge (iter 5 face (edge x))
  end.

Coercion subpart_loc_move : subpart_loc >-> Funclass.

Section FitPart.

Variable g : hypermap.

Fixpoint fitp (x : g) (p : part) {struct p} : bool :=
  let ax := arity (edge x) in
  let axn n := arity (edge (iter n face (edge x))) in
  match p with
  | Pcons s h p' =>
    and3b (s (arity (Pspoke g x))) (h (arity (Phat g x))) (fitp (face x) p')
  | Pcons6 h f1 p' =>
    and4b (Pr66 (arity (Pspoke g x))) (h (arity (Phat g x)))
          (f1 (arity (Pfan1 g x)))
          (fitp (face x) p')
  | Pcons7 h f1 f2 p' =>
    and5b (Pr77 (arity (Pspoke g x))) (h (arity (Phat g x)))
          (f1 (arity (Pfan1 g x))) (f2 (arity (Pfan2 g x))) (fitp (face x) p')
  | Pcons8 h f1 f2 f3 p' =>
    and5b (Pr88 (arity (Pspoke g x))) (h (arity (Phat g x)))
          (f1 (arity (Pfan1 g x))) (f2 (arity (Pfan2 g x)))
          (f3 (arity (Pfan3 g x)) && fitp (face x) p')
  | Pnil =>
    true
  end.

Definition exact_fitp x p : bool := (arity x =d size_part p) && fitp x p.

(* An intermediate notion, for part converse : simple fit, plus an *)
(* explicit range check for the hub arity.                         *)
Definition tight_fitp x (up : prange * _):=
  let (u, p) := up in u (arity x) && fitp x p.

(* Simple properties of fitp (that do not require geometrical properties),  *)
(* that is, list functions, comparison, meet, and split.                    *)

Lemma fitp_drop : forall n p x, fitp x p -> fitp (iter n face x) (drop_part n p).
Proof.
move=> n; elim: n => [|n Hrec] p x //; rewrite -iter_f.
by case: p => [|s h p|h f1 p|h f1 f2 p|h f1 f2 f3 p] //=; rewrite ?andbA;
  case/andP; auto.
Qed.

Lemma fitp_cat : forall x p1 p2,
  fitp x (cat_part p1 p2) = fitp x p1 && fitp (iter (size_part p1) face x) p2.
Proof.
move=> x p1 p2.
elim: p1 x => [|s h p1 Hrec|h f1 p1 Hrec|h f1 f2 p1 Hrec|h f1 f2 f3 p1 Hrec] x //=;
  by rewrite -?andbA f_iter -iter_f -Hrec.
Qed.

Lemma fitp_rot : forall n p, n <= size_part p ->
 forall x, exact_fitp x p = exact_fitp (iter n face x) (rot_part n p).
Proof.
move=> n p Hn x; rewrite /exact_fitp size_rot_part arity_iter_face.
case: (arity x =P size_part p) => //= Hx.
rewrite /rot_part -{1}(cat_take_drop_part n p) !fitp_cat andbC.
congr andb; congr fitp.
  congr (iter _ face x); move: (congr1 size_part (cat_take_drop_part n p)).
  rewrite -(leq_add_sub Hn) size_cat_part size_drop_part; apply: addn_injr.
by rewrite -iter_addn size_drop_part addnC (leq_add_sub Hn) -Hx iter_face_arity.
Qed.

Lemma fitp_catrev : forall x p1 p2,
 fitp x (catrev_part p1 p2)
   = fitp x (rev_part p1) && fitp (iter (size_part p1) face x) p2.
Proof. by move=> *; rewrite catrev_part_eq fitp_cat size_rev_part. Qed.

(* Comparison and meet.                                                      *)

Remark Epr : forall m n : nat,
 (m =d n) = match m with 6 => Pr66 n | 7 => Pr77 n | 8 => Pr88 n | _ => m =d n end.
Proof. by do 9 case=> //. Qed.

Lemma fitp_cmp : forall p x, fitp x p ->
   forall q, fitp x q = cmp_part p q (fitp x q).
Proof.
(elim; first by move=> x _ []) => [sp hp|hp f1p|hp f1p f2p|hp f1p f2p f3p];
  move=> p Hrec x H; simpl in H; case/and3P: H => Hs Hh;
  try case/andP=> Hf1; try case/andP=> Hf2; try case/andP=> Hf3; move=> Hp;
  case=> //= [sq hq|hq f1q|hq f1q f2q|hq f1q f2q f3q] q;
  rewrite 1?Epr 1?(mem_cmp_range Hs) -?(eqP Hs) //(mem_cmp_range Hh) (Hrec _ Hp);
  rewrite 1?(mem_cmp_range Hf1) 1?(mem_cmp_range Hf2) 1?(mem_cmp_range Hf3);
  try (first [ move: (cmp_range sp sq) | move: (sp) | move: (sq) ]; case);
  rewrite //=; case: (cmp_range hp hq); rewrite /= ?andbF //;
  try (case: (cmp_range f1p f1q); rewrite /= ?andbF //);
  try (case: (cmp_range f2p f2q); rewrite /= ?andbF //);
  try (case: (cmp_range f3p f3q); rewrite /= ?andbF //);
  by case (cmp_part p q); rewrite /= ?andbF.
Qed.

Lemma fitp_meet : forall p q x, fitp x p -> fitp x q -> fitp x (meet_part p q).
Proof.
elim=> [|sp hp p Hrec|hp f1p p Hrec|hp f1p f2p p Hrec|hp f1p f2p f3p p Hrec];
  first [ move=> q x H; simpl in H; case/and3P: H => Hsp Hhp | by case ];
  try case/andP=> Hf1p; try case/andP=> Hf2p; try case/andP=> Hf3p; move=> Hp;
  case: q => [|sq hq q|hq f1q q|hq f1q f2q q|hq f1q f2q f3q q] /=;
  rewrite -?(eqP Hsp) ?Hsp ?Hhp ?Hf1p ?Hf2p ?Hf3p //; case/and3P=> Hsq Hhq;
  try case/andP=> Hf1q; try case/andP=> Hf2q; try case/andP=> Hf3q; move=> Hq;
  by rewrite (Hrec _ _ Hp Hq) ?Hsq ?Hf1q ?Hf2q ?Hf3q !mem_meet_range.
Qed.

Lemma exact_fitp_meet : forall p q x, exact_fitp x p -> fitp x q ->
  exact_fitp x (meet_part p q).
Proof.
move=> p q x; rewrite /exact_fitp size_meet_part.
by case (eqd (arity x) (size_part p)); first exact: fitp_meet.
Qed.

End FitPart.

(* Part location sematics: a constructor function is valid wrt a location if *)
(* it only affects the validity of the range at that location.               *)
(* This definition appears here because we need to quantify over the map.    *)

Definition part_update fp (i : subpart_loc) :=
  forall (r : prange) p,
      size_part (fp r p) = S (size_part p)
  /\ (forall g x, @fitp g x (fp r p) ->
        r (arity (i g x))
     /\ (forall r' : prange, r' (arity (i g x)) -> fitp x (fp r' p))).

Lemma updatePs : forall h, part_update (fun r => Pcons r h) Pspoke.
Proof.
move=> h r p; split; move=> //= g x; move/andP=> [Hr Hp].
by split; last by move=> r' Hr'; rewrite Hr'.
Qed.

Lemma updatePh : forall s, part_update (fun r => Pcons s r) Phat.
Proof.
move=> s r p; split; move=> //= g x; move/and3P=> [Hs Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hr'.
Qed.

Lemma updateP6h : forall f1, part_update (fun r => Pcons6 r f1) Phat.
Proof.
move=> f1 r p; split; move=> //= g x; move/and3P=> [Hs Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hr'.
Qed.

Lemma updateP6f1 : forall h, part_update (fun r => Pcons6 h r) Pfan1.
Proof.
move=> h r p; split; move=> //= g x; move/and4P=> [Hs Hh Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hh Hr'.
Qed.

Lemma updateP7h : forall f1 f2, part_update (fun r => Pcons7 r f1 f2) Phat.
Proof.
move=> f1 f2 r p; split; move=> //= g x; move/and3P=> [Hs Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hr'.
Qed.

Lemma updateP7f1 : forall h f2, part_update (fun r => Pcons7 h r f2) Pfan1.
Proof.
move=> h f2 r p; split; move=> //= g x; move/and4P=> [Hs Hh Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hh Hr'.
Qed.

Lemma updateP7f2 : forall h f1, part_update (fun r => Pcons7 h f1 r) Pfan2.
Proof.
move=> h f1 r p; split; move=> //= g x; move/and5P=> [Hs Hh Hf1 Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hh Hf1 Hr'.
Qed.

Lemma updateP8h : forall f1 f2 f3, part_update (fun r => Pcons8 r f1 f2 f3) Phat.
Proof.
move=> f1 f2 f3 r p; split; move=> //= g x; move/and3P=> [Hs Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hr'.
Qed.

Lemma updateP8f1 : forall h f2 f3, part_update (fun r => Pcons8 h r f2 f3) Pfan1.
Proof.
move=> h f2 f3 r p; split; move=> //= g x; move/and4P=> [Hs Hh Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hh Hr'.
Qed.

Lemma updateP8f2 : forall h f1 f3, part_update (fun r => Pcons8 h f1 r f3) Pfan2.
Proof.
move=> h f1 f3 r p; split; move=> //= g x; move/and5P=> [Hs Hh Hf1 Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hh Hf1 Hr'.
Qed.

Lemma updateP8f3 : forall h f1 f2, part_update (fun r => Pcons8 h f1 f2 r) Pfan3.
Proof.
split; move=> //= g x; case/and5P=> [Hs Hh Hf1 Hf2]; move/andP=> [Hr Hp].
by split; last by move=> r' Hr'; rewrite Hs Hh Hf1 Hf2 Hr'.
Qed.

Section FitMirrorPart.

(* Properties of fitp that do depend on geometrical assumptions. They are *)
(* all grouped here, although fitp_pcons_ and fitp_split depend only on   *)
(* the pentagonal property, while fitp_mirror doesn't depend on it.       *)

Variable g : hypermap.
Hypothesis Hg : plain_cubic g.
Let De2 := plain_eq Hg.
Let Dn3 := cubic_eq Hg.

Ltac PopAnd Hn :=
  match goal with
  |  |- (?X1 && _ = _) => case Hn: (X1); rewrite /= ?andbF // ?andbT
  end.

Lemma fitp_mirror : forall p x,
  @exact_fitp g x (mirror_part p) = @exact_fitp (mirror g) x p.
Proof.
move Dars: (fun n g' x => arity (edge (iter n face (@edge g' x)))) => ars.
have Darsg := fun n g' x => erefl (ars n g' x).
move: {Darsg}(Darsg 2) (Darsg 3) (Darsg 4) (Darsg 5).
rewrite -{2 4 6 8}Dars /= => Dars2 Dars3 Dars4 Dars5.
have Ears2: forall x : g, ars 2 (mirror g) x = ars 2 g x.
  move=> x; rewrite -{1}Dars arity_mirror /= /comp arity_face.
  rewrite -[node x]Enode -{1}[x]Eedge Dn3 !(finv_f (Iface g)).
  rewrite -{1}[face (edge x)]Eface De2.
  by rewrite -{1}[face (face (edge x))]Eedge Dn3 arity_face -Dars2.
have Earsf: forall n m (x : g), m =d arity (edge x) -> n <= m -> 
    ars n (mirror g) (face x) = ars (m - n) g x.
  move=> n m x Dm Hnm; rewrite -{1}Dars /= -{1}[x]De2 /comp Eedge.
  rewrite -arity_face in Dm; rewrite (iter_finv (Iface g)) -(eqP Dm) //.
  rewrite iter_f /= -[iter (m - n) _ _]De2 Eedge.
  by rewrite (order_finv (Iface g)) arity_face -Dars.
have Ears: forall x : g, arity (edge (@face g x : mirror g)) = arity (edge x).
  by move=> x; rewrite arity_mirror /= /comp -{1}[x]De2 Eedge arity_face.
move: {Earsf}Ears Ears2 (Earsf 3) (Earsf 4) (Earsf 5).
rewrite -{1 3 5 7}Dars /= => Ears Ears2 Ears3 Ears4 Ears5.
have Hgars: forall x p h0, fitp x p -> p = Pnil \/ next_hat h0 p (ars 2 _ x).
  move=> g' x p h0; rewrite -Dars.
  case Dp: p; first [ by left | by case/and3P; right ].
move=> p x; rewrite /exact_fitp size_mirror_part arity_mirror /mirror_part.
set h0 := get_hat p; pose h0hx := h0 (ars 2 _ x); symmetry.
case: (arity x =P size_part p) => // Hax.
pose sz0 q := size_part q =d 0; set q := Pnil.
transitivity (fitp x q && @fitp (mirror g) x p && (sz0 p || h0hx)).
  case Hxp: (@fitp (mirror g) x p); rewrite {Hax}//= {}/h0hx {}/h0.
  case: (Hgars (mirror g) x p Pr59 Hxp) => [Dp|Hh0x]; first by rewrite Dp.
  by rewrite -Dars /= Ears2 /= in Hh0x; apply: esym; apply/orP; right.
have Eqp: next_hat h0 q = next_hat h0 p by rewrite /h0; case p.
have Hq0: implb (sz0 q) (next_hat h0 q (ars 2 _ x) =d h0hx) by apply: set11.
clearbody h0; move: q Eqp Hq0; rewrite -{1 2 3}[x]iter_face_arity {}Hax.
elim: p => [|s h p Hrec|h f1 p Hrec|h f2 f1 p Hrec|h f3 f2 f1 p Hrec] q;
 (rewrite /= ?andbT //; set y := iter (size_part p) face x; case=> <- Hq0;
   rewrite Ears Ears2; apply: (etrans _ (Hrec _ _ _));
   rewrite // -/y /= -Dars2 -?Dars3 -?Dars4 -?Dars5 -?andbA;
   PopAnd ipattern : Hyq; PopAnd ipattern : Hs; try rewrite (Ears3 _ _ Hs);
   try rewrite (Ears4 _ _ Hs); try rewrite (Ears5 _ _ Hs);
   rewrite // /subn /= (finv_f (Iface g)) andbC;
   rewrite -(andbC h0hx) -?andbA [andb h0hx]lock; repeat BoolCongr;
   rewrite andbC -lock andbA andbC; PopAnd ipattern : Hyp;
   by transitivity h0hx;
     [ case: (Hgars _ _ _ h0 Hyq) => [Dq|Hh0q];
        [ rewrite {1}Dq /= in Hq0; rewrite (eqP Hq0) andbb | rewrite Hh0q andbT ]
     | case: (Hgars _ _ _ h0 Hyp) => [Dp|Hh0p];
        [ rewrite /y Dp /= andbT
        | rewrite -Dars /= Ears2 in Hh0p; rewrite Hh0p /=; move: Hh0p;
           rewrite /y; case p ] ]).
Qed.

Lemma fitp_sym : forall p, cmp_part p (mirror_part p) = Psubset ->
  forall x : g, @exact_fitp (mirror g) x p = exact_fitp x p.
Proof.
move=> p Hp x; apply/idP/idP; move/andP=> [Exp Hxp].
  rewrite -{1}[p]mirror_mirror_part fitp_mirror /exact_fitp size_mirror_part.
  by rewrite Exp (fitp_cmp Hxp) Hp.
by rewrite -fitp_mirror /exact_fitp size_mirror_part Exp (fitp_cmp Hxp) Hp.
Qed.

End FitMirrorPart.

Section FitConversePart.

Variable g : hypermap.
Hypothesis Hg : plain_cubic_pentagonal g.
Let HgF : pentagonal g := Hg.
Let De2 := plain_eq Hg.
Let Dn3 := cubic_eq Hg.

Definition inv_face2 x : g := edge (node (edge (node x))).

Lemma fitp_converse : forall p x, exact_fitp x p ->
   tight_fitp (inv_face2 (edge (face (face x)))) (converse_part p).
Proof.
pose t59 h := if h is Pr59 then true else false.
have Et59: forall h (A : Set) (r1 r2 : A),
    (if h is Pr59 then r1 else r2) = if t59 h then r1 else r2.
  by move=> h; case h.
have eEnf: forall y : g, edge y = node (face y).
  by move=> y; rewrite -{2}[y]De2 Eedge.
have fEnne: forall y : g, face y = node (node (edge y)).
  by move=> y; rewrite eEnf Dn3.
move=> p1 x; move/andP=> [Exp1 Hxp1]; rewrite /converse_part.
set effx := edge (face (face x)).
have Hrq4: let (h45, q4) := conv_part4 p1 in
    h45 (arity (edge (face (face (edge (face (face effx)))))))
 /\ (forall q5, fitp (face (face effx)) q5 -> fitp (face effx) (q4 q5)).
  case: p1 Hxp1 {Exp1}; try by simpl; split.
  move=> h34 h p2 H; simpl in H; case/and3P: H => [Hh34 _ Hfxp2].
  rewrite fEnne -arity_face Enode fEnne De2 -eEnf fEnne /effx De2 -eEnf.
  rewrite -{1}[edge (face x)](iter_face_subn (ltnW (ltnW (HgF _)))).
  set n := arity (edge (face x)).
  rewrite -iter_addn addnC iter_addn {1}[Pcons]lock /= !Eface -eEnf -lock.
  have En: arity (edge (node (edge (face x)))) = n by rewrite -arity_face Enode.
  rewrite -[edge x]Enode arity_face -[node (edge x)]Enode -fEnne in Hh34.
  case: p2 Hfxp2 => [|s4 f41 p|f41 h45 p|f41 f42 h45 p|h' f1 f2 f3 p];
    rewrite /= ?Et59 -/n; try by split.
  - move/and3P=> [Hs4 Hf41 _].
    case (t59 f41); first by rewrite /= En HgF Enode Hh34 Hs4; split.
    case: s4 Hs4 => //= Hs4; rewrite ?HgF // Enode En Hs4 Hh34 ?Hf41; split=> //.
    by rewrite -(eqP Hs4).
  - move/and4P=> [Dn Hf41 Hh45 _].
    by rewrite En -(eqP Dn) !Enode set11 Hh34 Hf41; split.
  move/and5P=> [Dn Hf41 Hf42 Hh45 _].
  by rewrite En -(eqP Dn) !Enode set11 Hh34 Hf41 Hf42; split.
move: (conv_part4 p1) Hrq4 => [h45 q4] [Hh45 Hq4].
move: (drop_part 2 p1) (fitp_drop 2 Hxp1) => p3 Hxp3; simpl in Hxp3.
have Huq5: let (u, q5) := conv_part5 h45 p3 in
    u (arity effx) /\ fitp (face (face effx)) q5.
  case: p3 Hxp3 => [|u s5 p|h f p|s5 s6 s7 p|h f1 f2 f3 p] /=; try by split.
    by rewrite -/effx Hh45 /= andbT; move/and3P=> [Hu Hs5 _]; split.
  rewrite -/effx Hh45 !HgF /= andbT; move/andP=> [Hu Hs57].
  by rewrite !andbA andbC -!andbA in Hs57; case (andP Hs57); split.
move: {p3 h45 Hxp3 Hh45}(conv_part5 h45 p3) Huq5 => [u q5] [Hu Hq5].
move: {q4 q5 Hq4 Hq5}(q4 q5) (Hq4 _ Hq5) => q Hq.
move: (drop_part 3 p1) (fitp_drop 3 Hxp1) => p4 Hxp4; simpl in Hxp4.
have Hh23q12: let (h23, q12) := conv_part12 p4 in
        h23 (arity (edge (face (face (edge effx)))))
    /\ (forall q3, fitp effx q3 -> fitp (inv_face2 effx) (q12 q3)).
  set ef3x := edge (face (face (face x))); set n := arity ef3x.
  have Es1: arity (edge (inv_face2 effx)) = arity (edge (face (face ef3x))).
    by symmetry; rewrite 2!fEnne -arity_face Enode /ef3x /inv_face2 !De2 -eEnf.
  have Es2: edge (face (inv_face2 effx)) = face ef3x.
    by rewrite /inv_face2 Enode De2 -[node effx]Enode /effx -fEnne.
  rewrite {1}/effx De2; set ef4x := edge (face (face (face (face x)))).
  have Ef21:
       arity (edge (face (face ef4x))) = arity (edge (iter (n - 2) face ef3x)).
    rewrite /ef4x 3!fEnne -/ef3x -arity_face Enode De2 Dn3.
    rewrite -{1}[ef3x]iter_face_arity /n -(leq_add_sub (HgF ef3x)) -/n /=.
    by rewrite Eface -eEnf.
  case: p4 Hxp4 => [|s2 s1 p|s1 h12 p|s1 h12 f21 p|h f1 f2 f3 p]; first
    [ by simpl; split | case: p; rewrite /= ?Et59 ?if_same /=; try by split ].
  - move=> h23 f21 p; move/and5P=> [Hs2 Hs1 Hh23 Hf21 _] {p}; rewrite !Et59 /=.
    case (t59 f21); first split=> //=.
      by rewrite //= !HgF Es1 Es2 /ef3x Hs1 arity_face Hs2 /inv_face2 !Enode.
    case: s2 Hs2 => /=; try (by split);
     rewrite Es1 Es2 arity_face -/ef3x -/n => Dn;
     split; rewrite // -(eqP Dn) set11 !HgF /inv_face2 !Enode;
     by rewrite -/ef4x Ef21 -(eqP Dn) /= in Hf21; rewrite Hf21 /ef3x Hs1 /=.
  - rewrite -/ef3x -/ef4x Es1 Es2 !HgF arity_face /=.
    move=> h23 f21 p; case/and5P=> Dn Hs1 Hh12 Hh23; move/andP=> [Hf21 _] {p}.
    rewrite Ef21 /n -(eqP Dn) /= in Hf21.
    by split; last by rewrite Dn Hs1 Hh12 Hf21 /inv_face2 !Enode.
  rewrite -/ef3x -/ef4x Es1 Es2 !HgF arity_face /=.
  move=> h23 f22 p; case/and5P=> Dn Hs1 Hh12 Hf21; move/and3P=> [Hh23 Hf22 _] {p}.
  rewrite Ef21 /n -(eqP Dn) /= in Hf22.
  by split; last by rewrite Dn Hs1 Hh12 Hf21 Hf22 /inv_face2 !Enode.
move: {p4 Hxp4}(conv_part12 p4) Hh23q12 => [h23 q12] [Hh23 Hq12].
move: (drop_part 5 p1) (size_drop_part 5 p1) (fitp_drop 5 Hxp1) => p6 Ep6.
have Exp6: arity x = 5 + size_part p6 by rewrite Ep6 -(eqP Exp1) leq_add_sub.
move=> {Exp1 Ep6}/= Hxp6.
rewrite -2!arity_face {1}/inv_face2 !Enode Hu /=; apply: {q12 Hq12}Hq12.
case: p6 Hxp6 Exp6 => //= [_ Ex5 | f31 h p7].
  by rewrite Hh23 /effx De2 !arity_face Ex5.
case/and3P=> Hf31 _ {h}; case: p7 => //= [_ Ex6 | f32 h p8].
  by rewrite Hh23 /effx De2 !arity_face Ex6 /=.
case/and3P=> Hf32 _ {h}; case: p8 => //= [_ Ex7 | f33 h p9].
  rewrite !Et59; case (t59 f31); case (t59 f32);
   by rewrite /= Hh23 /effx De2 !arity_face Ex7 ?Hf31 ?Hf32.
case/andP=> Hf33 _ {h}; case: p9 => //= Ex8.
by rewrite Hh23 /effx De2 !arity_face Hf31 Hf32 Hf33 Ex8.
Qed.

End FitConversePart.

Section FitSplitPart.

Variable g : hypermap.
Hypothesis HgF : pentagonal g.

Lemma fitp_pcons_ : forall (x : g) n, fitp x (pcons_ n).
Proof. by move=> x n; elim: n x => [|n Hrec] x //=; rewrite !HgF Hrec. Qed.

Lemma exact_fitp_pcons_ : forall x : g, exact_fitp x (pcons_ (arity x)).
Proof. by move=> x; rewrite /exact_fitp fitp_pcons_; elim (arity x). Qed.

Definition fitc (i : subpart_loc) j k (x : g) := k < arity (i g (iter j face x)).

Lemma fitp_split : forall i j k p, good_split i j k p -> forall lo (x : g),
  exact_fitp x (split_part i j k lo p) = (lo +b fitc i j k x) && exact_fitp x p.
Proof.
move=> i j k p Hp lo x; rewrite /exact_fitp size_split_part andbCA; congr andb.
move: Hp; rewrite /split_part /good_split.
have Hupdate: forall pc, part_update pc i -> forall p' r,
    size_part (drop_part j p) = size_part (pc r p') ->
    (forall y : g, fitp y (drop_part j p) = fitp y (pc r p')) ->
     good_rsplit k r ->
     let p'' := cat_part (take_part j p) (pc (split_range k lo r) p') in
     fitp x p'' = (lo +b (k < arity (i g (iter j face x)))) && fitp x p.
  move=> pc Hpc p' r Ep' Hp' Hkr.
  move: (Hpc r p') (Hpc (split_range k lo r) p') => [Erp Hrp] [Erp' Hrp'].
  rewrite -{2}(cat_take_drop_part j p) /= !fitp_cat; BoolCongr.
  have <-: j = size_part (take_part j p).
    apply: (@addn_injr (size_part (drop_part j p))).
    rewrite -size_cat_part cat_take_drop_part size_drop_part leq_add_sub //.
    by rewrite ltnW // ltn_lt0sub -size_drop_part Ep' Erp.
  rewrite Hp'; apply/idP/idP.
    move/Hrp'=> [Hx Hr]; rewrite fit_split_range // in Hx.
    by move/andP: Hx => [Hcx Hx]; rewrite Hcx Hr.
  by case/andP=> Hcx; case/Hrp=> Hx; apply; rewrite fit_split_range // Hcx.
case: (drop_part j p) Hupdate => [|s h p'|h f1 p'|h f1 f2 p'|h f1 f2 f3 p'];
  case: i => // Hupdate.
- exact: (Hupdate _ (updatePs h)).
- exact: (Hupdate _ (updatePh s)).
- case: s Hupdate => // [] Hupdate.
  + by apply: (Hupdate _ (updateP6f1 h)) => //= y; rewrite !HgF.
  + by apply: (Hupdate _ (updateP7f1 h Pr59)) => //= y; rewrite !HgF.
  by apply: (Hupdate _ (updateP8f1 h Pr59 Pr59)) => //= y; rewrite !HgF.
- case: s Hupdate => // [] Hupdate.
  + by apply: (Hupdate _ (updateP7f2 h Pr59)) => //= y; rewrite !HgF.
  by apply: (Hupdate _ (updateP8f2 h Pr59 Pr59)) => //= y; rewrite !HgF.
- case: s Hupdate => // [] Hupdate.
  by apply: (Hupdate _ (updateP8f3 h Pr59 Pr59)) => //= y; rewrite !HgF.
- exact: (Hupdate _ (updateP6h f1)).
- exact: (Hupdate _ (updateP6f1 h)).
- exact: (Hupdate _ (updateP7h f1 f2)).
- exact: (Hupdate _ (updateP7f1 h f2)).
- exact: (Hupdate _ (updateP7f2 h f1)).
- exact: (Hupdate _ (updateP8h f1 f2 f3)).
- exact: (Hupdate _ (updateP8f1 h f2 f3)).
- exact: (Hupdate _ (updateP8f2 h f1 f3)).
exact: (Hupdate _ (updateP8f3 h f1 f2)).
Qed.

End FitSplitPart.

Unset Implicit Arguments.