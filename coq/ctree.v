(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import color.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*   Sets of perimeter colorings are represented by a ternary tree structure *)
(* indexed by edge traces, with ``leaf'' nodes indicating full subtrees.     *)
(*   We use these trees to represent sets of unreachable traces, or a subset *)
(* of such traces that has just become reachable. In either case, all the    *)
(* leaves of a tree should be at the same depth (the ring size minus one).   *)
(*   The ctree_proper predicate checks this condition (we contract empty too *)
(* but this isn't necessary for correctness, so we don't check for this).    *)
(*   Trees representing full sets of unreachable traces store the number of  *)
(* matching unreachable chromograms at their leaves, in unary, as a stack of *)
(* ``subleaves''.                                                            *)
(*   We provide basic functions in this file : classifiers, accessors, and   *)
(* constructors, union and rotation of reachable path sets, and a disjoint   *)
(* test for checking contracts.                                              *)
(*   The more complex unreachable set functions, initialisation and matching *)
(* restriction by a will be defined in separate files.                       *)
(*   The restriction returns a pair of trees; these could be compressed into *)
(* a single ``marked tree'' structure, but the additional overhead doesn't   *)
(* seem worthwhile (in particular, it complicates the ``inner loop'' of the  *)
(* chromogram tree restriction operation).                                   *)

Inductive ctree : Set :=
  | Ctree_node : forall t1 t2 t3 : ctree, ctree
  | Ctree_leaf : forall lf :  (* leaf or empty *) ctree, ctree
  | Ctree_empty : ctree.

Inductive ctree_pair : Set :=
    Ctree_pair : forall t0 t1 : ctree, ctree_pair.

(* Classifiers. *)

Definition ctree_empty t := if t is Ctree_empty then true else false.

Definition ctree_leaf t := if t is Ctree_leaf _ then true else false.

(* Empty nodes are always contracted, so that we can check for an empty tree *)
(* by pattern-matching on Ctree_empty. The empty node test is used to        *)
(* interlock the computation in ctree_restrict: it is strict on all branches.*)

Definition ctree_empty_node t :=
  match t with
  | Ctree_node Ctree_empty Ctree_empty Ctree_empty => true
  | Ctree_node _ Ctree_empty Ctree_empty => false
  | Ctree_node _ _ Ctree_empty => false
  | _ => false
  end.

Inductive eq3_Ctree_empty : forall t1 t2 t3 : ctree, Prop :=
    Eq3_Ctree_empty : eq3_Ctree_empty Ctree_empty Ctree_empty Ctree_empty.

(* Node accessor. *)

Definition ctree_sel t : color -> ctree :=
  match t with
  | Ctree_node t1 t2 t3 => palette Ctree_empty t1 t2 t3
  | _ => fun _ => Ctree_empty
  end.

(* The correctness predicate for exact sets checks that leaves occur at a    *)
(* uniform height h, and only point to leaves or empty nodes.                *)

Fixpoint ctree_proper (h : nat) (t : ctree) {struct t} : Prop :=
  match t, h with
  | Ctree_empty, _ => True
  | Ctree_node t1 t2 t3, S h' =>
    and4 (ctree_empty_node t = false) (ctree_proper h' t1)
         (ctree_proper h' t2) (ctree_proper h' t3)
  | Ctree_leaf lf, O => ctree_proper 0 lf
  | _, _ => False
  end.

(* Path accessors : ctree_sub returns a count (for unreachable traces),      *)
(* which ctree_mem simplies to a boolean for reachable traces.               *)

Fixpoint ctree_sub (t : ctree) (et : colseq) {struct t} : nat :=
  match t, et with
  | Ctree_node t1 t2 t3, Adds e et' =>
    (palette (fun _ => 0) (ctree_sub t1) (ctree_sub t2) (ctree_sub t3)) e et'
  | Ctree_leaf lf, seq0 => S (ctree_sub lf et)
  | _, _ => 0
  end.

Definition ctree_mem t et := negb (0 =d (ctree_sub t et)).

(* Constructor and accessor for pairs.                                       *)

Definition ctree_empty_pair : ctree_pair :=
  Ctree_pair Ctree_empty Ctree_empty.

Definition ctree_pair_sub (ctp : ctree_pair) b :=
  let (t0, t1) := ctp in if b is false then t0 else t1.

(* A function for constructing canonical leaves. *)

Definition ctree_leaf_of n := iter n Ctree_leaf Ctree_empty.

(* A general cons function, used for now only in the restriction operation  *)
(* We could use it in the union and rot operations too, but it doesn't seem *)
(* worthwhile. The redundant case analysis is needed to interlock the       *)
(* computation and prevent the accumulation of thunks.                      *)

Definition ctree_cons t1 t2 t3 :=
  let t := Ctree_node t1 t2 t3 in
  match t with
  | Ctree_node Ctree_empty Ctree_empty Ctree_empty => t1
  | Ctree_node _ Ctree_empty Ctree_empty => t
  | Ctree_node _ _ Ctree_empty => t
  | _ => t
  end.

(* Specialized constructors, used to build single-branch trees.              *)

Definition ctree_cons0 (_ : ctree) := Ctree_empty.

Definition ctree_cons1 t := ctree_cons t Ctree_empty Ctree_empty.

Definition ctree_cons2 t := ctree_cons Ctree_empty t Ctree_empty.

Definition ctree_cons3 t := ctree_cons Ctree_empty Ctree_empty t.

(* Any proper leaf will do for reachable trees, so we provide a single one   *)
(* that can be shared.                                                       *)

Definition ctree_simple_leaf : ctree := Ctree_leaf Ctree_empty.

(* The actual, optimized construction of a single-branch tree from a config  *)
(* coloring map belongs in colorconfig.v, but we can give a spec right here, *)
(* and prove its main properties.                                            *)

Definition ctree_cons_e : color -> ctree -> ctree :=
  palette ctree_cons0 ctree_cons1 ctree_cons2 ctree_cons3.

Definition ctree_of_ttail : colseq -> ctree :=
  foldr ctree_cons_e ctree_simple_leaf.

(* The union operation is now interlocked, to match the rotlr operation that *)
(* is also interlocked now, to avoid the generation of a large number of     *)
(* transient thunks in the intermediate reachable tree (for the initial tree *)
(* the 150,000 or so thunks we unlikely to be a problem.                     *)

Fixpoint ctree_union (tl tr : ctree) {struct tr} : ctree :=
  match tl, tr with
  | Ctree_empty, _ => tr
  | _, Ctree_empty => tl
  | Ctree_leaf _, _ => ctree_simple_leaf
  | _, Ctree_leaf _ => ctree_simple_leaf
  | Ctree_node tl1 tl2 tl3, Ctree_node tr1 tr2 tr3 =>
      ctree_cons (ctree_union tl1 tr1) (ctree_union tl2 tr2) (ctree_union tl3 tr3)
  end.

(* Rotations are done directly on the reachable sets, in order to save work *)
(* during the inner loop of gram tree restriction. The input to the initial *)
(* restriction is the cons of the three rotations of the tree reflecting    *)
(* the normal paths.                                                        *)

Fixpoint ctree_rotl (t : ctree) : ctree :=
  if t is Ctree_node t1 t2 t3 then
    ctree_cons (ctree_rotl t3) (ctree_rotl t1) (ctree_rotl t2)
  else t.

Fixpoint ctree_rotr (t : ctree) : ctree :=
  if t is Ctree_node t1 t2 t3 then
      ctree_cons (ctree_rotr t2) (ctree_rotr t3) (ctree_rotr t1)
  else t.

Definition ctree_cons_rot t := ctree_cons t (ctree_rotl t) (ctree_rotr t).

(*   The input to subsequent restrictions is the union of the left and right *)
(* rotations of the set of traces that were reached in during the previous   *)
(* iteration (by construction, there are no chromograms left that match      *)
(* reached traces); here we define an optimized union-of-rotations function  *)
(* for that case.                                                            *)
(*   Oddly, with this design the chromogram tree is NEVER symmetrical except *)
(* when we reach the fixpoint. Forcing the symmetryby building the union of *)
(* all rotations would save half the work here, only to add 33% more to the  *)
(* gram tree restriction. Contrarily, it might be useful to intersect the    *)
(* set with actually unreachable paths as some pruning might occur higher;   *)
(* for now, we don't --- we'd need to define intersecting versions of rotl   *)
(* and rotr as those special cases of union occur often (reachable sets are  *)
(* sparse). We could also preremove these colorings that have been reached   *)
(* ``by permutation'', rather than wait for the next ctree iteration to      *)
(* clear them; again, it's not obvious how much we stand to gain.            *)

Fixpoint ctree_union_rotlr (tl tr : ctree) {struct tr} : ctree :=
  match tl, tr with
  | Ctree_empty, Ctree_node t1 t2 t3 =>
      ctree_cons (ctree_rotr t2) (ctree_rotr t3) (ctree_rotr t1)
  | Ctree_node t1 t2 t3, Ctree_empty =>
      ctree_cons (ctree_rotl t3) (ctree_rotl t1) (ctree_rotl t2)
  | Ctree_node tl1 tl2 tl3, Ctree_node tr1 tr2 tr3 =>
      let cur := ctree_union_rotlr in
      ctree_cons (cur tl3 tr2) (cur tl1 tr3) (cur tl2 tr1)
  | Ctree_empty, _ => tr
  | _, Ctree_empty => tl
  | _, Ctree_node t1 t2 t3 =>
    if ctree_cons (ctree_rotr t2) (ctree_rotr t3) (ctree_rotr t1) is Ctree_empty
    then tl else ctree_simple_leaf
  | Ctree_node t1 t2 t3, _ =>
    if ctree_cons (ctree_rotl t3) (ctree_rotl t1) (ctree_rotl t2) is Ctree_empty
    then tr else ctree_simple_leaf
  | _, _ => ctree_simple_leaf
  end.

Definition ctree_rotlr t := ctree_union_rotlr t t.

(* A disjointness test, for checking contracts.                             *)

Fixpoint ctree_disjoint (tl tr : ctree) {struct tr} : bool :=
  match tl, tr with
  | Ctree_leaf _, Ctree_leaf _ => false
  | Ctree_node tl1 tl2 tl3, Ctree_node tr1 tr2 tr3 =>
      if ctree_disjoint tl1 tr1
      then if ctree_disjoint tl2 tr2 then ctree_disjoint tl3 tr3 else false
      else false
  | _, _ => true
  end.

(* Properties of classifiers : folding back expanded tests, using equality. *)

Lemma fold_ctree_empty : forall A (ve vne : A) t,
 (if t is Ctree_empty then ve else vne) = (if ctree_empty t then ve else vne).
Proof. by move=> A ve vne; case. Qed.

Lemma fold_ctree_leaf : forall A (vlf vnlf : A) t,
 (if t is Ctree_leaf _ then vlf else vnlf) = (if ctree_leaf t then vlf else vnlf).
Proof. by move=> A vlf vnlf; case. Qed.

Lemma ctree_empty_eq : forall t, ctree_empty t -> t = Ctree_empty.
Proof. by case. Qed.

Lemma ctree_empty_node_eq : forall t1 t2 t3,
 ctree_empty_node (Ctree_node t1 t2 t3) = true -> eq3_Ctree_empty t1 t2 t3.
Proof. by do 3 (case; [ do 3 intro | intro | idtac ]). Qed.

Lemma ctree_empty_nodeP : forall t,
 reflect (t = Ctree_node Ctree_empty Ctree_empty Ctree_empty) (ctree_empty_node t).
Proof.
by case; first [right | do 3 (case; [do 3 intro | intro | idtac]); constructor].
Qed.

(* Most properties of ctree_sel and ctree_proper are given below, but there  *)
(* are a few identities that are not reductions.                             *)

Lemma ctree_sel_0 : forall t, ctree_sel t Color0 = Ctree_empty.
Proof. by case. Qed.

Lemma ctree_proper_sel : forall h t e,
 ctree_proper h t -> ctree_proper (pred h) (ctree_sel t e).
Proof. by move=> [|h] [t1 t2 t3|lf|] //= [|||] [Hne Ht1 Ht2 Ht3] /=. Qed.

(* Properties of the lookup functions.                                       *)

Lemma ctree_sub_0 : forall t (et : colseq), et Color0 -> ctree_sub t et = 0.
Proof.
move=> t et; elim: et t => [|e et Hrec] //.
by case=> // [t1 t2 t3]; case: e => /=; auto.
Qed.

Lemma ctree_mem_0 : forall t (et : colseq), et Color0 -> ctree_mem t et = false.
Proof. by move=> *; rewrite /ctree_mem ctree_sub_0. Qed.

Lemma ctree_mem_seq0 : forall t : ctree, ctree_mem t seq0 = ctree_leaf t.
Proof. by case. Qed.

Lemma ctree_sub_sel : forall t (e : color) (et : colseq),
 ctree_sub t (Adds e et) = ctree_sub (ctree_sel t e) et.
Proof. by move=> [t1 t2 t3|lf|] // [|||] et. Qed.

Lemma ctree_mem_sel : forall t (e : color) (et : colseq),
 ctree_mem t (Adds e et) = ctree_mem (ctree_sel t e) et.
Proof. by move=> *; rewrite /ctree_mem !ctree_sub_sel. Qed.

Lemma ctree_mem_leaf : forall lf et, ctree_mem (Ctree_leaf lf) et = (0 =d size et).
Proof. by move=> lf [|e et]. Qed.

(* Properties of the leaf constructor. *)

Lemma ctree_leaf_of_proper : forall n, ctree_proper 0 (ctree_leaf_of n).
Proof. by case=> //=; elim=> /=. Qed.

Lemma ctree_sub_leaf_of : forall n et,
 ctree_sub (ctree_leaf_of n) et = (if size et =d 0 then n else 0).
Proof. by move=> [|n] [|e et] //=; elim: n => [|n Hrec] /=; auto. Qed.

(* Properties of the interlocking constructor. *)

Lemma ctree_cons_spec : forall t1 t2 t3, let t := Ctree_node t1 t2 t3 in
 ctree_cons t1 t2 t3 = (if ctree_empty_node t then Ctree_empty else t).
Proof. by move=> t1 t2 t3; case t1; case t2; case t3. Qed.

Lemma ctree_leaf_cons : forall t1 t2 t3, ctree_leaf (ctree_cons t1 t2 t3) = false.
Proof.
move=> t1 t2 t3; rewrite ctree_cons_spec.
by case Ht: (ctree_empty_node (Ctree_node t1 t2 t3)).
Qed.

Lemma ctree_sel_cons : forall t1 t2 t3 e,
 ctree_sel (ctree_cons t1 t2 t3) e = ctree_sel (Ctree_node t1 t2 t3) e.
Proof.
move=> t1 t2 t3 e; rewrite ctree_cons_spec.
case Ht: (ctree_empty_node (Ctree_node t1 t2 t3)) => //.
by rewrite (ctree_empty_nodeP _ Ht); case e.
Qed.

Lemma ctree_cons_proper : forall h t1 t2 t3,
   ctree_proper h t1 -> ctree_proper h t2 -> ctree_proper h t3 ->
 ctree_proper (S h) (ctree_cons t1 t2 t3).
Proof.
move=> h t1 t2 t3 Ht1 Ht2 Ht3; rewrite ctree_cons_spec.
by case Ht: (ctree_empty_node (Ctree_node t1 t2 t3)); split.
Qed.

Lemma ctree_sub_cons : forall t1 t2 t3 et,
 ctree_sub (ctree_cons t1 t2 t3) et = ctree_sub (Ctree_node t1 t2 t3) et.
Proof.
move=> t1 t2 t3 [|e et]; rewrite ctree_cons_spec;
 case Ht: (ctree_empty_node (Ctree_node t1 t2 t3)) => //.
by rewrite (ctree_empty_nodeP _ Ht); case e.
Qed.

Lemma ctree_mem_cons : forall t1 t2 t3 et,
 ctree_mem (ctree_cons t1 t2 t3) et = ctree_mem (Ctree_node t1 t2 t3) et.
Proof. by move=> *; rewrite /ctree_mem ctree_sub_cons. Qed.

(* Properties of the branch constructors. *)

Lemma ctree_cons_e_spec : forall (e : color) t,
 let t_if_e c := if c =d e then t else Ctree_empty in
 ctree_cons_e e t = ctree_cons (t_if_e Color1) (t_if_e Color2) (t_if_e Color3).
Proof. by do 2 case. Qed.

Lemma ctree_cons_e_proper : forall h e t, ctree_proper h t ->
   ctree_proper (S h) (ctree_cons_e e t).
Proof.
move=> h e t Ht; rewrite ctree_cons_e_spec.
by apply ctree_cons_proper; case e; simpl.
Qed.

Lemma ctree_of_ttail_proper : forall h (et : colseq), size et = h ->
  ctree_proper h (ctree_of_ttail et).
Proof.
by move=> _ et <-; elim: et => [|e et Hrec] //; apply: ctree_cons_e_proper.
Qed.

Lemma ctree_of_ttail_mem : forall et et' : colseq,
 negb (et Color0) -> reflect (et' = et) (ctree_mem (ctree_of_ttail et) et').
Proof.
elim=> [|e et Hrec] et' /=; first by case et'; constructor.
move/norP=> [He Het]; rewrite ctree_cons_e_spec ctree_mem_cons.
case: et' => [|e' et'] /=; first by constructor.
case De': e'; first
 [ by constructor; move=> H; case/idP: He; case: H => <- _
 | rewrite ctree_mem_sel /= -De'; case: (e' =P e) => [Ee|He'] /=;
   try (rewrite -Ee /=; case: (Hrec et' Het) => [Det'|Het']);
   by constructor; first [ rewrite Det' | case ] ].
Qed.

(* Properties of the union. *)

Lemma ctree_union_Nl : forall t, ctree_union Ctree_empty t = t.
Proof. by case. Qed.

Lemma ctree_union_Nr : forall t, ctree_union t Ctree_empty = t.
Proof. by case. Qed.

Lemma ctree_union_sym : forall t1 t2, ctree_union t1 t2 = ctree_union t2 t1.
Proof.
elim=> [t11 Hrec1 t12 Hrec2 t13 Hrec3|l1 Hrec|] [t21 t22 t23|l2|] //=.
by rewrite Hrec1 Hrec2 Hrec3.
Qed.

Lemma ctree_union_proper : forall h tl tr,
 ctree_proper h tl -> ctree_proper h tr -> ctree_proper h (ctree_union tl tr).
Proof.
elim=> [|h Hrec] tl tr; first by case: tl => //; case tr.
case: tl => // [tl1 tl2 tl3|]; case: tr => //= tr1 tr2 tr3.
move=> [Htlne Htl1 Htl2 Htl3] [Htrne Htr1 Htr2 Htr3].
apply ctree_cons_proper; auto.
Qed.

Lemma ctree_mem_union : forall h tl tr et,
   ctree_proper h tl -> ctree_proper h tr ->
 ctree_mem (ctree_union tl tr) et = ctree_mem tl et || ctree_mem tr et.
Proof.
rewrite /ctree_mem; elim=> [|h Hrec] tl tr et.
  by case: tl; rewrite ?ctree_union_Nl //; case: tr => //; case et.
case: tl; rewrite ?ctree_union_Nl //=; move=> tl1 tl2 tl3 [Htlne Htl1 Htl2 Htl3].
case: tr => //= [tr1 tr2 tr3|]; last by rewrite orbF.
move=> [Htrne Htr1 Htr2 Htr3]; rewrite ctree_sub_cons.
case: et => [|[|||] et] /=; auto.
Qed.

(* Properties of the rotations. *)

Lemma ctree_rotl_proper : forall h t,
  ctree_proper h t -> ctree_proper h (ctree_rotl t).
Proof.
elim=> [|h Hrec] [t1 t2 t3|lf|] //= [Hne Ht1 Ht2 Ht3].
apply ctree_cons_proper; auto.
Qed.

Lemma ctree_rotr_proper :  forall h t,
  ctree_proper h t -> ctree_proper h (ctree_rotr t).
Proof.
elim=> [|h Hrec] [t1 t2 t3|lf|] //= [Hne Ht1 Ht2 Ht3].
apply ctree_cons_proper; auto.
Qed.

Lemma ctree_mem_rotl : forall t et,
 ctree_mem (ctree_rotl t) et = ctree_mem t (permt Eperm312 et).
Proof.
rewrite /ctree_mem; move=> t et;
 elim: et t => [|e et Hrec] [t1 t2 t3|lf|] //=;
 by rewrite ctree_sub_cons //; case: e => /=.
Qed.

Lemma ctree_mem_rotr : forall t et,
  ctree_mem (ctree_rotr t) et = ctree_mem t (permt Eperm231 et).
Proof.
rewrite /ctree_mem; move=> t et.
elim: et t => [|e et Hrec] [t1 t2 t3|lf|] //=;
 by rewrite ctree_sub_cons //; case: e => /=.
Qed.

(* Properties of the initial reachable set constructor. *)

Lemma ctree_cons_rot_proper : forall h t,
 ctree_proper h t -> ctree_proper (S h) (ctree_cons_rot t).
Proof.
move=> h t Ht; rewrite /ctree_cons_rot.
by apply ctree_cons_proper;
  [idtac | apply ctree_rotl_proper | apply ctree_rotr_proper].
Qed.

Lemma ctree_mem_cons_rot : forall t et,
 ctree_mem (ctree_cons_rot t) et = ctree_mem t (ttail et).
Proof.
rewrite /ctree_cons_rot /ttail; move=> t [|e et].
  by rewrite /= ctree_mem_seq0 ctree_leaf_cons ctree_mem_0.
case: e; first
 [ by rewrite /= !ctree_mem_0
 | rewrite ctree_mem_cons {1}/ctree_mem /=;
   by rewrite ?permt_id -1?ctree_mem_rotl -1?ctree_mem_rotr ].
Qed.

(* Properties of the union-of-rotations combination. *)

Lemma ctree_union_rotlr_spec : forall tl tr,
 ctree_union_rotlr tl tr = ctree_union (ctree_rotl tl) (ctree_rotr tr).
Proof.
move=> tl; elim: tl => [tl1 Hrec1 tl2 Hrec2 tl3 Hrec3|lfl Hrec|] tr.
- case: tr => [tr1 tr2 tr3|lf|] //=.
    symmetry; rewrite 2!ctree_cons_spec Hrec1 Hrec2 Hrec3.
    move: (ctree_rotl tl3) (ctree_rotl tl1) (ctree_rotl tl2) => tl1' tl2' tl3'.
    move: (ctree_rotr tr2) (ctree_rotr tr3) (ctree_rotr tr1) => tr1' tr2' tr3'.
    case Etl: (ctree_empty_node (Ctree_node tl1' tl2' tl3')).
      case (ctree_empty_node_eq Etl).
      by rewrite 4!ctree_union_Nl ctree_cons_spec.
    case Etr: (ctree_empty_node (Ctree_node tr1' tr2' tr3')); last done.
    case (ctree_empty_node_eq Etr).
    by rewrite 4!ctree_union_Nr ctree_cons_spec Etl.
  by case: (ctree_cons (ctree_rotl tl3) (ctree_rotl tl1) (ctree_rotl tl2)).
- case: tr => [tr1 tr2 tr3|lf|] //=.
  by case (ctree_cons (ctree_rotr tr2) (ctree_rotr tr3) (ctree_rotr tr1)).
by rewrite /ctree_rotl ctree_union_Nl; case tr.
Qed.

Lemma ctree_rotlr_proper : forall h t,
 ctree_proper h t -> ctree_proper h (ctree_rotlr t).
Proof.
move=> h t Ht; rewrite /ctree_rotlr ctree_union_rotlr_spec.
by apply ctree_union_proper; [apply ctree_rotl_proper | apply ctree_rotr_proper].
Qed.

Lemma ctree_mem_rotlr : forall h t, ctree_proper h t -> forall et,
 let mem_et312 := ctree_mem t (permt Eperm312 et) in
 let mem_et231 := ctree_mem t (permt Eperm231 et) in
 ctree_mem (ctree_rotlr t) et = mem_et312 || mem_et231.
Proof.
move=> h t Ht et; rewrite /ctree_rotlr ctree_union_rotlr_spec.
by rewrite -ctree_mem_rotl -ctree_mem_rotr (@ctree_mem_union h) //;
  [ apply ctree_rotl_proper | apply ctree_rotr_proper ].
Qed.

(* Exact interpretation of the disjointness test (the 4ct requires only one *)
(* direction).                                                              *)

Lemma ctree_mem_disjoint_spec : forall tl tr,
 reflect (exists et, ctree_mem tl et && ctree_mem tr et)
         (negb (ctree_disjoint tl tr)).
Proof.
move=> tl; have Ineg := negb_intro (ctree_disjoint _ _).
elim: tl => [tl1 Hrec1 tl2 Hrec2 tl3 Hrec3|lfl Hrec|] [tr1 tr2 tr3|lfr|];
 try (constructor; move=> [et Het]; case/negPf: Het => //=;
      case: et => //= *; apply andbF).
  rewrite /= -if_negb; case: {Hrec1}(Hrec1 tr1) => [Hc1|Hn1].
    by left; case: Hc1 => [et Het]; exists (Adds Color1 et); simpl.
  rewrite /= -if_negb; case: {Hrec2}(Hrec2 tr2) => [Hc2|Hn2].
    by left; case: Hc2 => [et Het]; exists (Adds Color2 et); simpl.
  case: {Hrec3}(Hrec3 tr3) => [Hc3|Hn3].
    by left; case: Hc3 => [et Het]; exists (Adds Color3 et); simpl.
  right; move=> [et Het]; case/idP: (Het).
  case: et Het => [|[|||] et] Het //; [case Hn1 | case Hn2 | case Hn3];
    by exists et.
by constructor; exists (seq0 : colseq).
Qed.

Lemma ctree_mem_disjoint : forall tl tr et, ctree_disjoint tl tr ->
 ctree_mem tr et -> ctree_mem tl et = false.
Proof.
move=> tl tr et Ht Hpr; apply: (introF idP) => Hpl.
by case/(ctree_mem_disjoint_spec _ _): Ht; exists et; rewrite Hpr Hpl.
Qed.

Unset Implicit Arguments.