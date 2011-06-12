(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import color.
Require Import chromogram.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Sets of chromograms are stored as 4-way trees, much like the edge traces. *)
(* In a way, gram trees are simpler than coloring trees because they don't   *)
(* store matching counts; however, to save space the last two layers have    *)
(* been collapsed, so that there are eight different kinds of leaves (three  *)
(* could suffice, but we would need to track context kinds in the inner loop *)
(* of the restrict procedure). The only real operations on gram trees are    *)
(* initialization and restriction, so this file is mostly boilerplate.       *)

Inductive gtree : Set :=
  | Gtree_node : forall t0 t1 t2 t3 : gtree, gtree
  | Gtree_leaf0 : gtree
  | Gtree_leaf1 : gtree
  | Gtree_leaf2 : gtree
  | Gtree_leaf3 : gtree
  | Gtree_leaf01 : gtree
  | Gtree_leaf12 : gtree
  | Gtree_leaf13 : gtree
  | Gtree_leaf23 : gtree
  | Gtree_empty : gtree.

(* The following classifiers are effective. *)

Definition gtree_empty t := if t is Gtree_empty then true else false.

Lemma fold_gtree_empty : forall A (ve vne : A) t,
  (if t is Gtree_empty then ve else vne) = (if gtree_empty t then ve else vne).
Proof. by move=> A ve vne; case. Qed.

Lemma gtree_emptyP : forall t, reflect (t = Gtree_empty) (gtree_empty t).
Proof. move=> t; case t; constructor; done. Qed.

Definition gtree_empty_empty t H := gtree_emptyP t H.
Opaque gtree_empty_empty.

(* Only the membership function needs to be defined on trees; enumerating *)
(* matches can be deifned based solely on the characteristic function.    *)

Fixpoint gtree_mem (t : gtree) (w : chromogram) {struct w} : bool :=
  match t, w with
  | Gtree_node t0 t1 t2 t3, Adds s w' =>
      gtree_mem (gram_symbol_rec (P := fun _ => _) t0 t1 t2 t3 s) w'
  | Gtree_leaf0, Adds Gpush seq0 => true
  | Gtree_leaf1, Adds Gskip seq0 => true
  | Gtree_leaf2, Adds Gpop0 seq0 => true
  | Gtree_leaf3, Adds Gpop1 seq0 => true
  | Gtree_leaf01, Adds Gpush seq0 => true
  | Gtree_leaf01, Adds Gskip seq0 => true
  | Gtree_leaf12, Adds Gskip seq0 => true
  | Gtree_leaf12, Adds Gpop0 seq0 => true
  | Gtree_leaf13, Adds Gskip seq0 => true
  | Gtree_leaf13, Adds Gpop1 seq0 => true
  | Gtree_leaf23, Adds Gpop0 seq0 => true
  | Gtree_leaf23, Adds Gpop1 seq0 => true
  | _, _ => false
  end.

(* Functions that check for / count matches for arbitrary predicates. *)
(* Could move to bare chromograms, or to a separate ``match'' file.   *)

Definition spec_ctree := colseq -> bool.

Fixpoint has_match (bs : bit_stack) (ct : spec_ctree) (w : chromogram) {struct w}
                   : bool :=
  let sct e et := ct (Adds e et) in
  match w with
  | seq0 =>
    ct seq0
  | Adds Gpush w' =>
    has_match (Bpush0 bs) (sct Color2) w' || has_match (Bpush1 bs) (sct Color3) w'
  | Adds Gskip w' =>
    has_match bs (sct Color1) w'
  | Adds Gpop0 w' =>
    match bs with
    | Bpush0 bs' => has_match bs' (sct Color2) w'
    | Bpush1 bs' => has_match bs' (sct Color3) w'
    | _ => false
    end
  | Adds Gpop1 w' =>
    match bs with
    | Bpush0 bs' => has_match bs' (sct Color3) w'
    | Bpush1 bs' => has_match bs' (sct Color2) w'
    | _ => false
    end
  end.

Lemma has_matchP : forall bs (ct : spec_ctree) w,
  reflect (exists2 et, ct et & matchpg bs et w) (has_match bs ct w).
Proof.
move=> bs ct w; elim: w bs ct => [|s w Hrec] bs ct.
  simpl; case Hct: (ct seq0); constructor; first by exists (seq0 : colseq).
  by move=> [[|c et] Hct' Het] //; case/idP: Hct.
case: s; rewrite /= -/colseq.
case: (Hrec (Bpush0 bs) (fun et => ct (Adds Color2 et))) => [Hc02|Hn02].
 by left; case: Hc02 => [et Hct Hm]; exists (Adds Color2 et).
 case: (Hrec (Bpush1 bs) (fun et => ct (Adds Color3 et))) => [Hc13|Hn13].
    by left; case: Hc13 => [et Hct Hm]; exists (Adds Color3 et).
  by right; case=> [[|[|||] et] Hct Het] //; [apply Hn02 | apply Hn13]; exists et.
 case: (Hrec bs (fun et => ct (Adds Color1 et))) => [Hc1|Hn1].
    by left; case: Hc1 => [et Hct Hm]; exists (Adds Color1 et).
  by right; case=> [[|[|||] et] Hct Het] //; apply Hn1; exists et.
 case: bs => [|bs|bs].
   by right; case=> [[|[|||] et] Hct Het].
   case: (Hrec bs (fun et => ct (Adds Color2 et))) => [Hc2|Hn2].
      by left; case: Hc2 => [et Hct Hm]; exists (Adds Color2 et).
    by right; case=> [[|[|||] et] Hct Het] //; apply Hn2; exists et.
  case: (Hrec bs (fun et => ct (Adds Color3 et))) => [Hc3|Hn3].
    by left; case: Hc3 => [et Hct Hm]; exists (Adds Color3 et).
  by right; case=> [[|[|||] et] Hct Het] //; apply Hn3; exists et.
case: bs => [|bs|bs].
 by right; case=> [[|[|||] et] Hct Het].
 case: (Hrec bs (fun et => ct (Adds Color3 et))) => [Hc3|Hn3].
    by left; case: Hc3 => [et Hct Hm]; exists (Adds Color3 et).
  by right; case=> [[|[|||] et] Hct Het] //; apply Hn3; exists et.
case: (Hrec bs (fun et => ct (Adds Color2 et))) => [Hc2|Hn2].
  by left; case: Hc2 => [et Hct Hm]; exists (Adds Color2 et).
by right; case=> [[|[|||] et] Hct Het] //; apply Hn2; exists et.
Qed.

Notation xmatchP := (has_matchP _ _ _).

Definition spec_gtree : Set := chromogram -> bool.

Fixpoint match_count (st : spec_gtree) (bs : bit_stack) (et : colseq) {struct et}
                     : nat :=
  let sub_st s w := st (Adds s w) in
  match et with
  | seq0 => if st seq0 then 1 else 0
  | Adds Color0 _ => 0
  | Adds Color1 et' => match_count (sub_st Gskip) bs et'
  | Adds Color2 et' =>
    let sub_pop := match bs with
    | Bstack0 => 0
    | Bpush0 bs' => match_count (sub_st Gpop0) bs' et'
    | Bpush1 bs' => match_count (sub_st Gpop1) bs' et' end in
    match_count (sub_st Gpush) (Bpush0 bs) et' + sub_pop
  | Adds Color3 et' =>
    let sub_pop := match bs with
    | Bstack0 => 0
    | Bpush0 bs' => match_count (sub_st Gpop1) bs' et'
    | Bpush1 bs' => match_count (sub_st Gpop0) bs' et' end in
    match_count (sub_st Gpush) (Bpush1 bs) et' + sub_pop
  end.

Definition gtree_sub t : bit_stack -> colseq -> nat := match_count (gtree_mem t).

Lemma match_countP : forall (st : spec_gtree) bs et,
  reflect (exists2 w, st w & matchpg bs et w) (negb (0 =d (match_count st bs et))).
Proof.
move=> st bs et; elim: et st bs.
move=> st bs; simpl; case Hst: (st seq0); constructor.
 by exists (seq0 : chromogram).
 by move=> [[|s w] Hwt Hwe]; rewrite ?Hst in Hwt.
have Eneq0addn: forall n n',
  let neq0 m := negb (0 =d m) in neq0 (n + n') = neq0 n || neq0 n'.
  by move=> [|n] [|n'].
move=> [|||] et Hrec st bs; rewrite /= ?eq0E ?eqnE ?Eneq0addn -/chromogram;
 [ idtac
 | case: {Hrec}(Hrec (fun w => st (Adds Gskip w)) bs) => [Hw|Hnw]
 | case: (Hrec (fun w => st (Adds Gpush w)) (Bpush0 bs)) => [Hw|Hnw]
 | case: (Hrec (fun w => st (Adds Gpush w)) (Bpush1 bs)) => [Hw|Hnw] ]; first
 [ constructor
 | case: bs Hnw => [|bs|bs] Hnw; first
    [ constructor
    | case: (Hrec (fun w => st (Adds Gpop0 w)) bs) => [Hw|Hnw']; constructor
    | case: (Hrec (fun w => st (Adds Gpop1 w)) bs) => [Hw|Hnw']; constructor ] ];
 first
 [ rename Hw into Hw; case: Hw => [w Hwe Hwt]; first
    [ by exists (Adds Gpush w)
    | by exists (Adds Gskip w)
    | by exists (Adds Gpop0 w)
    | by exists (Adds Gpop1 w) ]
 | move=> [[|[|||] w] Hwe Hwt]; first
    [ done
    | by apply Hnw; exists w
    | by apply Hnw'; exists w ] ].
Qed.

Notation nmatchP := (match_countP _ _ _).

(* The gtree_empty4 function serves two purposes :                          *)
(*   - it allows contraction of empty trees, and reuse of unmodified trees  *)
(*   - it interlocks the tree computation, so that trees do NOT contain     *)
(*     thunks.                                                              *)
(* The latter point implies that the function must NOT short-circuit tests  *)

Definition gtree_empty_and t b :=
  match t, b with
  | _, false => false
  | Gtree_empty, true => true
  | _, _ => false
  end.

Lemma gtree_empty_and_spec : forall t b, gtree_empty_and t b = gtree_empty t && b.
Proof. by move=> t [|]; case t. Qed.

Definition gtree_empty4 t :=
  if t is Gtree_node t0 t1 t2 t3 then
    gtree_empty_and t0 (gtree_empty_and t1 (gtree_empty_and t2 (gtree_empty t3)))
  else false.

Inductive are_4_Gtree_empty : forall t0 t1 t2 t3 : gtree, Prop :=
  Gtree_empty4 : are_4_Gtree_empty Gtree_empty Gtree_empty Gtree_empty Gtree_empty.

Lemma gtree_empty4P : forall t0 t1 t2 t3,
  reflect (are_4_Gtree_empty t0 t1 t2 t3) (gtree_empty4 (Gtree_node t0 t1 t2 t3)).
Proof.
move=> t0 t1 t2 t3; rewrite /gtree_empty4 3!gtree_empty_and_spec.
apply introP; first by move: t0 t1 t2 t3; do 4 case=> //.
by move=> H H'; case: H' H.
Qed.

(* The restriction operation returns a partition of a gram tree into a pair *)
(* of gram trees.                                                           *)

Inductive gtree_pair : Set := Gtree_pair (t0 t1 : gtree).

Definition empty_gtree_pair : gtree_pair :=
  Gtree_pair Gtree_empty Gtree_empty.

Definition gtree_pair_sub (pt : gtree_pair) b :=
  let (t0, t1) := pt in if b is false then t0 else t1.

Definition sgtree_partition (st st' st'' : spec_gtree) : Prop :=
  forall w, (if st w then eqb else orb) (st' w) (st'' w) = false.

Definition gtree_pair_partition t (pt : gtree_pair) : Prop :=
  let (t0, t1) := pt in
  sgtree_partition (gtree_mem t) (gtree_mem t0) (gtree_mem t1).

Lemma match_count_0 : forall st : spec_gtree, (forall w, ~ st w) ->
  forall bs et, match_count st bs et = 0.
Proof.
move=> st Hst bs et; move: st bs {Hst}(fun w => introF idP (Hst w)).
elim: et => [|c et Hrec] st bs Hst; first by rewrite /= Hst.
by case c; rewrite /= ?Hrec //; case: bs => *; rewrite /= ?Hrec.
Qed.

Lemma gtree_mem_empty : forall w, gtree_mem Gtree_empty w = false.
Proof. by case. Qed.

Lemma gtree_sub_empty : forall bs et, gtree_sub Gtree_empty bs et = 0.
Proof. exact (match_count_0 (fun w => elimF idP (gtree_mem_empty w))). Qed.

Lemma gtree_sub_node_0 : forall bs t0 t1 t2 t3 (et : colseq),
 pred (size et) = 0 -> gtree_sub (Gtree_node t0 t1 t2 t3) bs et = 0.
Proof.
move=> bs t0 t1 t2 t3 [|e [|e' et]] // _; rewrite /gtree_sub /=.
have Htf: forall t, (if t is Gtree_empty then false else false) = false by case.
rewrite (Htf t0) (Htf t1) (Htf t2) (Htf t3) {Htf}.
by case: e => //; trivial; case: bs.
Qed.

Lemma match_count_eq : forall st st' : spec_gtree,
  st =1 st' -> match_count st =2 match_count st'.
Proof.
rewrite /eqfun; move=> st st' Est bs et; elim: et st st' Est bs.
  by move=> st st' Est; rewrite /= Est.
move=> [|||] et Hrec st st' Est bs //=; auto;
  rewrite -(Hrec (fun w => st' (Adds Gpush w))); auto;
  congr addn; case: bs => /=; auto.
Qed.

Lemma match_count_partition : forall st st' st'', sgtree_partition st st' st'' ->
  forall bs et,
  match_count st bs et = addn (match_count st' bs et) (match_count st'' bs et).
Proof.
move=> st st' st'' Hw bs et; elim: et st st' st'' Hw bs.
move=> st st' st'' Hw bs; move: {Hw}(Hw seq0) => /=.
  by case (st seq0); case (st' seq0); case (st'' seq0).
rewrite /sgtree_partition; case=> [|||] et Hrec st st' st'' Hw bs /=; auto;
 symmetry; rewrite addnC addnCA -addnA addnA;
 (rewrite -(Hrec (fun w => st (Adds Gpush w))); [congr addn | auto]);
 rewrite addnC; symmetry; case: bs; auto.
Qed.

Definition gtree_cons_pairs (t : gtree) (pt0 pt1 pt2 pt3 : gtree_pair) :=
  let (t'0, t''0) := pt0 in
  let (t'1, t''1) := pt1 in
  let (t'2, t''2) := pt2 in
  let (t'3, t''3) := pt3 in
  let mkpair0 t' t'' :=
    if gtree_empty4 t' then Gtree_pair t'0 t else
    if gtree_empty4 t'' then Gtree_pair t t''0 else Gtree_pair t' t'' in
  mkpair0 (Gtree_node t'0 t'1 t'2 t'3) (Gtree_node t''0 t''1 t''2 t''3).

Lemma gtree_cons_pairs_partition : forall t0 t1 t2 t3 pt0 pt1 pt2 pt3,
   gtree_pair_partition t0 pt0 -> gtree_pair_partition t1 pt1 ->
   gtree_pair_partition t2 pt2 -> gtree_pair_partition t3 pt3 ->
 let t := Gtree_node t0 t1 t2 t3 in
 gtree_pair_partition t (gtree_cons_pairs t pt0 pt1 pt2 pt3).
Proof.
move=> t0 t1 t2 t3 [t'0 t''0] [t'1 t''1] [t'2 t''2] [t'3 t''3].
rewrite /gtree_cons_pairs; pose st := gtree_mem (Gtree_node t0 t1 t2 t3).
case: (gtree_empty4P t'0 t'1 t'2 t'3) => [[]|Hne'].
  by move=> /= *; move=> w; rewrite -/st gtree_mem_empty; case (st w).
case: (gtree_empty4P t''0 t''1 t''2 t''3) => [[]|Hne''].
  by move=> /= *; move=> w; rewrite -/st gtree_mem_empty; case (st w).
by rewrite /= /sgtree_partition; move=> Ht0 Ht1 Ht2 Ht3 [|[|||] w] /=.
Qed.

Lemma gtree_mem0_cons_pairs : forall t0 t1 t2 t3 pt0 pt1 pt2 pt3,
    gtree_pair_partition t0 pt0 -> gtree_pair_partition t1 pt1 ->
    gtree_pair_partition t2 pt2 -> gtree_pair_partition t3 pt3 ->
 let sub0 pt := gtree_pair_sub pt false in
 let t := Gtree_node t0 t1 t2 t3 in
 let t' := Gtree_node (sub0 pt0) (sub0 pt1) (sub0 pt2) (sub0 pt3) in
 gtree_mem (sub0 (gtree_cons_pairs t pt0 pt1 pt2 pt3)) =1 gtree_mem t'.
Proof.
move=> t0 t1 t2 t3 [t'0 t''0] [t'1 t''1] [t'2 t''2] [t'3 t''3].
rewrite /gtree_cons_pairs.
case: (gtree_empty4P t'0 t'1 t'2 t'3) => [[]|Hne'].
  by move=> Ht0 Ht1 Ht2 Ht3 [|[|||] [|s w]].
case: (gtree_empty4P t''0 t''1 t''2 t''3) => [[]|Hne''] //.
move=> Ht0 Ht1 Ht2 Ht3 [|[|||] w] //=.
case: (gtree_mem t0 w) (gtree_mem t'0 w) (Ht0 w) => [|] [|]; case w; auto.
case: (gtree_mem t1 w) (gtree_mem t'1 w) (Ht1 w) => [|] [|]; case w; auto.
case: (gtree_mem t2 w) (gtree_mem t'2 w) (Ht2 w) => [|] [|]; case w; auto.
case: (gtree_mem t3 w) (gtree_mem t'3 w) (Ht3 w) => [|] [|]; case w; auto.
Qed.

Unset Implicit Arguments.