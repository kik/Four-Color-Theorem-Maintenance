(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import color.
Require Import chromogram.
Require Import gtree.
Require Import dyck.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Creation of the initial (full) chromogram tree. We reuse pairs to create  *)
(* the 2D table of trees indexed by (depth, bit0).                           *)

Section InitialGtree.

Lemma gtreeDataP : comparable gtree.
Proof. rewrite /comparable; decide equality. Qed.
Lemma gtreePairDataP : comparable gtree_pair.
Proof. rewrite /comparable; decide equality; apply: gtreeDataP. Qed.
Definition gtreePairData : dataSet := Eval compute in compareData gtreePairDataP.
Canonical Structure gtreePairData.

Definition gtree_table : Set := seq gtreePairData.

Definition init_gtree_h1 : gtree_table :=
  seq3 (Gtree_pair Gtree_leaf01 Gtree_leaf0)
       (Gtree_pair Gtree_leaf13 Gtree_leaf12)
       (Gtree_pair Gtree_leaf23 Gtree_leaf23).

Definition gtree_merge_pairs (pt0 pt1 pt2 : gtree_pair) :=
  let (t0, t0') := pt0 in
  let (t1, t1') := pt1 in
  let (t2, t3) := pt2 in
  Gtree_pair (Gtree_node t0 t1' t2 t3) (Gtree_node t0' t1 t3 t2).

Fixpoint gtree_merge_line (pt0 pt1 pt2 : gtree_pair) (lpt : gtree_table) (d : nat)
               {struct d} : gtree_table :=
  let rest :=
    match d, lpt return gtree_table with
    | 0, _ => seq0
    | S d', seq0 =>
        seq2 (gtree_merge_pairs empty_gtree_pair pt0 pt1)
             (gtree_merge_pairs empty_gtree_pair empty_gtree_pair pt0)
    | S d', Adds pt lpt' => gtree_merge_line pt pt0 pt1 lpt' d'
    end in
  Adds (gtree_merge_pairs pt0 pt1 pt2) rest.

Fixpoint gtree_init_table (d h' : nat) {struct h'} : gtree_table :=
  match h' with
  | 0 => init_gtree_h1
  | S h'' =>
      let tab := gtree_init_table (S d) h'' in
      if tab is Adds pt1 (Adds pt0 lpt) then
        gtree_merge_line pt0 pt1 empty_gtree_pair lpt d
      else tab
  end.

Definition gtree_init_tree h :=
  match h, gtree_init_table 0 (pred h) with
  | S _, Adds (Gtree_pair t _) _ => t
  | _, _ => Gtree_empty
  end.

Definition init_gtree_spec h w :=
  (size w =d h) && gram_balanced 0 false (cgram 0 false w).

Lemma match_count_balanced : forall h et,
  match_count (init_gtree_spec h) Bstack0 et =
    if (size et =d h) && negb (ctrace et Color0) then
      dyck (count_cbit1 (ctrace et))
    else 0.
Proof.
move=> h et; rewrite /init_gtree_spec /ctrace /dyck; pose sb : bitseq := seq0.
rewrite -[Bstack0]/(stack_of_bitseq sb) -{-4}[0]/(size sb) -(add0c (sumt et)).
have Hc1: cbit1 Color0 = odd (size sb) by done.
move Dsbs: (foldr addb false) => sbs.
have Hc0: cbit0 Color0 = addb false (sbs sb) by rewrite -Dsbs.
elim: et h {-4}Color0 sb false Hc0 Hc1.
  move=> [|h] c // [|b lb] b0 /=; first by rewrite -Dsbs /= addbF => <-; case c.
  by clear; case: {lb}(size lb) => /=; case: c => //; case b0.
move=> e et Hrec h c lb b0; rewrite add_last_adds /= addcA; case: h => [|h].
case De: e (match_count_0) => [|||] Em0 Enn /=; auto; rewrite Em0 /addn //=;
 case (stack_of_bitseq lb); auto.
move=> Hc0 Hc1; move: {Hrec}(Hrec h (e +c c)).
rewrite cbit0_addc cbit1_addc (addcC e c) {}Hc0 {}Hc1 -{sbs}Dsbs /=.
move: (add_last et (c +c e +c sumt et)) => cet; rewrite /setU1 eqdSS.
move: {c cet}(size et =d h) (cet Color0) (count_cbit1 cet) => b_h bc0 n23.
move=> Hrec; move: {Hrec}(Hrec (Adds (cbit0 e) lb) b0) (Hrec).
rewrite /eqd /= 2!addbA (addbC b0).
case De: e => [|||] /= Hrec0 Hrec; first
 [ by rewrite andbC
 | exact: Hrec
 | by rewrite {}Hrec0 //; case: lb Hrec => [|b lb''] /=;
     [ clear; case: {3}n23 => *; rewrite /= ?addn0
     | rewrite ?negb_elim 1?addbA -1?(addbC b); case: b => /=; move=> H;
        try rewrite {}H ?negb_elim //; case: (b_h && negb bc0) ] ].
Qed.

Fixpoint gtree_table_sub (tab : gtree_table) (n : nat) {struct tab}
                         : bool -> gtree :=
  match tab, n with
  | seq0, _ => fun _ => Gtree_empty
  | Adds pt _, O => gtree_pair_sub pt
  | Adds _ tab', S n' => gtree_table_sub tab' n'
  end.

Notation Local tsub := gtree_table_sub.

Lemma gtree_mem_init_tree : forall h w,
  gtree_mem (gtree_init_tree h) w = init_gtree_spec h w.
Proof.
move=> [|h] w; [by rewrite gtree_mem_empty; case w | simpl].
transitivity (gtree_mem (gtree_table_sub (gtree_init_table 0 h) 0 false) w).
  by case (gtree_init_table 0 h).
have:= leqnn 0; rewrite /init_gtree_spec; move: 0 {-2 3}0 false w => d.
apply (@proj2 ((if d is 0 then 0 else 1) < size (gtree_init_table d h))).
elim: h d => [|h Hrec] d /=.
  by split; [ case d | move=> [|[|[|d']]] [|] [|s [|s' w']] //; case s ].
  case: {Hrec}(Hrec (S d)); move: (gtree_init_table (S d) h).
move=> [|pt1 [|pt0 lpt]] // _ Hsub.
split; first by case: d {Hsub} => [|[|d]]; case: lpt.
move=> dw bw w Hd.
transitivity
  (gtree_mem (let elt := Seq empty_gtree_pair pt1 pt0 & lpt in
              Gtree_node (tsub elt (S (S dw)) bw) (tsub elt (S dw) (negb bw))
                         (tsub elt dw bw)         (tsub elt dw (negb bw)))
             w).
  elim: dw d Hd pt0 pt1 empty_gtree_pair lpt {Hsub}.
    move=> d Hd [t0 t0'] [t1 t1'] [t2 t3] lpt; rewrite /gtree_merge_line /=.
    by case d; case: bw => /=.
  move=> dw Hrec [|d] Hd // pt0 pt1 pt2 [|pt lpt]; last by apply: (Hrec d).
  case: dw {Hrec Hd} => [|dw]; first by case: pt0 pt1 bw => [t1 t1'] [t2 t3] [|].
  case: dw => [|dw]; first by case: pt0 bw => [t2 t3] [|].
  by case: w bw => [|[|||] w] [|]; rewrite /= ?gtree_mem_empty.
case: w => [|[|||] w] //=; first
 [ exact (Hsub (S dw) _ w Hd)
 | exact (Hsub _ _ w (leqW Hd))
 | case: dw Hd => [|dw] Hd;
    [ rewrite andbF; case bw; exact (gtree_mem_empty w)
    | exact (Hsub _ _ w (leqW (leqW Hd))) ] ].
Qed.

End InitialGtree.

Unset Implicit Arguments.
