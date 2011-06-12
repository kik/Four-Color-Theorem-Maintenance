(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import color.
Require Import ctree.
Require Import dyck.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Creation of an initial (full) coloring tree, and its correctness theorem. *)
(* This tree is constructed by making successively tables of its non-empty   *)
(* leaves, then subtrees of height 1, 2, etc until h - 2, where h is the     *)
(* perimeter length (aka the ring size). Subtrees of odd traces are pruned   *)
(* at this stage, and the final tree (of height h - 1) is assembled from the *)
(* three pruned subtrees of height h - 2.                                    *)
(*   The tables are simply lists of tree pairs. The #n23th pair contains the *)
(* two subtrees that can occur after a trace where Color2 and Color3 occur a *)
(* total of n23 times; the first component of the tuple occurs at traces     *)
(* whose color sum is even ((color_bit0 (trace_sum et)) = false), the second *)
(* at odd-sum traces.                                                        *)

Lemma ctreeDataP : comparable ctree.
Proof. rewrite /comparable; decide equality. Qed.
Definition ctree_data : dataSet := Eval compute in compareData ctreeDataP.
Canonical Structure ctree_data.

Lemma ctreePairDataP : comparable ctree_pair.
Proof. rewrite /comparable; decide equality; apply: ctreeDataP. Qed.
Definition ctreePairData : dataSet := Eval compute in
  compareData ctreePairDataP.
Canonical Structure ctreePairData.

Definition ctree_table : Set := seq ctreePairData.

Section InitCtree.

Notation ctz := ctree_empty_pair (only parsing).

Definition ctree_table_sub (tab : ctree_table) (n23 : nat)
  (b0 : bool) : ctree := ctree_pair_sub (sub ctree_empty_pair tab n23) b0.

(* First, leaf construction.                                                 *)

Fixpoint ctree_add_dyck (m n : nat) {struct n} : ctree -> ctree :=
  if n is S n' then iter_n (S m) (fun m' => ctree_add_dyck (S m') n') else
  Ctree_leaf.

Fixpoint ctree_leaf_table_from (lf : ctree) (n h : nat) {struct h} : ctree_table :=
  match h with
  | O => seq0
  | S O => seq1 (Ctree_pair lf lf)
  | S (S h') =>
      Adds (Ctree_pair lf lf)
        (Adds (Ctree_pair Ctree_empty lf)
           (ctree_leaf_table_from (ctree_add_dyck 2 n lf) (S n) h'))
  end.

Definition ctree_leaf_table h : ctree_table :=
  let leaf1 := Ctree_leaf Ctree_empty in
  Adds (Ctree_pair Ctree_empty leaf1) (ctree_leaf_table_from leaf1 0 h).

(* Pairs are merged pairwise to build higher trees.                          *)
(* Ctree_node instead of ctree_cons would be correct here, but hard to prove.*)

Definition ctree_merge_pair (tu tu' : ctree_pair) : ctree_pair :=
  let (t0, t1) := tu in let (t2, t3) := tu' in
  Ctree_pair (ctree_cons t1 t2 t3) (ctree_cons t0 t3 t2).

Definition ctree_merge_table (tab : ctree_table) : ctree_table :=
  if tab is Adds line tab' then pairmap ctree_merge_pair line tab' else tab.

(* Pruning odd permutations.                                                 *)

Fixpoint ctree_prune_1 (t : ctree) : ctree :=
  if t is Ctree_node t1 t2 t3 then
    ctree_cons (ctree_prune_1 t1) t2 Ctree_empty
  else t.

Fixpoint ctree_prune_2 (t : ctree) : ctree :=
  if t is Ctree_node t1 t2 t3 then
    ctree_cons Ctree_empty (ctree_prune_2 t2) t3
  else t.

Fixpoint ctree_prune_3 (t : ctree) : ctree :=
  if t is Ctree_node t1 t2 t3 then
    ctree_cons t1 Ctree_empty (ctree_prune_3 t3)
  else t.

(* Putting everything together.                                              *)

Definition ctree_init_tree h :=
  if iter (pred h) ctree_merge_table (ctree_leaf_table h)
    is Adds (Ctree_pair t0 t1) (Adds (Ctree_pair t2 t3) _)
  then ctree_cons (ctree_prune_1 t1) (ctree_prune_2 t2) (ctree_prune_3 t3)
  else Ctree_empty.

(* Leaf correctness. *)

Lemma ctree_add_dyck_leaf_of : forall m n d : nat,
 ctree_add_dyck m n (ctree_leaf_of d) =
   ctree_leaf_of (gen_dyck (S m) (m + double n) + d).
Proof.
move=> m n; elim: n m => [|n Hrecn] m /=.
  by rewrite addn0 gen_dyck_all_close.
elim: m => [|m Hrecm] d; rewrite doubleS /=; first by rewrite addn0 Hrecn.
by rewrite Hrecm Hrecn doubleS addnA addnI !addnS.
Qed.

Lemma ctree_leaf_table_size : forall h, size (ctree_leaf_table h) = S h.
Proof.
move=> h; rewrite /ctree_leaf_table_from /=; congr S.
rewrite -(odd_double_half h) addnC; move: (Ctree_leaf Ctree_empty) 0.
by elim: (half h) => [|h2 Hrec] t n; [ case (odd h) | rewrite doubleS /= Hrec ].
Qed.

Lemma ctree_leaf_table_sub : forall h n23 b0, n23 <= h ->
 let c := ccons (odd n23) b0 in
 let cet := add_last seq0 (c +c (sumt seq0)) in
 let c23 := n23 + count_cbit1 cet in
 ctree_table_sub (ctree_leaf_table h) n23 b0 =
   (if cet Color0 then Ctree_empty else ctree_leaf_of (dyck c23)).
Proof.
move=> h n23 b0; rewrite /ctree_leaf_table -{1 2 4}[n23]odd_double_half.
move: (odd n23) (half n23) => b1 m; rewrite (addnC b1) => Hh.
rewrite /= addc0 cbit1_ccons /setU1 orbF addn0 -addnA -{2}[m]addn0.
set t1 := Ctree_leaf Ctree_empty.
rewrite -{1}[t1]/(ctree_leaf_of (dyck (double 0))).
rewrite -{t1}[t1]/(ctree_leaf_of (dyck (double 1))).
elim: m 0 h Hh => [|m Hrec] n.
  by rewrite /= !add0n addnC; case: b1; [ move=> [|[|h]] // | idtac ]; case b0.
move=> [|[|h]] Hh //.
by rewrite addSnnS -(Hrec (S n) h Hh) /dyck /= ctree_add_dyck_leaf_of !addn0.
Qed.

(* Global correctness; we run through the construction twice, once to check *)
(* that subtrees are proper, and once to check the counts.                  *)

Lemma ctree_init_tree_proper : forall h, ctree_proper h (ctree_init_tree h).
Proof.
move=> h; case Dh: h => [|h'] //=.
rewrite /ctree_init_tree; move Dltab: (ctree_leaf_table (S h')) => ltab /=.
move Dtab: (iter h' ctree_merge_table ltab) => tab.
have [Hlen Hsub]: h' + size tab = S h
  /\ forall n23, n23 < size tab -> forall b0,
     ctree_proper h' (ctree_table_sub tab n23 b0).
  move: (leq_addl 1 h'); rewrite -{tab}Dtab {1}/addn /= -Dh.
  elim: (h') => [|n Hrec] Hn.
    rewrite /= -{ltab}Dltab -Dh ctree_leaf_table_size; split; first done.
    move {Hn} => n23 Hn23 b0; rewrite ctree_leaf_table_sub //.
    move: (ccons (odd n23) b0) => c; rewrite /= addc0 /setU1.
    case: (c =d Color0) => //=; apply ctree_leaf_of_proper.
  move Dctp': (ctree_proper (S n)) => ctp' /=.
  case: (iter n ctree_merge_table ltab) {Hrec}(Hrec (leqW Hn)) => [|pt0 tab].
    by move=> [Dn _]; move: (ltnW Hn); rewrite leqNgt -Dn /= addn0 leqnn.
  move=> [Dn Htab]; rewrite /= addSnnS size_pairmap /=; split; first done.
  move=> n23 Hn23 b0; move: {Htab Dn}(Htab _ (ltnW Hn23)) (Htab (S _) Hn23).
  rewrite /ctree_table_sub (fun x => sub_pairmap x x) //=.
  case: {pt0 Hn23}(sub ctree_empty_pair (Adds pt0 tab) n23) => [t0 t1].
  case: {n23 tab}(sub ctree_empty_pair tab n23) => [t2 t3].
  do 2 (move=> Ht; move: {Ht}(Ht false) (Ht true) => /=; do 2 intro).
  by case: b0; rewrite /= -Dctp'; apply ctree_cons_proper.
have Dsz: size tab = 2 by apply addn_injl with h'; rewrite Hlen Dh addnC.
case: tab {Dtab Hlen}Dsz Hsub => [|[t0 t1] [|[t2 t3] tab']] //=.
move=> _ Hsub; have Hsub1 := Hsub 1 (erefl _).
move: {Hsub Hsub1}(Hsub 0 (erefl _) true) (Hsub1 false) (Hsub1 true).
rewrite /ctree_table_sub {t0 tab' h Dh ltab Dltab}/=.
move=> Ht1 Ht2 Ht3; apply ctree_cons_proper;
 [ move: t1 Ht1 {t2 Ht2 t3 Ht3}
 | move: {t1 Ht1}t2 Ht2 {t3 Ht3}
 | move: {t1 Ht1 t2 Ht2}t3 Ht3 ];
 elim: h' => [|h Hrec] [t1 t2 t3|lf|] //= [Hne Ht1 Ht2 Ht3];
 apply ctree_cons_proper; auto; split.
Qed.

Lemma ctree_sub_init_tree : forall h (et : colseq),
 let et_ok := and3b (size et =d h) (negb (ctrace et Color0)) (even_trace et) in
 ctree_sub (ctree_init_tree h) et = 
   (if et_ok then dyck (count_cbit1 (ctrace et)) else 0).
Proof.
move=> h; case Dh: h => [|h']; [by case | rewrite /ctree_init_tree /pred -Dh].
move Dltab: (ctree_leaf_table h) => ltab.
move Dtab: (iter h' ctree_merge_table ltab) => tab.
have [Hlen Hsub]: h' + size tab = S h
    /\ forall n23, n23 < size tab -> forall b0 et,
       let c := ccons (odd n23) b0 in
       let cet := add_last et (c +c sumt et) in
       let c23 := n23 + count_cbit1 cet in
       let et_ok := (size et =d h') && negb (cet Color0) in
       ctree_sub (ctree_table_sub tab n23 b0) et = (if et_ok then dyck c23 else 0).
  move: (leq_addl 1 h'); rewrite -{tab}Dtab {1}/addn /= -Dh.
  elim: (h') => [|n Hrec] Hn /=.
    rewrite -{ltab}Dltab ctree_leaf_table_size; split; first done.
    move=> /= n23 Hn23 b0; rewrite {Hn}ctree_leaf_table_sub //.
    move: (ccons (odd n23) b0) => c [|e et]; rewrite /= /setU1 addc0;
    by case: (c =d Color0) => //; apply: ctree_sub_leaf_of.
  case: (iter n ctree_merge_table ltab) {Hrec}(Hrec (leqW Hn)) => [|pt tab].
    by move=> [Dn _]; have:= ltnW Hn; rewrite leqNgt -Dn /= addn0 leqnn.
  rewrite /= -addSnnS /= size_pairmap; move=> [Dn Htab]; split; first done.
  move=> n23 Hn23 b0; move: {Htab Dn}(Htab _ (ltnW Hn23)) (Htab (S n23) Hn23).
  rewrite /ctree_table_sub (fun x => sub_pairmap x x) //=.
  case: {pt Hn23}(sub ctree_empty_pair (Adds pt tab) n23) => [t0 t1].
  case: {tab}(sub ctree_empty_pair tab n23) => [t2 t3].
  move=> Hsub; move: {Hsub}(Hsub false) (Hsub true) => /= Ht0 Ht1.
  move=> Hsub; move: {Hsub}(Hsub false) (Hsub true) => /= Ht2 Ht3.
  case=> [|e et]; first by case b0; rewrite ctree_sub_cons.
  rewrite /= {2}/addn addcA -(ccons_cbits (_ +c e)) /setU1.
  rewrite eqdSS cbit0_addc cbit0_ccons cbit1_addc cbit1_ccons.
  case: e; rewrite /= ?addbT ?addbF -1?addSnnS;
   by case: b0; rewrite /= ctree_sub_cons /= ?andbF.
have Dsz: size tab = 2 by apply addn_injl with h'; rewrite Hlen Dh addnC.
case: tab Dsz Hsub {Dtab Hlen} => [|[t0 t1] [|[t2 t3] tab']] //=.
move=> _ Hsub {ltab Dltab}; have Hsub1 := Hsub 1 (erefl _).
move: {Hsub Hsub1}(Hsub 0 (erefl _) true) (Hsub1 false) (Hsub1 true).
rewrite /ctree_table_sub /= {t0 tab' h}Dh.
move=> Ht1 Ht2 Ht3 et; rewrite ctree_sub_cons /=.
move: {1}(even_trace et) (erefl (even_trace et)).
case: et => [|e et] tec; rewrite // /ctrace add_last_adds /= eqdSS;
 case: e => /=; [ by rewrite andbF
   | move: (t1) (Ht1 et) | move: (t2) (Ht2 et) | move: (t3) (Ht3 et)];
 move{t1 Ht1 t2 Ht2 t3 Ht3} => t Ht Etec;
 by transitivity (if tec then ctree_sub t et else 0);
   [ rewrite {h' tec Ht}Etec; elim: et t => [|e et Hrec] [t1 t2 t3|lf|];
     rewrite /= ?if_same // ctree_sub_cons //; case: e; rewrite /= ?if_same
   | by rewrite -Etec andbA andbC; case tec].
Qed.

End InitCtree.

Unset Implicit Arguments.