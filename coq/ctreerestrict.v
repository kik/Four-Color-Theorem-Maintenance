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
Require Import ctree.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* This is the second phase of a D-reducibility step : adjusting the       *)
(* coloring set match counts to fit the new set of chromograms, thereby    *)
(* removing the colorings whose counts fall to zero.                       *)
(* The restriction function uses a depth counter to determine when to      *)
(* decrement counts.                                                       *)

Section CtreeRestriction.

Inductive ctree_restriction : Set :=
  Ctr_none | Ctr_some (bs : bit_stack) (t : gtree) (ctr : ctree_restriction).

Definition ctr_cons bs t r := if gtree_empty t then r else Ctr_some bs t r.

Fixpoint ctr_sub (r : ctree_restriction) (et : colseq) {struct r} : nat :=
  if r is Ctr_some bs t r' then gtree_sub t bs et + ctr_sub r' et else 0.

Lemma ctr_sub_cons : forall bs t r et,
  ctr_sub (ctr_cons bs t r) et = gtree_sub t bs et + ctr_sub r et.
Proof.
move=> bs t r et; rewrite /ctr_cons; case Ht: (gtree_empty t) => //=.
by rewrite (gtree_empty_empty Ht) gtree_sub_empty.
Qed.

Section CtrSplit.

Variables (A : Set) (continue : forall r1 r2 r3 : ctree_restriction, A).

Fixpoint ctr_split (r1 r2 r3 r : ctree_restriction) {struct r} : A :=
  match r with
  | Ctr_none => continue r1 r2 r3
  | Ctr_some bs (Gtree_node t0 t1 t2 t3) r' =>
      let addr bs t r' := if t is Gtree_empty then r' else Ctr_some bs t r' in
      let dorec r2' r3' :=
        if t0 is Gtree_empty then ctr_split (addr bs t1 r1) r2' r3' r' else
        let r2'' := Ctr_some (Bpush0 bs) t0 r2' in
        let r3'' := Ctr_some (Bpush1 bs) t0 r3' in
        ctr_split (addr bs t1 r1) r2'' r3'' r' in
      match bs with
      | Bstack0 => dorec r2 r3
      | Bpush0 bs' => dorec (addr bs' t2 r2) (addr bs' t3 r3)
      | Bpush1 bs' => dorec (addr bs' t3 r2) (addr bs' t2 r3)
      end
  | Ctr_some _ _ r' => ctr_split r1 r2 r3 r'
  end.

Lemma ctr_split_some : forall bs t0 t1 t2 t3 r1 r2 r3 r,
 let cons_pop t t' r' :=
   match bs with
   | Bstack0 => r'
   | Bpush0 bs' => ctr_cons bs' t r'
   | Bpush1 bs' => ctr_cons bs' t' r'
   end in
 ctr_split r1 r2 r3 (Ctr_some bs (Gtree_node t0 t1 t2 t3) r) =
 ctr_split (ctr_cons bs t1 r1) (ctr_cons (Bpush0 bs) t0 (cons_pop t2 t3 r2))
                               (ctr_cons (Bpush1 bs) t0 (cons_pop t3 t2 r3)) r.
Proof.
move=> [|bs|bs] t0 t1 t2 t3 r1 r2 r3 r;
 by rewrite /= !fold_gtree_empty /ctr_cons; case (gtree_empty t0).
Qed.

End CtrSplit.

Let csplit r e :=
  let rk t1 t2 t3 := palette Ctr_none t1 t2 t3 e in
  ctr_split rk Ctr_none Ctr_none Ctr_none r.

Lemma ctr_split_eq : forall A rk r,
 @ctr_split A rk Ctr_none Ctr_none Ctr_none r =
   rk (csplit r Color1) (csplit r Color2) (csplit r Color3).
Proof.
move=> A rk r; rewrite /csplit.
move: Ctr_none {2 4 6 8}Ctr_none {3 6 9 12}Ctr_none.
elim: r  => [|bs t r Hrec] r1 r2 r3 //.
by case: t; first [ move=> t0 t1 t2 t3; rewrite !ctr_split_some Hrec | simpl ].
Qed.

Lemma ctr_sub_csplit : forall r e et,
  ctr_sub (csplit r e) et = (if size et is 0 then 0 else ctr_sub r (Adds e et)).
Proof.
move=> r e et; case Det: {2}et => [|e' et'] /=.
rewrite {et}Det; elim: {r e}(csplit r e) => //= [bs t r Hrec].
  by rewrite Hrec addn0; case t.
apply: (etrans _ (add0n _)).
have <-: ctr_sub (csplit Ctr_none e) et = 0 by case e.
rewrite /csplit /=; move: {2 4}Ctr_none {3 6}Ctr_none {4 8}Ctr_none.
elim: r => [|bs t r Hrec] r1 r2 r3; first by rewrite /= addn0.
have Htlf: (forall s s' w, ~ gtree_mem t (Adds s (Adds s' w))) ->
    gtree_sub t bs (Adds e et) = 0.
  move{Hrec} => Ht; rewrite {}Det /gtree_sub; move: (gtree_mem t) Ht => st Hst.
  case: e => //; case: e' => //=;
    do 3 (rewrite ?match_count_0 //; case: bs => [|bs|bs] //=).
case: t Htlf; first
 [ move=> t0 t1 t2 t3 _; rewrite ctr_split_some {}Hrec
 | by move=> Htlf; rewrite /= {}Hrec {}Htlf //; case ].
rewrite /= addnA -2!(addnC (ctr_sub r (Adds e et))); congr addn; rewrite addnC.
have Hmceta := let f := gtree_mem _ in @match_count_eq (fun w => f w) _ (frefl f).
by case: e; rewrite //= ctr_sub_cons; first
  [ by rewrite /gtree_sub /= Hmceta
  | case: bs => *; rewrite ?ctr_sub_cons /gtree_sub /=;
    rewrite !Hmceta ?addnI ?addnA ?addn0 ].
Qed.

Fixpoint ctree_decr (lf : ctree) (n : nat) {struct n} : ctree :=
  match n, lf with
  | S n', Ctree_leaf lf' => ctree_decr lf' n'
  | _, _ => lf
  end.

Lemma ctree_val_decr : forall m n,
  ctree_decr (ctree_leaf_of m) n = ctree_leaf_of (m - n).
Proof. by move=> m n; elim: n m => [|n Hrec] [|m]; try exact (Hrec m). Qed.

Lemma ctree_no_decr : forall t n, ctree_leaf t = false -> ctree_decr t n = t.
Proof. by move=> [t1 t2 t3|lf|] [|n]. Qed.

Section CtrDecr.

Variables (A : Set) (cont : forall lf1 lf2 lf3 : ctree, A).

Let dlf lf klf : A := if lf is Ctree_leaf lf' then klf lf' else klf lf.

Definition ctr_decr := Eval compute in
  fix ctr_decr (lf1 lf2 lf3 : ctree) (r : ctree_restriction) {struct r} : A :=
  match r with
  | Ctr_none => cont lf1 lf2 lf3
  | Ctr_some bs t r' =>
    let dlf1 := dlf lf1 in
    let dlf2 := dlf lf2 in
    let dlf3 := dlf lf3 in
    let lfk lf1' lf2' lf3' := ctr_decr lf1' lf2' lf3' r' in
    match t, bs with
    | Gtree_leaf0, _ => dlf2 (fun lf2' => dlf3 (fun lf3' => lfk lf1 lf2' lf3'))
    | Gtree_leaf1, _ => dlf1 (fun lf1' => lfk lf1' lf2 lf3)
    | Gtree_leaf2, Bpush0 _ => dlf2 (fun lf2' => lfk lf1 lf2' lf3)
    | Gtree_leaf2, Bpush1 _ => dlf3 (fun lf3' => lfk lf1 lf2 lf3')
    | Gtree_leaf3, Bpush0 _ => dlf3 (fun lf3' => lfk lf1 lf2 lf3')
    | Gtree_leaf3, Bpush1 _ => dlf2 (fun lf2' => lfk lf1 lf2' lf3)
    | Gtree_leaf01, _ =>
        dlf1 (fun lf1' => dlf2 (fun lf2' => dlf3 (lfk lf1' lf2')))
    | Gtree_leaf12, Bstack0 => dlf1 (fun lf1' => lfk lf1' lf2 lf3)
    | Gtree_leaf12, Bpush0 _ =>
        dlf1 (fun lf1' => dlf2 (fun lf2' => lfk lf1' lf2' lf3))
    | Gtree_leaf12, Bpush1 _ =>
        dlf1 (fun lf1' => dlf3 (fun lf3' => lfk lf1' lf2 lf3'))
    | Gtree_leaf13, Bstack0 => dlf1 (fun lf1' => lfk lf1' lf2 lf3)
    | Gtree_leaf13, Bpush0 _ =>
        dlf1 (fun lf1' => dlf3 (fun lf3' => lfk lf1' lf2 lf3'))
    | Gtree_leaf13, Bpush1 _ =>
        dlf1 (fun lf1' => dlf2 (fun lf2' => lfk lf1' lf2' lf3))
    | Gtree_leaf23, Bpush0 _ =>
        dlf2 (fun lf2' => dlf3 (fun lf3' => lfk lf1 lf2' lf3'))
    | Gtree_leaf23, Bpush1 _ =>
        dlf2 (fun lf2' => dlf3 (fun lf3' => lfk lf1 lf2' lf3'))
    | _, _ => lfk lf1 lf2 lf3
    end
  end.

Definition ctr_e_decr bs t e lf := ctree_decr lf (gtree_sub t bs (seq1 e)).

Lemma ctr_decr_some : forall lf1 lf2 lf3 bs t r,
 let cde := ctr_e_decr bs t in
 ctr_decr lf1 lf2 lf3 (Ctr_some bs t r) =
   ctr_decr (cde Color1 lf1) (cde Color2 lf2) (cde Color3 lf3) r.
Proof.
move=> lf1 lf2 lf3 bs t r; case: t;
 by first [ move=> t0 t1 t2 t3; rewrite /ctr_e_decr !gtree_sub_node_0
          | case: lf1 => //; case: bs => // *; case: lf2; case: lf3 ].
Qed.

End CtrDecr.

Let cdecr e := ctr_decr (fun ct1 ct2 ct3 => palette Ctree_empty ct1 ct2 ct3 e).

Lemma ctr_decr_eq : forall A lfk lf1 lf2 lf3 r,
 let cdecr_r e := cdecr e lf1 lf2 lf3 r in
 @ctr_decr A lfk lf1 lf2 lf3 r =
   lfk (cdecr_r Color1) (cdecr_r Color2) (cdecr_r Color3).
Proof.
move=> A lfk lf1 lf2 lf3 r; elim: r lf1 lf2 lf3; rewrite // /cdecr.
by move=> bs t r Hrec *; rewrite !ctr_decr_some Hrec.
Qed.

Lemma ctree_proper_leaf_of_val : forall lf,
  ctree_proper 0 lf -> lf = ctree_leaf_of (ctree_sub lf seq0).
Proof. by elim=> // [lf Hrec] Hlf; congr Ctree_leaf; apply Hrec. Qed. 

Lemma cdecr_leaf : forall e lf1 lf2 lf3 r,
 let t := ctree_cons lf1 lf2 lf3 in
 let et := seq1 e in
 ctree_proper 1 t ->
   cdecr e lf1 lf2 lf3 r = ctree_leaf_of (ctree_sub t et - ctr_sub r et).
Proof.
move=> e lf1 lf2 lf3 r /= Ht.
elim: r => [|bs t r Hrec] in lf1 lf2 lf3 Ht |- *;
  move: {Ht}(ctree_proper_leaf_of_val (ctree_proper_sel _ Ht)) => Hlf.
  by rewrite /= subn0 ctree_sub_cons; case: e (Hlf e); rewrite ctree_sel_cons.
rewrite /cdecr !ctr_decr_some -/(cdecr e) {}Hrec /=.
congr ctree_leaf_of; move: {Hlf}(Hlf e).
  move: (ctree_sub (ctree_sel (ctree_cons lf1 lf2 lf3) e) seq0) => m.
  rewrite ctree_sel_cons 2!ctree_sub_cons; case: e => //= Dlf;
  by rewrite /ctr_e_decr Dlf ctree_val_decr !ctree_sub_leaf_of -subn_sub.
apply ctree_cons_proper;
 [ move: (Hlf Color1) | move: (Hlf Color2) | move: (Hlf Color3) ];
 rewrite ctree_sel_cons /=; move=> Dlf;
 rewrite /ctr_e_decr Dlf ctree_val_decr; apply ctree_leaf_of_proper.
Qed.

Definition ctree_cons_pairs (pt1 pt2 pt3 : ctree_pair) :=
  let (t1, t1') := pt1 in
  let (t2, t2') := pt2 in
  let (t3, t3') := pt3 in
  (fun t t' =>
   match ctree_empty_node t, ctree_empty_node t' with
   | true, true => Ctree_pair Ctree_empty Ctree_empty
   | true, false => Ctree_pair Ctree_empty t'
   | false, true => Ctree_pair t Ctree_empty
   | false, false => Ctree_pair t t'
   end) (Ctree_node t1 t2 t3) (Ctree_node t1' t2' t3').

Lemma ctree_cons_pairs_spec : forall t1 t1' t2 t2' t3 t3',
 ctree_cons_pairs (Ctree_pair t1 t1') (Ctree_pair t2 t2') (Ctree_pair t3 t3') =
   Ctree_pair (ctree_cons t1 t2 t3) (ctree_cons t1' t2' t3').
Proof.
move=> t1 t1' t2 t2' t3 t3'; rewrite 2!ctree_cons_spec /=.
by do 2 (apply cases_of_if => ->).
Qed.

Definition sctree_partition (st st' st'' : colseq -> bool) :=
  forall et, (if st et then eqb else orb) (st' et) (st'' et) = false.

Definition ctree_partition t (pt : ctree_pair) :=
  let (t', t'') := pt in
  sctree_partition (ctree_mem t) (ctree_mem t') (ctree_mem t'').

Lemma ctree_cons_pairs_partition : forall t1 t2 t3 pt1 pt2 pt3,
    ctree_partition t1 pt1 ->
    ctree_partition t2 pt2 ->
    ctree_partition t3 pt3 ->
 ctree_partition (Ctree_node t1 t2 t3) (ctree_cons_pairs pt1 pt2 pt3).
Proof.
move=> t1 t2 t3 [t1' t1''] [t2' t2''] [t3' t3''].
rewrite ctree_cons_pairs_spec /= /ctree_mem; move=> Ht1 Ht2 Ht3 et.
by rewrite 2!ctree_sub_cons; case: et => [|[|||] et] /=.
Qed.

Lemma ctree_sub0_cons_pairs : forall pt1 pt2 pt3 et,
 let cp0 pt := ctree_pair_sub pt false in
 ctree_sub (cp0 (ctree_cons_pairs pt1 pt2 pt3)) et =
   ctree_sub (Ctree_node (cp0 pt1) (cp0 pt2) (cp0 pt3)) et.
Proof.
move=> [t1 t1'] [t2 t2'] [t3 t3'] et.
by rewrite ctree_cons_pairs_spec /= ctree_sub_cons; case et.
Qed.

Definition ctree_leaf_pair lf1 lf2 lf3 lf1' lf2' lf3' :=
  (fun lf' =>
   match lf' with
   | Ctree_node Ctree_empty Ctree_empty Ctree_empty =>
       Ctree_pair lf1' (ctree_cons lf1 lf2 lf3)
   | Ctree_node Ctree_empty Ctree_empty _ =>
       Ctree_pair lf' (ctree_cons lf1 lf2 lf1')
   | Ctree_node Ctree_empty _ Ctree_empty =>
       Ctree_pair lf' (ctree_cons lf1 lf1' lf3)
   | Ctree_node Ctree_empty _ _ => Ctree_pair lf' (ctree_cons lf1 lf1' lf1')
   | Ctree_node _ Ctree_empty Ctree_empty =>
       Ctree_pair lf' (ctree_cons lf2' lf2 lf3)
   | Ctree_node _ Ctree_empty _ => Ctree_pair lf' (ctree_cons lf2' lf2 lf2')
   | Ctree_node _ _ Ctree_empty => Ctree_pair lf' (ctree_cons lf3' lf3' lf3)
   | _ => Ctree_pair lf' Ctree_empty
   end) (Ctree_node lf1' lf2' lf3').

Lemma ctree_leaf_pair_spec : forall lf1 lf2 lf3 lf1' lf2' lf3',
  let if_e lf lf' := if ctree_empty lf' then lf else Ctree_empty in
  let t' := ctree_cons lf1' lf2' lf3' in
  let t'' := ctree_cons (if_e lf1 lf1') (if_e lf2 lf2') (if_e lf3 lf3') in
  ctree_leaf_pair lf1 lf2 lf3 lf1' lf2' lf3' = Ctree_pair t' t''.
Proof.
by move=> lf1 lf2 lf3 lf1' lf2' lf3'; case lf1'; case lf2'; case lf3'.
Qed.

Fixpoint ctree_restrict (h : nat) (t : ctree) (r : ctree_restriction) {struct h}
                        : ctree_pair :=
  match r, h, t with
  | Ctr_none, _, _ => Ctree_pair t Ctree_empty
  | _, S h', Ctree_node t1 t2 t3 =>
      let rh' := ctree_restrict h' in
      let rk r1 r2 r3 := ctree_cons_pairs (rh' t1 r1) (rh' t2 r2) (rh' t3 r3) in
      ctr_split rk Ctr_none Ctr_none Ctr_none r
  | _, O, Ctree_node lf1 lf2 lf3 =>
      ctr_decr (ctree_leaf_pair lf1 lf2 lf3) lf1 lf2 lf3 r
  | _, _, _ => ctree_empty_pair
  end.

Lemma ctree_restrict_correct : forall h t r, ctree_proper (S h) t ->
 let pt := ctree_restrict h t r in
 and3 (forall b, ctree_proper (S h) (ctree_pair_sub pt b))
      (ctree_partition t pt)
      (forall et, ctree_sub (ctree_pair_sub pt false) et =
                       ctree_sub t et - ctr_sub r et).
Proof.
elim=> [|h' Hrec].
  move=> t r Ht; move Dpt: (ctree_restrict 0 t r) => pt.
  case Dt: t Ht Dpt => [lf1 lf2 lf3|lf|] Ht //.
    case Dr: r => [|bs gt r']; [ simpl | rewrite /ctree_restrict -{bs gt r'}Dr ].
      move<-; split; try by case.
        by move=> et; rewrite -Dt /=; case (ctree_mem t et).
      move=> et; exact (esym (subn0 _)).
    rewrite ctr_decr_eq ctree_leaf_pair_spec.
    have Dlf := ctree_proper_leaf_of_val (ctree_proper_sel _ Ht).
    have Et := ctree_cons_spec lf1 lf2 lf3; case: (Ht) => [Htne _ _ _].
    rewrite [ctree_empty_node]lock /= -lock {}Htne in Et; rewrite -Et in Ht.
    rewrite !(cdecr_leaf _ r Ht) !ctree_sub_cons /=.
    move: {Dlf}(Dlf Color1) (Dlf Color2) (Dlf Color3) => /=.
    move: (ctree_sub lf1 _) (ctree_sub lf2 _) (ctree_sub lf3 _) => n1 n2 n3.
    move=> Dlf1 Dlf2 Dlf3 <- {pt}; split.
    - case=> /=; last by apply ctree_cons_proper; apply ctree_leaf_of_proper.
      have Hife: forall b n,
          ctree_proper 0 (if b then ctree_leaf_of n else Ctree_empty).
      + by case; first exact ctree_leaf_of_proper.
      by rewrite Dlf1 Dlf2 Dlf3; apply ctree_cons_proper; apply Hife.
    - move=> et; rewrite !ctree_mem_cons /= /ctree_mem.
      case: et => [|[|||] et] //=.
      + rewrite {}Dlf1; case: n1 => [|n1] //; move: (S n1 - _) => m1.
        by rewrite 2!ctree_sub_leaf_of; case: et; case: m1.
      + rewrite {}Dlf2; case: n2 => [|n2] //; move: (S n2 - _) => m2.
        by rewrite 2!ctree_sub_leaf_of; case: et; case: m2.
      rewrite {}Dlf3; case: n3 => [|n3] //; move: (S n3 - _) => m3.
      by rewrite 2!ctree_sub_leaf_of; case: et; case: m3.
    move=> et; rewrite /= ctree_sub_cons /=; case: et => [|[|||] et] //=;
    by rewrite ?Dlf1 ?Dlf2 ?Dlf3 !ctree_sub_leaf_of; case et.
  move=> Dpt; have Ept: pt = ctree_empty_pair by case: r Dpt.
  by rewrite Ept /=; split; try case.
move=> [t1 t2 t3|lf|] r Ht //.
move Dpt: (ctree_restrict (S h') (Ctree_node t1 t2 t3) r) => /= pt.
  case Dr: r Dpt => [|bs gt r']; [ simpl | rewrite -{bs gt r'}Dr ].
    move=> <-{pt}; split; first [by case | move=> et]; last exact (esym (subn0 _)).
    by case (ctree_mem (Ctree_node t1 t2 t3) et).
  rewrite ctr_split_eq.
  have Hrece := fun e => Hrec _ (csplit r e) (ctree_proper_sel e Ht).
  move: {Hrec Hrece}(Hrece Color1) (Hrece Color2) (Hrece Color3) => /=.
  case: (ctree_restrict h' t1 (csplit r Color1)) => [t1' t1''].
  case: (ctree_restrict h' t2 (csplit r Color2)) => [t2' t2''].
  case: (ctree_restrict h' t3 (csplit r Color3)) => [t3' t3''].
  move=> [Hpt1 Ht1' Et1'] [Hpt2 Ht2' Et2'] [Hpt3 Ht3' Et3'] <- {pt}; split.
   rewrite ctree_cons_pairs_spec => b0.
     by case: b0 (Hpt1 b0) (Hpt2 b0) (Hpt3 b0) (ctree_cons_proper) => /=; auto.
   by apply ctree_cons_pairs_partition.
  move {Hpt1 Hpt2 Hpt3 Ht1' Ht2' Ht3'} => et; rewrite ctree_sub0_cons_pairs.
  case: et => [|e et] //=; move: {Et1' Et2' Et3'}(Et1' et) (Et2' et) (Et3' et).
  rewrite !ctr_sub_csplit /=; case: et => [|e' et'] /= Et1' Et2' Et3';
  case: e {Ht}(ctree_proper_sel e Ht) => //=.
  - by rewrite Et1'; case t1.
  - by rewrite Et2'; case t2.
  by rewrite Et3'; case t3.
have <-: ctree_empty_pair = ctree_restrict (S h') Ctree_empty r by case r.
by split; try case.
Qed.

End CtreeRestriction.

Unset Implicit Arguments.