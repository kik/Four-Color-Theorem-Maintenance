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

(* Chromograms are words representing congruence classes of regions wrt. *)
(* Kempe inversions for a single edge color (and color permutation).     *)
(* The relevant topological information for each class consists of a set *)
(* of non-intersecting chords linking perimeter edges, and the parity of *)
(* the number of links for each chord. The word representation of these  *)
(* chords is a Dyck word augmented with spaces (for perimeter edges that *)
(* are not linked because they are colored with the inversion color) and *)
(* parities (on closing brackets), each chord being represented with a   *)
(* matching bracket pair.                                                *)
(*   The relationship between chromograms and graphs will be developped  *)
(* elsewhere. Here we develop correctness of the words, and the matching *)
(* relation between (completed) edge traces and chromograms. We also     *)
(* define the relation on incomplete edge traces and chromograms with    *)
(* the last symbol removed; this is the form actually used for the       *)
(* correctness proof of the reducibility check.                          *)

Inductive gram_symbol : Set := Gpush | Gskip | Gpop0 | Gpop1.

Definition eqgs s1 s2 :=
  match s1, s2 with
  | Gpush, Gpush => true
  | Gskip, Gskip => true
  | Gpop0, Gpop0 => true
  | Gpop1, Gpop1 => true
  | _, _ => false
  end.

Lemma eqgsP : reflect_eq eqgs.
Proof. by do 2 case; constructor. Qed.

Canonical Structure gramSymbolData := DataSet eqgsP.

Definition chromogram : Set := seq gramSymbolData.

Fixpoint gram_balanced (d : nat) (b0 : bool) (w : chromogram) {struct w} : bool :=
  match w, d with
  | Seq0, O => negb b0
  | Adds Gpush w', _ => gram_balanced (S d) b0 w'
  | Adds Gskip w', _ => gram_balanced d (negb b0) w'
  | Adds Gpop0 w', S d' => gram_balanced d' b0 w'
  | Adds Gpop1 w', S d' => gram_balanced d' (negb b0) w'
  | _, _ => false
  end.

Fixpoint matchg (lb : bitseq) (et : colseq) (w : chromogram) {struct w} : bool :=
  match w, et, lb with
  | Seq0, Seq0, Seq0 => true
  | Adds s w', Adds e et', _ =>
      match e, s, lb with
      | Color1, Gskip, _ => matchg lb et' w'
      | Color2, Gpush, _ => matchg (Adds false lb) et' w'
      | Color2, Gpop0, Adds false lb' => matchg lb' et' w'
      | Color2, Gpop1, Adds true lb' => matchg lb' et' w'
      | Color3, Gpush, _ => matchg (Adds true lb) et' w'
      | Color3, Gpop0, Adds true lb' => matchg lb' et' w'
      | Color3, Gpop1, Adds false lb' => matchg lb' et' w'
      | _, _, _ => false
      end
  | _, _, _ => false
  end.

Definition kempe_closed (P : colseq -> Prop) :=
  forall et, P et -> (forall g, P (permt g et))
                  /\ (exists2 w, matchg seq0 et w
                              & forall et', matchg seq0 et' w -> P et').

Definition kempe_coclosure P et :=
  forall P', kempe_closed P' -> P' et -> exists2 et', P et' & P' et'.

Lemma matchg_size : forall et lb w, matchg lb et w -> size w = size et.
Proof.
elim=> [|e et Hrec] lb [|s w] Hm //=; congr S; case: s Hm.
- by case: e (Hrec (Adds (cbit0 e) lb) w).
- by case: e (Hrec lb w).
- by case: e lb (Hrec (behead lb) w); do 3 case=> //.
by case: e lb (Hrec (behead lb) w); do 3 case=> //.
Qed.

Lemma matchg_memc0 : forall et lb w,  matchg lb et w -> et Color0 = false.
Proof.
elim=> [|e et Hrec] lb [|s w] //=; case: s.
- by case: e (Hrec (Adds (cbit0 e) lb) w).
- by case: e (Hrec lb w).
- by case: e lb (Hrec (behead lb) w); do 3 case=> //.
by case: e lb (Hrec (behead lb) w); do 3 case=> //.
Qed.

Section BalanceLemmas.

Let sumb : bitseq -> bool := foldr addb false.

Lemma matchg_balanced : forall et w, matchg seq0 et w ->
  cbit1 (sumt et) = false /\ gram_balanced 0 (cbit0 (sumt et)) w.
Proof.
move=> et; rewrite -(fun c => addFb (cbit0 c)) -(fun c => addFb (cbit1 c)).
set sb := seq0 : bitseq; rewrite -{3}[false]/(sumb sb).
rewrite -{1}[false]/(odd 0) -[0]/(size sb).
elim: et sb => [|e et Hrec] lb [|s w] //; first by case lb.
rewrite /= cbit0_addc cbit1_addc 2!addbA -addTb.
rewrite -(addbC (cbit0 e)) -(addbC (cbit1 e)) !addbA.
case: s {Hrec}(Hrec (Adds (cbit0 e) lb) w) (Hrec lb w) (Hrec (behead lb) w);
 case: e => //=; auto; case: lb => [|[|] lb] //=; rewrite ?negb_elim //; auto.
Qed.

Lemma balanced_inj : forall w n1 n2 b1 b2,
 gram_balanced n1 b1 w -> gram_balanced n2 b2 w -> n1 = n2 /\ b1 = b2.
Proof.
by elim=> [|[|||] w Hrec] [|n1] [|n2] [|] [|] //= Hw1 Hw2;
  case: (Hrec _ _ _ _ Hw1 Hw2) => // [] [<-].
Qed.

Lemma balanced_sumt0 : forall w et,
  gram_balanced 0 false w -> matchg seq0 et w -> sumt et = Color0.
Proof.
move=> w et Hwf; move/matchg_balanced=> [Hst1 Hwt].
rewrite -(ccons_cbits (sumt et)) Hst1.
by case: (balanced_inj Hwf Hwt) => [_ <-].
Qed.

Lemma match_etrace : forall et w, matchg seq0 (etrace et) w = matchg seq0 et w.
Proof.
move=> et; rewrite /etrace /etrace_perm; set sb : bitseq := seq0.
case (even_trace et); first by rewrite permt_id.
rewrite -{2}[sb]/(maps negb sb).
elim: et sb => [|e et Hrec] lb [|s w] //; first by case lb.
by case: e; case: s => //=; first [ rewrite Hrec | case: lb => //; case=> //= ].
Qed.

(* Algorithmic predicates, for chromogram paths. *)

Inductive bit_stack : Set :=
  | Bstack0
  | Bpush0 (bs : bit_stack)
  | Bpush1 (bs : bit_stack).

Fixpoint bitseq_of_stack (bs : bit_stack) : bitseq :=
  match bs with
  | Bstack0 => seq0
  | Bpush0 bs' => Adds false (bitseq_of_stack bs')
  | Bpush1 bs' => Adds true (bitseq_of_stack bs')
  end.

Definition stack_of_bitseq : bitseq -> bit_stack :=
  foldr (fun b : bool => if b then Bpush1 else Bpush0) Bstack0.

Fixpoint cgram (d : nat) (b0 : bool) (w : chromogram) {struct w} : chromogram :=
  match w with
  | Seq0 => seq1 (if d is 0 then Gskip else if b0 then Gpop1 else Gpop0)
  | Adds s w' =>
      Adds s
        match s with
        | Gpush => cgram (S d) b0 w'
        | Gskip => cgram d (negb b0) w'
        | Gpop0 => cgram (pred d) b0 w'
        | Gpop1 => cgram (pred d) (negb b0) w'
        end
  end.

Fixpoint matchpg (bs : bit_stack) (et : colseq) (w : chromogram) {struct w}
       : bool :=
  match w, et with
  | Seq0, Seq0 => true
  | Adds s w', Adds e et' =>
      match e, s, bs with
      | Color1, Gskip, _ => matchpg bs et' w'
      | Color2, Gpush, _ => matchpg (Bpush0 bs) et' w'
      | Color2, Gpop0, Bpush0 bs' => matchpg bs' et' w'
      | Color2, Gpop1, Bpush1 bs' => matchpg bs' et' w'
      | Color3, Gpop0, Bpush1 bs' => matchpg bs' et' w'
      | Color3, Gpush, _ => matchpg (Bpush1 bs) et' w'
      | Color3, Gpop1, Bpush0 bs' => matchpg bs' et' w'
      | _, _, _ => false
      end
  | _, _ => false
  end.

Lemma matchg_cgram : forall cw et,
 matchg seq0 (ctrace et) cw -> cw = cgram 0 false (take (pred (size cw)) cw).
Proof.
move=> cw et Hm; case (matchg_balanced Hm); clear; rewrite sumt_ctrace /=.
case: cw Hm 0 false => [|s w] /=; first by case et.
clear; elim: w s => [|s' w Hrec] s d b0; first by case: s b0 d; do 3 case=> //.
by case: s => //= Hw; congr Adds; apply: Hrec; case: d Hw; case b0.
Qed.

Lemma matchg_pg : forall et w, gram_balanced 0 false (cgram 0 false w) ->
  matchg seq0 (ctrace et) (cgram 0 false w) = matchpg Bstack0 et w.
Proof.
move=> et; rewrite /ctrace -(add0c (sumt et)); set sb : bitseq := seq0.
rewrite -[Color0]/(ccons (odd 0) (sumb sb)) -(addFb (sumb sb)).
rewrite -[0]/(size sb) -[Bstack0]/(stack_of_bitseq sb).
elim: et sb false => [|e et Hrec] lb b.
  case=> [|s w] /=; first by do 2 case: b lb => [] [|b lb] //.
  move: (size lb) => d _; rewrite addc0.
  by case: (ccons (odd d) (b +b sumb lb)) => //;
     case: s => //; case: w => //; case: lb => //; case.
case=> [|s w]; rewrite ?add_last_adds /=.
  by case: lb => [|b' [|b'' lb]] // _; case: e => {Hrec}//;
     case: et => //; case b; case b'.
case: s; try (case: lb; first done; case=> lb /=);
  case: e (Hrec (Adds (cbit0 e) lb)) => //= Hrec' Hm;
  try case: {Hrec}(Hrec _ _ _ Hm); try case: {Hrec' Hm}(Hrec' _ _ Hm);
   by case (sumt et); case (odd (size lb)); case b; case (sumb lb).
Qed.

Lemma matchpg_etrace : forall et w,
  matchpg Bstack0 (etrace et) w = matchpg Bstack0 et w.
Proof.
move=> et; rewrite /etrace /etrace_perm; set sb := seq0 : bitseq.
case: (even_trace et) => /=; first by rewrite permt_id.
rewrite -[Bstack0]/(stack_of_bitseq sb) -{1}[sb]/(maps negb sb).
elim: et sb => [|e et Hrec] lb [|s w] //.
by case: e (Hrec (Adds (cbit0 e) lb) w); case: s => //=; case: lb => //; case=> /=.
Qed.

Lemma matchpg_size : forall et bs w, matchpg bs et w -> size w = size et.
Proof.
elim=> [|e et Hrec] bs [|s w] Hm //=; congr S; case: s Hm.
- by case: e (Hrec ((if cbit0 e then Bpush1 else Bpush0) bs) w).
- by case: e (Hrec bs w).
- by case: e bs => [|||] [|bs|bs] Hm; try apply: Hrec Hm.
by case: e bs => [|||] [|bs|bs] Hm; try apply: Hrec Hm.
Qed.

Lemma matchpg_flip : forall et,
  matchpg Bstack0 (permt Eperm132 et) =1 matchpg Bstack0 et.
Proof.
pose sb : bitseq := seq0; rewrite -[Bstack0]/(stack_of_bitseq sb).
rewrite -{1}[sb]/(maps negb sb) /eqfun.
move=> et; elim: et sb => [|e et Hrec] lb [|s w] //.
by case: e (Hrec (Adds (cbit0 e) lb) w); case: s => //=; case: lb => //; case=> /=.
Qed.

End BalanceLemmas.

Unset Implicit Arguments.