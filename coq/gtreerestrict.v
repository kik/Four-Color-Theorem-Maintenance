(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import color.
Require Import ctree.
Require Import chromogram.
Require Import gtree.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* This is the first phase of a D-reducibility step : restricting the      *)
(* chromogram set to fit a given set of colorings. The result of this step *)
(* is a pair of trees, containing respectively the deleted and remaining   *)
(* chromograms.                                                            *)
(*   To keep the two versions straight it is desireable to iterate at most *)
(* once over each subtree; since a chromogram can be matched in several    *)
(* ways, this means that the recursive procedure must restrict with a LIST *)
(* of trees (that list has at most 32 trees in it, and not more than 8     *)
(* for the most part); this is the type gtree_restrictor given below.      *)

Section GtreeRestrict.

Inductive gtree_restriction : Set :=
  | Gtr_none
  | Gtr_some (bs : bit_stack) (t : ctree) (gtr : gtree_restriction).

(* A restriction set ``represents'' a set of matching chromograms *)

Fixpoint gtr_mem (r : gtree_restriction) (w : chromogram) {struct r} : bool :=
  if r is Gtr_some bs t r' then
    has_match bs (ctree_mem t) w || gtr_mem r' w
  else false.

Definition gtr_cons bs t r := if ctree_empty t then r else Gtr_some bs t r.

Lemma gtr_mem_cons : forall bs t r w,
 gtr_mem (gtr_cons bs t r) w = has_match bs (ctree_mem t) w || gtr_mem r w.
Proof.
move=> bs t r w; rewrite /gtr_cons; case Ht: (ctree_empty t) => //.
by rewrite (ctree_empty_eq Ht) /= (fun P => introF (has_matchP bs P w)) //; case.
Qed.

Section GtrSplit.

Variables (A : Set) (continue : forall r0 r1 r2 r3 : gtree_restriction, A).

Fixpoint gtr_split (r0 r1 r2 r3 r : gtree_restriction) {struct r} : A :=
  match r with
  | Gtr_none => continue r0 r1 r2 r3
  | Gtr_some bs (Ctree_node t1 t2 t3) r' =>
      let r02 := Gtr_some (Bpush0 bs) t2 r0 in
      let r03 := Gtr_some (Bpush1 bs) t3 r0 in
      let r023 := Gtr_some (Bpush0 bs) t2 r03 in
      let r1' := if t1 is Ctree_empty then r1 else Gtr_some bs t1 r1 in
      let r2' bs' t':= Gtr_some bs' t' r2 in
      let r3' bs' t' := Gtr_some bs' t' r3 in
      match t2, t3, bs with
      | Ctree_empty, Ctree_empty, _ => gtr_split r0 r1' r2 r3 r'
      | Ctree_empty, _, Bstack0 => gtr_split r03 r1' r2 r3 r'
      | Ctree_empty, _, Bpush0 bs' => gtr_split r03 r1' r2 (r3' bs' t3) r'
      | Ctree_empty, _, Bpush1 bs' => gtr_split r03 r1' (r2' bs' t3) r3 r'
      | _, Ctree_empty, Bstack0 => gtr_split r02 r1' r2 r3 r'
      | _, Ctree_empty, Bpush0 bs' => gtr_split r02 r1' (r2' bs' t2) r3 r'
      | _, Ctree_empty, Bpush1 bs' => gtr_split r02 r1' r2 (r3' bs' t2) r'
      | _, _, Bstack0 => gtr_split r023 r1' r2 r3 r'
      | _, _, Bpush0 bs' => gtr_split r023 r1' (r2' bs' t2) (r3' bs' t3) r'
      | _, _, Bpush1 bs' => gtr_split r023 r1' (r2' bs' t3) (r3' bs' t2) r'
      end
  | Gtr_some _ _ r' => gtr_split r0 r1 r2 r3 r'
  end.

Lemma gtr_split_some : forall bs t1 t2 t3 r0 r1 r2 r3 r,
 let cons_pop t t' r' := match bs with
   | Bstack0 => r'
   | Bpush0 bs' => gtr_cons bs' t r'
   | Bpush1 bs' => gtr_cons bs' t' r'
   end in
 gtr_split r0 r1 r2 r3 (Gtr_some bs (Ctree_node t1 t2 t3) r) =
 gtr_split (gtr_cons (Bpush0 bs) t2 (gtr_cons (Bpush1 bs) t3 r0))
           (gtr_cons bs t1 r1) (cons_pop t2 t3 r2) (cons_pop t3 t2 r3) r.
Proof.
move=> bs t1 t2 t3 r0 r1 r2 r3 r; rewrite /= !fold_ctree_empty.
case: bs => [|bs|bs]; rewrite ?fold_ctree_empty /gtr_cons;
  by case: (ctree_empty t2); case: (ctree_empty t3).
Qed.

End GtrSplit.

Let gsplit r s :=
  let gtk gt0 gt1 gt2 gt3 := @gram_symbol_rec (fun _ => _) gt0 gt1 gt2 gt3 s in
  gtr_split gtk Gtr_none Gtr_none Gtr_none Gtr_none r.

Lemma gtr_split_eq : forall A rk r,
 @gtr_split A rk Gtr_none Gtr_none Gtr_none Gtr_none r =
   rk (gsplit r Gpush) (gsplit r Gskip) (gsplit r Gpop0) (gsplit r Gpop1).
Proof.
move=> A rk r; rewrite /gsplit; move: Gtr_none => rn.
elim: r rn {2 4 6 8 10}rn {3 6 9 12 15}rn {4 8 12 16 20}rn => //.
move=> bs [t1 t2 t3|lf|] r Hrec *; rewrite ?gtr_split_some; apply: Hrec.
Qed.

Lemma gtr_mem_gsplit : forall r s w, gtr_mem r (Adds s w) = gtr_mem (gsplit r s) w.
Proof.
move=> r s w; rewrite /gsplit; move Drn: Gtr_none => rn.
apply: (etrans (esym (orFb _)) _).
have <-: gtr_mem (@gram_symbol_rec (fun _ => _) rn rn rn rn s) w = false.
  by rewrite -Drn; case s.
elim: r rn {2 4}rn {3 6}rn {4 8}rn {Drn}; first by move=> *; rewrite /= orbF.
move=> bs [t1 t2 t3|lf|] r Hrec r0 r1 r2 r3.
- rewrite gtr_split_some -{}Hrec;
  case: s; rewrite /= ?gtr_mem_cons orbA {-2 3}[orb]lock orbC -?orbA -!lock //;
  by case: bs => *; rewrite ?gtr_mem_cons.
- rewrite [Adds s]lock /= -lock.
  by rewrite (introF (has_matchP bs _ _)); [apply: Hrec | do 2 case].
move Dsw: (Adds s w) => sw; rewrite /= (introF (has_matchP bs _ sw)) -{sw}Dsw //.
by do 2 case.
Qed.

Fixpoint gtr_match0 (r : gtree_restriction) : bool :=
  match r with
  | Gtr_none => false
  | Gtr_some _ (Ctree_node _ (Ctree_leaf _) _) _ => true
  | Gtr_some _ (Ctree_node _ _ (Ctree_leaf _)) _ => true
  | Gtr_some _ _ r' => gtr_match0 r'
  end.

Lemma gtr_match0_spec : forall r, gtr_match0 r = gtr_mem r (seq1 Gpush).
Proof.
simpl; elim=> [|bs t r Hrec] //=.
by case: t => //= [t1 t2 t3]; rewrite -{}Hrec; case: t2 => //; case: t3.
Qed.

Fixpoint gtr_match1 (r : gtree_restriction) : bool :=
  match r with
  | Gtr_none => false
  | Gtr_some _ (Ctree_node (Ctree_leaf _) _ _) _ => true
  | Gtr_some _ _ r' => gtr_match1 r'
  end.

Lemma gtr_match1_spec : forall r, gtr_match1 r = gtr_mem r (seq1 Gskip).
Proof.
simpl; elim=> [|bs t r Hrec] //=.
by case: t => //= [t1 t2 t3]; rewrite -{}Hrec; case: t1.
Qed.

Fixpoint gtr_match2 (r : gtree_restriction) : bool :=
  match r with
  | Gtr_none => false
  | Gtr_some (Bpush0 _) (Ctree_node _ (Ctree_leaf _) _) _ => true
  | Gtr_some (Bpush1 _) (Ctree_node _ _ (Ctree_leaf _)) _ => true
  | Gtr_some _ _ r' => gtr_match2 r'
  end.

Lemma gtr_match2_spec : forall r, gtr_match2 r = gtr_mem r (seq1 Gpop0).
Proof.
simpl; elim=> [|bs t r Hrec] //=.
by case: t => /=; case: bs => [|bs|bs] // t1 t2 t3; rewrite -{}Hrec;
  [ case: t2 | case: t3 ].
Qed.

Fixpoint gtr_match3 (r : gtree_restriction) : bool :=
  match r with
  | Gtr_none => false
  | Gtr_some (Bpush0 _) (Ctree_node _ _ (Ctree_leaf _)) _ => true
  | Gtr_some (Bpush1 _) (Ctree_node _ (Ctree_leaf _) _) _ => true
  | Gtr_some _ _ r' => gtr_match3 r'
  end.

Lemma gtr_match3_spec : forall r, gtr_match3 r = gtr_mem r (seq1 Gpop1).
Proof.
simpl; elim=> [|bs t r Hrec] //=.
by case: t => /=; case: bs => [|bs|bs] // t1 t2 t3; rewrite -{}Hrec;
  [ case t3 | case t2 ].
Qed.

Definition gtp_0_e := Gtree_pair Gtree_leaf0 Gtree_empty.
Definition gtp_1_e := Gtree_pair Gtree_leaf1 Gtree_empty.
Definition gtp_2_e := Gtree_pair Gtree_leaf2 Gtree_empty.
Definition gtp_3_e := Gtree_pair Gtree_leaf3 Gtree_empty.
Definition gtp_01_e := Gtree_pair Gtree_leaf01 Gtree_empty.
Definition gtp_12_e := Gtree_pair Gtree_leaf12 Gtree_empty.
Definition gtp_13_e := Gtree_pair Gtree_leaf13 Gtree_empty.
Definition gtp_23_e := Gtree_pair Gtree_leaf23 Gtree_empty.

Definition gtp_e_0 := Gtree_pair Gtree_empty Gtree_leaf0.
Definition gtp_e_1 := Gtree_pair Gtree_empty Gtree_leaf1.
Definition gtp_e_2 := Gtree_pair Gtree_empty Gtree_leaf2.
Definition gtp_e_3 := Gtree_pair Gtree_empty Gtree_leaf3.
Definition gtp_e_01 := Gtree_pair Gtree_empty Gtree_leaf01.
Definition gtp_e_12 := Gtree_pair Gtree_empty Gtree_leaf12.
Definition gtp_e_13 := Gtree_pair Gtree_empty Gtree_leaf13.
Definition gtp_e_23 := Gtree_pair Gtree_empty Gtree_leaf23.

Definition gtp_0_1 := Gtree_pair Gtree_leaf0 Gtree_leaf1.
Definition gtp_1_0 := Gtree_pair Gtree_leaf1 Gtree_leaf0.
Definition gtp_1_2 := Gtree_pair Gtree_leaf1 Gtree_leaf2.
Definition gtp_2_1 := Gtree_pair Gtree_leaf2 Gtree_leaf1.
Definition gtp_1_3 := Gtree_pair Gtree_leaf1 Gtree_leaf3.
Definition gtp_3_1 := Gtree_pair Gtree_leaf3 Gtree_leaf1.
Definition gtp_2_3 := Gtree_pair Gtree_leaf2 Gtree_leaf3.
Definition gtp_3_2 := Gtree_pair Gtree_leaf3 Gtree_leaf2.

Lemma gtree_partition_left : forall t,
  gtree_pair_partition t (Gtree_pair t Gtree_empty).
Proof. by move=> t w; rewrite gtree_mem_empty; case (gtree_mem t w). Qed.

Lemma gtree_partition_right : forall t,
  gtree_pair_partition t (Gtree_pair Gtree_empty t).
Proof. by move=> t w; rewrite gtree_mem_empty; case (gtree_mem t w). Qed.

Fixpoint gtree_restrict (t : gtree) (r : gtree_restriction) {struct t}
                        : gtree_pair :=
  match r, t with
  | Gtr_none, _ => Gtree_pair Gtree_empty t
  | _, Gtree_node t0 t1 t2 t3 =>
    let cont r0 r1 r2 r3 :=
      gtree_cons_pairs t (gtree_restrict t0 r0) (gtree_restrict t1 r1)
                         (gtree_restrict t2 r2) (gtree_restrict t3 r3) in
    gtr_split cont Gtr_none Gtr_none Gtr_none Gtr_none r
  | _, Gtree_leaf0 => if gtr_match0 r then gtp_0_e else gtp_e_0
  | _, Gtree_leaf1 => if gtr_match1 r then gtp_1_e else gtp_e_1
  | _, Gtree_leaf2 => if gtr_match2 r then gtp_2_e else gtp_e_2
  | _, Gtree_leaf3 => if gtr_match3 r then gtp_3_e else gtp_e_3
  | _, Gtree_leaf01 =>
    if gtr_match0 r
    then if gtr_match1 r then gtp_01_e else gtp_0_1
    else if gtr_match1 r then gtp_1_0 else gtp_e_01
  | _, Gtree_leaf12 =>
    if gtr_match1 r
    then if gtr_match2 r then gtp_12_e else gtp_1_2
    else if gtr_match2 r then gtp_2_1 else gtp_e_12
  | _, Gtree_leaf13 =>
    if gtr_match1 r
    then if gtr_match3 r then gtp_13_e else gtp_1_3
    else if gtr_match3 r then gtp_3_1 else gtp_e_13
  | _, Gtree_leaf23 =>
    if gtr_match2 r
    then if gtr_match3 r then gtp_23_e else gtp_2_3
    else if gtr_match3 r then gtp_3_2 else gtp_e_23
  | _, Gtree_empty => empty_gtree_pair
  end.

Let gtpl := gtree_partition_left.
Let gtpr := gtree_partition_right.

Theorem gtree_restrict_partition : forall t r,
  gtree_pair_partition t (gtree_restrict t r).
Proof.
elim=> [t0 Hrec0 t1 Hrec1 t2 Hrec2 t3 Hrec3|||||||||] r /=; simpl;
 case Dr: r => [|bs ct r']; try apply: gtpr; rewrite -{r' ct bs}Dr.
  by rewrite gtr_split_eq; apply gtree_cons_pairs_partition.
  case (gtr_match0 r); [ apply: gtpl | apply: gtpr ].
  case (gtr_match1 r); [ apply: gtpl | apply: gtpr ].
  case (gtr_match2 r); [ apply: gtpl | apply: gtpr ].
  case (gtr_match3 r); [ apply: gtpl | apply: gtpr ].
  by case: (gtr_match0 r) (gtr_match1 r) => [|] [|] [|[|||] [|s' w']].
  by case: (gtr_match1 r) (gtr_match2 r) => [|] [|] [|[|||] [|s' w']].
  by case: (gtr_match1 r) (gtr_match3 r) => [|] [|] [|[|||] [|s' w']].
  by case: (gtr_match2 r) (gtr_match3 r) => [|] [|] [|[|||] [|s' w']].
Qed.

Theorem gtree_mem0_restrict : forall t r w,
  let t' := gtree_pair_sub (gtree_restrict t r) false in
  gtree_mem t' w = gtree_mem t w && gtr_mem r w.
Proof.
simpl; elim=> [t0 Hrec0 t1 Hrec1 t2 Hrec2 t3 Hrec3|||||||||] r w /=;
 case Dr: r => [|bs ct r']; first
 [ by rewrite /= gtree_mem_empty ?andbF
 | rewrite -{bs ct r'}Dr ].
- rewrite gtr_split_eq gtree_mem0_cons_pairs; try apply gtree_restrict_partition.
  by case: w => [|s w]; rewrite // (gtr_mem_gsplit r); case: s => /=.
- case Hr: (gtr_match0 r) w => [|] [|[|||] [|s' w']];
  by rewrite // -gtr_match0_spec Hr.
- case Hr: (gtr_match1 r) w => [|] [|[|||] [|s' w']];
  by rewrite // -gtr_match1_spec Hr.
- case Hr: (gtr_match2 r) w => [|] [|[|||] [|s' w']];
  by rewrite // -gtr_match2_spec Hr.
- case Hr: (gtr_match3 r) w => [|] [|[|||] [|s' w']];
  by rewrite // -gtr_match3_spec Hr.
- case Hr: (gtr_match0 r); case Hr': (gtr_match1 r) w => [|] [|[|||] [|s' w']];
  by rewrite // -?gtr_match0_spec -?gtr_match1_spec ?Hr ?Hr'.
- case Hr: (gtr_match1 r); case Hr': (gtr_match2 r) w => [|] [|[|||] [|s' w']];
  by rewrite // -?gtr_match1_spec -?gtr_match2_spec ?Hr ?Hr'.
- case Hr: (gtr_match1 r); case Hr': (gtr_match3 r) w => [|] [|[|||] [|s' w']];
  by rewrite // -?gtr_match1_spec -?gtr_match3_spec ?Hr ?Hr'.
case Hr: (gtr_match2 r); case Hr': (gtr_match3 r) w => [|] [|[|||] [|s' w']];
by rewrite // -?gtr_match2_spec -?gtr_match3_spec ?Hr ?Hr'.
Qed.

End GtreeRestrict.

Unset Implicit Arguments.
