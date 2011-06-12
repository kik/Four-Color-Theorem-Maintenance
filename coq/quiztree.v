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
Require Import geometry.
Require Import color.
Require Import coloring.
Require Import quiz.
Require Import cfmap.
Require Import cfquiz.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Compile a sequencs of (reducible) configurations into a set of quizzes,  *)
(* and store them in a tree structure according to the arities of the three *)
(* center regions. Rotations and reflections are also stored, so that the   *)
(* reducibility search can do a single lookup per triangle in the searched  *)
(* part (see file redpart.v).                                               *)
(* The middle nodes of the tree have four branches, for each of the arities *)
(* 5, 6, 7 and 8; the top node also has four branches, but with a different *)
(* interpretation: the first is a subtree for arities less than 9, and the  *)
(* other three for arities 9, 10, and 11 (we don't need to store those      *)
(* lower in the tree, since only the most central region of our             *)
(* configurations can have more than 8 sides). Also, since such a large     *)
(* region can only match the hub, we don't store the rotations of its quiz. *)
(*   The quiz fork and trees are traversed in the inner loop of the         *)
(* unavoidability computation, so, like parts, their representation has     *)
(* been compressed, with the quiz triples integrated in the list structure, *)
(* and the tree structure feeding directly in the list structure.           *)

Inductive quiz_tree : Set :=
  | QztNil : quiz_tree
  | QztLeaf : forall q1 q2 q3 : question, quiz_tree -> quiz_tree
  | QztNode : forall t5 t6 t7 t8 : quiz_tree, quiz_tree
  | QztHubNode : forall t58 t9 t10 t11 : quiz_tree, quiz_tree.

(* Not-nil test.                                                            *)

Definition qzt_proper qt' := if qt' is QztNil then false else true.

(* Update/store operations.                                                 *)

Fixpoint qzt_put1 (qa : qarity) (qr : quiz_tree -> quiz_tree) (t : quiz_tree)
    {struct t} : quiz_tree :=
  match t, qa with
  | QztNode t5 t6 t7 t8, Qa5 => QztNode (qr t5) t6 t7 t8
  | QztNode t5 t6 t7 t8, Qa6 => QztNode t5 (qr t6) t7 t8
  | QztNode t5 t6 t7 t8, Qa7 => QztNode t5 t6 (qr t7) t8
  | QztNode t5 t6 t7 t8, Qa8 => QztNode t5 t6 t7 (qr t8)
  | QztHubNode t58 t9 t10 t11, Qa9 => QztHubNode t58 (qr t9) t10 t11
  | QztHubNode t58 t9 t10 t11, Qa10 => QztHubNode t58 t9 (qr t10) t11
  | QztHubNode t58 t9 t10 t11, Qa11 => QztHubNode t58 t9 t10 (qr t11)
  | QztHubNode t58 t9 t10 t11, _ =>
      QztHubNode (qzt_put1 qa qr t58) t9 t10 t11
  | _, _ => t
  end.

Definition qzt_put3 qa1 qa2 qa3 q1 q2 q3 :=
  qzt_put1 qa1 (qzt_put1 qa2 (qzt_put1 qa3 (QztLeaf q1 q2 q3))).

Definition qzt_put3rot qa1 qa2 qa3 q1 q2 q3 t :=
  qzt_put3 qa1 qa2 qa3 q1 q2 q3
    (qzt_put3 qa2 qa3 qa1 q2 q3 q1 (qzt_put3 qa3 qa1 qa2 q3 q1 q2 t)).

Definition qzt_put (qa1 qa2 qa3 : qarity) q1 q2 q3 :=
  if 8 < qa1 then qzt_put3 qa1 qa2 qa3 q1 q2 q3 else
  qzt_put3rot qa1 qa2 qa3 q1 q2 q3.

Definition qzt_empty :=
  let mkn t := QztNode t t t t in
  let n2 := mkn (mkn QztNil) in QztHubNode (mkn n2) n2 n2 n2.

Definition normq q :=
  match q with
  | Qask1 qa => QaskLR qa Qask0 Qask0
  | QaskL qa ql => QaskLR qa ql Qask0
  | QaskR qa qr => QaskLR qa Qask0 qr
  | _ => q
  end.

Definition store_qz qz :=
  if qz is Quiz (QaskR qa1 q1) (QaskR qa2 q2) then
      match normq q1, normq q2 with
      | QaskLR qa1r q1l q1r, QaskLR qa2r q2l q2r =>
          if qa1r < qa2r then qzt_put qa1 qa2 qa1r q1l q2 q1r else
                              qzt_put qa1 qa2r qa2 q1 q2r q2l
      | QaskLR qa1r q1l q1r, _ => qzt_put qa1 qa2 qa1r q1l q2 q1r
      | _, QaskLR qa2r q2l q2r => qzt_put qa1 qa2r qa2 q1 q2r q2l
      | _, _ => fun t => t
      end
  else fun t => t.

Definition store_cf_qz qz (sym : bool) t :=
   store_qz qz (if sym then t else store_qz (flipqz qz) t).

Fixpoint cfquiz_tree_rec (qt : quiz_tree) (cfs : configseq)
          {struct cfs} : quiz_tree :=
  if cfs is Adds cf cfs' then
    if store_cf_qz (cfquiz cf) (cfsym cf) qt is QztHubNode t58 t9 t10 t11 then
      cfquiz_tree_rec (QztHubNode t58 t9 t10 t11) cfs'
    else QztNil
  else qt.

Definition cfquiz_tree := cfquiz_tree_rec qzt_empty.

(* Sanity checks; both computations should return the same result *)
(* (3361 for the full config list).                               *)

Fixpoint qzt_size (t : quiz_tree) : nat :=
  match t with
  | QztLeaf _ _ _ t' => S (qzt_size t')
  | QztNode t5 t6 t7 t8 =>
      qzt_size t5 + (qzt_size t6 + (qzt_size t7 + qzt_size t8))
  | QztHubNode t58 t9 t10 t11 =>
      qzt_size t58 + (qzt_size t9 + (qzt_size t10 + qzt_size t11))
  | _ => 0
  end.

Definition cf_main_arity cf :=
  if cfquiz cf is Quiz (QaskR qa _) _ then qa : nat else 0.

Definition cf_qzt_size1 cf :=
  let nperm := if cf_main_arity cf <= 8 then 3 else 1 in
  if cfsym cf then nperm else double nperm.

Definition cf_qzt_size := foldr (fun cf => plus (cf_qzt_size1 cf)) 0.

Definition configs_compiled cfs := qzt_size (cfquiz_tree cfs) = cf_qzt_size cfs.

(* end of sanity checks. *)

Fixpoint qzt_get1 (qa : qarity) (t : quiz_tree) {struct t} : quiz_tree :=
  match t, qa with
  | QztNode t' _ _ _, Qa5 => t'
  | QztNode _ t' _ _, Qa6 => t'
  | QztNode _ _ t' _, Qa7 => t'
  | QztNode _ _ _ t', Qa8 => t'
  | QztHubNode _ t' _ _, Qa9 => t'
  | QztHubNode _ _ t' _, Qa10 => t'
  | QztHubNode _ _ _ t', Qa11 => t'
  | QztHubNode t' _ _ _, _ => qzt_get1 qa t'
  | _, _ => QztNil
  end.

Definition qzt_get2 qa2 qa3 t := qzt_get1 qa3 (qzt_get1 qa2 t).

Definition qzt_get3 qa1 qa2 qa3 t := qzt_get2 qa2 qa3 (qzt_get1 qa1 t).

Section FitQuizTree.

Variables (cfs : configseq) (g : hypermap).
Hypothesis Hg : plain_cubic g.
Let De2 := plain_eq Hg.
Let Dn3 := cubic_eq Hg.

Lemma fit_normq : forall (x : g) q, fitq x (normq q) = fitq x q.
Proof. by move=> x q; case: q => *; rewrite /fitq /= ?cats0. Qed.

Variable x1 : g.
Notation x2 := (node x1).
Notation x3 := (node x2).
Let ax1 := qarity_of_nat (arity x1).
Let ax2 := qarity_of_nat (arity x2).
Let ax3 := qarity_of_nat (arity x3).

Notation "x '=a' y" := ((x : nat) =d arity y) (at level 70, only parsing).
Definition qzt_fita := and3b (ax1 =a x1) (ax2 =a x2) (ax3 =a x3).

Fixpoint qzt_fitl (t : quiz_tree) : bool :=
  if t is QztLeaf q1 q2 q3 t' then
      and3b (fitq (qstepR x1) q1) (fitq (qstepR x2) q2) (fitq (qstepR x3) q3)
    || qzt_fitl t'
  else false.

Definition qzt_fit t := qzt_fita && qzt_fitl (qzt_get3 ax1 ax2 ax3 t).

Notation quiz3 := (fun qa1 qa2 qa3 q1 q2 q3 =>
   Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2)).

Lemma qzt_get_put1 : forall qa qa' qr t,
    qa = qa' /\ qr (qzt_get1 qa t) = qzt_get1 qa (qzt_put1 qa' qr t)
 \/ qzt_get1 qa t = qzt_get1 qa (qzt_put1 qa' qr t).
Proof. move=> qa qa' qr; elim; auto; case qa'; auto; case qa; auto. Qed.

Let Hfp1 := qzt_get_put1.
Lemma qzt_fit_put3 : forall qa1 qa2 qa3 q1 q2 q3 t,
                     qzt_fit (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t) ->
 fitqz (edge x2) (quiz3 qa1 qa2 qa3 q1 q2 q3) \/ qzt_fit t.
Proof.
move=> qa1 qa2 qa3 q1 q2 q3 t; case/andP=> [Hax]; rewrite /qzt_fit Hax.
rewrite /fitqz /= /eqd /= eqseqE -arity_face Enode /qstepR De2 /qstepL Dn3 -!catA.
rewrite /= 2!fitq_cat maps_adds eqseq_adds; case/and3P: Hax; do 3 move/eqP => <-.
rewrite /qzt_get3 /qzt_get2 /qzt_put3; set qr := QztLeaf q1 q2 q3.
case: (Hfp1 ax1 qa1 (qzt_put1 qa2 (qzt_put1 qa3 qr)) t) => [[<- <-]|<-]; auto.
case: (Hfp1 ax2 qa2 (qzt_put1 qa3 qr) (qzt_get1 ax1 t)) => [[<- <-]|<-]; auto.
case: (Hfp1 ax3 qa3 qr (qzt_get1 ax2 (qzt_get1 ax1 t))) => [[<- <-]|<-]; auto.
rewrite !set11 /= {1}[andb]lock andbC -lock; case/orP; auto.
Qed.

Lemma fitqz_rot : forall (y : g) qa1 qa2 qa3 q1 q2 q3,
  fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3)
   = fitqz (edge (face y)) (quiz3 qa3 qa1 qa2 q3 q1 q2).
Proof.
move=> y qa1 qa2 qa3 q1 q2 q3; rewrite /fitqz /= /eqd /= !eqseqE -!catA.
rewrite !fitq_cat !maps_adds !eqseq_adds /qstepL /qstepR !De2 Eface.
rewrite -{1}[node (edge y)]Enode !arity_face -{1 2}[edge y]Eedge De2 Dn3.
rewrite -{8 9}[y]De2 Eedge.
case: (qa1 =a y) => /=; last by rewrite !andbF.
congr andb; rewrite andbC -!andbA.
by case (qa2 =a edge y); last by rewrite /= !andbF.
Qed.

Lemma qzt_fit_put : forall qa1 qa2 qa3 q1 q2 q3 t,
   qzt_fit (qzt_put qa1 qa2 qa3 q1 q2 q3 t) ->
 (exists y : g, fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3)) \/ qzt_fit t.
Proof.
move=> qa1 qa2 qa3 q1 q2 q3 t; rewrite /qzt_put /qzt_put3rot.
case (8 < qa1); first by case/qzt_fit_put3; auto; left; exists (edge x2).
case/qzt_fit_put3; first by left; exists (edge x2).
case/qzt_fit_put3; first by rewrite fitqz_rot Enode; left; exists (edge x1).
case/qzt_fit_put3; auto.
by rewrite 2!fitqz_rot -[x1]Dn3 !Enode; left; exists (edge x3).
Qed.

Lemma fitqz_swap : forall (y : g) qa1 qa2 qa3 q1 q2 q3,
 fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3) =
   fitqz (face y) (Quiz (QaskR qa1 q1) (QaskR qa3 (QaskLR qa2 q3 q2))).
Proof.
move=> y qa1 qa2 qa3 q1 q2 q3; rewrite /fitqz /= /eqd /= !eqseqE -!catA.
rewrite !fitq_cat !maps_adds !eqseq_adds fitq_cat.
rewrite /qstepR /qstepL !De2 -{1}[node (edge y)]Enode !arity_face Eface.
by rewrite -{1 2}[edge y]Eedge De2 Dn3 -{10 11}[y]De2 Eedge; repeat BoolCongr.
Qed.

Lemma qzt_fit_store : forall qz t, qzt_fit (store_qz qz t) ->
  (isQuizR qz /\ exists y : g, fitqz y qz) \/ qzt_fit t.
Proof.
move=> [q1 q2] t; case: q1; auto; case: q2; auto => qa2 q2 qa1 q1 Hx.
set qz := Quiz _ _; set G := (exists y : g, fitqz y qz) \/ qzt_fit t.
suffice: G by move=> [H|H]; [ left; split | right ].
have HxG1: forall qa1r q1l q1r, normq q1 = QaskLR qa1r q1l q1r ->
    qzt_fit (qzt_put qa1 qa2 qa1r q1l q2 q1r t) -> G.
  move=> qa1r q1l q1r Dq1'; case/qzt_fit_put; last by right.
  move=> [y Hy]; left; exists y; move: Hy; rewrite -Dq1' /fitqz /eqd /= !eqseqE.
  by rewrite fitq_cat fit_normq -fitq_cat.
have HxG2: forall qa2r q2l q2r, normq q2 = QaskLR qa2r q2l q2r ->
    qzt_fit (qzt_put qa1 qa2r qa2 q1 q2r q2l t) -> G.
  move=> qa2r q2l q2r Dq2'; case/qzt_fit_put; last by right.
  move=> [y Hy]; left; exists (face y); apply: etrans Hy.
  rewrite fitqz_swap -Dq2' /fitqz /eqd /= !eqseqE !fitq_cat !maps_adds.
  by rewrite !eqseq_adds !andbA; congr andb; symmetry; apply: fit_normq.
move: Hx; simpl; case: {-1}(normq q1) (erefl (normq q1));
 case: {-1}(normq q2) (erefl (normq q2)); first [ by right | eauto ].
move=> qa2r q2l q2r Dq2 qa1r q1l q1r Dq1; case (qa1r < qa2r); eauto.
Qed.

Lemma qzt_fit_store_cf : forall qz sym t, qzt_fit (store_cf_qz qz sym t) ->
    isQuizR qz /\ ((exists y : g, fitqz y qz) \/ (exists y : mirror g, fitqz y qz))
 \/ qzt_fit t.
Proof.
move=> qz sym t; rewrite /store_cf_qz /=.
case: sym; repeat case/qzt_fit_store; auto; move=> [Hqz Hgqz]; left;
 try by split; auto.
have Hqz': (isQuizR qz) by case: (qz) Hqz => [q1 q2]; case q1; case q2.
split; auto; right; case: Hgqz => [y Hy]; rewrite fitqz_flip //= in Hy.
by exists (face y).
Qed.

Lemma qzt_fit_cfquiz : forall cfs, qzt_fit (cfquiz_tree cfs) ->
 exists2 cf, cfs cf &
 exists2 qz, (exists y : g, fitqz y qz) \/ (exists y : mirror g, fitqz y qz)
          & embeddable (cfring cf) /\ (exists u, valid_quiz (cfring cf) u qz).
Proof.
move=> cfs'; rewrite /cfquiz_tree.
have: qzt_fit qzt_empty = false.
  by rewrite /qzt_fit andbC; case: ax1 => //; case: ax2 => //; case ax3.
elim: cfs' qzt_empty => [|cf cfs' Hrec] qt0 Hqt0 /=; first by rewrite Hqt0.
have Hqt00: qzt_fit QztNil = false by apply: andbF.
set qt := store_cf_qz _ _ qt0.
case Dqt: qt => [|q1 q2 q3 t|t5 t6 t7 t8|t58 t9 t10 t11]; try by rewrite Hqt00.
 rewrite -{t58 t9 t10 t11}Dqt => Hqt'; case Hqt: (qzt_fit qt).
  case/qzt_fit_store_cf: Hqt; last by rewrite Hqt0.
  move=> [Hqz Hgqz]; exists cf; [ apply: setU11 | exists (cfquiz cf); auto ].
  by split; [ apply embeddable_cfquiz | apply valid_cfquiz ].
  case: {Hrec Hqt' Hqt}(Hrec _ Hqt Hqt') => [cf' Hcf' Hx].
by exists cf'; first by apply setU1r.
Qed.

Definition qzt_truncate t :=
  if t is  QztHubNode (QztNode _ _ _ _ as t58) _ _ _ then t58 else t.

Lemma qzt_get1_truncate : forall qa t,
 let t' := qzt_get1 qa (qzt_truncate t) in
 qzt_proper t' -> t' = qzt_get1 qa t.
Proof. by do 3 case=> //. Qed.

End FitQuizTree.

(*  global sanity check, using the functions define above
Require configurations.

Eval Compute in (qzt_size (cfquiz_tree the_configs)).
Eval Compute in (cf_qzt_size the_configs).
Goal (configs_compiled the_configs).
Split.
Save the_configs_compiled.
*)


Unset Implicit Arguments.