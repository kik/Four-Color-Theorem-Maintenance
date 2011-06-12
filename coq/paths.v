(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The basic theory of paths over a dataSet; this is essentially a   *)
(* complement to seq.v.                                              *)
(* Paths are non-empty sequences that obey a progression relation.   *)
(* They are passed around in three parts : the head and tail of the  *)
(* sequence, and a (boolean) predicate asserting the progression.    *)
(* This is rarely embarrassing, as the first two are usually         *)
(* implicit parameters inferred from the predicate, and it saves the *)
(* hassle of constantly constructing and destructing a dependent     *)
(* record. We allow duplicates; uniqueness, if desired (as is the    *)
(* case for several geometric constructions), must be asserted       *)
(* separately. We do provide shorthand, but for cycles only, because *)
(* the equational properties of "path" and "uniq" are unfortunately  *)
(* incompatible (esp. wrt "cat").                                    *)
(*    We define similarly cycles, but in this case we allow the      *)
(* empty sequence (which is a non-rooted empty cycle; by contrast,   *)
(* the empty path from x is the one-item sequence containing only x) *)
(*    We define notations for the common cases of function paths,    *)
(* where the progress relation is actually a function. We also       *)
(* define additional traversal/surgery operations, many of which     *)
(* could have been in seq.v, but are here because they only really   *)
(* are useful for sequences considered as paths :                    *)
(*  - directed surgery : splitPl, splitP, splitPr are dependent      *)
(*    predicates whose elimination splits a path x0:p at one of its  *)
(*    elements (say x). The three variants differ as follows:        *)
(*      - splitPl applies when x in in x0:p, generates two paths p1  *)
(*        and p2, along with the equation x = (last x0 p), and       *)
(*        replaces p with (cat p1 p2) in the goal (the patterned     *)
(*        Elim can be used to select occurrences and generate an     *)
(*        equation p = (cat p1 p2).                                  *)
(*      - splitP applies when x is in p, and replaces p with         *)
(*        (cat (add_last p1 x) p2), where x appears explicitly at    *)
(*        the end of the left part.                                  *)
(*      - splitPr similarly replaces p with (cat p1 (Adds x p2)),    *)
(*        where appears explicitly at the right of the split, when x *)
(*        is actually in p.                                          *)
(*    The parts p1 and p2 are computed using index/take/drop. The    *)
(*    splitP variant (but not the others) attempts to replace the    *)
(*    explicit expressions for p1 and p2 by p1 and p2, respectively. *)
(*    This is moderately useful, allows for defining other splitting *)
(*    lemmas with conclusions of the form (split x p p1 p2), with    *)
(*    other expressions for p1 and p2 that might be known to occur.  *)
(*  - function trajectories: traject, and a looping predicate.       *)
(*  - cycle surgery : arc extracts the sub-arc between two points    *)
(*    (including the first, excluding the second). (arc p x y) is    *)
(*    thus only meaningful if x and y are different points in p.     *)
(*  - cycle traversal : next, prev                                   *)
(*  - path order: mem2 checks whether two points belong to a         *)
(*    and appear in order (i.e., (mem2 p x y) checks that y appears  *)
(*    after an occurrence of x in p). This predicate a crucial part  *)
(*    of the definition of the abstract Jordan property.             *)
(*  - loop removal : shorten returns a shorter, duplicate-free path  *)
(*    with the same endpoints as its argument. The related shortenP  *)
(*    dependent predicate simultaneously substitutes a new path p',  *)
(*    for (shorten e x p), (last x p') for (last x p), and generates *)
(*    predicates asserting that p' is a duplicate-free subpath of p. *)
(* Although these functions operate on the underlying sequences, we  *)
(* provide a series of lemmas that define their interaction with the *)
(* path and cycle predicates, e.g., the path_cat equation can be     *)
(* used to split the path predicate after splitting the underlying   *)
(* sequence.                                                         *)

Section Paths.

Variables (n0 : nat) (d : dataSet) (x0 : d).

Notation dsub := (sub x0).

Section Path.

Variable e : rel d.

Fixpoint path (x : d) (p : seq d) {struct p} : bool :=
  if p is Adds y p' then e x y && path y p' else true.

Lemma path_cat : forall x p1 p2,
  path x (cat p1 p2) = path x p1 && path (last x p1) p2.
Proof.
by move=> x p1 p2; elim: p1 x => [|y p1 Hrec] x //=; rewrite Hrec -!andbA.
Qed.

Inductive split (x : d) : seq d -> seq d -> seq d -> Set :=
  Split : forall p1 p2 : seq d, split x (cat (add_last p1 x) p2) p1 p2.

Lemma splitP : forall (p : seq d) x, p x ->
   let i := index x p in split x p (take i p) (drop (S i) p).
Proof.
move=> p x Hx i; have := esym (cat_take_drop i p).
have Hi := Hx; rewrite -index_mem -/i in Hi; rewrite (drop_sub x Hi) -cat_add_last.
by rewrite {2}/i (sub_index x Hx) => Dp; rewrite {1}Dp.
Qed.

Inductive splitl (x1 x : d) : seq d -> Set :=
  Splitl : forall p1 p2 : seq d, last x1 p1 = x -> splitl x1 x (cat p1 p2).

Lemma splitPl : forall x1 p x, Adds x1 p x -> splitl x1 x p.
Proof.
move=> x1 p x; rewrite /= /setU1.
case: (x1 =P x) => [<-|_]; first by rewrite -(cat0s p).
case/splitP; split; exact: last_add_last.
Qed.

Inductive splitr (x : d) : seq d -> Set :=
  Splitr : forall p1 p2 : seq d, splitr x (cat p1 (Adds x p2)).

Lemma splitPr : forall (p : seq d) x, p x -> splitr x p.
Proof. by move=> p x H; case (splitP H); move=> p1 p2; rewrite cat_add_last. Qed.

Lemma pathPx : forall x p,
 reflect (forall i, i < size p -> e (dsub (Adds x p) i) (dsub p i)) (path x p).
Proof.
move=> x p; elim: p x => [|y p Hrec] x /=; first by left.
apply: (iffP andP) => [[Hxy Hp]|Hp].
  move=> [|i] Hi //; exact: Hrec _ Hp i Hi.
split; first exact: Hp 0 (leq0n (size p)).
apply/(Hrec y) => i; exact: Hp (S i).
Qed.

Fixpoint next_at (x y0 y : d) (p : seq d) {struct p} : d :=
  match p with
  | Seq0 => if x =d y then y0 else x
  | Adds y' p' => if x =d y then y' else next_at x y0 y' p'
  end.

Definition next p x := if p is Adds y p' then next_at x y y p' else x.

Fixpoint prev_at (x y0 y : d) (p : seq d) {struct p} : d :=
  match p with
  | Seq0 => if x =d y0 then y else x
  | Adds y' p' => if x =d y' then y else prev_at x y0 y' p'
  end.

Definition prev p x := if p is Adds y p' then prev_at x y y p' else x.

Lemma next_sub : forall p x,
  next p x = if p x then if p is Adds y p' then sub y p' (index x p) else x else x.
Proof.
move=> [|y0 p] x //=; elim: p {2 3 5}y0 => [|y' p Hrec] y /=;
  by rewrite /setU1 -(eqd_sym x); case (x =d y); try exact: Hrec.
Qed.

Lemma prev_sub : forall p x,
  prev p x = if p x then if p is Adds y p' then sub y p (index x p') else x else x.
Proof.
move=> [|y0 p] x //=; rewrite /setU1 eqd_sym orbC.
elim: p {2 5}y0 => [|y' p Hrec] y; rewrite /= /setU1 eqd_sym //.
case (y' =d x); simpl; auto.
Qed.

Lemma mem_next : forall (p : seq d) x, p (next p x) = p x.
Proof.
move=> p x; rewrite next_sub; case Hpx: (p x) => [|] //.
case: p (index x p) Hpx => [|y0 p'] //= i _; rewrite /setU1.
case: (ltnP i (size p')) => Hi; first by rewrite (mem_sub y0 Hi) orbT.
by rewrite (sub_default y0 Hi) set11.
Qed.

Lemma mem_prev : forall (p : seq d) x, p (prev p x) = p x.
Proof.
move=> p x; rewrite prev_sub; case Hpx: (p x) => [|] //.
case: p Hpx => [|y0 p'] Hpx //.
by apply mem_sub; rewrite /= ltnS index_size.
Qed.

Definition cycle p := if p is Adds x p' then path x (add_last p' x) else true.

(* ucycleb is the boolean predicate, but ucycle is defined as a Prop *)
(* so that it can be used as a coercion target. *)
Definition ucycleb p := cycle p && uniq p.
Definition ucycle p : Prop := cycle p && uniq p.

(* Projections, used for creating local lemmas. *)
Lemma ucycle_cycle : forall p, ucycle p -> cycle p.
Proof. by move=> p; case/andP. Qed.

Lemma ucycle_uniq : forall p, ucycle p -> uniq p.
Proof. by move=> p; case/andP. Qed.

Lemma cycle_path : forall p, cycle p = path (last x0 p) p.
Proof. by move=> [|x p] //=; rewrite -cats1 path_cat /= andbT andbC. Qed.

Lemma next_cycle : forall p x, cycle p -> p x -> e x (next p x).
Proof.
move=> [|y0 p] //= x.
elim: p {1 3 5}y0 => [|y' p Hrec] y /=; rewrite eqd_sym /setU1.
  by rewrite andbT orbF=> Hy Dy; rewrite Dy -(eqP Dy).
move/andP=> [Hy Hp]; case: (y =P x) => [<-|_] //; exact: Hrec.
Qed.

Lemma prev_cycle : forall p x, cycle p -> p x -> e (prev p x) x.
Proof.
move=> [|y0 p] //= x; rewrite /setU1 orbC.
elim: p {1 5}y0 => [|y' p Hrec] y /=; rewrite /= ?(eqd_sym x) /setU1.
  by rewrite andbT=> Hy Dy; rewrite Dy -(eqP Dy).
move/andP=> [Hy Hp]; case: (y' =P x) => [<-|_] //; exact: Hrec.
Qed.

Lemma cycle_rot : forall p, cycle (rot n0 p) = cycle p.
Proof.
case: (n0) => [|n] [|y0 p] //=; first by rewrite /rot /= cats0.
rewrite /rot /= -{3}(cat_take_drop n p) -cats1 -catA path_cat.
case: (drop n p) => [|z0 q]; rewrite /= -cats1 !path_cat /= !andbT andbC //.
by rewrite last_cat; repeat BoolCongr.
Qed.

Lemma ucycle_rot : forall p, ucycle (rot n0 p) = ucycle p.
Proof. by move=> *; rewrite /ucycle uniq_rot cycle_rot. Qed.

Lemma cycle_rotr : forall p, cycle (rotr n0 p) = cycle p.
Proof. by move=> p; rewrite -cycle_rot rot_rotr. Qed.

Lemma ucycle_rotr : forall p, ucycle (rotr n0 p) = ucycle p.
Proof. by move=> *; rewrite /ucycle uniq_rotr cycle_rotr. Qed.

(* The "appears no later" partial preorder defined by a path. *)

Definition mem2 (p : seq d) x y : bool := drop (index x p) p y.

Lemma mem2l : forall p x y, mem2 p x y -> p x.
Proof.
move=> p x y; rewrite /mem2 -!index_mem size_drop; move=> Hxy.
by rewrite ltn_lt0sub -(ltnSpred Hxy) ltnS leq0n.
Qed.

Lemma mem2lf : forall (p : seq d) x, p x = false -> forall y, mem2 p x y = false.
Proof. move=> p x Hx y; apply/idP => [Hp]; case/idP: Hx; apply: mem2l Hp. Qed.

Lemma mem2r : forall p x y, mem2 p x y -> p y.
Proof.
rewrite /mem2; move=> p x y Hxy.
by rewrite -(cat_take_drop (index x p) p) mem_cat /setU Hxy orbT.
Qed.

Lemma mem2rf : forall (p : seq d) y, p y = false -> forall x, mem2 p x y = false.
Proof. move=> p y Hy x; apply/idP => [Hp]; case/idP: Hy; apply: mem2r Hp. Qed.

Lemma mem2_cat : forall p1 p2 x y,
 mem2 (cat p1 p2) x y = mem2 p1 x y || mem2 p2 x y || p1 x && p2 y.
Proof.
move=> p1 p2 x y; rewrite {1}/mem2 index_cat drop_cat; case Hp1x: (p1 x).
  rewrite index_mem Hp1x mem_cat /setU /= -orbA.
  by case Hp2: (p2 y); [ rewrite !orbT // | rewrite (mem2rf Hp2) ].
by rewrite ltnNge leq_addr /= orbF subn_addr (mem2lf Hp1x).
Qed.

Lemma mem2_splice : forall p1 p3 x y p2,
  mem2 (cat p1 p3) x y -> mem2 (cat p1 (cat p2 p3)) x y.
Proof.
move=> p1 p3 x y p2 Hxy; move: Hxy; rewrite !mem2_cat mem_cat /setU.
case: (mem2 p1 x y) (mem2 p3 x y) => [|] // [|] /=; first by rewrite orbT.
by case: (p1 x) => [|] //= Hy; rewrite Hy !orbT.
Qed.

Lemma mem2_splice1 : forall p1 p3 x y z,
  mem2 (cat p1 p3) x y -> mem2 (cat p1 (Adds z p3)) x y.
Proof. move=> p1 p3 x y z; apply: (mem2_splice (seq1 z)). Qed.

Lemma mem2_adds : forall x p y,
  mem2 (Adds x p) y =1 (if x =d y then setU1 x p else mem2 p y).
Proof. by move=> x p y z; rewrite {1}/mem2 /= eqd_sym; case (x =d y). Qed.

Lemma mem2_last : forall y0 p x, mem2 (Adds y0 p) x (last y0 p) = Adds y0 p x.
Proof.
move=> y0 p x; apply/idP/idP; first by apply mem2l.
rewrite -index_mem /mem2; move: (index x (Adds y0 p)) => i Hi.
by rewrite lastI drop_add_last ?size_belast // mem_add_last /= setU11.
Qed.

Lemma mem2l_cat : forall (p1 : seq d) x, p1 x = false ->
  forall p2, mem2 (cat p1 p2) x =1 mem2 p2 x.
Proof. by move=> p1 x Hx p2 y; rewrite mem2_cat (Hx) (mem2lf Hx) /= orbF. Qed.

Lemma mem2r_cat : forall (p2 : seq d) y, p2 y = false ->
   forall p1 x, mem2 (cat p1 p2) x y = mem2 p1 x y.
Proof. by move=> p2 y Hy p1 x; rewrite mem2_cat (Hy) (mem2rf Hy) andbF !orbF. Qed.

Lemma mem2lr_splice : forall (p2 : seq d) x y, p2 x = false -> p2 y = false ->
  forall p1 p3, mem2 (cat (cat p1 p2) p3) x y = mem2 (cat p1 p3) x y.
Proof.
move=> p2 x y Hx Hy p1 p3.
by rewrite !mem2_cat !mem_cat /setU (Hx) Hy (mem2lf Hx) !andbF !orbF.
Qed.

Inductive split2r (x y : d) : seq d -> Set :=
  Split2l : forall p1 p2, Adds x p2 y -> split2r x y (cat p1 (Adds x p2)).

Lemma splitP2r : forall p x y, mem2 p x y -> split2r x y p.
Proof.
move=> p x y Hxy; have Hx := mem2l Hxy.
have Hi := Hx; rewrite -index_mem in Hi.
move: Hxy; rewrite /mem2 (drop_sub x Hi) (sub_index x Hx).
by case (splitP Hx); move=> p1 p2; rewrite cat_add_last; split.
Qed.

Fixpoint shorten (x : d) (p : seq d) {struct p} : seq d :=
  if p is Adds y p' then
    if p x then shorten x p' else Adds y (shorten y p')
  else seq0.

Inductive shorten_spec (x : d) (p : seq d) : d -> seq d -> Set :=
   ShortenSpec : forall p', path x p' -> uniq (Adds x p') -> sub_set p' p ->
                 shorten_spec x p (last x p') p'.

Lemma shortenP : forall x p, path x p -> shorten_spec x p (last x p) (shorten x p).
Proof.
move=> x p Hp; elim: p x {1 2 5}x Hp (setU11 x p) => [|y2 p Hrec] y0 y1.
  by rewrite /setU1 orbF; move=> _ Dy1; rewrite (eqP Dy1); repeat split; move.
rewrite /setU1 /= orbC; case/andP=> [Hy12 Hp].
case Hpy0: (setU1 y2 p y0).
case: (Hrec _ _ Hp Hpy0) => [p' Hp' Up' Hp'p] _; split; auto; simpl.
  move=> z; move/Hp'p; apply: setU1r.
case: (Hrec _ _ Hp (setU11 y2 p)) => [p' Hp' Up' Hp'p] Dy1.
have Hp'p2: sub_set (setU1 y2 p') (setU1 y2 p).
  move=> z; rewrite /= /setU1; case: (y2 =d z) => [|] //; apply: Hp'p.
rewrite -[last y2 p']/(last y0 (Adds y2 p')); split; auto.
  by rewrite -(eqP Dy1) /= Hy12.
by simpl; case Hy0: (setU1 y2 p' y0); first by rewrite (Hp'p2 _ Hy0) in Hpy0.
Qed.

End Path.

Lemma eq_path : forall e e', e =2 e' -> path e =2 path e'.
Proof.
by move=> e e' Ee x p; elim: p x => [|y p Hrec] x //=; rewrite Ee Hrec.
Qed.

Lemma sub_path : forall e e', sub_rel e e' ->
  forall x p, path e x p -> path e' x p.
Proof.
move=> e e' He x p; elim: p x => [|y p Hrec] x //=.
by case/andP=> [Hx Hp]; rewrite (He _ _ Hx) (Hrec _ Hp).
Qed.

End Paths.

Notation "'pathP' x0" := (pathPx x0 _ _ _) (at level 10, x0 at level 8).

Notation "'fpath' f" := (path (eqdf f)) (at level 10, f at level 8).

Notation "'fcycle' f" := (cycle (eqdf f)) (at level 10, f at level 8).

Notation "'ufcycle' f" := (ucycle (eqdf f)) (at level 10, f at level 8).

Prenex Implicits path next prev cycle ucycle mem2.

Section Trajectory.

Variables (d : dataSet) (f : d -> d).

Fixpoint traject (x : d) (n : nat) {struct n} : seq d :=
  if n is S n' then Adds x (traject (f x) n') else seq0.

Lemma size_traject : forall x n, size (traject x n) = n.
Proof. by move=> x n; elim: n x => [|n Hrec] x //=; NatCongr. Qed.

Lemma last_traject : forall x n, last x (traject (f x) n) = iter n f x.
Proof. by move=> x n; elim: n x => [|n Hrec] x //; rewrite -iter_f -Hrec. Qed.

Lemma fpathPx : forall x p, reflect (exists n, traject (f x) n = p) (fpath f x p).
Proof.
move=> x p; elim: p x => [|y p Hrec] x; first by left; exists 0.
rewrite /= andbC; case: {Hrec}(Hrec y) => Hrec.
  apply: (iffP eqP); first by case: Hrec => [n <-] <-; exists (S n).
  by case=> [] [|n] // [Dp].
by right; move=> [[|n] Dp] //; case: Hrec; exists n; case: Dp => <- <-.
Qed.

Lemma fpath_traject : forall x n, fpath f x (traject (f x) n).
Proof. by move=> x n; apply/(fpathPx x _); exists n. Qed.

Definition looping x n := traject x n (iter n f x).

Lemma loopingPx : forall x n,
  reflect (forall m, traject x n (iter m f x)) (looping x n).
Proof.
move=> x n; apply introP; last by move=> Hn Hn'; rewrite /looping Hn' in Hn.
case: n => [|n] Hn //; elim=> [|m Hrec]; first by apply: setU11.
move: (fpath_traject x n) Hn; rewrite /looping -!f_iter -last_traject /=.
rewrite /= in Hrec; case/splitPl: Hrec; move: (iter m f x) => y p1 p2 Ep1.
rewrite path_cat last_cat Ep1; case: p2 => [|z p2] //; case/and3P=> [_ Dy _] _.
by rewrite /setU1 mem_cat /setU /= (eqP Dy) /= setU11 !orbT.
Qed.

Lemma sub_traject : forall i n, i < n ->
  forall x, sub x (traject x n) i = iter i f x.
Proof.
move=> i n Hi x; elim: n {2 3}x i Hi => [|n Hrec] y [|i] Hi //=.
by rewrite Hrec ?iter_f.
Qed.

Lemma trajectPx : forall x n y,
  reflect (exists2 i, i < n & iter i f x = y) (traject x n y).
Proof.
move=> x n y; elim: n x => [|n Hrec] x; first by right; case.
  rewrite /= /setU1 orbC; case: {Hrec}(Hrec (f x)) => Hrec.
  by left; case: Hrec => [i Hi <-]; exists (S i); last by rewrite iter_f.
apply: (iffP eqP); first by exists 0; first by rewrite ltnNge.
by move=> [[|i] Hi Dy] //; case Hrec; exists i; last by rewrite iter_f.
Qed.

Lemma looping_uniq : forall x n, uniq (traject x (S n)) = negb (looping x n).
Proof.
move=> x n; rewrite /looping; elim: n x => [|n Hrec] x //.
rewrite -iter_f {2}[S]lock /= -lock {}Hrec -negb_orb /setU1; BoolCongr.
set y := iter n f (f x); case (trajectPx (f x) n y); first by rewrite !orbT.
rewrite !orbF; move=> Hy; apply/idP/eqP => [Hx|Dy].
  case/trajectPx: Hx => [m Hm Dx].
  have Hx': looping x (S m) by rewrite /looping -iter_f Dx /= setU11.
  case/trajectPx: (loopingPx _ _ Hx' (S n)); rewrite -iter_f -/y.
  move=> [|i] Hi //; rewrite -iter_f; move=> Dy.
  by case: Hy; exists i; first by exact (leq_trans Hi Hm).
by rewrite {2}Dy /(y) -last_traject /= mem_lastU.
Qed.

End Trajectory.

Notation fpathP := (fpathPx _ _ _).
Notation loopingP := (loopingPx _ _ _).
Notation trajectP := (trajectPx _ _ _ _).

Prenex Implicits traject.

Section UniqCycle.

Variables (n0 : nat) (d : dataSet) (e : rel d) (p : seq d).

Hypothesis Up : uniq p.

Lemma prev_next : forall x, prev p (next p x) = x.
Proof.
move=> x; rewrite prev_sub mem_next next_sub.
case Hpx: (p x) => [|] //; case Dp: p Up Hpx => [|y p'] //.
rewrite -(Dp) {1}Dp /=; move/andP=> [Hpy Hp'] Hx.
set i := index x p; rewrite -(sub_index y Hx) -/i; congr (sub y).
rewrite -index_mem -/i Dp /= ltnS leq_eqVlt in Hx.
case/setU1P: Hx => [Di|Hi]; last by apply: index_uniq.
rewrite Di (sub_default y (leqnn _)).
rewrite -index_mem -leqNgt in Hpy.
by apply: eqP; rewrite eqn_leq Hpy /index find_size.
Qed.

Lemma next_prev : forall x, next p (prev p x) = x.
Proof.
move=> x; rewrite next_sub mem_prev prev_sub.
case Hpx: (p x) => [|] //; case Dp: p Up Hpx => [|y p'] //.
rewrite -(Dp); move=> Hp Hpx; set i := index x p'.
have Hi: i < size p by rewrite Dp /= ltnS /i /index find_size.
rewrite (index_uniq y Hi Hp); case Hx: (p' x); first by apply: sub_index.
rewrite Dp /= /setU1 (Hx) orbF in Hpx; rewrite (eqP Hpx).
rewrite -index_mem ltnNge -/i in Hx; exact (sub_default _ (negbEf Hx)).
Qed.

Lemma cycle_next : fcycle (next p) p.
Proof.
case: p Up => [|x p'] Up' //; apply/(pathP x) => [i Hi].
rewrite size_add_last in Hi.
rewrite -cats1 -cat_adds sub_cat /= (Hi) /eqdf next_sub mem_sub //.
rewrite index_uniq // sub_cat /=; rewrite ltnS leq_eqVlt in Hi.
case/setU1P: Hi => [Di|Hi]; last by rewrite Hi set11.
by rewrite Di ltnn subnn sub_default ?leqnn /= ?set11.
Qed.

Lemma cycle_prev : cycle (fun x y => x =d (prev p y)) p.
Proof.
apply: etrans cycle_next; symmetry; case Dp: p => [|x p'] //.
apply: eq_path; rewrite -Dp; exact (monic2_eqd prev_next next_prev).
Qed.

Lemma cycle_from_next : (forall x, p x -> e x (next p x)) -> cycle e p.
Proof.
move=> He; case Dp: p cycle_next => [|x p'] //; rewrite -(Dp) !(cycle_path x).
have Hx: p (last x p) by rewrite Dp /= mem_lastU.
move: (next p) He {Hx}(He _ Hx) => np.
elim: (p) {x p' Dp}(last x p) => [|y p' Hrec] x He Hx //=.
case/andP=> [Dy Hp']; rewrite -{1}(eqP Dy) Hx /=.
apply: Hrec Hp' => [z Hz|]; apply: He; [exact: setU1r | exact: setU11].
Qed.

Lemma cycle_from_prev : (forall x, p x -> e (prev p x) x) -> cycle e p.
Proof.
move=> He; apply: cycle_from_next => [x Hx].
by rewrite -{1}[x]prev_next He ?mem_next.
Qed.

Lemma next_rot : next (rot n0 p) =1 next p.
Proof.
move=> x; have Hp := cycle_next; rewrite -(cycle_rot n0) in Hp.
case Hx: (p x); last by rewrite !next_sub mem_rot Hx.
rewrite -(mem_rot n0) in Hx; exact (esym (eqP (next_cycle Hp Hx))).
Qed.

Lemma prev_rot : prev (rot n0 p) =1 prev p.
Proof.
move=> x; have Hp := cycle_prev; rewrite -(cycle_rot n0) in Hp.
case Hx: (p x); last by rewrite !prev_sub mem_rot Hx.
rewrite -(mem_rot n0) in Hx; exact (eqP (prev_cycle Hp Hx)).
Qed.

End UniqCycle.

Section UniqRotrCycle.

Variables (n0 : nat) (d : dataSet) (p : seq d).

Hypothesis Up : uniq p.

Lemma next_rotr : next (rotr n0 p) =1 next p. Proof. exact: next_rot. Qed.

Lemma prev_rotr : prev (rotr n0 p) =1 prev p. Proof. exact: prev_rot. Qed.

End UniqRotrCycle.

Section UniqCycleRev.

Variable d : dataSet.

Lemma prev_rev : forall p : seq d, uniq p -> prev (rev p) =1 next p.
Proof.
move=> p Up x; case Hx: (p x); last by rewrite next_sub prev_sub mem_rev Hx.
case/rot_to: Hx (Up) => [i p' Dp] Urp; rewrite -uniq_rev in Urp.
rewrite -(prev_rotr i Urp); do 2 rewrite -(prev_rotr 1) ?uniq_rotr //.
rewrite -rev_rot -(next_rot i Up) {i p Up Urp}Dp.
case: p' => [|y p'] //; rewrite !rev_adds rotr1_add_last /= set11.
by rewrite -add_last_adds rotr1_add_last /= set11.
Qed.

Lemma next_rev : forall p : seq d, uniq p -> next (rev p) =1 prev p.
Proof. by move=> p Up x; rewrite -{2}[p]rev_rev prev_rev // uniq_rev. Qed.

End UniqCycleRev.

Section MapPath.

Variables (d d' : dataSet) (h : d' -> d) (e : rel d) (e' : rel d').

Definition rel_base (b : set d) :=
  forall x' y', negb (b (h x')) -> e (h x') (h y') = e' x' y'.

Lemma path_maps : forall b x' p',
   rel_base b -> negb (has (comp b h) (belast x' p')) ->
 path e (h x') (maps h p') = path e' x' p'.
Proof.
move=> b x' p' Hb; elim: p' x' => [|y' p' Hrec] x' //=; move/norP=> [Hbx Hbp].
congr andb; auto.
Qed.

Hypothesis Hh : injective h.

Lemma mem2_maps : forall x' y' p', mem2 (maps h p') (h x') (h y') = mem2 p' x' y'.
Proof. by move=> *; rewrite {1}/mem2 (index_maps Hh) -maps_drop mem_maps. Qed.

Lemma next_maps : forall p, uniq p ->
  forall x, next (maps h p) (h x) = h (next p x).
Proof.
move=> p Up x; case Hx: (p x); last by rewrite !next_sub (mem_maps Hh) Hx.
case/rot_to: Hx => [i p' Dp].
rewrite -(next_rot i Up); rewrite -(uniq_maps Hh) in Up.
rewrite -(next_rot i Up) -maps_rot {i p Up}Dp /=.
by case: p' => [|y p] //=; rewrite !set11.
Qed.

Lemma prev_maps : forall p, uniq p ->
  forall x, prev (maps h p) (h x) = h (prev p x).
Proof.
move=> p Up x; rewrite -{1}[x](next_prev Up) -(next_maps Up).
by rewrite prev_next ?uniq_maps.
Qed.

End MapPath.

Definition fun_base d d' h f f' := @rel_base d d' h (eqdf f) (eqdf f').

Section CycleArc.

Variable d : dataSet.

Definition arc (p : seq d) x y :=
  let px := rot (index x p) p in take (index y px) px.

Lemma arc_rot : forall p x, uniq p -> p x -> forall i, arc (rot i p) x =1 arc p x.
Proof.
move=> p x Up Hx i y; congr (fun q => take (index y q) q); move: Up Hx {y}.
rewrite -{1 2 5 6}(cat_take_drop i p) /rot uniq_cat; case/and3P=> [_ Hp _].
rewrite !drop_cat !take_cat !index_cat mem_cat /setU orbC.
case Hx: (drop i p x) => [|] /=.
  move=> _; rewrite (negbE (hasPn Hp _ Hx)).
  by rewrite index_mem Hx ltnNge leq_addr /= subn_addr catA.
by move=> Hx'; rewrite Hx' index_mem Hx' ltnNge leq_addr /= subn_addr catA.
Qed.

Lemma left_arc : forall x y p1 p2, let p := Adds x (cat p1 (Adds y p2)) in
  uniq p -> arc p x y = Adds x p1.
Proof.
move=> x y p1 p2 p Up; rewrite /arc {1}/p /= set11 rot0.
move: Up; rewrite /p -cat_adds uniq_cat index_cat; move: (Adds x p1) => xp1.
rewrite /= negb_orb -!andbA; case/and3P=> [_ Hy _].
by rewrite (negbE Hy) set11 addn0 take_size_cat.
Qed.

Lemma right_arc : forall x y p1 p2, let p := Adds x (cat p1 (Adds y p2)) in
   uniq p -> arc p y x = Adds y p2.
Proof.
move=> x y p1 p2 p Up; set n := size (Adds x p1); rewrite -(arc_rot Up _ n).
  move: Up; rewrite -(uniq_rot n) /p -cat_adds /n rot_size_cat.
  by move=> *; rewrite /= left_arc.
by rewrite /p -cat_adds mem_cat /setU /= setU11 orbT.
Qed.

Inductive rot_to_arc_spec (p : seq d) (x y : d) : Set :=
    RotToArcSpec : forall i p1 p2,
      Adds x p1 = arc p x y ->
      Adds y p2 = arc p y x ->
      rot i p = Adds x (cat p1 (Adds y p2)) ->
    rot_to_arc_spec p x y.

Lemma rot_to_arc : forall p x y,
 uniq p -> p x -> p y -> negb (x =d y) -> rot_to_arc_spec p x y.
Proof.
move=> p x y Up Hx Hy Hxy; case: (rot_to Hx) (Hy) (Up) => [i p' Dp] Hy'.
rewrite -(mem_rot i) (Dp) /= /setU1 (negbE Hxy) in Hy'; rewrite -(uniq_rot i) Dp.
case/splitPr: p' / Hy' Dp => [p1 p2] Dp Up'; exists i p1 p2; auto.
  by rewrite -(arc_rot Up Hx i) Dp (left_arc Up').
by rewrite -(arc_rot Up Hy i) Dp (right_arc Up').
Qed.

End CycleArc.

Prenex Implicits arc.

Unset Implicit Arguments.

