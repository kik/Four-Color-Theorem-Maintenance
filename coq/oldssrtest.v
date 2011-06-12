(* Unit test for ssr tactics *)

Require Import ssreflect.


Goal forall m n, n <= m -> m + m = n -> n = 0.
move=> m n; case: m /.
  by elim: {1 3}n => //= [m Hm] []. 
move=> m Hm Dn; elim: {-2}n / Dn Hm.
elim: {1 3}m => [|p Hrec]; first by case Dz: 0 /.
move=> /= Hm; apply: {Hrec}Hrec => /=.
rewrite -{2 p}(refl_equal (pred (S p))).
move: {m n}(S (p + _)) Hm => n.
by elim: {p}(S p) / => // [[|p] _] //=; right.
Qed.

Goal forall m n, (m, n) <> (n, m + 1).
move=> m n [Dm Dn].
perform idtac in Dm |- *.
rewrite {n}Dn in Dm.
by elim: m Dm => //= [m Hrec] [].
Qed.

Goal forall m n, n <= m -> m + m = n -> True.
move=> m n; elim Dn: n => [|n' Hrec]; first done.
clear n' Dn Hrec.
elim Dm: m / => [|p Hp Hrec].
  elim/eq_protect_rect: Dm.
  rewrite /protect_term.
  move: (refl_equal (n + n)).
  rewrite /(m + _).
  done.
rewrite -{2 p}/(pred (S p)).
elim Dq: {2}(S p) / Dm.
done.
Qed.
 
Definition mkopt A x : option A := Some x.

Implicit Arguments mkopt [A].

Inductive is_some (A : Set) : option A -> Prop :=
  IsSome : forall x : A, is_some A (Some x).

Implicit Arguments is_some [A].

Contextual Implicits mkopt is_some.

Inductive inhab (A : Set) : Prop := Inhab (x : A).

Definition inhab_some A (o : option A) (H : is_some o) : inhab A :=
  let: IsSome x := H in Inhab A x.

Coercion inhab_some : is_some >-> inhab.

Definition f1 x := let: (y, z) as x := x : nat * nat return y = y in refl_equal y.
Print f1.

Definition f2 m n (H : m <= n) :=
  if H is le_S n' H' as H'' in _ <= p return m <= p then le_S _ _ H' else le_n m.

Print f2.

Inductive ff : Prop := FFL x (_ : forall y, x <= y) | FFR y (_ : y = y :> nat).

Goal ff /\ True.
split; last done.
by left with 0; elim; constructor.
Qed.

Goal ff.
cut ff; last by right with 1.
step: ff; first by idtac; left with 0; elim; constructor.
step: (forall x, 0 + x = x) /\ (forall x y, x = y -> x <= y).
  split=> [x | x y <-] /=; [split | left].
step: ff by idtac; right with 1.
step: (forall x, x <= x) \/ False by left=> x.
step: False \/ (forall x, x <= x) by right=> x.
do 4 clear.
step: ff by left with 0 => y; elim: y; constructor.
step: (forall x, 0 <= x) /\ (forall x, 0 + x = x).
  by split=> x //; elim: x => //; right.
step: exists x, forall y, x <= y.
  by exists 0 => y; elim: y => //; right.
right with 1 => //.
Qed.

Goal forall m n, m + (1 + n) = m -> True.
move=> m n; move: (1 + _).
move Dp: {2}m => p _ _.
step := refl_equal (m - n + m).
move: {-1 3}m.
move: {}n.
move: m {n}p {H} Dp.
move=> m _ _ n p.
move/(minus m): n.
move=> n; move: p.
move/(plus n) {n} => p.
pose h := forall y, _ <= y \/ True.
step: h 0.
  move.
  by right.
step: h 0.
  move=> *.
  by right.
move: (_ + p * _).
done.
Qed.

Goal forall p, let: (x, _) := p : _ * nat in 0 <= x + 1.
move=> [x _] /=.
by elim: {x}(x + 1) => //; right.
Qed.

Goal forall n m, 0 + (1 + n) = m - m + n + 1.
move=> n m; rewrite {_ + n}/=.
step Emnn: forall p, p - p = 0 by elim.
rewrite -{1 0}(Emnn m).
rewrite Emnn.
step Em' := Emnn.
rewrite -{-3 0}(Emnn n) in Em' |- *.
rewrite Emnn in Em'.
rewrite -(Emnn m).
rewrite {m - _}Emnn.
rewrite Emnn.
rewrite -2!{1 0}(Emnn n).
rewrite ~Emnn /= {m Em'}.
elim : n => //= n Hrec.
congr S.
done.
Qed.

Goal True.
cut: _ * 0 = 0; last by elim.
pose f n := n * n.
pose g (n m : nat) (p := n + m) (q : nat := p - n) : nat := n - m.
pose fix h (m n : nat) := if n is S p then f p else g m m.
move=> H; step:= H 3.
set x := _ * _.
rewrite /x.
set y : nat := {1}0.
done.
Qed.




