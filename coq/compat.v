Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import path.
Require Import fintype.


Section FiniteSet.

Variable d : finType.

Lemma filter_enum : forall a : pred d, filter a (enum d) =i a.
Proof. by move=> a x; rewrite mem_filter /predI andbC mem_enum. Qed.

Lemma cardIC : forall b a : pred d, #|predI a b| + #|predI a (predC b)| = #|a|.
Proof.
by move=> b a; apply: etrans _ (add0n _); rewrite -cardUI addnC -(@card0 d);
   congr (_ + _); apply: eq_card => x; rewrite /predI /predU /predC /= /in_mem /=;
   case (a x); case (b x).
Qed.

End FiniteSet.
