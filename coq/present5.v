(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrnat.
Require Import part.
Require Import znat.
Require Import hubcap.
Require Import present.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma exclude5 : reducibility -> excluded_arity 5.
Proof.
move=> Hred; Presentation.
Pcase L0_1: s[1] <= 5.
  Pcase L1_1: s[2] <= 5.
    Pcase L2_1: s[3] <= 6.
      Pcase: s[3] <= 5.
        Reducible.
      Pcase: s[4] <= 5.
        Reducible.
      Pcase: s[5] > 6.
        Hubcap T[1,2]<=0 T[3,4]<=(-6) T[5]<=(-4) [].
      Pcase: s[5] > 5.
        Hubcap T[1,2]<=0 T[3,4]<=(-7) T[5]<=(-3) [].
      Reducible.
    Pcase: s[5] <= 6.
      Similar to *L2_1[3].
    Pcase: s[4] > 5.
      Hubcap T[1,2]<=0 T[3,4]<=(-6) T[5]<=(-4) [].
    Hubcap T[1,2]<=0 T[3,4]<=(-5) T[5]<=(-5) [].
  Pcase: s[5] <= 5.
    Similar to L1_1[4].
  Pcase L1_2: s[3] <= 5.
    Pcase: s[2] <= 6.
      Reducible.
    Pcase: s[4] <= 5.
      Similar to L1_1[2].
    Pcase L2_1: s[4] <= 6.
      Pcase: s[5] <= 6.
        Reducible.
      Hubcap T[1,2]<=(-4) T[3,4]<=(-2) T[5]<=(-4) [].
    Pcase: s[5] <= 6.
      Similar to *L2_1[2].
    Hubcap T[1,2]<=(-4) T[3,4]<=(-3) T[5]<=(-3) [].
  Pcase: s[4] <= 5.
    Similar to *L1_2[4].
  Pcase L1_3: s[2] > 6.
    Pcase: s[5] > 6.
      Hubcap T[1,2]<=(-3) T[3,4]<=(-4) T[5]<=(-3) [].
    Hubcap T[1,2]<=(-3) T[3,4]<=(-5) T[5]<=(-2) [].
  Pcase: s[5] > 6.
    Similar to *L1_3[4].
  Hubcap T[1,2]<=(-2) T[3,4]<=(-6) T[5]<=(-2) [].
Pcase: s[2] <= 5.
  Similar to L0_1[1].
Pcase: s[3] <= 5.
  Similar to L0_1[2].
Pcase: s[4] <= 5.
  Similar to L0_1[3].
Pcase: s[5] <= 5.
  Similar to L0_1[4].
Hubcap T[1,2]<=(-4) T[3,4]<=(-4) T[5]<=(-2) [].
Qed.

Set Strict Implicit.
Unset Implicit Arguments.