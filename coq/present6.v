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

Lemma exclude6 : reducibility -> excluded_arity 6.
Proof.
move=> Hred; Presentation.
Pcase L0_1 : s[1] > 6.
  Pcase L1_1 : s[3] > 6.
    Pcase : s[2] > 5.
      Pcase : s[5] > 6.
        Pcase : s[4] > 5.
          Pcase : s[6] > 5.
            Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
          Hubcap T[1,2]<=(-1) T[3,5]<=(-1) T[4,6]<=2 [].
        Pcase : s[6] > 5.
          Hubcap T[1,2]<=0 T[3,5]<=(-2) T[4,6]<=2 [].
        Hubcap T[1,2]<=(-1) T[3,5]<=(-3) T[4,6]<=4 [].
      Pcase L3_1 : s[6] > 6.
        Pcase : s[4] > 6.
          Pcase : s[5] > 5.
            Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
          Hubcap T[1,2]<=0 T[3,5]<=2 T[4,6]<=(-2) [].
        Pcase : s[4] > 5.
          Pcase : s[5] > 5.
            Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
          Hubcap T[1,2]<=0 T[3,5]<=1 T[4,6]<=(-1) [].
        Pcase : s[5] > 5.
          Hubcap T[1,2]<=0 T[3,5]<=(-1) T[4,6]<=1 [].
        Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
      Pcase : s[4] > 6.
        Similar to *L3_1[3].
      Pcase L3_2 : s[6] <= 5.
        Pcase : s[4] <= 5.
          Reducible.
        Pcase : s[5] <= 5.
          Hubcap T[2,3]<=(-1) T[1,5]<=0 T[4,6]<=1 [].
        Hubcap T[2,3]<=0 T[1,5]<=(-1) T[4,6]<=1 [].
      Pcase : s[4] <= 5.
        Similar to *L3_2[3].
      Pcase : s[5] <= 5.
        Pcase L4_1 : h[6] > 6.
          Hubcap T[1,2]<=(-1) T[3,5]<=1 T[4,6]<=0 [].
        Pcase : h[5] > 6.
          Similar to *L4_1[3].
        Hubcap T[2,3]<=(-1) T[1,5]<=1 T[4,6]<=0 [].
      Pcase : h[6] > 6.
        Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
      Pcase : h[6] <= 5.
        Pcase : f1[6] > 6.
          Hubcap T[1,2]<=(-1) T[3,5]<=1 T[4,6]<=0 [].
        Pcase : f1[6] <= 5.
          Hubcap T[1,2]<=(-2) T[3,5]<=2 T[4,6]<=0 [].
        Hubcap T[1,2]<=(-1) T[3,5]<=1 T[4,6]<=0 [].
      Pcase : f1[6] > 6.
        Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
      Pcase : f1[6] <= 5.
        Pcase : h[1] <= 5.
          Hubcap T[1,2]<=(-2) T[3,5]<=2 T[4,6]<=0 [].
        Hubcap T[1,2]<=(-1) T[3,5]<=1 T[4,6]<=0 [].
      Pcase : h[1] <= 5.
        Hubcap T[1,2]<=(-1) T[3,5]<=1 T[4,6]<=0 [].
      Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
    Pcase : s[5] > 6.
      Pcase : s[4] > 5.
        Pcase : s[6] > 5.
          Hubcap T[1,2]<=1 T[3,5]<=(-1) T[4,6]<=0 [].
        Hubcap T[1,2]<=0 T[3,5]<=(-2) T[4,6]<=2 [].
      Pcase : s[6] > 5.
        Hubcap T[1,2]<=1 T[3,5]<=(-3) T[4,6]<=2 [].
      Hubcap T[1,2]<=0 T[3,5]<=(-4) T[4,6]<=4 [].
    Pcase L3_1 : s[6] > 6.
      Pcase : s[4] > 6.
        Pcase : s[5] > 5.
          Hubcap T[1,2]<=1 T[3,5]<=(-1) T[4,6]<=0 [].
        Hubcap T[1,2]<=1 T[3,5]<=1 T[4,6]<=(-2) [].
      Pcase : s[4] > 5.
        Pcase : s[5] > 5.
          Hubcap T[1,2]<=1 T[3,5]<=(-1) T[4,6]<=0 [].
        Hubcap T[1,2]<=1 T[3,5]<=0 T[4,6]<=(-1) [].
      Pcase : s[5] > 5.
        Hubcap T[1,2]<=1 T[3,5]<=(-2) T[4,6]<=1 [].
      Hubcap T[1,2]<=1 T[3,5]<=(-1) T[4,6]<=0 [].
    Pcase : s[4] > 6.
      Similar to *L3_1[3].
    Pcase L3_2 : s[6] <= 5.
      Pcase : s[4] <= 5.
        Reducible.
      Pcase : s[5] <= 5.
        Hubcap T[2,3]<=0 T[1,5]<=(-1) T[4,6]<=1 [].
      Hubcap T[2,3]<=1 T[1,5]<=(-2) T[4,6]<=1 [].
    Pcase : s[4] <= 5.
      Similar to *L3_2[3].
    Pcase : s[5] <= 5.
      Pcase L4_1 : h[6] > 6.
        Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
      Pcase : h[5] > 6.
        Similar to *L4_1[3].
      Hubcap T[2,3]<=0 T[1,5]<=0 T[4,6]<=0 [].
    Pcase : h[6] > 6.
      Hubcap T[1,2]<=1 T[3,5]<=(-1) T[4,6]<=0 [].
    Pcase : h[6] <= 5.
      Pcase : f1[6] > 6.
        Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
      Pcase : f1[6] <= 5.
        Hubcap T[1,2]<=(-1) T[3,5]<=1 T[4,6]<=0 [].
      Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
    Pcase : f1[6] > 6.
      Hubcap T[1,2]<=1 T[3,5]<=(-1) T[4,6]<=0 [].
    Pcase : f1[6] <= 5.
      Pcase : h[1] <= 5.
        Hubcap T[1,2]<=(-1) T[3,5]<=1 T[4,6]<=0 [].
      Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
    Pcase : h[1] <= 5.
      Hubcap T[1,2]<=0 T[3,5]<=0 T[4,6]<=0 [].
    Hubcap T[1,2]<=1 T[3,5]<=(-1) T[4,6]<=0 [].
  Pcase : s[5] > 6.
    Similar to L1_1[4].
  Pcase : s[4] > 6.
    Pcase : s[2] > 6.
      Similar to L1_1[1].
    Pcase : s[6] > 6.
      Similar to L1_1[3].
    Pcase L2_1 : s[2] <= 5.
      Pcase : s[3] <= 5.
        Pcase L4_1 : s[5] <= 5.
          Pcase : s[6] <= 5.
            Pcase : h[6] <= 5.
              Hubcap T[1,3]<=(-3) T[2,4]<=(-3) T[5,6]<=6 [].
            Hubcap T[1,3]<=(-2) T[2,4]<=(-2) T[5,6]<=4 [].
          Pcase : h[3] <= 5.
            Hubcap T[1,5]<=(-2) T[4,6]<=(-4) T[2,3]<=6 [].
          Hubcap T[1,5]<=(-1) T[4,6]<=(-3) T[2,3]<=4 [].
        Pcase : s[6] <= 5.
          Similar to *L4_1[2].
        Pcase : h[3] <= 5.
          Hubcap T[1,5]<=(-3) T[4,6]<=(-3) T[2,3]<=6 [].
        Hubcap T[1,5]<=(-2) T[4,6]<=(-2) T[2,3]<=4 [].
      Pcase : s[5] <= 5.
        Pcase : s[6] <= 5.
          Pcase : h[6] <= 5.
            Hubcap T[1,3]<=(-4) T[2,4]<=(-2) T[5,6]<=6 [].
          Hubcap T[1,3]<=(-3) T[2,4]<=(-1) T[5,6]<=4 [].
        Pcase : h[6] <= 5.
          Pcase : h[5] > 5.
            Hubcap T[1,3]<=(-3) T[2,4]<=(-1) T[5,6]<=4 [].
          Hubcap T[1,3]<=(-3) T[2,4]<=(-2) T[5,6]<=5 [].
        Pcase : h[6] <= 6.
          Pcase : h[5] > 5.
            Hubcap T[1,3]<=(-2) T[2,4]<=0 T[5,6]<=2 [].
          Hubcap T[1,3]<=(-2) T[2,4]<=(-1) T[5,6]<=3 [].
        Hubcap T[1,3]<=(-2) T[2,4]<=0 T[5,6]<=2 [].
      Pcase : s[6] <= 5.
        Pcase : h[6] <= 5.
          Pcase : h[1] > 5.
            Hubcap T[1,3]<=(-3) T[2,4]<=(-1) T[5,6]<=4 [].
          Hubcap T[1,3]<=(-4) T[2,4]<=(-1) T[5,6]<=5 [].
        Pcase : h[1] > 5.
          Hubcap T[1,3]<=(-2) T[2,4]<=0 T[5,6]<=2 [].
        Pcase : h[6] > 6.
          Hubcap T[1,3]<=(-2) T[2,4]<=0 T[5,6]<=2 [].
        Hubcap T[1,3]<=(-3) T[2,4]<=0 T[5,6]<=3 [].
      Pcase : h[3] <= 5.
        Pcase : h[2] <= 5.
          Hubcap T[1,5]<=(-3) T[4,6]<=(-2) T[2,3]<=5 [].
        Hubcap T[1,5]<=(-2) T[4,6]<=(-2) T[2,3]<=4 [].
      Pcase : h[3] > 6.
        Hubcap T[1,5]<=(-1) T[4,6]<=(-1) T[2,3]<=2 [].
      Pcase : h[2] <= 5.
        Hubcap T[1,5]<=(-2) T[4,6]<=(-1) T[2,3]<=3 [].
      Hubcap T[1,5]<=(-1) T[4,6]<=(-1) T[2,3]<=2 [].
    Pcase : s[3] <= 5.
      Similar to *L2_1[2].
    Pcase : s[5] <= 5.
      Similar to L2_1[3].
    Pcase : s[6] <= 5.
      Similar to *L2_1[5].
    Pcase : h[3] > 6.
      Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
    Pcase : h[3] <= 5.
      Pcase L3_1 : f1[2] <= 5.
        Hubcap T[1,5]<=(-2) T[4,6]<=(-1) T[2,3]<=3 [].
      Pcase : f1[3] <= 5.
        Similar to *L3_1[2].
      Hubcap T[1,5]<=(-1) T[4,6]<=(-1) T[2,3]<=2 [].
    Pcase L2_2 : f1[2] <= 5.
      Pcase : h[2] <= 5.
        Hubcap T[1,5]<=(-2) T[4,6]<=0 T[2,3]<=2 [].
      Hubcap T[1,5]<=(-1) T[4,6]<=0 T[2,3]<=1 [].
    Pcase : f1[3] <= 5.
      Similar to *L2_2[2].
    Pcase L2_3 : f1[2] > 6.
      Pcase : f1[3] > 6.
        Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
      Pcase : h[4] > 5.
        Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
      Hubcap T[1,5]<=0 T[4,6]<=(-1) T[2,3]<=1 [].
    Pcase : f1[3] > 6.
      Similar to *L2_3[2].
    Pcase L2_4 : h[2] <= 5.
      Hubcap T[1,5]<=(-1) T[4,6]<=0 T[2,3]<=1 [].
    Pcase : h[4] <= 5.
      Similar to *L2_4[2].
    Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
  Pcase L1_2 : s[2] > 6.
    Pcase : s[6] > 6.
      Similar to L1_1[5].
    Pcase L2_1 : s[3] <= 5.
      Pcase : s[5] <= 5.
        Reducible.
      Pcase : s[6] <= 5.
        Reducible.
      Pcase : s[4] <= 5.
        Hubcap T[3,5]<=1 T[2,4]<=0 T[1,6]<=(-1) [].
      Hubcap T[3,5]<=1 T[2,4]<=(-1) T[1,6]<=0 [].
    Pcase : s[6] <= 5.
      Similar to *L2_1[4].
    Pcase L2_2 : s[4] <= 5.
      Pcase : s[5] <= 5.
        Hubcap T[1,2]<=(-2) T[3,5]<=1 T[4,6]<=1 [].
      Pcase : h[4] > 5.
        Hubcap T[1,2]<=(-1) T[3,5]<=0 T[4,6]<=1 [].
      Hubcap T[4,2]<=1 T[3,5]<=0 T[1,6]<=(-1) [].
    Pcase : s[5] <= 5.
      Similar to *L2_2[4].
    Pcase L2_3 : h[4] > 6.
      Pcase : h[5] > 6.
        Hubcap T[1,5]<=0 T[2,3]<=0 T[4,6]<=0 [].
      Pcase : h[5] <= 5.
        Pcase : f1[4] > 5.
          Hubcap T[1,5]<=1 T[2,3]<=(-1) T[4,6]<=0 [].
        Hubcap T[1,5]<=2 T[2,3]<=(-2) T[4,6]<=0 [].
      Pcase : f1[4] <= 5.
        Hubcap T[1,5]<=1 T[2,3]<=(-1) T[4,6]<=0 [].
      Hubcap T[1,5]<=0 T[2,3]<=0 T[4,6]<=0 [].
    Pcase : h[6] > 6.
      Similar to *L2_3[4].
    Pcase : h[5] > 6.
      Pcase : h[4] <= 5.
        Pcase : f1[3] <= 5.
          Hubcap T[1,5]<=(-1) T[4,6]<=2 T[2,3]<=(-1) [].
        Pcase : f1[4] <= 5.
          Hubcap T[1,5]<=(-2) T[4,6]<=1 T[2,3]<=1 [].
        Hubcap T[1,5]<=(-1) T[4,6]<=1 T[2,3]<=0 [].
      Pcase : f1[3] <= 5.
        Pcase : h[3] <= 5.
          Hubcap T[1,5]<=0 T[4,6]<=2 T[2,3]<=(-2) [].
        Hubcap T[1,5]<=0 T[4,6]<=1 T[2,3]<=(-1) [].
      Pcase : f1[4] <= 5.
        Hubcap T[1,5]<=(-1) T[4,6]<=0 T[2,3]<=1 [].
      Pcase : f1[3] > 6.
        Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
      Pcase : h[3] <= 5.
        Hubcap T[1,5]<=0 T[4,6]<=1 T[2,3]<=(-1) [].
      Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
    Pcase L2_4 : h[6] <= 5.
      Pcase : h[4] <= 5.
        Reducible.
      Pcase : f1[3] <= 5.
        Pcase : h[3] <= 5.
          Hubcap T[1,5]<=0 T[4,6]<=2 T[2,3]<=(-2) [].
        Hubcap T[1,5]<=0 T[4,6]<=1 T[2,3]<=(-1) [].
      Pcase : f1[3] > 6.
        Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
      Pcase : h[3] <= 5.
        Hubcap T[1,5]<=0 T[4,6]<=1 T[2,3]<=(-1) [].
      Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
    Pcase : h[4] <= 5.
      Similar to *L2_4[4].
    Pcase L2_5 : f1[4] > 6.
      Pcase : h[5] > 5.
        Pcase : f1[3] > 6.
          Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
        Pcase : f1[3] > 5.
          Pcase : h[3] > 5.
            Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
          Hubcap T[1,5]<=0 T[4,6]<=1 T[2,3]<=(-1) [].
        Pcase : h[3] > 5.
          Hubcap T[1,5]<=0 T[4,6]<=1 T[2,3]<=(-1) [].
        Hubcap T[1,5]<=0 T[4,6]<=2 T[2,3]<=(-2) [].
      Pcase : f1[3] > 6.
        Hubcap T[1,5]<=1 T[4,6]<=0 T[2,3]<=(-1) [].
      Pcase : f1[3] > 5.
        Pcase : h[3] > 5.
          Hubcap T[1,5]<=1 T[4,6]<=0 T[2,3]<=(-1) [].
        Hubcap T[1,5]<=1 T[4,6]<=1 T[2,3]<=(-2) [].
      Pcase : h[3] > 5.
        Hubcap T[1,5]<=1 T[4,6]<=1 T[2,3]<=(-2) [].
      Hubcap T[1,5]<=1 T[4,6]<=2 T[2,3]<=(-3) [].
    Pcase : f1[5] > 6.
      Similar to *L2_5[4].
    Pcase : f1[3] > 6.
      Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
    Pcase : f1[3] > 5.
      Pcase : h[3] > 5.
        Hubcap T[1,5]<=0 T[4,6]<=0 T[2,3]<=0 [].
      Hubcap T[1,5]<=0 T[4,6]<=1 T[2,3]<=(-1) [].
    Pcase : h[3] > 5.
      Hubcap T[1,5]<=0 T[4,6]<=1 T[2,3]<=(-1) [].
    Hubcap T[1,5]<=0 T[4,6]<=2 T[2,3]<=(-2) [].
  Pcase : s[6] > 6.
    Similar to *L1_2[5].
  Pcase L1_3 : s[2] <= 5.
    Pcase : s[4] <= 5.
      Reducible.
    Pcase : s[5] <= 5.
      Reducible.
    Pcase : s[6] <= 5.
      Reducible.
    Pcase : h[6] <= 5.
      Reducible.
    Pcase : s[3] <= 5.
      Hubcap T[1,3]<=0 T[2,4]<=1 T[5,6]<=(-1) [].
    Pcase : h[6] > 6.
      Hubcap T[1,3]<=(-1) T[2,4]<=1 T[5,6]<=0 [].
    Pcase : f1[5] <= 5.
      Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
    Pcase : f1[6] > 6.
      Hubcap T[1,3]<=(-1) T[2,4]<=1 T[5,6]<=0 [].
    Pcase : f1[6] <= 5.
      Reducible.
    Pcase : h[1] > 5.
      Hubcap T[1,3]<=(-1) T[2,4]<=1 T[5,6]<=0 [].
    Hubcap T[1,3]<=(-2) T[2,4]<=1 T[5,6]<=1 [].
  Pcase : s[6] <= 5.
    Similar to *L1_3[5].
  Pcase L1_4 : s[3] <= 5.
    Pcase : s[5] <= 5.
      Reducible.
    Pcase : s[4] <= 5.
      Hubcap T[1,6]<=(-2) T[2,4]<=1 T[3,5]<=1 [].
    Pcase : h[3] > 6.
      Hubcap T[1,6]<=(-1) T[2,4]<=0 T[3,5]<=1 [].
    Hubcap T[1,3]<=1 T[2,4]<=0 T[5,6]<=(-1) [].
  Pcase : s[5] <= 5.
    Similar to *L1_4[5].
  Pcase : s[4] <= 5.
    Pcase : h[4] > 6.
      Hubcap T[1,2]<=(-1) T[3,5]<=0 T[4,6]<=1 [].
    Hubcap T[1,6]<=(-1) T[2,4]<=1 T[3,5]<=0 [].
  Pcase L1_5 : h[3] <= 5.
    Pcase : h[6] <= 5.
      Hubcap T[1,3]<=(-1) T[2,4]<=(-1) T[5,6]<=2 [].
    Pcase : h[6] > 6.
      Pcase : h[5] <= 5.
        Reducible.
      Pcase : h[5] > 6.
        Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
      Pcase : f1[5] <= 5.
        Hubcap T[1,3]<=0 T[2,4]<=1 T[5,6]<=(-1) [].
      Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
    Pcase : f1[6] <= 5.
      Reducible.
    Pcase : f1[6] > 6.
      Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
    Pcase : h[1] > 5.
      Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
    Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
  Pcase : h[6] <= 5.
    Similar to *L1_5[5].
  Pcase L1_6 : h[4] <= 5.
    Pcase : f1[3] <= 5.
      Pcase : f1[4] <= 5.
        Hubcap T[1,5]<=(-2) T[2,3]<=0 T[4,6]<=2 [].
      Hubcap T[1,5]<=(-1) T[2,3]<=(-1) T[4,6]<=2 [].
    Pcase : f1[4] <= 5.
      Pcase : h[3] > 6.
        Hubcap T[1,5]<=(-2) T[2,3]<=1 T[4,6]<=1 [].
      Pcase : f1[2] <= 5.
        Reducible.
      Pcase : f1[2] > 6.
        Hubcap T[1,5]<=(-2) T[2,3]<=1 T[4,6]<=1 [].
      Pcase : h[2] > 5.
        Hubcap T[1,5]<=(-2) T[2,3]<=1 T[4,6]<=1 [].
      Hubcap T[1,5]<=(-3) T[2,3]<=2 T[4,6]<=1 [].
    Pcase : h[3] > 6.
      Hubcap T[1,5]<=(-1) T[2,3]<=0 T[4,6]<=1 [].
    Pcase : f1[2] <= 5.
      Reducible.
    Pcase : f1[2] > 6.
      Hubcap T[1,5]<=(-1) T[2,3]<=0 T[4,6]<=1 [].
    Pcase : h[2] > 5.
      Hubcap T[1,5]<=(-1) T[2,3]<=0 T[4,6]<=1 [].
    Hubcap T[1,5]<=(-2) T[2,3]<=1 T[4,6]<=1 [].
  Pcase : h[5] <= 5.
    Similar to *L1_6[5].
  Pcase L1_7 : h[4] > 6.
    Pcase : h[5] > 6.
      Pcase L3_1 : h[3] > 6.
        Hubcap T[1,5]<=0 T[2,3]<=0 T[4,6]<=0 [].
      Pcase : h[6] > 6.
        Similar to *L3_1[5].
      Pcase : f1[5] <= 5.
        Hubcap T[1,3]<=0 T[2,4]<=(-1) T[5,6]<=1 [].
      Pcase : f1[6] > 6.
        Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
      Pcase : f1[6] <= 5.
        Pcase : h[1] <= 5.
          Hubcap T[1,3]<=(-2) T[2,4]<=0 T[5,6]<=2 [].
        Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
      Pcase : h[1] <= 5.
        Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
      Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
    Pcase : h[6] > 6.
      Pcase : f1[4] > 5.
        Pcase : f1[5] > 5.
          Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
        Hubcap T[1,3]<=0 T[2,4]<=1 T[5,6]<=(-1) [].
      Pcase : f1[5] > 5.
        Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
      Hubcap T[1,3]<=(-1) T[2,4]<=1 T[5,6]<=0 [].
    Pcase : f1[4] <= 5.
      Pcase : f1[6] <= 5.
        Hubcap T[1,3]<=(-2) T[2,4]<=0 T[5,6]<=2 [].
      Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
    Pcase : f1[6] > 6.
      Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
    Pcase : f1[6] <= 5.
      Pcase : h[1] <= 5.
        Hubcap T[1,3]<=(-2) T[2,4]<=0 T[5,6]<=2 [].
      Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
    Pcase : h[1] <= 5.
      Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
    Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
  Pcase : h[5] > 6.
    Similar to *L1_7[5].
  Pcase L1_8 : h[6] > 6.
    Pcase : f1[5] > 5.
      Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
    Hubcap T[1,3]<=0 T[2,4]<=1 T[5,6]<=(-1) [].
  Pcase : h[3] > 6.
    Similar to *L1_8[5].
  Pcase : f1[6] > 6.
    Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
  Pcase : f1[6] <= 5.
    Pcase : h[1] <= 5.
      Hubcap T[1,3]<=(-2) T[2,4]<=0 T[5,6]<=2 [].
    Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
  Pcase : h[1] <= 5.
    Hubcap T[1,3]<=(-1) T[2,4]<=0 T[5,6]<=1 [].
  Hubcap T[1,3]<=0 T[2,4]<=0 T[5,6]<=0 [].
Pcase : s[2] > 6.
  Similar to L0_1[1].
Pcase : s[3] > 6.
  Similar to L0_1[2].
Pcase : s[4] > 6.
  Similar to L0_1[3].
Pcase : s[5] > 6.
  Similar to L0_1[4].
Pcase : s[6] > 6.
  Similar to L0_1[5].
Pcase : s[1] <= 5.
  Reducible.
Pcase : s[2] <= 5.
  Reducible.
Pcase : s[3] <= 5.
  Reducible.
Pcase : s[4] <= 5.
  Reducible.
Pcase : s[5] <= 5.
  Reducible.
Pcase : s[6] <= 5.
  Reducible.
Pcase L0_2 : h[1] > 6.
  Pcase L1_1 : h[3] > 6.
    Pcase : h[5] > 6.
      Pcase L3_1 : h[2] > 6.
        Pcase : h[6] > 6.
          Hubcap T[1,6]<=0 T[2,4]<=0 T[3,5]<=0 [].
        Pcase : h[6] <= 5.
          Pcase : f1[5] <= 5.
            Hubcap T[1,6]<=1 T[2,4]<=(-2) T[3,5]<=1 [].
          Pcase : f1[6] <= 5.
            Hubcap T[1,6]<=(-1) T[2,4]<=(-1) T[3,5]<=2 [].
          Hubcap T[1,6]<=0 T[2,4]<=(-1) T[3,5]<=1 [].
        Pcase : f1[5] <= 5.
          Hubcap T[1,6]<=1 T[2,4]<=(-1) T[3,5]<=0 [].
        Pcase : f1[6] <= 5.
          Hubcap T[1,6]<=(-1) T[2,4]<=0 T[3,5]<=1 [].
        Hubcap T[1,6]<=0 T[2,4]<=0 T[3,5]<=0 [].
      Pcase : h[6] > 6.
        Similar to *L3_1[0].
      Pcase L3_2 : h[2] <= 5.
        Pcase : f1[1] <= 5.
          Pcase : f1[5] <= 5.
            Hubcap T[1,6]<=0 T[2,4]<=1 T[3,5]<=(-1) [].
          Pcase : f1[6] <= 5.
            Hubcap T[1,6]<=(-2) T[2,4]<=2 T[3,5]<=0 [].
          Hubcap T[1,6]<=(-1) T[2,4]<=2 T[3,5]<=(-1) [].
        Pcase : f1[2] <= 5.
          Pcase : f1[5] <= 5.
            Hubcap T[1,6]<=2 T[2,4]<=0 T[3,5]<=(-2) [].
          Pcase : f1[6] <= 5.
            Hubcap T[1,6]<=0 T[2,4]<=1 T[3,5]<=(-1) [].
          Hubcap T[1,6]<=1 T[2,4]<=1 T[3,5]<=(-2) [].
        Pcase : f1[5] <= 5.
          Hubcap T[1,6]<=1 T[2,4]<=0 T[3,5]<=(-1) [].
        Pcase : f1[6] <= 5.
          Hubcap T[1,6]<=(-1) T[2,4]<=1 T[3,5]<=0 [].
        Hubcap T[1,6]<=0 T[2,4]<=1 T[3,5]<=(-1) [].
      Pcase : h[6] <= 5.
        Similar to *L3_2[0].
      Pcase L3_3 : f1[1] <= 5.
        Pcase : f1[5] <= 5.
          Hubcap T[1,6]<=0 T[2,4]<=0 T[3,5]<=0 [].
        Pcase : f1[6] <= 5.
          Hubcap T[1,6]<=(-2) T[2,4]<=1 T[3,5]<=1 [].
        Hubcap T[1,6]<=(-1) T[2,4]<=1 T[3,5]<=0 [].
      Pcase : f1[6] <= 5.
        Similar to *L3_3[0].
      Pcase L3_4 : f1[2] <= 5.
        Pcase : f1[5] <= 5.
          Hubcap T[1,6]<=2 T[2,4]<=(-1) T[3,5]<=(-1) [].
        Hubcap T[1,6]<=1 T[2,4]<=0 T[3,5]<=(-1) [].
      Pcase : f1[5] <= 5.
        Similar to *L3_4[0].
      Hubcap T[1,6]<=0 T[2,4]<=0 T[3,5]<=0 [].
    Pcase L2_1 : h[4] > 6.
      Pcase : h[6] > 6.
        Pcase : h[5] <= 5.
          Pcase : f1[5] <= 5.
            Hubcap T[1,3]<=(-1) T[2,6]<=(-2) T[4,5]<=3 [].
          Pcase : f1[4] <= 5.
            Hubcap T[1,3]<=(-2) T[2,6]<=(-1) T[4,5]<=3 [].
          Hubcap T[1,3]<=(-1) T[2,6]<=(-1) T[4,5]<=2 [].
        Pcase : f1[5] <= 5.
          Hubcap T[1,3]<=0 T[2,6]<=(-1) T[4,5]<=1 [].
        Pcase : f1[4] <= 5.
          Hubcap T[1,3]<=(-1) T[2,6]<=0 T[4,5]<=1 [].
        Hubcap T[1,3]<=0 T[2,6]<=0 T[4,5]<=0 [].
      Pcase : h[5] <= 5.
        Pcase : f1[4] <= 5.
          Pcase : f1[6] <= 5.
            Hubcap T[1,3]<=(-3) T[2,6]<=(-1) T[4,5]<=4 [].
          Hubcap T[1,3]<=(-2) T[2,6]<=(-1) T[4,5]<=3 [].
        Pcase : f1[6] <= 5.
          Hubcap T[1,3]<=(-2) T[2,6]<=(-1) T[4,5]<=3 [].
        Hubcap T[1,3]<=(-1) T[2,6]<=(-1) T[4,5]<=2 [].
      Pcase : h[6] <= 5.
        Pcase : f1[4] <= 5.
          Pcase : f1[6] <= 5.
            Hubcap T[1,3]<=(-3) T[2,6]<=1 T[4,5]<=2 [].
          Hubcap T[1,3]<=(-2) T[2,6]<=1 T[4,5]<=1 [].
        Pcase : f1[6] <= 5.
          Hubcap T[1,3]<=(-2) T[2,6]<=1 T[4,5]<=1 [].
        Hubcap T[1,3]<=(-1) T[2,6]<=1 T[4,5]<=0 [].
      Pcase : f1[4] <= 5.
        Pcase : f1[6] <= 5.
          Hubcap T[1,3]<=(-2) T[2,6]<=0 T[4,5]<=2 [].
        Hubcap T[1,3]<=(-1) T[2,6]<=0 T[4,5]<=1 [].
      Pcase : f1[6] <= 5.
        Hubcap T[1,3]<=(-1) T[2,6]<=0 T[4,5]<=1 [].
      Hubcap T[1,3]<=0 T[2,6]<=0 T[4,5]<=0 [].
    Pcase : h[6] > 6.
      Similar to *L2_1[4].
    Pcase L2_2 : h[4] <= 5.
      Pcase : f1[3] <= 5.
        Pcase : f1[6] <= 5.
          Hubcap T[1,3]<=0 T[2,6]<=(-2) T[4,5]<=2 [].
        Hubcap T[1,3]<=1 T[2,6]<=(-2) T[4,5]<=1 [].
      Pcase : f1[6] <= 5.
        Hubcap T[1,3]<=0 T[2,6]<=(-1) T[4,5]<=1 [].
      Hubcap T[1,3]<=1 T[2,6]<=(-1) T[4,5]<=0 [].
    Pcase : h[6] <= 5.
      Similar to *L2_2[4].
    Pcase L2_3 : f1[3] <= 5.
      Pcase : f1[6] <= 5.
        Hubcap T[1,3]<=(-1) T[2,6]<=(-1) T[4,5]<=2 [].
      Pcase : h[5] <= 5.
        Hubcap T[1,3]<=(-1) T[2,6]<=(-2) T[4,5]<=3 [].
      Hubcap T[1,3]<=0 T[2,6]<=(-1) T[4,5]<=1 [].
    Pcase : f1[6] <= 5.
      Similar to *L2_3[4].
    Pcase : h[5] <= 5.
      Hubcap T[1,3]<=(-1) T[2,6]<=(-1) T[4,5]<=2 [].
    Hubcap T[1,3]<=0 T[2,6]<=0 T[4,5]<=0 [].
  Pcase : h[5] > 6.
    Similar to L1_1[4].
  Pcase L1_2 : h[2] > 6.
    Pcase : h[4] > 6.
      Similar to L1_1[1].
    Pcase : h[6] > 6.
      Similar to L1_1[5].
    Pcase L3_1 : h[3] <= 5.
      Pcase : f1[2] <= 5.
        Hubcap T[1,5]<=(-2) T[2,3]<=3 T[4,6]<=(-1) [].
      Hubcap T[1,5]<=(-1) T[2,3]<=2 T[4,6]<=(-1) [].
    Pcase : h[6] <= 5.
      Similar to *L3_1[5].
    Pcase L3_2 : f1[2] <= 5.
      Pcase : f1[6] <= 5.
        Hubcap T[1,6]<=(-2) T[2,4]<=0 T[3,5]<=2 [].
      Pcase : h[5] <= 5.
        Hubcap T[1,6]<=(-2) T[2,4]<=1 T[3,5]<=1 [].
      Hubcap T[1,6]<=(-1) T[2,4]<=0 T[3,5]<=1 [].
    Pcase : f1[6] <= 5.
      Similar to *L3_2[5].
    Pcase : h[5] <= 5.
      Hubcap T[1,6]<=(-1) T[2,4]<=1 T[3,5]<=0 [].
    Hubcap T[1,6]<=0 T[2,4]<=0 T[3,5]<=0 [].
  Pcase : h[6] > 6.
    Similar to *L1_2[0].
  Pcase L1_3 : h[2] <= 5.
    Pcase : h[5] <= 5.
      Hubcap T[1,6]<=(-1) T[2,4]<=2 T[3,5]<=(-1) [].
    Pcase : f1[1] <= 5.
      Hubcap T[1,6]<=(-1) T[2,4]<=2 T[3,5]<=(-1) [].
    Hubcap T[1,6]<=0 T[2,4]<=1 T[3,5]<=(-1) [].
  Pcase : h[6] <= 5.
    Similar to *L1_3[0].
  Pcase L1_4 : h[3] <= 5.
    Hubcap T[1,6]<=(-1) T[2,4]<=0 T[3,5]<=1 [].
  Pcase : h[5] <= 5.
    Similar to *L1_4[0].
  Pcase L1_5 : f1[1] <= 5.
    Pcase : f1[6] <= 5.
      Hubcap T[1,6]<=(-2) T[2,4]<=1 T[3,5]<=1 [].
    Hubcap T[1,6]<=(-1) T[2,4]<=1 T[3,5]<=0 [].
  Pcase : f1[6] <= 5.
    Similar to *L1_5[0].
  Hubcap T[1,6]<=0 T[2,4]<=0 T[3,5]<=0 [].
Pcase : h[2] > 6.
  Similar to L0_2[1].
Pcase : h[3] > 6.
  Similar to L0_2[2].
Pcase : h[4] > 6.
  Similar to L0_2[3].
Pcase : h[5] > 6.
  Similar to L0_2[4].
Pcase : h[6] > 6.
  Similar to L0_2[5].
Pcase L0_3 : h[1] <= 5.
  Hubcap T[1,6]<=2 T[2,4]<=(-1) T[3,5]<=(-1) [].
Pcase : h[2] <= 5.
  Similar to L0_3[1].
Pcase : h[3] <= 5.
  Similar to L0_3[2].
Pcase : h[4] <= 5.
  Similar to L0_3[3].
Pcase : h[5] <= 5.
  Similar to L0_3[4].
Pcase : h[6] <= 5.
  Similar to L0_3[5].
Hubcap T[1,6]<=0 T[2,4]<=0 T[3,5]<=0 [].
Qed.

Set Strict Implicit.
Unset Implicit Arguments.