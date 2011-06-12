(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(***********************************************************************)
(*  The library real syntax, adapted to setoid reals                   *)
(***********************************************************************)

Require Import real.

(***********************************************************************)
(* There are several differences with the library syntax:              *)
(*    - the math priorities are strictly adhered to:                   *)
(*      unary `-` binds tightest                                       *)
(*     '/' binds strictly tighter than '*', and does not associate     *)
(*     '*' binds tighter than `+` and binary `-`, and associates left  *)
(*     '+' and binary '-' have equal priorities, and associate left    *)
(*     `=` `<>` `<` `>` `<=` `>=` have the lowest priority and don't   *)
(*      associate. The double comparison syntax is not supported.      *)
(*    - the syntax for the sup function is                             *)
(*          sup E or sup {x | P(x)} where P(x) can be a comparison,    *)
(*          e.g., sup {x | x * x <= 2}                                 *)
(*    - <, >=, <, <>, /, and binary - are all strictly sugar, and are  *)
(*      expanded at parse time, e.g., x < y means ~(y <= x).           *)
(*    - the syntax for the inverse of x is 1/x. "1 divided by x" is    *)
(*      printed as its expansion, 1 * 1/x.                             *)
(*    - small integer constants (up to 10) are expanded at parse time, *)
(*      but larger ones are kept as calls to natr. This means that     *)
(*      x + 11 will print as x + (natr R [11]) (in a structure R);     *)
(*      it will print as x + 11 after a Simpl or an Eval.              *)
(*    - One can specify the structure interpreting integer constants,  *)
(*      e.g., 1%R means (real1 R).                                     *)
(*    - The syntax for escaping back to Gallina, [term1 ... termn]     *)
(*      is systematically used for calls with explicit arguments and   *)
(*      for integer constants (as in the call (natr R [11]) above).    *)
(*    - The pretty-printer doesn't generate useless brackets, e.g.,    *)
(*      around function arguments, and puts space around the operators *)
(*      (except in atomic fractions such as 3/4, 1/x, or -x/2).        *)
(***********************************************************************)

Bind Scope real_scope with real_carrier.
Delimit Scope real_scope with R.
Delimit Scope realset_scope with Rset.

Arguments Scope leqr [_ real_scope real_scope].
Arguments Scope supr [_ realset_scope].
Arguments Scope addr [_ real_scope real_scope].
Arguments Scope oppr [_ real_scope].
Arguments Scope mulr [_ real_scope real_scope].
Arguments Scope invr [_ real_scope].
Arguments Scope eqr [_ real_scope real_scope].
Arguments Scope supr [_ realset_scope].
Arguments Scope ubr [_ realset_scope real_scope].
Arguments Scope has_supr [_ realset_scope].
Arguments Scope boundedr [_ real_scope realset_scope].

Notation "0" := O : nat_scope.
Notation "1" := (S 0) : nat_scope.
Notation "2" := (S 1) : nat_scope.
Notation "3" := (S 2) : nat_scope.
Notation "4" := (S 3) : nat_scope.
Notation "5" := (S 4) : nat_scope.
Notation "6" := (S 5) : nat_scope.
Notation "7" := (S 6) : nat_scope.
Notation "8" := (S 7) : nat_scope.
Notation "9" := (S 8) : nat_scope.
Notation "'10'" := (S 9) : nat_scope.

Notation "{ x | P }" := (fun x : (real_carrier _) => (P : Prop))
  (at level 0, x ident, P at level 200, format "{ x  |  P }") : realset_scope.

Notation "x <= y" := (leqr x y) : real_scope.
Notation "x >= y" := (y <= x)%R (only parsing) : real_scope.
Notation sup := (@supr _).
Notation "x + y" := (addr x y) : real_scope.
Notation "0" := (@real0 _) : real_scope.
Notation "- y" := (oppr y) : real_scope.
Notation "x - y" := (x + - y)%R : real_scope.
Notation "x * y" := (mulr x y) : real_scope.
Notation "1" := (@real1 _) : real_scope.
Notation "/ y" := (invr y) : real_scope.
Notation "x / y" := (x * / y)%R : real_scope.

Notation "x == y" := (eqr x y) (at level 70) : real_scope.
Notation "x != y" := (~(x == y)%R) (at level 70) : real_scope.
Notation "x < y" := (~(x >= y)%R) : real_scope.
Notation "x > y" := (y < x)%R (only parsing) : real_scope.
Notation "x == y == z" := ((x = y)%R /\ (y = z)%R)
   (at level 70, y at next level) : real_scope.
Notation "x <= y <= z" := ((x <= y)%R /\ (y <= z)%R) : real_scope.
Notation "x < y <= z" := (~(y <= x)%R /\ (y <= z)%R) : real_scope.
Notation "x <= y < z" := ((x <= y)%R /\ ~(z <= y)%R) : real_scope.
Notation "x < y < z" := ((x < y)%R /\ (y < z)%R) : real_scope.

Notation "2" := ((1 + 1)%R) : real_scope.
Notation "3" := ((1 + 2)%R) : real_scope.
Notation "4" := ((1 + 3)%R) : real_scope.
Notation "5" := ((1 + 4)%R) : real_scope.
Notation "6" := ((1 + 5)%R) : real_scope.
Notation "7" := ((1 + 6)%R) : real_scope.
Notation "8" := ((1 + 7)%R) : real_scope.
Notation "9" := ((1 + 8)%R) : real_scope.
Notation "10":= ((1 + 9)%R) : real_scope.

