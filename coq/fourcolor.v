(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import Arith.
Require Import real.
Require Import realmap.
Require Import combinatorial4ct.
Require Import discretize.
Require Import finitize.

Section FourColorTheorem.

Variable R : real_model.

Theorem four_color_finite :
  forall m : map R, finite_simple_map m -> map_colorable 4 m.
Proof.
exact (fun m Hm =>
       let: ex_intro2 g Hg Hgm := discretize_to_hypermap Hm in
       Hgm (four_color_hypermap Hg)).
Qed.

Theorem four_color : forall m : map R, simple_map m -> map_colorable 4 m.
Proof.
exact (compactness_extension four_color_finite).
Qed.

End FourColorTheorem.

Set Strict Implicit.
Unset Implicit Arguments.