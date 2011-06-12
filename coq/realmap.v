(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import Arith.
Require Import real.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section RealMap.

Variable R : real_structure.

(* Elementary set theory for the plane. *)

Inductive point : Type := Point (x y : R).

Definition region : Type := point -> Prop.

Identity Coercion mem_region : region >-> Funclass.

Definition union (r1 r2 : region) : region := fun z => r1 z \/ r2 z.

Definition intersect (r1 r2 : region) : region := fun z => r1 z /\ r2 z.

Definition nonempty (r : region) := exists z, r z.

Definition subregion (r1 r2 : region) := forall z, r1 z -> r2 z.

Definition meet (r1 r2 : region) := nonempty (intersect r1 r2).

(* Maps are represented as relations; proper maps are partial equivalence *)
(* relations (PERs).                                                      *)

Definition map : Type := point -> region.

Identity Coercion mem_map : map >-> Funclass.

Definition inmap (m : map) : region := fun z => m z z.

Definition covers (m m' : map) := forall z, subregion (m z) (m' z).

Definition size_at_most n m :=
  exists f, forall z, inmap m z -> exists2 i, i < n & m (f i) z.

Record proper_map (m : map) : Prop := ProperMap {
  map_sym : forall z1 z2, m z1 z2 -> m z2 z1;
  map_trans : forall z1 z2, m z1 z2 -> subregion (m z2) (m z1)
}.

(* Elementary geometry. *)

Inductive interval : Type := Interval (x0 x1 : R).

Definition mem_interval x01 y :=
  let: Interval x0 x1 := x01 in ltr x0 y /\ ltr y x1.

Coercion mem_interval : interval >-> Funclass.

Inductive rect : Type := Rect (xint yint : interval).

Definition mem_rect r : region :=
  fun z => let: Rect xint yint := r in let: Point x y := z in xint x /\ yint y.

Coercion mem_rect : rect >-> region.

(* Elementary topology. *)

Definition open (r : region) :=
  forall z, r z -> exists2 rr : rect, rr z & subregion rr r.

Definition closure r : region :=
  fun z => forall r', open r' -> r' z -> meet r r'.

Definition connected r :=
  forall r1 r2,
    subregion r (union r1 r2) ->
    meet r1 r -> meet r2 r ->
    open r1 -> open r2 ->
  meet r1 r2.

Record simple_map (m : map) : Prop := SimpleMap {
  simple_map_proper :> proper_map m;
  map_open : forall z, open (m z);
  map_connected : forall z, connected (m z)
}.

Record finite_simple_map (m : map) : Prop := FiniteSimpleMap {
  finite_simple_map_base :> simple_map m;
  finite_simple_map_size : exists n, size_at_most n m
}.

(* Borders, corners, adjacency and coloring. *)

Definition border (m : map) z1 z2 :=
  intersect (closure (m z1)) (closure (m z2)).

Definition corner_map m z : map := fun z1 z2 => m z1 z2 /\ closure (m z1) z.

Definition not_corner m z := size_at_most 2 (corner_map m z).

Definition adjacent m z1 z2 := meet (not_corner m) (border m z1 z2).

Record coloring (m k : map) : Prop := Coloring {
  coloring_proper :> proper_map k;
  coloring_inmap : subregion (inmap k) (inmap m);
  coloring_covers : covers m k;
  coloring_adj : forall z1 z2, k z1 z2 -> adjacent m z1 z2 -> m z1 z2
}.

Definition map_colorable n m := exists2 k, coloring m k & size_at_most n k.

End RealMap.

Set Strict Implicit.
Unset Implicit Arguments.