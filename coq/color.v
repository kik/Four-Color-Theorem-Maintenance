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

(* The four colors, with color sum (xor) and comparison.                    *)

Inductive color : Set := Color0 | Color1 | Color2 | Color3.

Notation "'palette' c0 c1 c2 c3" := (fun c =>
     match c with Color0 => c0 | Color1 => c1 | Color2 => c2 | Color3 => c3 end)
  (at level 10, c0, c1, c2, c3 at level 9).

(* Color comparison and sum; sum is used to compute traces, so it is taken *)
(* as primitive.                                                           *)

Definition addc : color -> color -> color :=
  palette (fun c => c)
          (palette Color1 Color0 Color3 Color2)
          (palette Color2 Color3 Color0 Color1)
          (palette Color3 Color2 Color1 Color0).

Notation "c1 '+c' c2" := (addc c1 c2) (at level 50).

Definition eqc (c c' : color) : bool :=
  if c +c c' is Color0 then true else false.

(* Properties of equality, and canonical dataSet.                       *)

Lemma eqcPx : reflect_eq eqc.
Proof. by do 2 case; constructor. Qed.

Canonical Structure colorData := DataSet eqcPx.

Notation eqcP := (eqcPx _ _).

Lemma eqcE : eqc = set1.
Proof. done. Qed.

(* Algebraic properties of addc *)

Lemma addcA : forall c1 c2 c3, c1 +c (c2 +c c3) = c1 +c c2 +c c3.
Proof. by do 3 case. Qed.

Lemma addcC : forall c1 c2, c1 +c c2 = c2 +c c1.
Proof. by do 2 case. Qed.

Lemma add0c : forall c, Color0 +c c = c.
Proof. by case. Qed.

Lemma addc0 : forall c, c +c Color0 = c.
Proof. by case. Qed.

Lemma addcc : forall c, c +c c = Color0.
Proof. by case. Qed.

Lemma addc_inv : forall c1 c2, c1 +c (c1 +c c2) = c2.
Proof. by do 2 case. Qed.

Lemma inj_addc : forall c, injective (addc c).
Proof. exact (fun c => monic_inj (addc_inv c)). Qed.

Lemma iso_addc : forall c, iso (addc c).
Proof. move=> c; exists (addc c); exact (addc_inv c). Qed.

Lemma eq_addc0 : forall c1 c2, (c1 =d c2) = (c1 +c c2 =d Color0).
Proof. by do 2 case. Qed.

(* Colors as bit vectors *)

Definition cbit0 := palette false true false true.

Definition cbit1 := palette false false true true.

Definition ccons b1 b0 := match b1, b0 with
  | false, false => Color0
  | false, true => Color1
  | true, false => Color2
  | true, true => Color3
  end.

(* Bit properties. *)

Lemma ccons_cbits : forall c, ccons (cbit1 c) (cbit0 c) = c.
Proof. by case. Qed.

Lemma cbit1_ccons : forall b1 b0, cbit1 (ccons b1 b0) = b1.
Proof. by do 2 case. Qed.

Lemma cbit0_ccons : forall b1 b0, cbit0 (ccons b1 b0) = b0.
Proof. by do 2 case. Qed.

Lemma cbit1_addc : forall c c', cbit1 (c +c c') = cbit1 c +b cbit1 c'.
Proof. by do 2 case. Qed.

Lemma cbit0_addc : forall c c', cbit0 (c +c c') = cbit0 c +b cbit0 c'.
Proof. by do 2 case. Qed.

(* The six "edge" permutations that leave Color0 unchanged. *)

Inductive edge_perm : Set :=
  | Eperm123 : edge_perm
  | Eperm132 : edge_perm
  | Eperm213 : edge_perm
  | Eperm231 : edge_perm
  | Eperm312 : edge_perm
  | Eperm321 : edge_perm.

Definition permc g :=
  match g with
  | Eperm123 => fun c => c
  | Eperm132 => palette Color0 Color1 Color3 Color2
  | Eperm213 => palette Color0 Color2 Color1 Color3
  | Eperm231 => palette Color0 Color2 Color3 Color1
  | Eperm312 => palette Color0 Color3 Color1 Color2
  | Eperm321 => palette Color0 Color3 Color2 Color1
  end.

Coercion permc : edge_perm >-> Funclass.

Definition inv_eperm g :=
  match g with
  | Eperm312 => Eperm231
  | Eperm231 => Eperm312
  | _ => g
  end.

Lemma inv_eperm_I : forall g, inv_eperm (inv_eperm g) = g.
Proof. by case. Qed.

Lemma inv_permc : forall g : edge_perm, monic g (inv_eperm g).
Proof. by do 2 case. Qed.

Lemma permc_inv : forall g, monic (inv_eperm g) g.
Proof. by do 2 case. Qed.

Lemma permc_inj : forall g : edge_perm, injective g.
Proof. move=> g; exact (monic_inj (inv_permc g)). Qed.

Lemma iso_permc : forall g : edge_perm, iso g.
Proof.
move=> g; exists (permc (inv_eperm g)); [ apply inv_permc | apply permc_inv ].
Qed.

Lemma permc_addc : forall (g : edge_perm) c1 c2, g (c1 +c c2) = g c1 +c g c2.
Proof. by do 3 case. Qed.

Lemma permc0 : forall g : edge_perm, g Color0 = Color0.
Proof. by case. Qed.

Lemma color_iso_permc : forall f, iso f -> f Color0 = Color0 ->
  exists g : edge_perm, f =1 g.
Proof.
move=> f Hf Ef0; have Hf0 := iso_eqd Hf Color0; rewrite Ef0 in Hf0.
case Ef1: (f Color1) (iso_eqd Hf Color1) (Hf0 Color1); move=> Hf1 // _;
 case Ef2: (f Color2) {Hf}(iso_eqd Hf Color2) (Hf0 Color2) (Hf1 Color2);
 move=> Hf2 // _ _;
 [ exists Eperm123 | exists Eperm132 | exists Eperm213
 | exists Eperm231 | exists Eperm312 | exists Eperm321 ]; case=> {Ef0 Ef1 Ef2}//;
 by case: {Hf0 Hf1 Hf2}(f Color3) (Hf0 Color3) (Hf1 Color3) (Hf2 Color3).
Qed.

Lemma other_colors : forall c, negb (c =d Color0) ->
  set4 Color0 c (Eperm312 c) (Eperm231 c) =1 colorData.
Proof. by case=> //; clear; case. Qed.

(* Basic operations on edge traces = pairwise sums of the list of colors on  *)
(* a configuration perimeter. Many of these operations use permutations of   *)
(* the non-zero colors, so we introduce an explicit enumeration of these six *)
(* permutations. A ``proper'' trace, one that begins with a non-zero color,  *)
(* has a ``normal'' tail, obtained by applying the rotation that sends the   *)
(* first color to Color1 to the rest of the trace. A trace is even if Color3 *)
(* does not occur before Color2 in its tail. To cut our work in half, we     *)
(* only consider even traces in our algorithm, as the match relation is      *)
(* invariant under swapping Color2 and Color3. The coloring function outputs *)
(* directly the even trace tail of colorings, so we prove here that this is  *)
(* invariant under permutations of the coloring.                             *)
(*   Allowing Color0 in traces allows us to carry fewer side conditions in   *)
(* our lemmas, and gives us a convenient ``bad'' value as well.              *)
(*   Finally, we define a completion operation that Adds the last ``cyclic'' *)
(* sum to a a trace, and prove its basic properties. These will be used with *)
(* the ``canonical'' match relation.                                         *)

(* Boolean correctness predicate *)

Definition colseq : Set := seq colorData.

Definition head_color : colseq -> color := head Color0.

Definition proper_trace et := negb (head_color et =d Color0).

(* Conversion from color lists to traces is done in two steps: compute the   *)
(* pairwise sum to get a partial (linear) trace, then append the last color  *)
(* which can be computed as the sum of the partial trace, to get a full      *)
(* (cyclic) trace. The trace computation inverse just computes partial sums. *)

Definition ptrace (lc : colseq) : colseq :=
  if lc is Adds c lc' then pairmap addc c lc' else seq0.

Definition permt (g : edge_perm) : colseq -> colseq := maps g.

Definition sumt : colseq -> color := foldr addc Color0.

Definition ctrace (et : colseq) : colseq := add_last et (sumt et).

Definition trace (lc : colseq) : colseq :=
  if lc is Adds _ _ then ctrace (ptrace lc) else seq0.

Definition urtrace (lc : colseq) : colseq := pairmap addc (last Color0 lc) lc.

Definition untrace c0 (et : colseq) : colseq := scanl addc c0 (belast Color0 et).

(* Trace normalization. *)

Definition edge_rot := palette Eperm123 Eperm123 Eperm312 Eperm231.

Definition ttail (et : colseq) : colseq :=
  if proper_trace et then
    if et is Adds c et' then permt (edge_rot c) et' else seq0
  else seq1 Color0.

Definition even_tail : colseq -> bool :=
  foldr (fun c b => palette b b true false c) true.

Definition even_trace et := even_tail (ttail et).

Definition etrace_perm et := if even_trace et then Eperm123 else Eperm132.

Definition etrace et := permt (etrace_perm et) et.

Definition etail et := permt (etrace_perm et) (ttail et).

Definition eptrace lc := etail (ptrace lc).

(* Counting cbit1, used to validate the initial tree construction.  *)

Definition count_cbit1 : colseq -> nat := foldr (fun c => addn (cbit1 c)) 0.

(* Lemmas for edge permutations : the standard iso lemmas, and commutation *)
(* with addc (proved by brute force).                                      *)

(* Trace permutation. *)

Lemma permt_id : forall et, permt Eperm123 et = et.
Proof. move=> et; unfold permt; exact (maps_id _). Qed.

Lemma etrace_id : forall et, permt Eperm132 (permt Eperm132 et) = et.
Proof. exact (monic_maps (inv_permc Eperm132)). Qed.

Lemma eqc0_permc : forall (g : edge_perm) c, (g c =d Color0) = (c =d Color0).
Proof. by move=> g c; case g; case c. Qed.

Lemma memc0_permt : forall g et, permt g et Color0 = et Color0.
Proof.
by move=> g et; elim: et => [|e et Hrec] //=; rewrite /setU1 Hrec eqc0_permc.
Qed.

Lemma proper_permt : forall g et, proper_trace (permt g et) = proper_trace et.
Proof. by case; case=> //; case. Qed.

Lemma memc0_ttail : forall et,
  ttail et Color0 = negb (proper_trace et) || et Color0.
Proof.
move=> et; rewrite /ttail; case Het: (proper_trace et) => //.
by case: et Het => //=; case=> *; rewrite /= ?memc0_permt; auto.
Qed.

(* Even and tail permutations. *)

Lemma even_etail : forall et, even_tail (etail et).
Proof.
move=> et; rewrite /etail /etrace_perm.
case Het: (even_trace et) => /=; first by rewrite permt_id.
by move: Het; rewrite /even_trace; elim: (ttail et) => //; case=> /= *; auto.
Qed.

Lemma ttail_etrace : forall et, ttail (etrace et) = etail et.
Proof.
move=> et; rewrite /etail /etrace /etrace_perm /ttail.
case (even_trace et); rewrite /= ?permt_id // proper_permt.
case Het: (proper_trace et) => //=; case: et Het => //.
by case=> // *; rewrite /ttail /permt /= -2!maps_comp; apply: eq_maps; case.
Qed.

Lemma even_etrace : forall et, even_trace (etrace et).
Proof. by move=> et; rewrite /even_trace ttail_etrace even_etail. Qed.

Lemma compose_permt : forall g g' et, exists h, permt h et = permt g (permt g' et).
Proof.
move=> g g' et; rewrite /permt; case (@color_iso_permc (comp g g')).
- by apply iso_comp; apply iso_permc.
- by rewrite /comp !permc0.
move=> h Eh; exists h; rewrite -maps_comp; apply: eq_maps; move; auto.
Qed.

Lemma etail_perm : forall et, proper_trace et ->
  exists g, permt g et = Adds Color1 (etail et).
Proof.
move=> et; rewrite -ttail_etrace /ttail /etrace.
move: (etrace_perm et) => h; rewrite -(proper_permt h); move=> Het; rewrite Het.
case Dhet: (permt h et) Het => [|e het'] // Het.
have [g Eg] := (compose_permt (edge_rot e) h et); exists g.
by rewrite {}Eg {}Dhet; case: e Het.
Qed.

Lemma etail_permt : forall g et, etail (permt g et) = etail et.
Proof.
move=> g et; case Het: (proper_trace et);
 last by rewrite /etail /ttail proper_permt Het /= 2!permc0.
move/etail_perm: Het (Het) => [h Eh].
rewrite -(proper_permt g); case/etail_perm.
move=> h'; case: (compose_permt h' g et) => [g' <-] {h'}.
rewrite {1}(monic_move (monic_maps (inv_permc h)) Eh) -Eh.
case: (compose_permt g' (inv_eperm h) (permt h et)).
rewrite {4}/permt; move=> g'' <- {g'}; rewrite {h}Eh /=; case=> Eg''1 Eg''.
move: Eg'' (even_etail et) (even_etail (permt g et)) => <-.
case: g'' Eg''1 => // _; first by move=> *; apply: permt_id.
elim: (etail et) => //; case=> //= *; congr Adds; auto.
Qed.

(* Perimeter-trace equations. *)

Lemma ptrace_addc : forall c (lc : colseq), ptrace (maps (addc c) lc) = ptrace lc.
Proof.
move=> c [|c' lc]; rewrite /ptrace //=.
elim: lc c' => [|c'' lc Hrec] c' //=.
by rewrite (addcC c) -addcA addc_inv Hrec.
Qed.

Lemma ptrace_permt : forall g lc, ptrace (permt g lc) = permt g (ptrace lc).
Proof.
move=> g [|c lc]; rewrite /ptrace //=.
by elim: lc c => [|c' lc Hrec] c //=; rewrite Hrec permc_addc.
Qed.

Lemma eptrace_iso : forall lc f, iso f -> eptrace (maps f lc) = eptrace lc.
Proof.
move=> lc f Hf; rewrite /eptrace -(ptrace_addc (f Color0)) -maps_comp.
case (@color_iso_permc (comp (addc (f Color0)) f)).
- by apply iso_comp; trivial; apply iso_addc.
- exact (addcc (f Color0)).
move=> g Eg; rewrite (eq_maps Eg) -/(permt g) ptrace_permt; apply etail_permt.
Qed.

(* Properties of the trace completion. *)

Lemma sumt_ctrace : forall et, sumt (ctrace et) = Color0.
Proof.
move=> et; rewrite /ctrace -(add0c (sumt et)).
elim: et Color0 => [|e et Hrec] c; first by rewrite /= 2!addc0.
rewrite add_last_adds /= addcA (addcC c e) Hrec; apply addc_inv.
Qed.

Lemma memc0_ctrace : forall et,
  ctrace et Color0 = (sumt et =d Color0) || et Color0.
Proof. by move=> et; rewrite /ctrace -cats1 mem_cat /setU mem_seq1 orbC. Qed.

Lemma proper_ctrace : forall et, proper_trace (ctrace et) = proper_trace et.
Proof. by case=> //; case. Qed.

Lemma sumt_permt : forall g et, sumt (permt g et) = g (sumt et).
Proof.
move=> g; elim=> [|e et Hrec]; first by exact (esym (permc0 g)).
by rewrite /= permc_addc Hrec.
Qed.

Lemma ctrace_permt : forall g et, ctrace (permt g et) = permt g (ctrace et).
Proof.
move=> g et; rewrite /ctrace sumt_permt /=.
by elim: et (sumt et) => [|e et Hrec] c //=; rewrite Hrec.
Qed.

Lemma even_ctrace : forall et, even_trace (ctrace et) = even_trace et.
Proof.
move=> [|e et] //=; rewrite /ctrace /even_trace /ttail /proper_trace /=.
case: (e =d Color0) => //=; move Dg: (edge_rot e) => g.
have He: cbit1 (g e) = false by rewrite -Dg; case e.
elim: et e He {Dg} => [|e' et Hrec] e /=; first by rewrite addc0; case (g e).
move=> He; case Dge': (g e');
  by rewrite //= addcA Hrec // permc_addc cbit1_addc He Dge'.
Qed.

Lemma ctrace_inj : injective ctrace.
Proof.
move=> et0 et0'; rewrite /ctrace.
elim: {-2}et0 {-2}et0' => [|c et Hrec]; first by move=> [|c [|c' et']].
move=> [|c' et'] /=; first by case et.
by case=> <- Eetr; congr Adds; auto.
Qed.

(* Properties of the full (cyclic) trace. *)

Lemma trace_permt : forall g lc, trace (permt g lc) = permt g (trace lc).
Proof. by move=> g [|c lc] //; rewrite /trace -ctrace_permt -ptrace_permt. Qed.

Lemma size_trace : forall lc, size (trace lc) = size lc.
Proof.
by case=> // *; rewrite /trace /ctrace /ptrace /= size_add_last size_pairmap.
Qed.

Lemma trace_untrace : forall c0 et, sumt et = Color0 -> trace (untrace c0 et) = et.
Proof.
move=> c0 [|e1 et] // Het; rewrite /untrace /= /ptrace /=.
rewrite (pairmap_scanl (f := addc) addc_inv) /ctrace lastI; congr add_last.
rewrite -[last e1 et]add0c -{}Het.
elim: et e1 => [|e2 et Hrec] e1 /=; rewrite -addcA ?addcc //.
by rewrite Hrec //= addcc.
Qed.

Lemma sumt_trace : forall lc, sumt (trace lc) = Color0.
Proof. by move=> [|c lc]; rewrite /trace ?sumt_ctrace. Qed.

Lemma untrace_trace : forall c0 lc, untrace c0 (trace (Adds c0 lc)) = Adds c0 lc.
Proof.
move=> c0 lc; rewrite /= /untrace /ctrace belast_add_last /= addc0.
congr Adds; apply: (scanl_pairmap addc_inv).
Qed.

Lemma trace_addc : forall c lc, trace (maps (addc c) lc) = trace lc.
Proof. move=> c [|c0 lc] //; congr ctrace; exact (ptrace_addc _ (Adds _ _)). Qed.

Lemma trace_adds : forall c lc, trace (Adds c lc) = pairmap addc c (add_last lc c).
Proof.
move=> c0 lc; rewrite /trace /ptrace /ctrace /= -(addc_inv c0 (sumt _)) /=.
elim: lc {-2 6}c0 => [|c2 lc Hrec] c1 /=; first by rewrite addc0 addcC.
by congr Adds; rewrite -!addcA !addc_inv.
Qed.

Lemma trace_add_last : forall c (lc : colseq),
 trace (add_last lc c) =
   if trace (Adds c lc) is Adds e et then add_last et e else lc.
Proof.
move=> c0 [|c1 lc]; rewrite // [trace]lock /= -lock !trace_adds /=.
by elim: lc {1 3}c1 => [|c3 lc Hrec] c2 /=; congr Adds.
Qed.

Lemma urtrace_trace : forall lc : colseq, urtrace (rot 1 lc) = trace lc.
Proof.
move=> [|x [|y p]]; rewrite // /urtrace /rot /= ?addcc // last_cat /=.
rewrite -(cat1s x) cats0 /ctrace -cats1 /= -addcA; congr Adds.
elim: p y => [|z p Hrec] y /=; first by rewrite addc0 addcC.
by rewrite -!addcA addc_inv Hrec.
Qed.

Lemma urtrace_rot : forall lc : colseq, urtrace (rot 1 lc) = rot 1 (urtrace lc).
Proof.
move=> [|x [|y p]] //; rewrite /urtrace /rot /= last_cat /=; congr Adds.
by rewrite -!cat1s !cats0; elim: p y => [|z p Hrec] y //=; rewrite Hrec.
Qed.

Lemma trace_rot : forall  n (lc : colseq), trace (rot n lc) = rot n (trace lc).
Proof.
move=> n lc; elim: n => [|n Hrec]; first by rewrite !rot0.
case: (ltnP n (size lc)) => [Hn|Hn].
  by rewrite -add1n !rot_addn ?size_trace // -Hrec -!urtrace_trace -urtrace_rot.
by rewrite !rot_oversize ?size_trace // ltnW.
Qed.

Lemma trace_rev : forall lc : colseq, trace (rev lc) = rot 1 (rev (trace lc)).
Proof.
move=> [|c0 lc] //; rewrite -!urtrace_trace !urtrace_rot; congr rot.
elim/last_ind: lc => [|lc c Hrec] //; move/(congr1 behead): Hrec.
case/lastP: lc => [|lc c']; first by rewrite /urtrace /= (addcC c).
rewrite -!add_last_adds !rev_add_last -2!rot1_adds !urtrace_rot -urtrace_rot.
repeat rewrite /urtrace !rot1_adds /=; rewrite !rev_add_last /=; move<-.
by rewrite rev_adds !last_add_last !(addcC c).
Qed.

Unset Implicit Arguments.
