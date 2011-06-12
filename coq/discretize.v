(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import paths.
Require Import hypermap.
Require Import geometry.
Require Import coloring.
Require Import znat.
Require Import grid.
Require Import matte.
Require Import gridmap.
Require Import real.
Require Import realmap.
Require Import realprop.
Require Import approx.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section DiscretizeMap.

(* Discretizing the coloring problem for an arbitrary finite map. We compute *)
(* a finite hypermap whose colorings induce colorings of the map, using the  *)
(* grid computation package.                                                 *)
(* The discrete approximation is constructed in five steps :                 *)
(* 1) enumerate the regions and adjacencies of m0, choosing a representative *)
(*    border point for each adjacency;                                       *)
(* 2) construct disjoint rectangles covering the border points;              *)
(* 3) construct approximations of the border rectangles;                     *)
(* 4) construct matte approximations of the regions that meet all the        *)
(*    corresponding border rectangles;                                       *)
(* 5) construct a hypermap from the mattes using the grid package.           *)

Variable R : real_model.

Notation point := (point R).
Notation region := (region R).
Notation map := (map R).
Notation rect := (rect R).
Notation interval := (interval R).

Let Hclassical : excluded_middle := reals_classic R.

Variable m0 : map.
Hypothesis Hm0 : finite_simple_map m0.

Definition map_repr : Type := nat -> nat -> point.
Definition adj_repr : Type := nat -> nat -> rect.

Definition adj_point z1 z2 z :=
  adjacent m0 z1 z2 -> intersect (not_corner m0) (border m0 z1 z2) z.

Definition proper_map_repr (mr : map_repr) n :=
    (forall i, i < n -> inmap m0 (mr i i))
 /\ (forall i j, i < j -> j < n ->
      ~ m0 (mr i i) (mr j j) /\ adj_point (mr i i) (mr j j) (mr i j)).

Definition cover_map_repr (mr : map_repr) n :=
  subregion (inmap m0) (fun z => exists2 i, i < n & m0 z (mr i i)).

Lemma exists_map_repr : exists n, exists2 mr,
  proper_map_repr mr n & cover_map_repr mr n.
Proof.
move: Hm0 => [_ [n0 Hmn0]]; pose n1 := S n0.
case: (Hclassical (exists mr, proper_map_repr mr n1)).
  move: Hmn0 => [f Hf] [mr [Hmr Imr]].
  have [s Ls Ds]: exists2 s, size s = n1
     & forall i, i < n1 -> let j := sub 0 s i in j < n0 /\ m0 (f j) (mr i i).
  - elim: n1 mr Hmr {Imr} => [|n Hrec] mr Hmr; first by exists (seq0 : natseq).
    case: {Hrec}(Hrec (fun i j => mr (S i) (S j))) ltnW => [|s Ls Hs]; auto.
    case: (Hf (mr 0 0)) => [|j Hjn0 Hjf _]; auto.
    exists (Adds j s); first by rewrite /= Ls.
    by move=> [|i]; [ split; first by apply/ltP | apply: Hs ].
  clear Hf Hmr; have Us: uniq s.
    rewrite -[s]take_size; move: (leqnn (size s)).
    elim: {-2}(size s) => [|n Hrec] Hn; first by rewrite take0.
    rewrite (take_sub 0 Hn) uniq_add_last {}Hrec 1?ltnW // andbT.
    apply/(subPx 0 _ _); rewrite size_take Hn; move=> [i Hi Ei].
    rewrite Ls in Hn; case: (Imr _ _ Hi Hn); case.
    case: (Ds _ Hn) => [_]; rewrite -Ei sub_take //; apply: (map_trans Hm0).
    by apply (map_sym Hm0); case: (Ds _ (ltn_trans Hi Hn)).
  have [s' Ls' Ds']: exists2 s', size s' = n0 & s' =1 (fun i => i < n0).
    exists (traject S 0 n0); first by rewrite size_traject.
    have EitS: forall i, iter i S 0 = i by elim=> //= *; congr S.
    by move=> i; apply/trajectP/idP => [[i' Hi' <-]|]; [ rewrite EitS | exists i ].
  case/idP: (ltnn n0); rewrite -/n1 -Ls -Ls'; apply: uniq_leq_size => // i.
  by rewrite Ds'; move/(subPx 0)=> [j Hj <-]; rewrite Ls in Hj; case: (Ds _ Hj).
elim: {n0 Hmn0}n1 => [|n Hrec] Hn.
  by case: Hn; exists (fun i j : nat => scale_point R 0 Gb00); split.
case: (Hclassical (exists mr, proper_map_repr mr n)); auto.
move=> [mr Hmr]; exists n; exists mr; move=> //= z Hz.
case: (Hclassical (exists2 i, i < n & m0 z (mr i i))) => // Hmrz.
suffice [f Hf]: exists f, forall i, i < n -> adj_point (mr i i) z (f i).
  case: Hn; case: Hmr => [Dmr Hmr].
  exists (fun i j => if j < n then mr i j else if i < j then f i else z).
  split; first by move=> i _; case Hi: (i < n); auto; rewrite ltnn.
  move=> i j Hi; rewrite ltnS leq_eqVlt orbC !ltnn Hi.
  case Hj: (j < n); first by rewrite (ltn_trans Hi Hj); auto.
  move/(j =P n)=> Dj; rewrite Dj in Hi; rewrite Hi; split; auto.
  by move=> Hiz; case Hmrz; exists i; last exact: (map_sym Hm0).
elim: n {Hrec Hn Hmr Hz Hmrz} => [|n [f Hf]].
  by exists (fun i : nat => scale_point R 0 Gb00).
case: (Hclassical (adjacent m0 (mr n n) z)) => Hn.
  case: Hn => [t Ht]; exists (fun i => if i < n then f i else t).
  move=> i; rewrite ltnS leq_eqVlt orbC; case Hi: (i < n); auto.
  by move/(i =P n)=> Di; rewrite Di; move.
exists f; move=> i; rewrite ltnS leq_eqVlt orbC; case Hi: (i < n); auto.
by move/(i =P n)=> Di; rewrite Di; move=> *; case Hn.
Qed.

Section AdjRepr.

Variables (nr : nat) (mr : map_repr).
Hypothesis Hmr : proper_map_repr mr nr.

Definition proper_adj_repr_at (ar : adj_repr) i j :=
  and4 (nonempty (ar i j) -> adjacent m0 (mr i i) (mr j j))
       (adjacent m0 (mr i i) (mr j j) -> ar i j (mr i j))
       (forall i', i' < nr -> meet (m0 (mr i' i')) (ar i j) -> set2 i j i')
       (forall i' j', meet (ar i j) (ar i' j') -> i = i' /\ j = j').

Lemma exists_proper_adj_repr : exists ar,
  forall i j, regpair nr i j -> proper_adj_repr_at ar i j.
Proof.
pose ltp i j i' j' := if j =d j' then i < i' else regpair j' i j.
have Eltp0: forall i j j', ltp i j 0 (S j') = ltp i j j' j'.
  move=> i j j'; rewrite /ltp /regpair ltnS (leq_eqVlt j).
  case: (j =P S j') => [Dj|_].
    by rewrite eqn_leq (ltn_neqAle j) Dj ltnn !andbF.
  by case: (j =P j') => // <-; rewrite andbT.
have EltpS: forall i j i' j',
    ltp i j (S i') j' = (i =d i') && (j =d j') || ltp i j i' j'.
  by move=> i j i' j'; rewrite andbC /ltp ltnS (leq_eqVlt i); case: (j =d j').
pose patp ar i' j' := forall i j : nat,
  if ltp i j i' j' then proper_adj_repr_at ar i j else ~ nonempty (ar i j).
suffice [ar Har]: exists ar, patp ar 0 nr.
  exists ar => i j Hij; move: (Har i j); rewrite /ltp Hij.
  by case: (j =P nr) => // Dj; rewrite Dj /regpair ltnn andbF in Hij.
elim: {-2}nr (leqnn nr) => [|j' Hrec] Hj'.
  pose r0 := real0 R; pose int0 := Interval r0 r0.
  exists (fun i j : nat => Rect int0 int0) => i j.
  by rewrite /ltp /regpair andbF if_same; move=> [[x y] [[Hx []]]]; exact: ltrW.
suffice [ar Har]: exists ar, patp ar j' j'.
  exists ar => i j; rewrite Eltp0; auto; apply: Har.
  elim: {1 3}j' (leqnn j') => [|i' Hrec'] Hi'; first by apply Hrec; exact:ltnW.
  case: {Hrec Hrec'}(Hrec' (ltnW Hi')) => [ar Har].
  case: (Hclassical (adjacent m0 (mr i' i') (mr j' j'))) => Ha.
    move: Hmr => [Emr Amr]; case: (Amr _ _ Hi' Hj').
    set zi' := mr i' i'; set zj' := mr j' j'; set zij' := mr i' j'.
  move=> _ H; move: {H}(H Ha) => [Hcij' [Hbi' Hbj']].
  have [rr Err Hrr]: exists2 rr : rect, rr zij'
      & forall i, i < nr -> meet (m0 (mr i i)) rr -> set2 i' j' i.
    elim: {-2}nr (leqnn nr) => [|i Hrec] Hi.
      by exists (sep_rect zij' zij'); first exact: mem_sep_rect.
    pose zi := mr i i; case: {Hrec}(Hrec (ltnW Hi)) => [rr Err Hrr].
    case: (Hclassical (exists2 rr' : rect, rr' zij' & ~ meet (m0 zi) rr')).
      move=> [rr' Err' Hrr']; have Drr := mem_cap_rect rr rr'.
      exists (cap_rect rr rr'); first by case (Drr zij'); tauto.
      move=> k; rewrite ltnS leq_eqVlt; case/setU1P=> [Dk|Hk].
        rewrite Dk -/zi; move=> [z [Hiz Hz]]; case: Hrr'; exists z.
        case (Drr z); split; tauto.
      move=> [z [Hkz Hz]]; apply Hrr; first done; exists z.
      case (Drr z); split; tauto.
    move=> Hzi; exists rr; first done; move=> k; rewrite ltnS leq_eqVlt.
    case/setU1P; [ move=> -> _ {k rr Err Hrr} | by auto ].
    case: Hcij' => f; set cij' := corner_map m0 zij' => Hf.
    have Hi'n: i' < nr by exact (ltn_trans Hi' Hj').
    have [ii Hii Dii]: exists2 ii, ii < 2 & m0 (f ii) zi'.
      case: (Hf zi'); first by split; auto; exact: Emr.
      by move=> ii Hii [Dii _]; exists ii; first by apply/ltP.
    have [ij Hij Dij]: exists2 ij, ij < 2 & m0 (f ij) zj'.
      case: (Hf zj'); first by split; auto; exact: Emr.
      by move=> ij Hij [Dij _]; exists ij; first by apply/ltP.
    have [ik Hik Dik]: exists2 ik, ik < 2 & m0 (f ik) zi.
      case: (Hf zi).
        split; first by apply: Emr.
        move=> r Hr Hrzij'; case: (Hr _ Hrzij') => [rr Hrr Err].
        case (Hclassical (meet (m0 zi) rr)).
          move=> [t [Hti Ht]]; exists t; split; auto.
        by move=> Hirr; case Hzi; exists rr.
      by move=> ik Hik [Dik _]; exists ik; first by apply/ltP.
    have If: forall i1 i2 j1 j2,
        m0 (f i1) (mr j1 j1) -> m0 (f i2) (mr j2 j2) ->
        j1 < nr -> j2 < nr -> negb (j1 =d j2) -> False \/ negb (i1 =d i2).
    - have If': forall i1 j1 j2,
          j1 < nr -> m0 (f i1) (mr j1 j1) -> m0 (f i1) (mr j2 j2) -> j1 <= j2.
      + move=> i1 j1 j2 Hj1 Hmj1 Hmj2; rewrite leqNgt; apply/idP => Hj2.
        case: (Amr _ _ Hj2 Hj1); case; apply: (map_trans Hm0) Hmj1.
        exact: (map_sym Hm0).
      move=> i1 i2 j1 j2 Hmj1 Hmj2 Hj1 Hj2 Hj12; right; apply/eqP => Di1.
      by rewrite Di1 in Hmj1; rewrite eqn_leq in Hj12; case/andP: Hj12; eauto.
    apply/norP; rewrite ltn_neqAle in Hi'; case/andP: Hi' => [Hi'j' _] [Hi'i Hj'i].
    case: (If _ _ _ _ Dii Dij) => //; case: {Dii}(If _ _ _ _ Dii Dik) => //.
    case: {If Dij Dik}(If _ _ _ _ Dij Dik) => //.
    by case: ii ij ik Hii Hij Hik => [|[|ii]] // [|[|ij]] // [|[|ik]].
  pose ar' i j := cap_rect (ar i j) (sep_rect zij' (mr i j)).
  have [rr' [Err' Drr'] Hrr']: exists2 rr' : rect, rr' zij' /\ subregion rr' rr
      & forall i j, ltp i j j' j' -> meet (ar' i j) rr' -> i = i' /\ j = j'.
    elim: {1 2}j' => [|j'' Hrec].
      exists rr; first by split; move.
      by move=> i j; rewrite /ltp /regpair andbF if_same.
    elim: {1}(S j'') => [|i'' Hreci].
      case: Hrec => [rr' Drr' Hrr']; exists rr'; first done.
      by move=> i j; rewrite Eltp0; auto.
    move: {Hrec}Hreci => [rr' [Err' Drr'] Hrr'].
    have Drr'' := mem_cap_rect rr' (sep_rect (mr i'' (S j'')) zij').
    exists (cap_rect rr' (sep_rect (mr i'' (S j'')) zij')).
      split; last by move=> z; case: (Drr'' z) (Drr' z); tauto.
      by case: (Drr'' zij') (mem_sep_rect (mr i'' (S j'')) zij'); tauto.
    move=> i j Hij [z [Harz Hrrz]]; rewrite EltpS in Hij.
    case: (Drr'' z) => [_ H]; case: {H Hrrz}(H Hrrz) => [Hrrz Hz].
    case/orP: Hij; last by move=> Hij; apply (Hrr' _ _ Hij); exists z; split.
    case/andP; move/eqP=> Di; move/eqP=> Dj.
    have Dar' := mem_cap_rect (ar i j) (sep_rect zij' (mr i j)).
    case: (Dar' z) => [_ H]; case: {H Harz}(H Harz) => [Harz Hz'].
    have Emrij: forall rr : rect, rr (mr i j) -> rr zij'.
      by rewrite -Di -Dj in Hz; apply meet_sep_rect; exists z; split.
    move: (Har i j); case Hij: (ltp i j i' j'); last by case; exists z.
    move=> [Hmrij1 Hmrij2 Harij _]; have Hmrij: ar i j (mr i j).
      by apply Hmrij2; apply Hmrij1; exists z.
    case Hij': (i =d j').
      move: Hij; rewrite (eqP Hij') /ltp; case: (j =P j') => [Dj'|_].
        by rewrite ltnNge ltnW.
      by rewrite /regpair ltn_neqAle leqNgt andbC andbCA andb_neg_b andbF.
    have Dj': j = j'.
      apply: eqP; case: (orP (Harij _ Hj' _)) => //; last by rewrite Hij'.
      rewrite -/zj'; apply: Hbj'; auto.
      by move=> t Ht; exists (ar i j); move.
    split; auto; apply: eqP.
    case: (orP (Harij _ (ltn_trans Hi' Hj') _)) => //.
      rewrite -/zi'; apply: Hbi'; auto.
      by move=> t Ht; exists (ar i j); move.
    by move/eqP=> Di'; rewrite -Di' -Dj' ltnn in Hi'.
  exists (fun i j => if (i =d i') && (j =d j') then rr' else ar' i j).
  move=> i j; rewrite EltpS /proper_adj_repr_at.
  case Dij: ((i =d i') && (j =d j')).
    case/andP: Dij; move/eqP=> Di; move/eqP=> Dj; rewrite {i}Di {j}Dj.
    split; auto.
      move=> i Hi [z [Hiz Hrrz]]; apply (Hrr _ Hi); exists z; split; auto.
      move=> i j; case Dij: ((i =d i') && (j =d j')).
      by case/andP: Dij; split; symmetry; apply: eqP.
    move=> [z [Hrrz Harz]]; case (Hrr' i j); try by try exists z; split.
    have Dar' := mem_cap_rect (ar i j) (sep_rect zij' (mr i j)).
    case: (Dar' z) => [_ H]; case: {H Harz}(H Harz) => [Harz _].
    case Hij: (ltp i j i' j') (Har i j); last by case; exists z.
    clear; move: Hij; rewrite /ltp; case: (j =d j') => // Hi.
    exact (ltn_trans Hi Hi').
  have Dar' := mem_cap_rect (ar i j) (sep_rect zij' (mr i j)).
  case Hij: (ltp i j i' j') (Har i j) {Dij} => //.
    move=> [Hmrij1 Hmrij2 Harij Iarij]; split.
    - by move=> [z Hz]; apply Hmrij1; exists z; case: (Dar' z); tauto.
    - by move/Hmrij2; case: (Dar' (mr i j)) (mem_sep_rect zij' (mr i j)); tauto.
    - move=> k Hk [z [Hkz Hz]]; apply (Harij _ Hk); exists z; case (Dar' z).
      by split; tauto.
    - move=> i'' j''; case Dij'': ((i'' =d i') && (j'' =d j')).
      case/andP: Dij''; do 2 move/eqP=> ->; apply: Hrr'.
      move: Hij; rewrite /ltp; case: (j =d j') => // Hi.
      exact (ltn_trans Hi Hi').
    move=> [z [Hiz Hi''z]]; apply Iarij; exists z.
    split; first by case (Dar' z); tauto.
    by case (mem_cap_rect (ar i'' j'') (sep_rect zij' (mr i'' j'')) z); tauto.
  move=> H [z Hz]; case: H; case (Dar' z); exists z; tauto.
exists ar; move=> i j; rewrite EltpS.
case Dij: ((i =d i') && (j =d j')) (Har i j) => //.
case/andP: Dij; do 2 move/eqP=> ->; clear i j.
rewrite /ltp set11 ltnn /=; move=> Harij'; split.
- by move=> *; case Harij'.
- by move=> *; case Ha.
- by move=> i _ [z [_ Hz]]; case: Harij'; exists z.
by move=> i j [z [Hz _]]; case: Harij'; exists z.
Qed.

Section DiscrAdj.

Variable ar : adj_repr.
Hypothesis Har : forall i j, regpair nr i j -> proper_adj_repr_at ar i j.

Definition proper_discr_adj_at s b i j :=
  if garea b =d 0 then ~ adjacent m0 (mr i i) (mr j j) else
  mem_approx s (inset2 b) (mr i j) /\ subregion (mem_approx s b) (ar i j).

Lemma refine_garea0 : forall s b,
  (garea (iter s refine_rect b) =d 0) = (garea b =d 0).
Proof.
move=> s b; rewrite -!leqn0; elim: s => //= [s Hrec].
by rewrite garea_refine_rect -2!double0 !leq_double.
Qed.

Lemma refine_discr_adj : forall s s' b i j, proper_discr_adj_at s' b i j ->
  proper_discr_adj_at (s + s') (iter s refine_rect b) i j.
Proof.
move=> s s' b i j; rewrite /proper_discr_adj_at refine_garea0.
case: (garea b =d 0) => // [] [Hbmr Hbar]; split.
  case: s => //= s; rewrite addSn; apply mem_approx_inset2.
  by apply: mem_approx_inset; apply: sub_mem_approx Hbmr => p; case/andP.
move=> p; case (mem_approx_refine_rect s s' b p); auto.
Qed.

Lemma exists_proper_discr_adj : exists s, exists da,
  forall i j, regpair nr i j -> proper_discr_adj_at s (da i j) i j.
Proof.
pose ltp i j i' j' := if j =d j' then i < i' else regpair j' i j.
have Eltp0: forall i j j', ltp i j 0 (S j') = ltp i j j' j'.
  move=> i j j'; rewrite /ltp /regpair ltnS (leq_eqVlt j).
  case: (j =P S j') => [Dj|_]; last by case: (j =P j') => // [<-]; rewrite andbT.
  by rewrite eqn_leq (ltn_neqAle j) Dj ltnn !andbF.
have EltpS: forall i j i' j',
    ltp i j (S i') j' = (i =d i') && (j =d j') || ltp i j i' j'.
  by move=> i j i' j'; rewrite andbC /ltp ltnS (leq_eqVlt i); case: (j =d j').
pose patp s da i' j' := forall i j,
  if ltp i j i' j' then proper_discr_adj_at s (da i j) i j else
  garea (da i j) =d 0.
suffice [s [da Hda]]: exists s, exists da, patp s da 0 nr.
  exists s; exists da => i j Hij; move: (Hda i j); rewrite /ltp Hij;
  by  case: (j =P nr) => // Dj; rewrite Dj /regpair ltnn andbF in Hij.
elim: {-2}nr (leqnn nr) => [|j' Hrec] Hj'.
  exists 0; exists (fun i j : nat => Grect 1 0 0 0).
  by move=> i j; rewrite /ltp /regpair andbF if_same.
suffice [s [da Hda]]: exists s, exists da, patp s da j' j'.
  exists s; exists da => i j; rewrite Eltp0; auto; exact: Hda.
elim: {1 3}j' (leqnn j') => [|i' Hrec'] Hi'; first by apply Hrec; exact:ltnW.
case: {Hrec Hrec'}(Hrec' (ltnW Hi')) => [s [da Hda]].
have Hij': regpair nr i' j' by apply/andP; split.
case: (Hclassical (adjacent m0 (mr i' i') (mr j' j'))) => Ha.
  case: (Har Hij') => [_ H Harij' Iarij']; move: {H}(H Ha) => Hmrij'.
  case: (approx_rect Hmrij') => [s' [b [p Dp Hbp] Hbar]]; exists (S (s + s')).
  have Hb: proper_discr_adj_at (S s') (refine_rect b) i' j'.
    move: (mem_sub_grect Hbp (gtouch_refl _)).
    rewrite /proper_discr_adj_at garea_refine_rect -size_enum_grect.
    rewrite -mem_enum_grect; case: (enum_grect b) => //= _ _ _; split.
      by apply mem_approx_inset2; exists p.
    by move=> z; case (mem_approx_refine1_rect s' b z); auto.
  exists (fun i j => if (i =d i') && (j =d j') then iter (S s) refine_rect b else
                     iter (S s') refine_rect (da i j)).
  move=> i j /=; rewrite /proper_discr_adj_at EltpS.
  case Dij: ((i =d i') && (j =d j')).
    rewrite /= f_iter -iter_f -addnS; apply: refine_discr_adj.
    by case/andP: Dij; do 2 move/eqP=> ->.
  rewrite /= f_iter -addnS addnC; move: (ltp i j i' j') (Hda i j).
  by case=> *; [ apply: refine_discr_adj | rewrite refine_garea0 ].
exists s; exists da => i j; move: (Hda i j); rewrite EltpS orbC.
case: (ltp i j i' j'); first done.
case Dij: ((i =d i') && (j =d j')); last done.
case/andP: Dij; do 2 move/eqP => ->; move{i j} => Hg0.
by rewrite /proper_discr_adj_at Hg0.
Qed.

Lemma connected_matte : forall z (r : region) s  (m : matte),
    let rm := mem_approx s m in
    r z -> subregion rm r -> open r -> connected r ->
  exists s', exists m' : matte,
  let rm' := mem_approx s' m' in
  and3 (rm' z) (subregion rm rm') (subregion rm' r).
Proof.
move=> z r s m rm Hrz Hrm Hr Cr.
pose r1p t s' m' := let rm' := mem_approx s' m' in
  and3 (rm' t) (subregion rm rm') (subregion rm' r).
pose r1 t := exists s', exists m' : matte, r1p t s' m'.
pose r2 t := r t /\ ~ r1 t.
have Hrr12: subregion r (union r1 r2).
  move=> t Ht; rewrite /union /r2; case: (Hclassical (r1 t)); tauto.
have Hr1r: meet r1 r.
  have [p Hmp]: exists p, m p.
    case: (m) => /= [[|p m'] c H _ _ _] //; exists p; exact: setU11.
  have [t Ht]: exists t, rm t.
    by exists (scale_point R s p); apply: (mem_approx_scale R s m p).
  by exists t; split; auto; exists s; exists m; split; try move.
case: (Hrr12 _ Hrz) => // Hr2z.
have Hr2r: meet r2 r by exists z; split.
pose sbr s' (t : point) := exists2 b,
  mem_approx s' (inset b) t & subregion (mem_approx s' b) r.
have Hr1: open r1.
  move=> t [s1 [m1 [Ht Hmm1 Hm1r]]].
  case: (Hr t (Hm1r _ Ht)) => [rr Hrrt Hrrr].
  case/approx_rect: Hrrt => [s2 [b2 Hb2t Hb2rr]].
  have [s3 Hb3 [m3 Hm3]]: exists2 s3, sbr s3 t & exists m3 : matte, r1p t s3 m3.
    exists (s1 + s2).
      exists (iter s1 refine_rect b2); first by apply mem_approx_inset.
      by move=> u; case (mem_approx_refine_rect s1 s2 b2 u); auto.
    exists (iter s2 refine_matte m1); rewrite addnC.
    split; try by move=> u; case (mem_approx_refine_matte s2 s1 m1 u); auto.
    by case (mem_approx_refine_matte s2 s1 m1 t); auto.
  clear s1 m1 Ht Hmm1 Hm1r rr Hrrr s2 b2 Hb2t Hb2rr.
  have [n Hn]: exists n, mem_approx s3 (fun p => matte_order m3 p <= n) t.
    case: Hb3 => [_ [p Hp _] _]; exists (matte_order m3 p); exists p; auto.
    exact: leqnn.
  elim: n s3 m3 Hn Hm3 Hb3 => [|n Hrec] s' m' [p Dp Hn].
    move: Hn; rewrite leqn0; move/eqP=> Hn Hm' _.
    case: (rect_approx Dp) => [rr Hrrt Hrr]; exists rr; first done.
    case Dmxy: p (matte_order0 Hn) Hrr => [mx my] Hbm' Hrrb.
    move=> u Hu; exists s'; exists m'; split; try by case Hm'.
    by apply sub_mem_approx with (1 := Hbm'); auto.
  move: Hn; rewrite leq_eqVlt; case/setU1P=> [Dn|Hn]; last by apply Hrec; exists p.
  move=> [Hm't Hmm' Hm'r] [b Hbt Hbr].
  case: (approx_point_exists (S s') t) => [p' Dp'].
  have Epp': halfg p' = p by apply: approx_point_inj Dp; apply approx_halfg.
  have Hm'p: m' p by case: Hm't => [q Dq Hq]; rewrite (approx_point_inj Dp Dq).
  have Hbp: inset b p by case: Hbt => [q Dq Hq]; rewrite (approx_point_inj Dp Dq).
  case: (@refine_matte_order m' b p'); rewrite ?Epp' ?Dn //.
  move=> m'' [Hm'm'' Hm''m'] Hn; apply: (Hrec (S s') m''); try by exists p'.
    split; try by exists p'; last by apply: Hm'm''; rewrite Epp'.
      move=> u; move/Hmm'.
      case: (mem_approx_refine1_matte s' m' u) => [_ H]; move/H {H}.
      by apply: sub_mem_approx u => [u]; rewrite mem_refine_matte; auto.
    move=> u [q Dq]; move/(Hm''m' _); case/orP=> Hu.
      by apply Hbr; exists (halfg q); try exact: approx_halfg.
    by apply Hm'r; exists (halfg q); try exact: approx_halfg.
  exists (refine_rect b); first exact: mem_approx_inset1.
  by move=> u; case (mem_approx_refine1_rect s' b u); auto.
have Hr2: open r2.
  move=> t [Hrt Hr1t]; move/Hr: Hrt => [rr Hrrt Hrrr].
  move/approx_rect: Hrrt => [s2 [b2 Hb2t Hb2rr]].
  case: (Hclassical (meet (mem_approx s2 b2) r1)).
    move=> [u [Hb2u [s1 [m1 [Hu Hmm1 Hm1r]]]]]; case: Hr1t.
    have [s' [b' [Hb'u Hb't Hb'r] [m' [Hm'u Hmm' Hm'r] Hm'b']]]:
      exists s', exists2 b' : grect,
        let rb' := mem_approx s' b' in
        and3 (rb' u) (mem_approx s' (inset b') t) (subregion rb' r)
      & exists2 m' : matte, r1p u s' m' & refined_in (m' : set _) b'.
    - exists (s1 + S s2); exists (iter (S s1) refine_rect b2).
        rewrite -addSnnS; split; try by apply mem_approx_inset.
          by case (mem_approx_refine_rect (S s1) s2 b2 u); auto.
        by move=> v; case (mem_approx_refine_rect (S s1) s2 b2 v); auto.
      exists (iter (S s2) refine_matte m1); rewrite 1?addnC.
        split; first [ by case (mem_approx_refine_matte (S s2) s1 m1 u); auto
        | by move=> v; case (mem_approx_refine_matte (S s2) s1 m1 v); auto ].
      exact: refine_matte_refined.
    clear s1 m1 Hu Hmm1 Hm1r rr Hrrr s2 b2 Hb2t Hb2u Hb2rr.
    have Hb'm': has b' m'.
      case: Hb'u Hm'u => [p Dp Hp] [p' Dp' Hp']; apply/hasP; exists p; auto.
      by rewrite (approx_point_inj Dp Dp').
    move: Hb't => [p Dp Hb'p].
    case: (refined_extends_in Hm'b' Hb'm' Hb'p) => [m'' Hm'm'' Hm''m' Hm''p].
    exists s'; exists m''; split; auto; try by exists p.
      by move=> v Hv; apply: sub_mem_approx (mem_extension Hm'm'') _ _; auto.
    move=> v [q Dq]; move/Hm''m'.
    by case/orP=> *; [ apply Hb'r | apply Hm'r ]; exists q.
  move: Hb2t => [p Dp Hp]; case: (rect_approx Dp) => [rr' Hrr't Hrr'b2] Hb2r1.
  exists rr'; auto => u Hu; have Hb2u: mem_approx s2 b2 u.
  apply: sub_mem_approx u {Hu}(Hrr'b2 _ Hu) => [[mx my]] Hu.
    apply: (mem_sub_grect Hp); move: (p) Hu => [mx' my'].
    move/and4P=> [Hx0 Hx1 Hy0 Hy1].
    by rewrite /= Hx0 Hy0 leqz_dec decz_inc Hx1 leqz_dec decz_inc Hy1 !orbT.
  by split; auto; move=> Hr1u; case: Hb2r1; exists u; split.
by case: (Cr _ _ Hrr12 Hr1r Hr2r Hr1 Hr2) => [t [Ht [_ []]]].
Qed.

Section DiscrMatte.

Variables (sab : nat) (ab : adjbox).
Hypothesis
  Hab : forall i j, regpair nr i j -> proper_discr_adj_at sab (ab i j) i j.

Definition ab_pair i j := regpair nr i j && ab_adj ab i j.

Definition ab_region i j : region := mem_approx sab (inset (ab i j)).

Definition proper_discr_matte_at s (m : matte) i nj :=
  let rm := mem_approx s (m : set _) in
  and3 (rm (mr i i)) (subregion rm (m0 (mr i i)))
       (forall j, j < nj -> (ab_pair i j -> meet rm (ab_region i j))
                         /\ (ab_pair j i -> meet rm (ab_region j i))).

Lemma refine_discr_matte : forall s s' m i nj, proper_discr_matte_at s' m i nj ->
  proper_discr_matte_at (s + s') (iter s refine_matte m) i nj.
Proof.
move=> s s' m i nj [Hmi Hmri Hmb]; split;
  try by move=> z; case (mem_approx_refine_matte s s' m z); auto.
- by case (mem_approx_refine_matte s s' m (mr i i)); auto.
have Href: forall r : region, meet (mem_approx s' m) r ->
    meet (mem_approx (s + s') (iter s refine_matte m)) r.
  move=> r [z Hz]; exists z; rewrite /intersect.
  by case (mem_approx_refine_matte s s' m z); case Hz; split; auto.
move=> j Hj; case (Hmb _ Hj); split; auto.
Qed.

Lemma exists_proper_discr_matte : exists s, exists cm,
  forall i, i < nr -> proper_discr_matte_at s (cm i) i nr.
Proof.
have Habp: forall i j, ab_pair i j ->
    let mij k := meet (m0 (mr k k)) (ab_region i j) in mij i /\ mij j.
  move=> i j; move/andP=> [Hij Habij]; rewrite /ab_adj ltnNge leqn0 in Habij.
  move: (Hab Hij); rewrite /proper_discr_adj_at (negbE Habij).
  move=> [Hmrij Harij]; case: (Hmrij) => [pij Dpij Hpij].
  move: (rect_approx Dpij) => [rr Hrrij Hrr].
  have Hrrab: subregion rr (ab_region i j).
    case: pij Hrr Hpij {Dpij} => [x y] Hrr Hpij u Hu.
    apply: sub_mem_approx u {Hu}(Hrr _ Hu) => [[x' y']].
    move/and4P=> [Hx'0 Hx'1 Hy'0 Hy'1]; case/andP: Hpij; case (ab i j).
    move=> x0 x1 y0 y1; move/and4P=> [_ Hx1 _ Hy1]; move/and4P=> [Hx0 _ Hy0 _].
    rewrite -!decz_def in Hx0 Hy0; rewrite /inset /=.
    rewrite -leqz_dec2 in Hx'0; rewrite -leqz_inc2 in Hx'1.
    rewrite -leqz_dec2 in Hy'0; rewrite -leqz_inc2 in Hy'1.
    by apply/and4P; split; eapply leqz_trans; eauto.
  have Hcij: forall k, let rk := m0 (mr k k) in
      closure rk (mr i j) -> meet rk (ab_region i j).
    move=> k rz Hk; case: (Hk rr); auto.
      by move=> t Ht; exists rr; try move.
    by move=> t [Ht Hrrt]; exists t; split; auto.
  have Harij': nonempty (ar i j).
    exists (mr i j); apply Harij; apply: sub_mem_approx Hmrij => p.
    case/andP=> [H _]; apply: {H}(mem_sub_grect H); exact: gtouch_refl.
  case: (Har Hij) => [Haij _ _ _]; case/andP: Hij => [Hi Hj].
  case: Hmr => [_ H]; case: {H}(H _ _ Hi Hj) => [_ Hapij].
  by case: (Hapij (Haij Harij')) => [_ [Hcli Hclj]]; split; auto.
elim: {1 3}nr (leqnn nr) => [|i Hrec] Hi.
  by exists 0; exists (fun i : nat => point_matte Gb00).
suffice: exists s, exists m, proper_discr_matte_at s m i nr.
  move: {Hrex}(Hrec (ltnW Hi)) => [s1 [cm Hcm]] [s2 [m2 Hm2]]; exists (s1 + s2).
  exists (fun i' => if i' =d i then iter s1 refine_matte m2 else
                                    iter s2 refine_matte (cm i')).
    move=> i'; rewrite ltnS leq_eqVlt; case: (i' =P i) => [Di' _|_ Hi'].
    by rewrite Di'; apply: refine_discr_matte.
  by rewrite addnC; apply: refine_discr_matte; auto.
elim: nr {Hrec} => [|j [s [m [Hmi Hmri Hma]]]].
case: Hmr => [H _]; move: {H}(H _ Hi) => Hzi.
case: (map_open Hm0 Hzi) => [rr Hrri Hrrm0].
case: (approx_rect Hrri) => [s [b [p Dp Hbp] Hbrr]]; exists s.
  exists (point_matte p); split; try done.
    by exists p; last by apply: setU11.
  move=> z Hz; apply Hrrm0; apply Hbrr; apply: sub_mem_approx z Hz => q /=.
  case/setU1P=> // [<-]; apply (mem_sub_grect Hbp); exact: gtouch_refl.
have Hmm: forall r1 r2 r3 : region, subregion r1 r2 -> meet r1 r3 -> meet r2 r3.
  by move=> r1 r2 r3 Hr12 [z [Hz1 Hz3]]; exists z; split; auto.
case Hij: (ab_pair i j).
  case: (Habp _ _ Hij) => [[z [Hzi Hzj]] _].
  case: (connected_matte Hzi Hmri ((map_open Hm0) _) ((map_connected Hm0) _)).
  move=> s' [m' [Hm'z Hmm' Hm'ri]]; exists s'; exists m'; split; auto.
  move=> j'; rewrite ltnS leq_eqVlt; case/setU1P=> [Dj'|Hj'].
    rewrite Dj'; split; first by exists z; split; auto.
    case/andP: Hij; case/andP=> [Hij _] _; rewrite /ab_pair /regpair.
    by rewrite ltn_neqAle leqNgt Hij andbF.
  by case: (Hma _ Hj'); split; eauto.
case Hji: (ab_pair j i).
  case: (Habp _ _ Hji) => [_ [z [Hzi Hzj]]].
  case: (connected_matte Hzi Hmri ((map_open Hm0) _) ((map_connected Hm0) _)).
  move=> s' [m' [Hm'z Hmm' Hm'ri]]; exists s'; exists m'; split; auto.
  move=> j'; rewrite ltnS leq_eqVlt; case/setU1P=> [Dj'|Hj'].
    by rewrite Dj' Hij; split; last by exists z; split; auto.
  by case: (Hma _ Hj'); split; eauto.
exists s; exists m; split; auto.
move=> j'; rewrite ltnS leq_eqVlt; case/setU1P=> [Dj'|Hj']; auto.
by rewrite Dj' Hij Hji; split.
Qed.

End DiscrMatte.

End DiscrAdj.

End AdjRepr.

Lemma discretize_to_hypermap : exists2 g,
  planar_bridgeless g & four_colorable g -> map_colorable 4 m0.
Proof.
case: exists_map_repr => [nr [mr Hmr Emr]].
case: (exists_proper_adj_repr Hmr) => [ar Har].
case: (exists_proper_discr_adj Har) => [s1 [ab1 Hab1]].
case: (exists_proper_discr_matte Hmr Har Hab1) => [s2 [cm2 Hcm2]].
pose s := s1 + s2.
pose ab i j := iter s2 refine_rect (ab1 i j).
pose cm i := iter s1 refine_matte (cm2 i).
have Hab0: forall i j, regpair nr i j -> proper_discr_adj_at mr ar s (ab i j) i j.
  by move=> *; rewrite /s addnC; apply: refine_discr_adj; auto.
have Hcm0: forall i, i < nr -> proper_discr_matte_at nr mr s ab s (cm i) i nr.
  have Hrab: (forall (r : realmap.region R) (i j : nat),
              meet r (ab_region s1 ab1 i j) -> meet r (ab_region s ab i j)).
    move=> r i j [u [Hru Hu]]; exists u; split; auto.
    by rewrite /ab_region /s addnC; apply: mem_approx_inset.
  have Eabp: ab_pair nr ab =2 ab_pair nr ab1.
    by move=> i j; rewrite /ab_pair /ab_adj !ltnNge !leqn0 /ab refine_garea0.
  move=> i Hi; apply: refine_discr_matte.
  case: (Hcm2 _ Hi) => [Hcmi Hcmr Hcma]; split; auto.
  by move=> j Hj; rewrite !Eabp; case (Hcma _ Hj); split; auto.
move: {s1 s2}s {ab1 Hab1}ab {cm2 Hcm2}cm => s ab cm in Hab0 Hcm0.
have Hab1: forall i j, regpair nr i j ->
    subregion (mem_approx s (ab i j)) (ar i j).
- move=> i j Hij; move: (Hab0 _ _ Hij); rewrite /proper_discr_adj_at.
  case Dab: (garea (ab i j) =d 0); last by case.
  move=> _ z [p _]; move: Dab; rewrite -size_enum_grect -mem_enum_grect.
  by case (enum_grect (ab i j)).
have Hab: ab_proper nr ab.
  move=> i1 j1 i2 j2 Hij1 Hij2 p Hab1p Hab2p.
  case: (Har _ _ Hij1) => [_ _ _ H]; apply: H; exists (scale_point R s p).
  split; apply: Hab1 => //; exact: mem_approx_scale.
have Hcm: cm_proper nr cm.
  move=> i j Hij; apply/hasP => [[p Hpi Hpj]].
  case/andP: Hij => [Hij Hj]; have Hi := ltn_trans Hij Hj.
  case: Hmr => [_ H]; case: {H}(H _ _ Hij Hj); case.
  case: (Hcm0 _ Hi) (Hcm0 _ Hj) => [_ Hcmi _] [_ Hcmj _].
  apply (map_trans Hm0) with (scale_point R s p);
    [ apply Hcmi | apply (map_sym Hm0); apply Hcmj ]; exact: mem_approx_scale.
have Habcm: ab_cm_proper nr ab cm.
  move=> i j Hij Habij.
  case/andP: Hij (Hij) => [Hij Hj] Hijn; have Hi := ltn_trans Hij Hj.
  have Habi: has (inset (ab i j)) (cm i).
    case: (Hcm0 _ Hi) => [_ _ H]; case: {H}(H _ Hj); case.
      by rewrite /ab_pair Hijn.
    move=> z [[p Dp Hip] [p' Dp' Habp']] _; apply/hasP; exists p; auto.
    by rewrite (approx_point_inj Dp Dp').
  have Habj: has (inset (ab i j)) (cm j).
    case: (Hcm0 _ Hj) => [_ _ H]; case: {H}(H _ Hi); clear; case.
      by rewrite /ab_pair Hijn.
    move=> z [[p Dp Hip] [p' Dp' Habp']]; apply/hasP; exists p; auto.
    by rewrite (approx_point_inj Dp Dp').
  split; auto; move=> k; apply/andP/idP => [[Hk]|Dk].
  move/hasP=> [p Habp Hip]; case: (Har _ _ Hijn) => [_ _ H _]; apply: H => //.
    exists (scale_point R s p); split.
      case: (Hcm0 _ Hk) => [_ Hcmk _]; apply Hcmk; exact: mem_approx_scale.
    apply Hab1; auto; exact: mem_approx_scale.
  suffice: k < nr /\ has (inset (ab i j)) (cm k).
    case; move=> Hk; move/hasP=> [p Hkp Habp]; split; auto.
    apply/hasP; exists p; auto; apply (mem_sub_grect Habp); exact: gtouch_refl.
  by case/orP: Dk; move/eqP=> <-; split.
exists (grid_map Hab Hcm Habcm); first by apply planar_bridgeless_grid_map.
move/grid_map_coloring=> [k0 Ek0 Hk0].
pose k z1 z2 := exists2 i1, i1 < nr /\ m0 (mr i1 i1) z1
              & exists2 i2, i2 < nr /\ m0 (mr i2 i2) z2 & k0 i1 = k0 i2.
have Hm0k: forall z1 z2, m0 z1 z2 ->
    forall i1, i1 < nr /\ m0 (mr i1 i1) z1 ->
    forall i2, i2 < nr /\ m0 (mr i2 i2) z2 -> i1 = i2.
- case: Hmr => [_ Hmr] z1 z2 Hz12 i1 [Hi1 Hiz1] i2 [Hi2 Hiz2].
  have Hm0i12: m0 (mr i1 i1) (mr i2 i2).
    by apply: (map_trans Hm0 (map_trans Hm0 Hiz1 Hz12)); exact: (map_sym Hm0).
  apply: eqP; rewrite eqn_leq; apply/nandP; case; rewrite -ltnNge.
    by move=> Hi21; case: (Hmr _ _ Hi21 Hi1); case; exact: (map_sym Hm0).
  by move=> Hi12; case: (Hmr _ _ Hi12 Hi2); case.
exists k.
  have Hpm0: forall z1 z2, m0 z1 z2 -> inmap m0 z1 /\ inmap m0 z2.
    move=> z1 z2 Hz12; have Hz21 := (map_sym Hm0 Hz12).
    by move: (map_trans Hm0); rewrite /inmap /subregion; split; eauto.
  split.
  - split; move=> z1 z2 [i1 Hiz1 [i2 Hiz2 Hi12]].
      by exists i2; last by exists i1.
    move: (Hiz2) => [_ Hz2] z3 [j2 Hjz2 [i3 Hiz3 Hi23]].
    exists i1; auto; exists i3; auto; rewrite {i1 Hiz1}Hi12 -{i3 Hiz3}Hi23.
    by congr k0; case/(Hpm0 _ _): Hz2 => *; eapply Hm0k; eauto.
  - by move=> z [i [Hi Hiz] _]; case/Hpm0: Hiz.
  - move=> z1 z2 Hz12; case/Hpm0: (Hz12).
    move/Emr=> [i1 Hi1 Hiz1]; move/Emr=> [i2 Hi2 Hiz2].
    exists i1; first by split; last exact: (map_sym Hm0).
    exists i2; first by split; last exact: (map_sym Hm0).
    by congr k0; apply: (Hm0k _ _ Hz12); (split; last exact: (map_sym Hm0)).
  move=> z1 z2 [i1 [Hi1 Hiz1] [i2 [Hi2 Hiz2] Hi12]] Hz12a.
  apply: (map_trans Hm0) (Hiz2); apply (map_sym Hm0); suffice: i1 = i2 by move <-.
  have Hi12a: adjacent m0 (mr i1 i1) (mr i2 i2).
    have Hm0c: forall z z', m0 z z' ->
        subregion (closure (m0 z')) (closure (m0 z)).
    - move=> z z' Hzz' t Ht r Hr Hrt.
      case: (Ht r Hr Hrt) => [u [Hu Hur]]; exists u; split; auto.
      exact: (map_trans Hm0) Hu.
    move: Hz12a => [t [Ht [Ht1 Ht2]]]; rewrite /subregion in Hm0c.
    by exists t; repeat split; eauto.
  clear z1 z2 Hiz1 Hiz2 Hz12a.
  suffice Heq: forall i j, j < nr -> k0 i = k0 j ->
      adjacent m0 (mr i i) (mr j j) -> j <= i.
  - apply: eqP; rewrite eqn_leq; apply/andP; split; auto.
    by apply Heq; auto; case: Hi12a => [z [Hz [Hz1 Hz2]]]; exists z; repeat split.
  clear i1 i2 Hi1 Hi2 Hi12 Hi12a.
  move=> i j Hj Ekij Haij; rewrite leqNgt; apply/idP => Hij.
  have Hijn: regpair nr i j by rewrite /regpair Hij.
  move: (Hab0 _ _ Hijn); rewrite /proper_discr_adj_at -leqn0 leqNgt.
  case Habij: (0 < garea (ab i j)); last by case.
  by case/eqP: (Hk0 _ _ Hijn Habij).
pose ic c := index c (maps k0 (traject S 0 nr)).
exists (fun c => mr (ic c) (ic c)).
have EitS: forall n, iter n S 0 = n by elim=> //= n ->.
move=> z [i [Hi Hiz] _]; exists (k0 i); first by apply: ltP; auto.
have Hk0i: maps k0 (traject S 0 nr) (k0 i).
  by apply maps_f; apply/trajectP; exists i; rewrite ?EitS.
set j := ic (k0 i).
have Hj: j < nr by rewrite -index_mem size_maps size_traject in Hk0i.
exists j; first by case: Hmr => [H _]; split; try exact: H.
exists i; first by split.
by rewrite -(sub_index 0 Hk0i) (sub_maps 0 0) ?size_traject ?sub_traject // EitS.
Qed.

End DiscretizeMap.

Set Strict Implicit.
Unset Implicit Arguments.

