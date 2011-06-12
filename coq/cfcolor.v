(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import finset.
Require Import paths.
Require Import connect.
Require Import hypermap.
Require Import geometry.
Require Import color.
Require Import coloring.
Require Import cfmap.
Require Import ctree.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Compute the set of colorings of a configuration ring, directly from the   *)
(* contruction program. The algorithm handles the six kinds of steps, as it  *)
(* is also used to color contracts and explicit configurations.              *)

(* First, the optimized all-in-one production of the tree branch, directly   *)
(* from the ring trace.                                                      *)

Section Cpbranch2.

Variable h : color -> ctree -> ctree.

Fixpoint cfcbr2 (et : colseq) : ctree :=
  if et is Adds e et' then h e (cfcbr2 et') else ctree_simple_leaf.

End Cpbranch2.

Definition ctree_cons_perm g :=
  let cte c := ctree_cons_e (g c) in
  palette (cte Color0) (cte Color1) (cte Color2) (cte Color3).

Section Cpbranch1.

Variable g : color -> color.

Fixpoint cfcbr1 (et : colseq) : ctree :=
  if et is Adds e et' then match g e with
  | Color0 => Ctree_empty
  | Color1 => ctree_cons1 (cfcbr1 et')
  | Color2 => ctree_cons2 (cfcbr2 (ctree_cons_perm g) et')
  | Color3 => ctree_cons2 (cfcbr2 (ctree_cons_perm (comp Eperm132 g)) et')
  end else ctree_simple_leaf.

End Cpbranch1.

Definition cpbranch (et : colseq) : ctree :=
  if et is (Seq _  e & et') then
    if e =d Color0 then Ctree_empty else cfcbr1 (edge_rot e) et'
  else Ctree_empty.

(* The coloring procedure uses higher-order programming : we first create a  *)
(* generic iterator over all equivalence classes of colorings of a map given *)
(* by a construction program, then apply it to cpbranch. The iterator is     *)
(* specialized to ctrees, and computes the union of all the trees returned   *)
(* by the function.                                                          *)

Definition cpcolor1 s (f : colseq -> ctree) (et : colseq) :=
  let f2 c et' := f (Seq c c & et') in
  match s, et with
  | CpR n, _ =>
    f (rot n et)
  | CpR', _ =>
    if size et <= 1 then Ctree_empty else f (rotr 1 et)
  | CpU, _ =>
    ctree_union (f2 Color1 et) (ctree_union (f2 Color2 et) (f2 Color3 et))
  | CpK, (Seq e1 e2 & et') =>
    if e1 =d e2 then Ctree_empty else f (Adds (e1 +c e2) et')
  | CpY, (Seq e1 & et') =>
    let e2 := Eperm231 e1 in let e3 := Eperm312 e1 in
    ctree_union (f (Seq e2 e3 & et')) (f (Seq e3 e2 & et'))
  | CpH, (Seq e1 e2 & et') =>
    if e1 =d e2 then ctree_union (f2 (Eperm231 e1) et') (f2 (Eperm312 e1) et')
    else f (Seq e2 e1 & et')
  | CpA, (Seq e1 e2 & et') =>
    if e1 =d e2 then f (if et' is Seq0 then et else et') else Ctree_empty
  | _, _ => Ctree_empty
  end.

(* For the very first steps, we can examine fewer colorings. *)

Fixpoint cpcolor0 (cp : cprog) : ctree :=
  let cpcol := foldr cpcolor1 cpbranch in
  match cp with
  | Adds (CpR _) cp' => cpcolor0 cp'
  | Adds CpY cp' => cpcol cp' (seq3 Color1 Color2 Color3)
  | Adds CpU cp' =>
      ctree_union (cpcol cp' (seq4 Color1 Color1 Color2 Color2))
                  (cpcol cp' (seq4 Color1 Color1 Color1 Color1))
  | _ => cpcol cp (seq2 Color1 Color1)
  end.

Definition cpcolor (cp : cprog) := ctree_cons_rot (cpcolor0 (rev cp)).

(* Basic correctness lemmatas first. *)

Lemma cpbranch_spec : forall et, cpbranch et = ctree_of_ttail (etail (behead et)).
Proof.
move=> [|e0 [|e1 et]] {e0}//=.
rewrite /etail /etrace_perm /even_trace /ttail /proper_trace /head_color /head.
 case: (eqd e1 Color0) => //; move/edge_rot: e1 => g /=.
elim: et => //= [e et Hrec] //=; case/g: e => //=;
  by first [ rewrite -Hrec; case (even_tail (permt g et))
           | congr ctree_cons2; elim: et {Hrec} => //= [e et <-]; case e].
Qed.

(* The main coloring invariant. *)

Section CprogColoringCorrectness.

Variable et0 : colseq.

Section CpcolInvariant.

Variables (cp1 cp2 : cprog) (f : colseq -> ctree) (k : cpmap cp2 -> color).

Definition cp_ht0 := pred (pred (cprsize (catrev cp2 cp1))).

Definition cp_tr0 k0 :=
  ttail et0 = eptrace (rot 1 (maps k0 (cpring (cpmap (catrev cp2 cp1))))).

Inductive cp_extcol : Set :=
  CpExtcol : let et := trace (maps k (cpring (cpmap cp2))) in
    ctree_proper cp_ht0 (f et) ->
    reflect (exists2 k0, coloring k0 /\ cp_tr0 k0 & comp k0 (@injcp cp1 cp2) =1 k)
            (ctree_mem (f et) (ttail et0)) ->
  cp_extcol.

End CpcolInvariant.

Section GlobalColoring.

Variables (cp1 cp2 : cprog) (k0 : cpmap (catrev cp2 cp1) -> color).

Lemma gcol_perm : coloring k0 /\ cp_tr0 k0 -> forall c (h : edge_perm),
 let k x := c +c h (k0 x) in coloring k /\ cp_tr0 k.
Proof.
move=> [Hk0 Ek0] c h k; split.
  apply: (coloring_inj (h := comp (addc c) h)) Hk0 => //.
  apply: inj_comp; [ apply inj_addc | apply permc_inj ].
rewrite /cp_tr0 /eptrace (maps_comp (addc c) (comp h k0)) (maps_comp h k0).
by rewrite -2!maps_rot ptrace_addc -/(permt h) ptrace_permt etail_permt.
Qed.

Lemma gcol_cface : coloring k0 -> forall x y : cpmap cp2, cface x y -> 
  let k z := k0 (injcp cp1 z) in k x = k y.
Proof.
move=> [_ Hk0F] x y Hxy k; apply: (fconnect_invariant Hk0F).
by apply sub_cface_injcp.
Qed.

Lemma gcol_adj : coloring k0 -> forall x p, adj x =1 fband p ->
  let k (x : cpmap cp2) := k0 (injcp cp1 x) in
  all (fun y => negb (k y =d k x)) p.
Proof.
move=> [Hk0E Hk0F] x p Dp /=; apply/allP => [y Hy]; apply/negPf.
have Hxy: (adj x y) by rewrite Dp (subsetP (ring_fband p)).
case/adjP: (sub_adj_injcp cp1 Hxy) => [u Hxu Huy].
rewrite (fconnect_invariant Hk0F Hxu) -(fconnect_invariant Hk0F Huy); apply: Hk0E.
Qed.

End GlobalColoring.

Section TraceCpring.

Variables (g : hypermap) (x0 : g) (k : g -> color).
Hypothesis Hk : coloring k.
Let et : colseq := trace (maps k (cpring x0)).

Lemma memc0_trace_cpring : et Color0 = false.
Proof.
move: Hk => [HkE HkF]; rewrite -mem_rev -(mem_rot 1) /et -trace_rev.
rewrite -maps_rev -urtrace_trace urtrace_rot mem_rot.
case: (rev (cpring x0)) (cycle_rev_cpring x0) => [|x p] //.
rewrite (cycle_path x) [path]lock /urtrace {2}[maps]lock /= last_maps -!lock.
elim: {x p}(Adds x p) (last x p) => [|y p Hrec] x //=; move/andP=> [Dy Hp].
rewrite /setU1 (Hrec _ Hp) orbF -[x]Enode (eqP Dy) (eqcP (HkF (edge y))).
by rewrite -eq_addc0; apply: HkE.
Qed.

Lemma coloring_proper_cpring : proper_cpring x0.
Proof.
move: memc0_trace_cpring; rewrite /et size_proper_cpring ltnNge head_cpring.
by case (behead (cpring x0)).
Qed.

Let e1 := k (node x0) +c k x0.
Let e2 := k x0 +c k (face (edge x0)).
Let et'' := ptrace (maps k (add_last (drop 2 (cpring x0)) (node x0))).

Lemma trace_cpring_eq : et = Seq e1 e2 & et''.
Proof.
move: (size_long_cpring x0).
rewrite /et (head_proper_cpring coloring_proper_cpring) ltnNge.
rewrite -urtrace_trace /= rot1_adds /urtrace last_add_last /= /et''.
case Dcp: {1}(drop 2 (cpring x0)) => [|z p].
  by rewrite Dcp /e1 /e2 /=; move/eqP=> <-.
by move/head_long_cpring {Dcp} => Dcp {z p}; rewrite -maps_add_last Dcp.
Qed.

Lemma proper_trace_cpring : proper_trace (behead et).
Proof.
move: memc0_trace_cpring; rewrite trace_cpring_eq.
by case/norP; clear; case/norP.
Qed.

End TraceCpring.

Section Cpcol1Inv.

Variable cp1 cp2 : cprog.
Let g2 := cpmap cp2.
Variable k : g2 -> color.
Hypothesis Hk : coloring k.
Let et := trace (maps k (cpring g2)).

Remark Hetc0 : et Color0 = false. Proof. exact (memc0_trace_cpring _ Hk). Qed.

Remark Hg2p : proper_cpring g2. Proof. exact (coloring_proper_cpring _ Hk). Qed.

Let e1 := k (node g2) +c k g2.
Let e2 := k g2 +c k (face (edge g2)).
Let et'' := ptrace (maps k (add_last (drop 2 (cpring g2)) (node g2))).
Let et' := Adds e2 et''.

Remark Det : et = Adds e1 et'. Proof. exact (trace_cpring_eq _ Hk). Qed.

Remark Hetp : proper_trace et'.
Proof. by move: (proper_trace_cpring g2 Hk); rewrite -/et Det. Qed.

Lemma cpbranch_correct : cp_extcol seq0 cpbranch k.
Proof.
split; rewrite /cp_ht0 /cp_tr0 /= -/g2 -/et cpbranch_spec.
  rewrite -size_ring_cpmap -/g2 -(size_maps k) -size_trace -/et Det /=.
  apply ctree_of_ttail_proper; case: (etail_perm Hetp) => [g Eg].
  by move: (congr1 size Eg); rewrite /permt size_maps /=; case=> <-.
have Heet: negb (etail (behead et) Color0).
  move: (etail_perm Hetp) Hetc0 => [g Eg].
  by rewrite Det [et']lock /= /setU1 -lock -(memc0_permt g) Eg; case/norP.
apply: (iffP (ctree_of_ttail_mem _ Heet)).
  move=> D0; exists k; last done; split; rewrite // /eptrace {}D0; congr etail.
  by rewrite /et (head_proper_cpring Hg2p) -urtrace_trace.
move=> [k0 [_ Det0] Dk].
rewrite {}Det0 /eptrace /et {k0 Dk}(eq_maps (Dk : k0 =1 _)).
by rewrite (head_proper_cpring Hg2p) -urtrace_trace.
Qed.

Lemma cpcolor1U_correct : forall f,
    (forall k', coloring k' -> @cp_extcol cp1 (Adds CpU cp2) f k') ->
  cp_extcol (Adds CpU cp1) (cpcolor1 CpU f) k.
Proof.
rewrite /cpmap -/cpmap -/g2.
pose k' e u :=
  if pick (fun x => cface u (icpU g2 x)) is Some x then k x else e +c k (node g2).
have Hk'F: forall e, invariant face (k' e) =1 ecpU g2.
  move=> e u; apply/eqP; congr (fun v c => if v is Some x then k x else c).
  by apply: eq_pick => [v]; rewrite -cface1.
have Ek': forall e x, k' e (icpU g2 x) = k x.
  move=> e x; rewrite /k' -(@eq_pick _ (cface x)).
  case: (pickP (cface x)) Hk => [y Hxy|Hx] [_ HkF].
  - exact (esym (fconnect_invariant HkF Hxy)).
  - by case/idP: (Hx x); apply connect0.
  by move=> y; rewrite /eqfun cface_icpU.
have Ek'X: forall e, k' e (ecpU g2) = addc e (k (node g2)).
move=> e; rewrite /k'; case: (pickP (fun x => cface (ecpU g2) (icpU g2 x))) => //.
  by move=> x; rewrite cface_ecpU.
have Ek'Xe: forall e, k' e (edge (ecpU g2)) = k (node g2).
  move=> e; rewrite -(Ek' e); apply: (fconnect_invariant (Hk'F e)).
  apply: fconnect1.
have Hk': forall e, negb (e =d Color0) -> coloring (k' e).
  move=> e He; have Hk'EX: invariant edge (k' e) (ecpU g2) = false.
    by rewrite /invariant Ek'X Ek'Xe addcC eq_addc0 addc_inv (negbE He).
  split; auto; move=> [||x] //; rewrite /invariant; first by rewrite eqd_sym.
  by rewrite -/(icpU g2 x) -icpU_edge !Ek'; case: Hk => [HkE _]; apply: HkE.
have Ek't: forall e, trace (maps (k' e) (cpring (ecpU g2))) = Seq e e & et.
  move=> e; rewrite cpring_ecpU !maps_adds Ek'X addcC -maps_comp.
  simpl in Ek'Xe; rewrite (@eq_maps _ _ (comp (k' _) _) _ (Ek' e)) /= Ek'Xe.
  by rewrite addc_inv /et head_cpring /= addcC addc_inv /ctrace /= addc_inv.
move=> f Hf; case: (Hf _ (Hk' Color3 (erefl _))).
case: (Hf _ (Hk' Color2 (erefl _))); case: {Hf}(Hf _ (Hk' Color1 (erefl _))).
rewrite /cpmap -/cpmap !Ek't; move=> Ht1 Et1 Ht2 Et2 Ht3 Et3.
split; first by repeat apply: ctree_union_proper.
rewrite /cpcolor1 !(@ctree_mem_union (cp_ht0 cp1 (Adds CpU cp2))) //;
 last by apply: ctree_union_proper.
apply: (iffP or3P).
  case; [ case/Et1 | case/Et2 | case/Et3 ]; rewrite /comp; move=> k0 Hk0 Dk';
   by exists k0; last by move=> x; rewrite /comp /= Dk' Ek'.
move=> [k0 Hk0 Dk]; case: (Hk0) => [Hk0c _].
pose ic2 := @injcp cp1 (Adds CpU cp2).
pose e0 := k0 (ic2 (ecpU g2)) +c k (node g2).
have Dk': comp k0 ic2 =1 k' e0.
  rewrite /comp /cpmap -/cpmap -/g2; move=> u.
  case: (fband_icpU u) => [[x Hx]|Hu].
    rewrite (fconnect_invariant (Hk'F e0) Hx) Ek' -Dk /injcp -/injcp.
    by apply: gcol_cface.
  rewrite -(fconnect_invariant (Hk'F e0) Hu) Ek'X /e0 -addcA addcc addc0.
  by apply: esym; apply: gcol_cface.
case De0: e0 in Dk'; [ idtac
 | by constructor 1; apply/Et1; exists k0
 | by constructor 2; apply/Et2; exists k0
 | by constructor 3; apply/Et3; exists k0 ].
case/andP: (@gcol_adj _ (Adds CpU cp2) _ Hk0c _ _ (@adj_ecpU g2 g2)); case/idP.
by rewrite /comp /injcp -/injcp in Dk; rewrite Dk eq_addc0 -/ic2 addcC -/e0 De0.
Qed.

Lemma cpcolor1K_correct : forall f,
   (forall k', coloring k' -> @cp_extcol cp1 (Adds CpK cp2) f k') ->
 cp_extcol (Adds CpK cp1) (cpcolor1 CpK f) k.
Proof.
rewrite /cpmap -/cpmap -/g2.
pose k' u := if pick (fun x => cface u (icpK g2 x)) is Some x then k x else Color0.
have Hk'F: invariant face k' =1 ecpK g2.
  move=> u; apply/eqP; congr (fun v c => if v is Some x then k x else c).
  by apply: eq_pick => [v]; rewrite -cface1.
have Ek': forall x, k' (icpK g2 x) = k x.
  move=> x; rewrite /k' -(@eq_pick _ (cface x)).
  case: (pickP (cface x)) Hk => [y Hxy|Hx] [_ HkF].
  - exact (esym (fconnect_invariant HkF Hxy)).
  - by case/idP: (Hx x); apply connect0.
  by move=> y; rewrite /eqfun cface_icpK.
pose ic2 := @injcp cp1 (Adds CpK cp2).
case He12: (e1 =d e2).
  split; rewrite /cpcolor1 -/g2 -/et Det /et' /= He12 //; right.
  move=> [k0 [[Hk0E Hk0F] _] Dk].
  rewrite /e1 /e2 addcC (inj_eqd (@inj_addc _)) in He12.
  have HaX: adj (ic2 (icpK g2 (node g2))) (ic2 (icpK g2 (face (edge g2)))).
    apply: sub_adj_injcp; rewrite (adj_icpK g2); apply/or3P; constructor 3.
    by rewrite fconnect1 connect0.
  case/adjP: HaX => [u HXu HuX]; case/idP: (Hk0E u).
  rewrite /comp /injcp -/injcp -/g2 -/ic2 in Dk.
  rewrite /invariant -(fconnect_invariant Hk0F HXu).
  by rewrite (fconnect_invariant Hk0F HuX) !Dk eqd_sym.
have Hk': coloring k'.
  rewrite /e1 /e2 addcC (inj_eqd (@inj_addc _)) in He12.
  split; last done; move=> u; rewrite /invariant.
  case: (fband_icpK u) (fband_icpK (edge u)) => [x Hx] [y Hy].
  rewrite (fconnect_invariant Hk'F Hx) (fconnect_invariant Hk'F Hy) !Ek'.
  have Hxy: adj (icpK g2 x) (icpK g2 y).
    by apply/adjP; exists u; first by rewrite Sface.
  case: Hk {u Hx Hy} => [HkE HkF]; rewrite (eqcP (HkF (edge g2))) in He12.
  rewrite adj_icpK in Hxy; case/or3P: Hxy.
  - move/adjP=> [z Hxz Hzy]; rewrite (fconnect_invariant HkF Hxz).
    by rewrite -(fconnect_invariant HkF Hzy); apply: HkE.
  - move/andP=> [Hx Hy]; rewrite -(fconnect_invariant HkF Hx).
    by rewrite -(fconnect_invariant HkF Hy).
  move/andP=> [Hy Hx]; rewrite -(fconnect_invariant HkF Hx).
  by rewrite -(fconnect_invariant HkF Hy) eqd_sym.
move=> f Hf; case: {Hf}(Hf _ Hk'); rewrite /cpmap -/cpmap -/g2.
have <-: Adds (e1 +c e2) et'' = trace (maps k' (cpring (ecpK g2))).
  rewrite cpring_ecpK !maps_adds -maps_comp (eq_maps (Ek' : comp k' _ =1 _)).
  rewrite (fconnect_invariant Hk'F (cface_node_ecpK g2)) Ek'.
  move: (esym Det); rewrite /et drop_behead (head_proper_cpring Hg2p).
  rewrite maps_adds -!urtrace_trace /urtrace !rot1_adds !last_add_last /=.
  rewrite headI /= /et'; case=> De2 <-.
  by rewrite /e1 De2 -addcA addc_inv.
move=> Ht Et; split; rewrite /cpcolor1 -/g2 -/et Det /et' He12 //.
apply: (iffP Et) => {Ht Et} [] [k0 Hk0 Dk]; exists k0; auto.
  by rewrite /comp in Dk; move=> x; rewrite /comp /injcp -/injcp Dk Ek'.
move=> u; rewrite /comp -/ic2; rewrite /comp /injcp -/injcp -/ic2 -/g2 in Dk.
case: (fband_icpK u) => [x Hu]; rewrite (fconnect_invariant Hk'F Hu).
by case: Hk0 => [Hk0 _]; rewrite /ic2 (@gcol_cface _ (Adds CpK _) _ Hk0 _ _ Hu) Dk.
Qed.

Lemma cpcolor1A_correct : forall f,
    (forall k', coloring k' -> @cp_extcol cp1 (Adds CpA cp2) f k') ->
  cp_extcol (Adds CpA cp1) (cpcolor1 CpA f) k.
Proof.
rewrite /cpmap -/cpmap -/g2; case He1: (negb (e1 =d e2)).
  split; rewrite /cpcolor1 -/g2 -/et Det /et' (negbE He1) //.
  right; move=> [k0 [[_ Hk0F] _] Dk]; rewrite /comp /= in Dk; case/eqP: He1.
  rewrite /e1 addcC; congr addc; rewrite -!Dk; apply: (fconnect_invariant Hk0F).
  apply: (sub_cface_injcp cp1); rewrite (cface_icpA g2); apply/orP; right.
  by rewrite /= !connect0 !orbT.
pose k' : ecpA g2 -> color := k; move/idP: He1 => He1.
move/eqP: (He1); rewrite /e1 addcC; move/inj_addc=> DkXn.
have Hk'F: invariant face k' =1 ecpA g2.
  move=> x; apply/eqP; move: (fconnect1 face x); rewrite cface_icpA /k'.
  case: Hk => [_ HkF]; case/orP=> Hx.
    by apply: esym; apply: (fconnect_invariant HkF).
  have EkX: forall y, set2 x (face x) y -> k y = k (node g2).
    move=> y; rewrite -mem_seq2; move=> Hy.
    move: (allP Hx _ Hy); rewrite /fband; case/hasP=> [z Hz Hyz].
    rewrite (fconnect_invariant HkF Hyz); repeat case/setU1P: Hz => [<-|Hz] //.
  by rewrite (EkX _ (set21 _ _)) (EkX _ (set22 _ _)).
have Hk': coloring k'.
  split; auto; rewrite /invariant /k' /= /ecpA_edge; move: Hk => [HkE HkF] x.
  case Hg2: (cface (edge g2) (node g2)); last by apply: HkE.
  case: (x =P g2) => [Dx|_] /=.
    rewrite -(eqcP (HkF _)) Enode -[x]Enode (eqcP (HkF _)) eqd_sym Dx; apply: HkE.
  case: (x =P node (node g2)) => [Dx|_]; last by apply: HkE.
  rewrite -[node g2]Enode -Dx -cface1r in Hg2.
  by rewrite (fconnect_invariant HkF Hg2); apply: HkE.
move=> f Hf; case: {Hf}(Hf _ Hk'); rewrite /cpmap -/cpmap -/g2.
suffice ->: trace (maps k' (cpring (ecpA g2))) = if et'' is Seq0 then et else et''.
  by move=> Ht Et; split; rewrite /cpcolor1 -/g2 /k' -/et Det /et' -/et' -Det He1.
rewrite /k' cpring_ecpA; case Hg2l: (long_cpring g2).
  rewrite -urtrace_trace /et'' (head_long_cpring Hg2l) /= rot1_adds.
  by rewrite -DkXn /urtrace last_add_last -maps_add_last headI.
by rewrite -/et /et'' drop_oversize // leqNgt -size_long_cpring Hg2l.
Qed.

Lemma cpcolor1R_correct : forall n f,
   (forall k', coloring k' -> @cp_extcol cp1 (Adds (CpR n) cp2) f k') ->
  cp_extcol (Adds (CpR n) cp1) (cpcolor1 (CpR n) f) k.
Proof.
move=> n f Hf; case: {Hf}(Hf k Hk); rewrite /cpmap -/cpmap -/g2 cpring_ecpR.
by rewrite maps_rot trace_rot; split.
Qed.

Lemma cpcolor1R'_correct : forall f,
   (forall k', coloring k' -> @cp_extcol cp1 (Adds CpR' cp2) f k') ->
 cp_extcol (Adds CpR' cp1) (cpcolor1 CpR' f) k.
Proof.
move=> f Hf; case: {Hf}(Hf k Hk); rewrite /cpmap -/cpmap -/g2 /ecpR' cpring_ecpR.
rewrite -subn1 -size_cpring -/(rotr 1 (cpring g2)) maps_rotr.
rewrite -(rotr_rot 1 (trace _)) -trace_rot rot_rotr.
split; rewrite /cpcolor1 size_trace size_maps leqNgt -/g2;
  by rewrite -size_proper_cpring Hg2p.
Qed.

End Cpcol1Inv.

Definition cpexpand1 (s : cpstep) : cprog :=
  match s with
  | CpY => (Seq CpR' CpK (CpR 1) CpU)
  | CpH => (Seq CpR' CpK CpK (CpR 1) CpU)
  | _ => seq1 s
  end.

Fixpoint cpexpand (cp : cprog) : cprog :=
  if cp is Adds s cp' then cat (cpexpand1 s) (cpexpand cp') else seq0.

Lemma cpexpand_add_last : forall cp s,
 cpexpand (add_last cp s) = cat (cpexpand cp) (cpexpand (seq1 s)).
Proof. by elim=> [|s' cp Hrec] s //=; rewrite Hrec -catA. Qed.

Lemma cpcolor1_cpexpand_rev : forall cp f (et : colseq), negb (et Color0) ->
  foldr cpcolor1 f (rev cp) et = foldr cpcolor1 f (rev (cpexpand cp)) et :> ctree.
Proof.
have EctE: forall ct, (if ct is Ctree_empty then Ctree_empty else ct) = ct by case.
elim/last_ind=> [|cp s Hrec] // f et Het.
rewrite cpexpand_add_last -cats1 !rev_cat !foldr_cat; case Ds: s => [n||||||].
- by rewrite /= -Hrec // mem_rot.
- by rewrite /= -Hrec // mem_rotr.
- case: et Het => [|[|||] et] //= Het; rewrite -?Hrec ?ctree_union_Nl ?EctE //;
  rewrite !seq1I !cats1 -!add_last_adds !rotr1_add_last //;
  by repeat rewrite headI //=; rewrite ctree_union_sym.
- case: et Het => [|e1 [|e2 et]] //=; first by rewrite !if_same.
  rewrite !seq1I !cats1 -!add_last_adds !rotr1_add_last -!rot1_adds !size_rot /=.
  case He12: (e1 =d e2).
    rewrite -{e2 He12}(eqP He12).
    case: e1 => //= Het; rewrite -?Hrec ?ctree_union_Nl ?EctE //.
    by rewrite ctree_union_sym.
  by case: e1 He12 => //; case: e2 => //= *; rewrite -?Hrec ?ctree_union_Nl ?EctE.
- by rewrite /= -?Hrec.
- case: et Het => [|e1 [|e2 et]] //=; case He12: (eqd e1 e2) => //.
  case/norP; clear; move/norP=> [_ Het]; apply Hrec.
  by rewrite /= /setU1 -eq_addc0 He12.
case: et Het => [|e1 [|e2 et]] //= Het; rewrite -?Hrec //.
by case: et Het => [|e3 et] //; case/norP; clear; case/norP.
Qed.

Inductive pmap_eqdep (A : Set) (g : pointed_map) (h : A -> g)
                   : forall g' : pointed_map, (A -> g') -> Prop :=
    PmapEqdepRefl : pmap_eqdep h h.

Lemma pmap_eqdep_sym : forall A g g' h h',
  @pmap_eqdep A g h g' h' -> pmap_eqdep h' h.
Proof. by move=> A g g' h h' []. Qed.

Lemma pmap_eqdep_comp : forall A B f g g' h h',
 @pmap_eqdep B g (fun x => h x) g' (fun x => h' x) ->
 @pmap_eqdep A g (fun x => h (f x)) g' (fun x => h' (f x)).
Proof.
move=> A B f g g' h h'.
by rewrite -[fun x => h' (f x)]/(fun x => (fun y => h' y) (f x)); case.
Qed.

Lemma pmap_eqdep_split : forall A (g g' : pointed_map) h (h' : _ -> g'),
  @pmap_eqdep A g h (PointedMap g' g') h' -> pmap_eqdep h h'.
Proof. by move=> A g [x g']. Qed.

Lemma injcp_adds : forall s (cp1 cp2 : cprog),
 pmap_eqdep (fun x => @injcp cp1 (Adds s cp2) (injcp (seq1 s) x))
            (@injcp (Adds s cp1) cp2).
Proof. done. Qed.

Lemma injcp_cat : forall cp1 cp2 cp3 : cprog,
  pmap_eqdep (fun x => injcp cp2 (injcp cp1 x)) (@injcp (cat cp1 cp2) cp3).
Proof.
move=> cp1 cp2; elim: cp1 => [|s' cp1 Hrec] cp3; first by case cp2.
rewrite cat_adds; case (injcp_adds s' (cat cp1 cp2) cp3).
by case: (Hrec (Adds s' cp3)).
Qed.

Lemma eqdep_injcpRR' : forall cp,
 pmap_eqdep (fun x => icpU (cpmap cp) x)
            (@injcp (rev (Seq CpR' (CpR 1) CpU)) cp).
Proof.
move=> cp; rewrite /rev /catrev /injcp -/injcp /cpmap -/cpmap.
by apply pmap_eqdep_split; rewrite ecpR1_eq ecpR'_eq Eedge; case: (cpmap cp).
Qed.

Lemma eqdep_injcpRK : forall cp dcp (g : pointed_map) (h : cpmap cp -> g),
 pmap_eqdep (fun x => h x) (@injcp (rev (Adds CpR' dcp)) cp) ->
 pmap_eqdep (fun x => icpN g (h x)) (@injcp (rev (Seq CpR' CpK & dcp)) cp).
Proof.
move=> cp dcp g h Dh.
rewrite -[fun x => icpN g (h x)]/(comp (icpN g) (fun x => h x)).
case/pmap_eqdep_sym: {g h}Dh; rewrite !rev_adds -!cats1 -catA cat1s /seq1.
case (injcp_cat (rev dcp) (Seq CpR') cp).
case (injcp_cat (rev dcp) (Seq CpK CpR') cp).
move: {cp}(cpmap cp) {dcp}(catrev cp (rev dcp)) (@injcp (rev dcp) cp) => A cp'.
rewrite /catrev /injcp /cpmap -/cpmap; case/cpmap: cp' => [g' x] f.
by apply pmap_eqdep_split; rewrite /icpK /ecpK !ecpR1_eq !ecpR'_eq Eedge.
Qed.

Lemma injcp_expand : forall cp1 cp2,
  pmap_eqdep (@injcp (rev cp1) cp2) (@injcp (rev (cpexpand cp1)) cp2).
Proof.
move=> cp1 cp2; elim: cp1 => [|s cp1 Hrec] //=; rewrite rev_adds -cats1 rev_cat.
 case: (injcp_cat (rev cp1) (seq1 s) cp2).
 case: (injcp_cat (rev (cpexpand cp1)) (rev (cpexpand1 s)) cp2).
 simpl; case/pmap_eqdep_sym: Hrec; move: {cp1}(rev (cpexpand cp1)) => rcp.
 move: {cp2}(cpmap cp2) {rcp}(catrev cp2 rcp) (@injcp rcp cp2) => A cp ic.
move Dcps: (rev (cpexpand1 s)) => cps.
case: s Dcps => [n||||||] //= Dcps; rewrite -{cps}Dcps //;
 apply: {A ic}(pmap_eqdep_comp ic); repeat apply: eqdep_injcpRK;
 exact: eqdep_injcpRR'.
Qed.

Lemma cpcolor1_correct : forall cp1 cp2 k,
  coloring k -> @cp_extcol cp1 cp2 (foldr cpcolor1 cpbranch cp1) k.
Proof.
move=> cp1 cp2 k Hk; rewrite -(rev_rev cp1); move/rev: cp1 => cp1.
pose ecp1 := rev (cpexpand cp1).
have Hecp1: (cp_extcol ecp1 (foldr cpcolor1 cpbranch ecp1) k).
  rewrite {Eecp1}/ecp1; elim/last_ind: cp1 cp2 k Hk => [|cp1 s Hrec] cp2 k Hk.
    by apply: cpbranch_correct.
  rewrite cpexpand_add_last rev_cat; case: s => [n||||||] /=.
  - by apply: cpcolor1R_correct; auto.
  - by apply: cpcolor1R'_correct; auto.
  - apply: cpcolor1U_correct; [ done | idtac ].
    move=> k1 Hk1; apply: cpcolor1R_correct; auto.
    move=> k2 Hk2; apply: cpcolor1K_correct; auto.
    by move=> k3 Hk3; apply: cpcolor1R'_correct; auto.
  - apply: cpcolor1U_correct; [ done | idtac ].
    move=> k1 Hk1; apply: cpcolor1R_correct; auto.
    move=> k2 Hk2; apply: cpcolor1K_correct; auto.
    move=> k3 Hk3; apply: cpcolor1K_correct; auto.
    move=> k4 Hk4; apply: cpcolor1R'_correct; auto.
    by apply: cpcolor1U_correct; auto.
  - by apply: cpcolor1K_correct; auto.
  by apply: cpcolor1A_correct; auto.
case: Hecp1; rewrite {}/ecp1 -cpcolor1_cpexpand_rev ?memc0_trace_cpring //.
move=> Ht Et; split.
  by move: Ht; rewrite /cp_ht0 -!size_ring_cpmap; case: (injcp_expand cp1 cp2).
by move: Et; rewrite /cp_tr0; case: (injcp_expand cp1 cp2).
Qed.

Lemma cpcolor0_correct : forall cp,
  @cp_extcol cp seq0 (fun _ => cpcolor0 cp) (ccons true).
Proof.
move=> cp1; set cp2 : cprog := seq0; set g2 := cpmap cp2.
have: g2 = cpmap seq0 :> hypermap by done.
set k : g2 -> color := ccons true.
have: trace (maps k (cpring g2)) = seq2 Color1 Color1 by done.
have: coloring k by split; case.
move: k; rewrite {}/g2; elim: cp1 cp2 => [|s cp1 Hrec] cp2 k Hk Ek Dg2.
  by case: (cpcolor1_correct seq0 Hk); rewrite Ek; split.
case: (cpcolor1_correct (Adds s cp1) Hk); rewrite Ek.
set g2 := cpmap cp2; have DknX: k (node g2) = Color1 +c (k g2).
  move: Ek; rewrite trace_cpring_eq // -/g2; case=> <- _ _.
  by rewrite -addcA addcc addc0.
have Hg2b: cface g2 (node g2) = false.
  by move: (g2 : g2); rewrite /g2 Dg2; case.
have Hg2b': (node g2 =d g2) = false.
  by move: (g2 : g2); rewrite /g2 Dg2; case.
have Hg2: forall x, g2 = x :> g2 \/ node g2 = x.
  by move: (g2 : g2); rewrite /g2 Dg2; do 2 case; auto.
case: s => [n||||||]; try by split.
- case: (Hrec (Adds (CpR n) cp2) k Hk) => //; last by split.
  rewrite /cpmap -/cpmap cpring_ecpR maps_rot trace_rot Ek.
  by case: (n) => [|[|[|n']]].
- simpl; pose k' u := if cface u (ecpY g2) then Color2 else
                      if cface u (icpY g2 g2) then Color0 else Color3.
  have <-: trace (maps k' (cpring (ecpY g2))) = seq3 Color1 Color2 Color3.
    by rewrite /k'; move: (g2 : g2); rewrite /g2 Dg2; case.
  have Hk'F: invariant face k' =1 ecpY g2.
    by move=> u; apply/eqP; rewrite /k' -!cface1.
  have Hk': coloring k'.
    split; last done; rewrite /k'; move: (g2 : g2); rewrite /g2 Dg2.
    by case=> [|] [||[||[|]]].
  case: (@cpcolor1_correct cp1 (Adds CpY cp2) _ Hk'); rewrite /cpmap -/cpmap -/g2.
  move=> Ht Et; split; first done; apply: {Et Ht}(iffP Et).
    move=> [k0 Hk0 Dk']; pose h0 := locked Eperm231.
    exists (fun x => k g2 +c h0 (k0 x)); first exact: (gcol_perm Hk0).
    move=> x; rewrite /comp in Dk'; rewrite /comp /= Dk' addcC.
    unlock h0; move: x DknX; rewrite /k' -/g2; move: (k) (g2 : g2).
    by rewrite /g2 Dg2; move=> k''; do 2 case.
  move=> [k0 Hk0 Dk].
  pose e0 := k g2 +c k0 (@injcp cp1 (Adds CpY cp2) (ecpY g2)).
  pose h0 := if e0 =d Color2 then Eperm321 else Eperm312.
  exists (fun x => h0 (k g2) +c h0 (k0 x)); first exact: (gcol_perm Hk0).
  move=> u; rewrite /comp in Dk; rewrite /comp /= -permc_addc /k'.
  rewrite /comp /injcp -/injcp in Dk.
  case: (fband_icpY u) Hk0 => [[x Hu]|Hu] [Hk0 _].
    rewrite (@gcol_cface _ (Adds CpY _) _ Hk0 _ _ Hu) {}Dk.
    rewrite !{Hu}(same_cface Hu) cface_icpY Sface cface_ecpY {}/h0 /=.
    case: (Hg2 x); case=> <- {x}; first by rewrite addcc permc0 connect0.
    by rewrite DknX (addcC Color1) addc_inv Sface Hg2b; case e0.
  rewrite Sface Hu -(@gcol_cface _ (Adds CpY _) _ Hk0 _ _ Hu) -/e0 /h0.
  have := adj_ecpY (coloring_proper_cpring g2 Hk).
  move/(@gcol_adj _ (Adds CpY _) _ Hk0); case/and3P.
  by rewrite !Dk -/g2 DknX eq_addc0 (eq_addc0 (k g2)) -addcA -/e0; case e0.
pose k' e u :=
  if u =d (ecpU g2) then Color1 else if u =d (icpU g2 g2) then e else Color0.
have Hk'F: forall e, invariant face (k' e) =1 ecpU g2.
  rewrite /k'; move: (g2 : g2); rewrite /g2 Dg2; do 2 case; repeat case=> //.
have Hk': forall e, negb (e =d Color0) -> coloring (k' e).
  move=> e He; split; last done; rewrite /k';
  move: (g2 : g2); rewrite /g2 Dg2.
  case: e He => // _; case; repeat case=> //.
have Ek': forall e,
   trace (maps (k' e) (cpring (ecpU g2))) = seq4 Color1 Color1 e e.
  by rewrite /k'; move: (g2 : g2); rewrite /g2 Dg2; do 2 case.
case: (@cpcolor1_correct cp1 (Adds CpU cp2) _ (Hk' Color2 (erefl _))).
case: {Hk'}(@cpcolor1_correct cp1 (Adds CpU cp2) _ (Hk' Color1 (erefl _))).
rewrite /cpmap -/cpmap -/g2 /cpcolor0 !{}Ek'; move=> Ht1 Et1 Ht2 Et2.
split; first by apply: ctree_union_proper.
rewrite {Ht1 Ht2}(ctree_mem_union (ttail et0) Ht2 Ht1); apply: (iffP orP).
  case.
    case/Et2=> [k0 Hk0 Dk'].
    exists (fun x => k (node g2) +c Eperm213 (k0 x)); first exact: gcol_perm.
    rewrite /comp in Dk'; move=> x; rewrite /comp /injcp -/injcp Dk' /k' /=.
    rewrite /eqd /= addcC; case: (Hg2 x) => [] <- {x}; last by rewrite Hg2b'.
    by rewrite set11 DknX addc_inv.
  case/Et1=> [k0 Hk0 Dk'].
  exists (fun x => k (node g2) +c Eperm123 (k0 x)); first exact: gcol_perm.
  rewrite /comp in Dk'; move=> x; rewrite /comp /injcp -/injcp Dk' /k' /=.
  rewrite /eqd /= addcC; case: (Hg2 x) => [] <- {x}; last by rewrite Hg2b'.
  by rewrite set11 DknX addc_inv.
move=> [k0 Hk0 Dk]; rewrite /= /cpmap /injcp -/cpmap -/injcp /comp in k0 Hk0 Dk.
pose e0 := k (node g2) +c k0 (@injcp cp1 (Adds CpU _) (ecpU g2)).
case He00: (e0 =d Color0).
  case: Hk0 => [Hk0 _]; case/andP: (gcol_adj Hk0 (@adj_ecpU _ _)); case/idP.
  by rewrite -/cpmap Dk eq_addc0.
case He01: (e0 =d Color1).
  right; apply/Et1; exists (fun w => k (node g2) +c Eperm123 (k0 w)).
    by apply: gcol_perm.
  move=> u; case: (fband_icpU u) Hk0 => [[x Hu]|Hu] [Hk0 _].
    rewrite (fconnect_invariant (Hk'F Color1) Hu) /comp (gcol_cface Hk0 Hu) Dk /k'.
    rewrite /eqd /=; case: (Hg2 x) => [] <- {x Hu}; last by rewrite Hg2b' addcc.
    by rewrite set11 DknX -addcA addcc addc0.
  rewrite -(fconnect_invariant (Hk'F Color1) Hu) /comp -(gcol_cface Hk0 Hu).
  rewrite /k' set11; exact (eqP He01).
left; apply/Et2; pose h0 := if e0 =d Color2 then Eperm213 else Eperm231.
exists (fun w => h0 (k (node g2)) +c h0 (k0 w)); first by apply: gcol_perm.
move=> u; rewrite /comp -permc_addc.
case: (fband_icpU u) Hk0 => [[x Hu]|Hu] [Hk0 _].
  rewrite (fconnect_invariant (Hk'F _) Hu) /comp {Hu}(gcol_cface Hk0 Hu) Dk.
  rewrite /k' /eqd /=; case: (Hg2 x) => [] <-; last by rewrite Hg2b' addcc permc0.
  by rewrite set11 DknX -addcA addcc addc0 /h0; case e0.
rewrite -(fconnect_invariant (Hk'F _) Hu) /comp -{Hu}(gcol_cface Hk0 Hu).
by rewrite /k' set11 /h0 -/e0; case: (e0) He00 He01.
Qed.

End CprogColoringCorrectness.

Theorem cpcolor_proper : forall cp, ctree_proper (pred (cprsize cp)) (cpcolor cp).
Proof.
move=> cp; rewrite /cpcolor.
case Dh: (pred (cprsize cp)) => [|h].
case: (cpcolor0_correct (seq1 Color1) (rev cp)) => /= [Ht Et].
move: (elimT Et) Ht; rewrite /cp_ht0 -/(rev (rev cp)).
case: (cpcolor0 (rev cp)) => [t1 t2 t3|lf|] //.
- by clear; rewrite rev_rev Dh.
- case=> // [k0 [Hk0 _] _] _; rewrite rev_rev in k0 Hk0.
  move: (coloring_proper_cpring (cpmap cp) Hk0).
  by rewrite size_proper_cpring size_ring_cpmap ltn_lt0sub subn1 Dh.
apply ctree_cons_rot_proper.
case: (cpcolor0_correct seq0 (rev cp)) => /= [Ht _].
by rewrite /cp_ht0 -/(rev (rev cp)) rev_rev Dh in Ht.
Qed.

Theorem ctree_mem_cpcolor : forall cp et,
 reflect (even_trace et /\ ring_trace (cpring (cpmap cp)) (Adds (sumt et) et))
         (ctree_mem (cpcolor cp) et).
Proof.
move=> cp et0; rewrite /cpcolor ctree_mem_cons_rot.
case: (cpcolor0_correct et0 (rev cp)) => /= [_ H]; apply: {H}(iffP H).
  move=> [k [Hk Ek] _]; move: k Hk Ek; rewrite /cp_tr0 -/(rev (rev cp)) rev_rev.
  set g := cpmap cp; move=> k Hk; set rc := rot 1 _; move=> Erc.
  have [Hrcp Het0p]: proper_trace (ptrace rc) /\ proper_trace et0.
    move: (memc0_trace_cpring g Hk) (proper_trace_cpring g Hk) Erc.
    rewrite -urtrace_trace -/rc; case: rc => // [y rc].
    rewrite /urtrace /ptrace /= /ttail /eptrace; case/norP; clear.
    case: (proper_trace et0); first by split.
    move=> Hrc0 Hrcp; move/(congr1 (fun s => mem s Color0)).
    by rewrite /etail memc0_permt memc0_ttail /= (negbE Hrc0) Hrcp.
  move: (etail_perm Het0p) (etail_perm Hrcp) => [h1 Eh1] [h2 Eh2].
  rewrite /etail /etrace_perm /even_trace {}Erc /eptrace even_etail in Eh1 |- *.
  split; rewrite // permt_id -{}Eh2 in Eh1.
  pose h1' := inv_eperm h1; pose h12 := comp h1' h2; exists (comp h12 k).
    by apply: (@coloring_inj _ h12) Hk => //; apply: inj_comp; apply permc_inj.
  rewrite (maps_comp h12 k) (maps_comp h1' h2) -/(permt h1') -/(permt h2).
  rewrite !trace_permt; apply: (monic_move (monic_maps (inv_permc h1))).
  rewrite /= -sumt_permt -/(permt h1) Eh1 sumt_permt /permt -maps_adds.
  congr (maps h2); apply: (monic_inj (@rotr_rot 1 _)).
  by rewrite -trace_rot -/rc rot1_adds; case: (rc) Hrcp.
move=> [Het0e H]; rewrite -(rev_rev cp) {1 3 5}/rev in H; case: H.
set g := cpmap (catrev seq0 (rev cp)); set ic0 := @injcp _ _.
move=> k Hk Ek; pose e0 := k (ic0 true) +c k (ic0 false).
have Hetp' := proper_trace_cpring g Hk.
have He0: proper_trace (seq1 e0).
  rewrite /proper_trace /= /e0 -eq_addc0.
  by case: (andP (@gcol_adj _ _ _ Hk false (seq1 true) _)); first by case.
case: (etail_perm He0) => [h0 [Eh0 _]].
exists (fun w => Color2 +c h0 (k (ic0 false)) +c h0 (k w)).
  apply: gcol_perm; split; first done.
  move: Ek Hetp'; rewrite /cp_tr0 -/g /eptrace -urtrace_trace.
  case: (rot 1 (maps k (cpring g))) => [|x p] //=.
  rewrite /urtrace /=; case=> _ <-.
  by rewrite /etail /etrace_perm Het0e permt_id.
move=> x; rewrite /comp -addcA addcC -permc_addc; case: x => /=.
  by rewrite {1}[addc]lock addcC -/e0 -lock Eh0.
by rewrite addcc permc0.
Qed.

Unset Implicit Arguments.

