(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import paths.
Require Import color.
Require Import finset.
Require Import connect.
Require Import hypermap.
Require Import geometry.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Configuration maps are entered as little linear construction programs : *)
(* staring from a basic triangle, it builds a sequence of concentric quasi *)
(* cubic maps, alternatively rotating the perimeter, and adding a single   *)
(* outer node (and a new region) or two adjacent ones (which closes up a   *)
(* region, and introduces a new one).                                      *)
(*   We also need two generalizations of this construction:                *)
(*    - the proof of the birkhoff theorem requires computing the coloring  *)
(* of a few non-two connected quasi cubic plain maps; they can be obtained *)
(* by starting the construction from a single edge, and allowing adding    *)
(* a disconnected face during the construction.                            *)
(*    - the contract colorings are computed as colorings of reduced maps,  *)
(* whose construction is similar to the above, but also two operations     *)
(* that enclose a region by either merging its two neighbors (this creates *)
(* a binary node), or making them adjacent (this creates a ternary node).  *)
(*    We define all the necessary map constructions here. The two "add     *)
(* node" contructions are factored through the "add face" and a rotated    *)
(* variant of the "enclose face" constructions.                            *)
Inductive cpstep : Set :=
  | CpR (n : nat) (* rotation around the outer ring (noop on overflow) *)
  | CpR'          (* single-step reverse rotation (for encodings)      *)
  | CpY           (* new Y junction and face                           *)
  | CpH           (* new H junction and face (closing an inner face)   *)
  | CpU           (* new face, no junctions (U-shaped loop)            *)
  | CpK           (* new K (inverted Y) junction (closing off a face)  *)
  | CpA.          (* inverted-V junction, merging neighbors of a face  *)

Lemma cpstepDataP : comparable cpstep.
Proof. rewrite /comparable; decide equality; exact: comparable_data. Qed.
Definition cpstepData := Eval compute in compareData cpstepDataP.
Canonical Structure cpstepData.

(* A configuration map construction program is just a sequence of steps.     *)
(* It is interpreted RIGHT TO LEFT, starting from a simple U-shaped map.     *)

Definition cprog : Set := seq cpstepData.

Fixpoint cubic_prog (cp : cprog) : bool :=
  match cp with
  | Seq0 => true
  | Adds (CpR _) cp' => cubic_prog cp'
  | Adds CpU cp' => cubic_prog cp'
  | Adds CpY cp' => cubic_prog cp'
  | Adds CpH cp' => cubic_prog cp'
  | _ => false
  end.

(* The configuration data comprises the construction program for the         *)
(* configuration map, the reducibility contract, represented as a sequence   *)
(* of integers (indexing the contract edges in the construction process),    *)
(* and a boolean flagging symmetrical maps, whose reflection does not need   *)
(* to be checked when scanning a part for reducible patterns (see quiztree). *)
(*   The reducibility program aways starts with an H, and ends with a Y; we  *)
(* need to check this explicitly (both in cfquiz.v and cfcontract.v). The    *)
(* initial H signals the end of the contract in the concrete syntax. The     *)
(* pattern-matching tree store further assumes that if a face has arity 9,   *)
(* 10, or 11, it is the one containing the first dart created.               *)
(*    We define equality on configurations, but only in order to be able to  *)
(* use sequences of configurations.                                          *)

Record config : Set := ConfigRecord {
  cfsym : bool;
  cfcontract_ref : natseq;
  cfprog : cprog
}.

Fixpoint config_prog (cp : cprog) : bool :=
  match cp with
  | Adds (CpR _) cp' => config_prog cp'
  | Adds CpY seq0 => true
  | Adds CpY cp' => config_prog cp'
  | Adds CpH cp' => config_prog cp'
  | _ => false
  end.

Lemma config_prog_cubic : forall cp, config_prog cp -> cubic_prog cp.
Proof. by elim=> [|[n||||||] cp Hrec] //=; case: cp Hrec; auto. Qed.

Lemma configDataP : comparable config.
Proof. rewrite /comparable; decide equality; apply: comparable_data. Qed.
Definition configData := Eval compute in compareData configDataP.
Canonical Structure configData.

Definition configseq := seq configData.

Module ConfigSyntax.

Definition H := CpH.
Definition Y := CpY.
Definition U := CpU.
Coercion CpR : nat >-> cpstep.

Definition add_cp : cpstep -> cprog -> cprog := adds.

Notation "'Cprog' s1 .. sn" :=
  (add_cp s1 .. (add_cp sn seq0) .. )
  (at level 100, s1, sn at level 9, format "'Cprog'  s1  ..  sn").

Notation "'Cprog'" := (seq0 : cprog) (at level 100).

Coercion datum_of_cprog := fun (cp : cprog) => (cp : seq _) : datum _.

Fixpoint parse_config (sym : bool) (cc : natseq) (cp : cprog) {struct cp}
                   : config :=
  if cp is Adds (CpR i) cp' then parse_config sym (Adds i cc) cp' else
  ConfigRecord sym (rev cc) cp.

Notation "'Config' * s1 .. sn" :=
  (parse_config true seq0 (add_cp s1 .. (add_cp sn seq0) .. ))
  (at level 100, s1, sn at level 9, format "'Config' *  s1  ..  sn").
Notation "'Config' s1 .. sn" :=
  (parse_config false seq0 (add_cp s1 .. (add_cp sn seq0) .. ))
  (at level 100, s1, sn at level 9, format "'Config'  s1  ..  sn").

End ConfigSyntax.

Section ConfigSamples.

(* Samples: the pentaton map construction, and the first reducible config.   *)

Import ConfigSyntax.

Let pentamap := Cprog H 4 Y Y.
Let config1 := Config* 15 H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y.

(* Eval Compute in (config_prog (cfprog config1)). *)

End ConfigSamples.

Record pointed_map : Type := PointedMap {pointee :> hypermap; pointer :> pointee}.

Implicit Arguments PointedMap [].

Section CpRing.

Variables (g : hypermap) (x0 : g).

Definition cpring := rev (orbit node (node (node x0))).

Definition proper_cpring := negb (x0 =d node x0).
Definition long_cpring := negb (face (edge x0) =d node x0).

Lemma uniq_cpring : uniq cpring.
Proof. by rewrite /cpring uniq_rev uniq_orbit. Qed.

Lemma mem_cpring : cpring =1 cnode x0.
Proof. by move=> x; rewrite /cpring mem_rev -fconnect_orbit -!cnode1. Qed.

Lemma size_cpring : size cpring = order node x0.
Proof. by rewrite -(card_uniqP uniq_cpring) (eq_card mem_cpring). Qed.

Lemma size_proper_cpring : proper_cpring = (1 < size cpring).
Proof.
move: (iter_order (Inode g) x0) (uniq_orbit node x0).
rewrite size_cpring /proper_cpring eqd_sym /orbit -(orderSpred node x0).
case: (pred (order node x0)) => [|n] //= Dnx; first by rewrite Dnx set11.
by case/andP; case/norP.
Qed.

Lemma size_long_cpring : long_cpring = (2 < size cpring).
Proof.
move: (orderSpred node x0) (iter_order (Inode g) x0) (uniq_orbit node x0).
rewrite size_cpring /long_cpring eqd_sym -(monic2F_eqd (Enode g)) /orbit.
case: (order node x0) => [|[|[|n]]] //= _ Dnx; try by rewrite !Dnx set11.
by case/andP; case/norP; clear; case/norP.
Qed.

Lemma cycle_rev_cpring : fcycle node (rev cpring).
Proof. by rewrite /cpring rev_rev (cycle_orbit (Inode g)). Qed.

Lemma ucycle_rev_cpring : ufcycle node (rev cpring).
Proof. by rewrite /ucycle uniq_rev uniq_cpring cycle_rev_cpring. Qed.

Lemma cpring_def : forall p, (if p is Adds x _ then x = node x0 else False) ->
  ufcycle node (rev p) -> cpring = p.
Proof.
move=> p; case Dp: {1}p => // [x p'] Dx; rewrite {}Dx in Dp; move/andP=> [Hp Up].
have Dn: size (rev p) = order node (node (node x0)).
  have Hx0: rev p (node x0) by rewrite mem_rev Dp /= setU11.
  by rewrite (order_cycle Hp Up) // -(fconnect_cycle Hp Hx0) fconnect1.
rewrite (cycle_path x0) {1}Dp rev_adds last_add_last in Hp.
move/fpathP: Hp {Up} => [n Dp']; rewrite -Dp' size_traject in Dn.
by rewrite /cpring /orbit -Dn Dp' rev_rev.
Qed.

Lemma head_cpring : cpring = Adds (node x0) (behead cpring).
Proof.
rewrite /cpring /orbit -orderSpred /= lastI rev_add_last; congr Adds.
by apply Inode; rewrite last_traject f_iter orderSpred (iter_order (Inode g)).
Qed.

Lemma head_long_cpring : long_cpring ->
  cpring = Seq (node x0) x0 (face (edge x0)) & (drop 3 cpring).
Proof.
move: cycle_rev_cpring; rewrite size_long_cpring head_cpring.
case: cpring => [|x' [|x [|y p]]] //= Hp _; rewrite !rev_adds in Hp.
do 3 rewrite -rot1_adds cycle_rot -?add_last_adds in Hp.
move/and3P: Hp => [Dy Dx _]; rewrite -(Inode g (eqP Dx)).
by rewrite -{5}(eqP Dy) Enode drop0.
Qed.

Lemma head_proper_cpring : proper_cpring ->
  cpring = Seq (node x0) x0 & (drop 2 cpring).
Proof.
case Hx0: long_cpring; first by rewrite head_long_cpring.
rewrite size_proper_cpring leq_eqVlt -size_long_cpring Hx0 orbF.
rewrite /cpring size_rev size_orbit /orbit; case/eqP=> <-.
by move/eqP: Hx0 => Dnx0; rewrite -{1}Dnx0 Eedge.
Qed.

End CpRing.

Section ExtConfig.

Variables (n0 : nat) (g : hypermap) (x0 : g).

(* We list all the assumptions on g here so that they appear in the standard *)
(* order, but most of the lemmas below only depend on a few assumptions. In  *)
(* particular, the map constructions do not depend on any assumption on g.   *)

Hypotheses (Hpg : planar g) (Hbg : bridgeless g).
Hypotheses (HgE : plain g) (HgN : quasicubic (rev (cpring x0))).
Hypotheses (Hcg : connected g) (Hrg : proper_cpring x0).

Remark Hg : ucycle_plain_quasicubic_connected (rev (cpring x0)).
Proof. repeat split; auto; apply ucycle_rev_cpring. Qed.

(* Reverse ring rotation; note that the map construction matches the ring   *)
(* rotation for arbitrary n0 (it is the identity if n0 >= (order node x0)). *)

Definition ecpR := PointedMap g (iter (order node x0 - n0) node x0).

Definition icpR (x : g) : ecpR := x.

Lemma cpring_ecpR : cpring ecpR = rot n0 (cpring x0).
Proof.
apply cpring_def; last by rewrite rev_rot ucycle_rotr; apply ucycle_rev_cpring.
rewrite /cpring -rev_rotr /rotr size_orbit /=; set m := order _ (node (node x0)).
have <-: m = order node x0 by apply: eq_card => x; rewrite -!cnode1.
case: (m - n0) (leq_subr n0 m) => [|n] Hn.
  by rewrite rot0 -/(cpring x0) head_cpring.
rewrite /rot rev_cat (take_sub (node (node x0))); last by rewrite size_orbit.
by rewrite rev_add_last /= /orbit -/m sub_traject // !iter_f.
Qed.

Lemma size_cpring_ecpR : size (cpring ecpR) = size (cpring x0).
Proof. by rewrite cpring_ecpR size_rot. Qed.

Lemma cubic_ecpR : quasicubic (rev (cpring ecpR)).
Proof.
apply: etrans HgN; apply: eq_subset => [x]; congr negb.
by rewrite cpring_ecpR !mem_rev mem_rot.
Qed.

(* Merging neighbors; this trivially produces a plain graph, but otherwise *)
(* it has very few properties; fortunately, we only need the preservation  *)
(* of face connectivity, since we only use the merge to build contract     *)
(* coloring maps. To make sure this property is always true, we must check *)
(* whether the neighbors are already merged, in which case we need to      *)
(* create a hyperedge to avoid the creation of a separate componenet.      *)
(*    The merge operation breaks both the cface and edge relation, but in  *)
(* the right direction for cface (the resulting map is more connected than *)
(* the base one), and it preserves the adj relation, which is enough for   *)
(* colorings.                                                              *)


Definition ecpA_edge x :=
  if negb (cface (edge x0) (node x0)) then edge x else
  if x =d x0 then edge (node (node x0)) else
  if x =d node (node x0) then edge x0 else edge x.

Definition ecpA_node x :=
  if x =d node x0 then x0 else
  if node x =d x0 then node (node x0) else node x.

Definition ecpA_face x :=
  if cface (edge x0) (node x0) then face x else
  if x =d edge x0 then node x0 else
  if face x =d node x0 then face (edge x0) else face x.

Lemma ecpAP : monic3 ecpA_edge ecpA_node ecpA_face.
Proof.
move=> x; rewrite /ecpA_edge /ecpA_face.
case (cface (edge x0) (node x0)); rewrite /= /ecpA_node.
case Dx: (x =d x0); first by rewrite Enode set11 (eqP Dx).
 case Dx': (x =d node (node x0)); rewrite -(inj_eqd (Inode g)) Eedge.
    by rewrite -(eqP Dx') set11 eqd_sym Dx.
  by rewrite Dx' Dx.
rewrite (inj_eqd (Iedge g)).
case Dx: (x =d x0); first by rewrite set11 (eqP Dx).
case Dfex: (face (edge x) =d node x0).
  by rewrite -(eqP Dfex) -(inj_eqd (Inode g)) !Eedge eqd_sym Dx set11.
by rewrite Dfex Eedge Dx.
Qed.

Definition ecpA_map := Hypermap ecpAP.

Definition ecpA := PointedMap ecpA_map (face (@edge ecpA_map (face (edge x0)))).

Definition icpA (x : g) : ecpA := x.

Lemma baseN_ecpA : fun_base icpA node node (set2 (node x0) (face (edge x0))).
Proof.
move=> x y; rewrite /icpA /= /eqdf /ecpA_node; move/norP=> [Hx1 Hx2].
by rewrite (monic2F_eqd (Enode g)) !(eqd_sym x) (negbE Hx1) (negbE Hx2).
Qed.

Lemma cpring_ecpA :
  cpring ecpA = if long_cpring x0 then behead (behead (cpring x0)) else cpring x0.
Proof.
case Hx0: (long_cpring x0).
  apply cpring_def; first by rewrite (head_long_cpring Hx0) /= ecpAP.
  apply/andP; split;
    last by move: (uniq_cpring x0);
    rewrite uniq_rev (head_long_cpring Hx0); case/and3P.
  move: (cycle_rev_cpring x0); rewrite (head_long_cpring Hx0) /= !rev_adds.
  do 4 rewrite -rot1_adds cycle_rot -?add_last_adds.
  rewrite /=; case/and3P; do 2 clear.
  have Eptr: ecpA_node (face (edge x0)) = node (node x0).
    rewrite /ecpA_node -(inj_eqd (Inode g)) Eedge set11.
    by case Dx0: (eqd x0 (node (node x0))) => //; rewrite -(eqP Dx0).
  case Dp: (rev (drop 3 (cpring x0))) => [|x p]; first by rewrite /eqdf /= Eptr.
  rewrite /= {3}/eqdf Eptr -(path_maps (d := ecpA) baseN_ecpA) /icpA ?maps_id //.
  rewrite belast_add_last -has_maps maps_id -(eq_has (mem_seq2 _ _)) has_sym /=.
  move: (uniq_cpring x0); rewrite (head_long_cpring Hx0) /=.
  case/and4P; do 2 (case/norP; clear); move=> Hfex0 _ Hnx0 _.
  rewrite -mem_rev Dp /= in Hfex0; rewrite -mem_rev Dp /= in Hnx0.
  by rewrite (negbE Hfex0) (negbE Hnx0).
apply cpring_def; first by move/eqP: Hx0 => Dx0; rewrite head_cpring /= ecpAP.
rewrite /ucycle uniq_rev /= uniq_cpring andbT.
move: Hx0 (cycle_rev_cpring x0) (uniq_cpring x0).
rewrite size_long_cpring head_cpring /= /eqdf /ecpA_node.
case: (behead (cpring x0)) => [|x [|y p]] //= _;
 rewrite !andbT !set11 !(inj_eqd (Inode g)) eqd_sym // /setU1 orbF.
case/andP; move/eqP=> <- {x}; clear; move/negPf=> Hx0.
by rewrite -(eqd_sym x0) Hx0 !set11.
Qed.

Definition sub2ifgt2 n := if n is S (S (S n')) then S n' else n.

Lemma size_cpring_ecpA : size (cpring ecpA) = sub2ifgt2 (size (cpring x0)).
Proof.
rewrite cpring_ecpA /=; case Hx0: (long_cpring x0).
  by rewrite head_long_cpring.
by move: Hx0; rewrite size_long_cpring; case: (size (cpring x0)) => [|[|[|n]]].
Qed.

Lemma baseF_ecpA :
  fun_base icpA face face (set2 (edge x0) (edge (node (node x0)))).
Proof.
move=> x y; rewrite /icpA /= /eqdf /ecpA_face; move/norP=> [Hx1 Hx2].
case (cface (edge x0) (node x0)); first done.
by rewrite (monic2F_eqd (Eface g)) !(eqd_sym x) (negbE Hx1) (negbE Hx2).
Qed.

Lemma ecpA_merge : cface (node ecpA) (node x0).
Proof.
rewrite /= ecpAP; case Hx02: (cface (edge x0) (node x0)).
  by rewrite /= /ecpA_face Hx02; rewrite cface1 in Hx02.
have Hx01: (cface (node x0) (edge (node (node x0)))).
  by rewrite cface1r Enode connect0.
case/connectP: Hx01; move=> p0; case/shortenP=> [p Hp Up _] {p0} Ep.
move: (Hp); rewrite -(@path_maps ecpA _ _ _ _ _ _ _ baseF_ecpA) /icpA ?maps_id.
  move=> {Hp} Hp; rewrite (Sface ecpA).
  apply connect_trans with (edge (node (node x0))).
    by apply/connectP; exists p.
  apply connect1; apply/eqP; rewrite /eqdf /= /ecpA_face Hx02.
  rewrite -(inj_eqd (Iface g)) Enode set11.
  by case: (node x0 =P face (edge x0)).
rewrite lastI Ep uniq_add_last in Up; move/andP: Up => [Hpx01 _].
rewrite -has_maps maps_id -(eq_has (mem_seq2 _ _)) has_sym /= (negbE Hpx01) orbF.
by apply/idP; move/mem_belast; move/(path_connect Hp); rewrite Sface Hx02.
Qed.

Lemma sub_cface_icpA : sub_rel (cface : rel g) (cface : rel ecpA).
Proof.
apply: connect_sub => [x y]; move/eqP=> <- {y}.
rewrite (@cface1 ecpA) /= {2}/ecpA_face.
case Hx02: (cface (edge x0) (node x0)); first by rewrite connect0.
have Hx01 := ecpA_merge; rewrite /= ecpAP in Hx01.
case: (x =P edge x0) => [Dx|_]; first by rewrite Dx (Sface ecpA).
by case: (face x =P node x0) => [->|_] //; rewrite connect0.
Qed.

Lemma cface_icpA : forall x y : g,
 (cface : rel ecpA) x y =
    cface x y || all (fband (seq2 (face (edge x0)) (node x0))) (seq2 x y).
Proof.
set a := fband (seq2 (face (edge x0)) (node x0)).
have: fun_adjunction (id : ecpA -> g) face face (setC a).
  apply: (strict_adjunction (Sface ecpA)) => //; try by move.
  - apply: setC_closed; exact: fbandF.
  - apply/subsetP => [x _]; apply/set0Pn; exists x; exact: set11.
  move=> x y; rewrite /id; move/negbE2=> Hx.
  symmetry; apply: baseF_ecpA; apply/orP; rewrite /icpA. 
  case; move/eqP=> Dx; case/idP: Hx; rewrite /a /= -{x}Dx ?fconnect1 //.
  by rewrite orbC cface1 Enode connect0.
case; rewrite /id /setC /=; move=> _ Ha x y; rewrite orbC.
case Hx: (a x); last by apply: Ha; rewrite Hx.
case Hy: (a y); last by rewrite Sface (Sface ecpA); apply: Ha; rewrite Hy.
rewrite /a /fband in Hx Hy; case/hasP: Hx => [x' Dx' Hxx'].
apply: {x Hxx'}(connect_trans (sub_cface_icpA Hxx')).
case/hasP: Hy => [y' Dy' Hyy']; rewrite Sface in Hyy'.
apply: {y Hyy'}connect_trans _ (sub_cface_icpA Hyy').
have Hx01 := ecpA_merge; rewrite /= ecpAP in Hx01.
move: Dx' Dy'; rewrite !mem_seq2.
by do 2 (case/orP; move/eqP=> <-); rewrite ?connect0 // (Sface ecpA).
Qed.

Lemma sub_adj_icpA : sub_rel (adj : rel g) (adj : rel ecpA).
Proof.
move=> x y; case/adjP=> [z Hxz Hzy]; apply/adjP.
exists z; apply: sub_cface_icpA; rewrite //= /ecpA_edge.
case Hx0: (cface (edge x0) (node x0)) => //=.
case: (z =P x0) => [Dz|_]; first by rewrite cface1 Enode -(same_cface Hx0) -Dz.
case: (z =P node (node x0)) => [Dz|_]; last done.
by rewrite (same_cface Hx0) -[node x0]Enode -Dz -cface1.
Qed.

(* The two basic extension constructions. Since they both add an edge pair, *)
(* they share the common underlying dart set construction. We use a special *)
(* purpose concrete type, rather than the general set sum, so that case     *)
(* analysis will be better behaved.                                         *)

Section EcpDatum.

Variable A : Set.

Inductive ecp_datum : Set := IcpX | IcpXe | Icp (x : A).

Lemma ecp_inj : injective Icp. Proof. by move=> x y [Dx]. Qed.

End EcpDatum.

Section EcpElement.

Variable d : dataSet.

Definition ecp_eq (x y : ecp_datum d) : bool :=
  match x, y with
  | IcpX, IcpX => true
  | IcpXe, IcpXe => true
  | Icp x', Icp y' => x' =d y'
  | _, _ => false
  end.

Lemma ecp_eqP : reflect_eq ecp_eq.
Proof.
move=> [||x] [||y]; first [by constructor | by apply: (iffP eqP) => [<-|[]]].
Qed.

Canonical Structure ecp_element := DataSet ecp_eqP.

End EcpElement.

Section EcpDart.

Variable d : finSet.

Definition ecp_enum := Seq (IcpX d) (IcpXe d) & (maps (@Icp d) (enum d)).

Lemma ecp_enumP : forall x, count (set1 x) ecp_enum = 1.
Proof.
move=> x; rewrite /= count_maps.
case: x => [||x] /=; last exact: count_set1_enum; congr S; exact: count_set0.
Qed.
Canonical Structure ecp_dart := FinSet ecp_enumP.

Lemma card_ecp : card ecp_dart = S (S (card d)).
Proof. by rewrite !cardA /= size_maps. Qed.

End EcpDart.

Definition ecp_edge x :=
  match x with
  | IcpX => IcpXe g
  | IcpXe => IcpX g
  | Icp x' => Icp (edge x')
  end.

Definition ecpU_node x :=
  match x with
  | IcpX => IcpXe g
  | IcpXe => Icp (node (node x0))
  | Icp y => if eqd y (node x0) then IcpX g else Icp (node y)
  end.

Definition ecpU_face x :=
  match x with
  | IcpX => IcpX g
  | IcpXe => Icp (node x0)
  | Icp y => if eqd (face y) (node x0) then IcpXe g else Icp (face y)
  end.

Lemma ecpUP : monic3 ecp_edge ecpU_node ecpU_face.
Proof.
move=> [||x] //=; first by rewrite set11.
case Hfex: (face (edge x) =d node x0); first by rewrite /= -(eqP Hfex) Eedge.
by rewrite /= Hfex Eedge.
Qed.

Definition ecpU_map := Hypermap ecpUP.

Definition ecpU := PointedMap ecpU_map (IcpX g).

Definition icpU : g -> ecpU := @Icp g.

Lemma icpU_inj : injective icpU. Proof. exact: ecp_inj. Qed.

Lemma icpU_edge : forall x, icpU (edge x) = edge (icpU x). Proof. done. Qed.

(* The N step is a K step applied immediately to the left of the ring head.   *)
(* We get the K step below by composition with R steps, and the H and Y steps *)
(* by composition with a U step.                                              *)

Definition ecpN_node x :=
  match x with
  | IcpX =>  if long_cpring x0 then Icp (node x0) else IcpX g
  | IcpXe => Icp (face (edge x0))
  | Icp y => if y =d x0 then IcpXe g else
             if node (node y) =d x0 then IcpX g else Icp (node y)
  end.

Definition ecpN_face x :=
  match x with
  | IcpX =>  Icp x0
  | IcpXe => if long_cpring x0 then Icp (face (edge (face (edge x0)))) else IcpX g
  | Icp y => if y =d edge (face (edge x0)) then IcpXe g else
             if y =d edge (node x0) then IcpX g else Icp (face y)
  end.

Lemma ecpNP : monic3 ecp_edge ecpN_node ecpN_face.
Proof.
move=> [||x]; rewrite /= ?set11 //.
case Hx0: (long_cpring x0) => /=; last by rewrite Hx0.
  by rewrite -(inj_eqd (Inode g)) !Eedge set11 (negbE Hx0).
rewrite !(inj_eqd (Iedge g)) -(monic2F_eqd (Enode g)).
case Dnx: (node x =d x0); first by rewrite /= -(eqP Dnx) Enode.
case Dx: (x =d node x0) => /=.
  by rewrite /= /long_cpring eqd_sym -(monic2F_eqd (Enode g)) -(eqP Dx) Dnx.
by rewrite -(inj_eqd (Inode g)) Eedge Dx Dnx.
Qed.

Definition ecpN_map := Hypermap ecpNP.

Definition ecpN := PointedMap ecpN_map (IcpX g).

Definition icpN : g -> ecpN := @Icp g.

Lemma icpN_inj : injective icpN. Proof. exact: ecp_inj. Qed.

Lemma icpN_edge : forall x, icpN (edge x) = edge (icpN x). Proof. done. Qed.

Lemma plain_ecpU : plain ecpU.
Proof.
apply/plainP; move=> [||x] // _; case: (plainP HgE x) => // [Dx Hx] /=.
by rewrite Dx; split.
Qed.

Lemma plain_ecpN : plain ecpN.
Proof. exact plain_ecpU. Qed.

Lemma baseN_ecpU : fun_base icpU node node (set1 (Icp (node x0))).
Proof. by move=> x y; rewrite /setC1 /eqd /eqdf /= eqd_sym; move/negPf=> ->. Qed.

Lemma icpU_node : forall x,
  negb (seq1 (node x0) x) -> node (icpU x) = icpU (node x).
Proof. by move=> x; rewrite mem_seq1 => HxnX; rewrite /= eqd_sym (negbE HxnX). Qed.

Lemma cpring_ecpU : cpring ecpU = Seq (node ecpU) ecpU & (maps icpU (cpring x0)).
Proof.
apply: cpring_def => //; apply/andP; split.
move: (uniq_cpring x0) (cycle_rev_cpring x0); rewrite head_cpring /=.
  rewrite !rev_adds -maps_rev -mem_rev -uniq_rev.
  move: (rev (behead (cpring x0))) => p; move/andP=> [Up _].
  do 4 rewrite -rot1_adds cycle_rot -?add_last_adds.
  rewrite /= {2}/eqdf /= !set11 /= -maps_add_last.
  case: p Up => [|x p] Up //=; rewrite (path_maps (d := ecpU) baseN_ecpU) //.
  by rewrite belast_add_last -has_maps has_set1 (mem_maps icpU_inj).
rewrite uniq_rev /= /setU1 /= (uniq_maps icpU_inj) uniq_cpring andbT.
by apply/andP; split; apply/mapsP; case.
Qed.

Lemma size_cpring_ecpU : size (cpring ecpU) = S (S (size (cpring x0))).
Proof. by rewrite cpring_ecpU /= size_maps. Qed.

Lemma cubic_ecpU : quasicubic (rev (cpring ecpU)).
Proof.
rewrite cpring_ecpU; apply/cubicP => [u]; rewrite /setC mem_rev /= /setU1.
case: u => [||x] //=; rewrite (mem_maps icpU_inj) -mem_rev; move=> Hx.
case: (cubicP HgN _ Hx) => [Dn3x Hn1x]; rewrite mem_rev mem_cpring in Hx.
case: (x =P node x0) => [Dx|_]; first by rewrite Dx fconnect1 in Hx.
split; last done; rewrite /= (inj_eqd (Inode g)).
case: (x =P x0) => [Dx|_]; first by rewrite Dx connect0 in Hx.
rewrite /= (inj_eqd (Inode g)) Dn3x.
by case: (node x =P x0) => [Dnx|_] //; rewrite -Dnx Snode fconnect1 in Hx.
Qed.

Lemma baseN_ecpN :
  fun_base icpN node node (set2 (Icp x0) (Icp (face (edge (face (edge x0)))))).
Proof.
move=> x y; rewrite /setC /icpN /set2 /eqd /eqdf /= -!(eqd_sym x).
rewrite -!(monic2F_eqd (Enode g)).
by move/norP=> [Hx Hnnx]; rewrite (negbE Hx) (negbE Hnnx).
Qed.

Lemma cpring_ecpN :
 cpring ecpN =
   if long_cpring x0 then
      Seq (icpN (node x0)) ecpN & (maps icpN (drop 3 (cpring x0)))
   else seq1 ecpN.
Proof.
case Hx0: (long_cpring x0);
 last by apply cpring_def; rewrite /ucycle /= /eqdf /ecpN_node Hx0 ?set11.
apply cpring_def; first by rewrite /= Hx0.
apply/andP; split.
move: (uniq_cpring x0) (cycle_rev_cpring x0).
rewrite (head_long_cpring Hx0) /= drop0; move: (drop 3 (cpring x0)) => p.
  rewrite !rev_adds -maps_rev /setU1 -!(mem_rev p) -uniq_rev (negbE Hx0) /=.
  move/rev: p => p; case/and4P; move/norP=> [Hnx0 Unx0]; move/norP=> [_ Ux0] _.
  move=> Up; do 5 rewrite -rot1_adds cycle_rot -?add_last_adds.
  rewrite (cycle_path x0) (cycle_path (IcpX g)) /= last_maps.
  case/and4P; move/eqP=> Ep _ _ Hp.
  move: baseN_ecpN => HbN; rewrite /icpN /= in HbN.
  rewrite {1 2}/eqdf {1 2}/ecpN_node Hx0 !set11 /=.
  rewrite (@path_maps ecpN _ _ _ _ _ _ _ HbN).
    by rewrite -(inj_eqd (Inode g)) Ep Hp (negbE Hx0) Eedge !set11.
  rewrite -Ep Enode -has_maps -(eq_has (mem_seq2 _ _)) has_sym /= orbF.
  rewrite !(mem_maps icpN_inj); apply/orP; case.
    by move/mem_belast; rewrite /= /setU1 eqd_sym (negbE Hnx0) (negbE Ux0).
  have Up': uniq (Adds (node x0) p) by rewrite /= Unx0.
  by apply: negP; rewrite lastI uniq_add_last in Up'; case/andP: Up'.
move: (uniq_cpring x0); rewrite (head_long_cpring Hx0) uniq_rev /= drop0.
move: (drop 3 (cpring x0)) => p; rewrite /setU1 /= (uniq_maps icpN_inj).
rewrite (mem_maps icpN_inj) orbA orbC; case/and4P.
by move/norP=> [Unx0 _] _ _ Up; rewrite Unx0 Up /= andbT; apply/mapsP; case.
Qed.

Lemma rot1_cpring_ecpN :
  rot 1 (cpring ecpN) = Adds ecpN (maps icpN (drop 2 (rot 1 (cpring x0)))).
Proof.
rewrite cpring_ecpN; case Hx0: (long_cpring x0).
  by rewrite (head_long_cpring Hx0) /= !drop0 maps_cat.
by move: Hx0; rewrite size_long_cpring; case: (cpring x0) => [|x [|y [|z p]]].
Qed.

Lemma size_cpring_ecpN : size (cpring ecpN) = S (pred (pred (size (cpring x0)))).
Proof.
rewrite -(size_rot 1) rot1_cpring_ecpN drop_behead.
by rewrite /= size_maps !size_behead size_rot.
Qed.

Lemma cubic_ecpN : quasicubic (rev (cpring ecpN)).
Proof.
pose qXe := seq3 (edge ecpN) (icpN (face (edge x0))) (icpN x0).
have HqXe: (cubicb qXe).
  have HqXeN: (fcycle node qXe).
    rewrite /= /eqdf /= !set11 -(inj_eqd (Inode g)) Eedge -(eqd_sym x0).
    by rewrite (negbE Hrg) set11.
  apply/subsetP => u Hu; rewrite /order_set (order_cycle HqXeN) //.
  by rewrite /= /setU1 /eqd /= -(monic2F_eqd (Enode g)) eqd_sym (negbE Hrg).
apply/cubicP => u; rewrite /setC mem_rev -(mem_rot 1) rot1_cpring_ecpN.
case HqXeu: (qXe u); first by clear; exact (cubicP HqXe _ HqXeu).
case: u HqXeu => [||x] //=.
rewrite /setU1 orbF (mem_maps icpN_inj) /= {1 2}/eqd /= !(eqd_sym x).
move/norP=> [Hfex0x Hx0x] Hx'; rewrite (negbE Hx0x).
have Hx: negb (rev (cpring x0) x).
  case Hx0': (long_cpring x0).
    move: Hx'; rewrite (head_long_cpring Hx0') rot1_adds /= drop0 mem_add_last.
    by rewrite /= mem_rev /= /setU1 (negbE Hx0x) (negbE Hfex0x).
  rewrite mem_rev mem_cpring fconnect_orbit /orbit.
  move: (Hx0') {Hx'}; rewrite size_long_cpring size_cpring -orderSpred /=.
  rewrite /setU1 (negbE Hx0x); case: (pred (order node x0)) => [|[|n]] //= _.
  by move/eqP: Hx0' => <-; rewrite /setU1 orbF.
move: (cubicP HgN _ Hx) => [Dn3x Hn1x]; rewrite mem_rev mem_cpring in Hx.
case Hnnx: (node (node x) =d x0).
  by rewrite 2!cnode1r (eqP Hnnx) connect0 in Hx.
rewrite eqd_sym -(monic2F_eqd (Enode g)) in Hfex0x.
split; last done; rewrite /= (negbE Hfex0x) Dn3x eqd_sym (negbE Hx0x) /= Hnnx.
by rewrite Dn3x (negbE Hfex0x).
Qed.

Lemma connected_ecpU : connected ecpU.
Proof.
apply/eqP; case (n_comp_connect (Sglink ecpU) (IcpX g)); symmetry.
have HXe: gcomp ecpU (edge ecpU) by apply connect1; apply glinkE.
have Hnnx0: gcomp ecpU (icpU (node (node x0))).
  by do 2 apply: (connect_trans (connect1 (glinkN _)) _); rewrite /= connect0.
apply: eq_n_comp_r => [[||x]]; rewrite /setA //; first exact: connect0.
case: (connected_clink Hcg x (node (node x0))) => p.
elim: p x => [|y p Hrec] x /=; first by move=> _ Dx; rewrite Dx.
case/andP; case/clinkP=> [Dx|Dy] Hp Ep; move: {p Hrec Hp Ep}(Hrec _ Hp Ep) => Hrec.
  move: {Hrec}(connect_trans Hrec (connect1 (glinkN _))) => /=.
  by rewrite -Dx; case: (y =P node x0) => [Dy|_] // _; rewrite Dx Dy.
rewrite (Sglink ecpU); apply: (connect_trans (connect1 (glinkF _)) _).
by rewrite (Sglink ecpU) /= Dy; case (y =d node x0).
Qed.

Lemma connected_ecpN : connected ecpN.
Proof.
apply/eqP; case (n_comp_connect (Sglink ecpN) ecpN); symmetry.
have HXe: (gcomp ecpN (edge ecpN)) by apply connect1; apply glinkE.
have Hx0: (gcomp ecpN (icpN x0)).
  by apply: (connect_trans (connect1 (glinkF _)) _); rewrite /= connect0.
have Hfex0: (gcomp ecpN (icpN (face (edge x0)))).
  apply: (connect_trans (connect_trans HXe (connect1 (glinkN _))) _).
  by rewrite /= connect0.
have Hnx0: (gcomp ecpN (icpN (node x0))).
  case Hx0p: (long_cpring x0); last by move/eqP: Hx0p => <-.
  by apply: (connect_trans (connect1 (glinkN _)) _); rewrite /= Hx0p connect0.
apply: eq_n_comp_r => [[||x]]; rewrite /setA //; first exact: connect0.
case: (connected_clink Hcg x x0) => p.
elim: p x => [|y p Hrec] x /=; first by move=> _ ->.
case/andP; case/clinkP=> [Dx|Dy] Hp; move/(Hrec _ Hp) {p Hrec Hp} => Hrec.
  move: {Hrec}(connect_trans Hrec (connect1 (glinkN _))) => /=.
  rewrite -Dx; case: (y =P x0) => [Dy|_]; first by rewrite Dx Dy.
  by case: (node x =P x0) => [Dnx|_]; first by rewrite -[x]Enode Dnx.
rewrite (Sglink ecpN); apply: (connect_trans (connect1 (glinkF _)) _).
rewrite (Sglink ecpN) /= Dy; case: (x =d edge (face (edge x0))) => //.
by case (x =d edge (node x0)); first by rewrite connect0.
Qed.

Lemma cface_ecpU : cface ecpU =1 eqd ecpU.
Proof. by move=> u; rewrite -mem_seq1; apply: fconnect_cycle. Qed.

Lemma closedF_ecpU : fclosed face (setC1 ecpU).
Proof.
by move=> u v; move/(_ =P v)=> <- {v}; rewrite /setC1 -!cface_ecpU -cface1r.
Qed.

Lemma adjnF_ecpU : fun_adjunction icpU face face (setC1 ecpU).
Proof.
pose h u (_ : setC1 ecpU u) := if u is Icp x then x else node x0.
apply: (intro_adjunction (Sface _) closedF_ecpU h).
  case=> [||x] //= _.
    split; first by apply connect1; rewrite /eqdf /= set11.
    case=> //= y _; rewrite {1}/eqdf {1}/eqd /=; move/eqP=> <-; exact: connect0.
  split; first exact: connect0.
  case=> [||y] //= _; rewrite {1}/eqdf /=; case: (face x =P node x0) => //.
    by move=> <- _; apply fconnect1.
  by clear; move/(_ =P y)=> <-; apply fconnect1.
move=> x /= _; split; first exact: connect0.
move=> y; move/eqP=> <- {y}; rewrite (@cface1 ecpU) /=.
case: (face x =P node x0) => [Dx|_]; last by rewrite connect0.
by rewrite (cface1 (g := ecpU)) Dx /= connect0.
Qed.

Lemma cface_icpU : forall x y, cface (icpU x) (icpU y) = cface x y.
Proof. by case: adjnF_ecpU => [_ H] x y; rewrite H. Qed.

Lemma adj_ecpU : adj ecpU =1 fband (seq1 (icpU (node x0))).
Proof.
move=> u; rewrite /adj /orbit /order (eq_card cface_ecpU) card1 /=.
by rewrite /rlink cface1 Sface.
Qed.

Lemma adj_icpU : forall x y, adj (icpU x) (icpU y) = adj x y.
Proof.
move=> x y; apply/adjP/adjP => [[[||z] Hxz Hzy]|[z Hxz Hzy]].
- by rewrite Sface cface_ecpU in Hxz.
- by rewrite /rlink /= cface_ecpU in Hzy.
- by exists z; rewrite /rlink -cface_icpU.
by rewrite /rlink -!cface_icpU in Hxz Hzy; exists (icpU z).
Qed.

Lemma fband_icpU : forall u, {x : g | cface u (icpU x)} + {cface ecpU u}.
Proof.
move=> u; case Hu: (cface ecpU u); [ by right | left; move: Hu ].
rewrite cface_ecpU; case: u => [||x] // _.
  by exists (node x0); rewrite cface1 /= cface_icpU connect0.
by exists x; rewrite cface_icpU connect0.
Qed.

Lemma bridgeless_ecpU : bridgeless ecpU.
Proof.
have HXF: cface ecpU (edge ecpU) = false by rewrite cface_ecpU.
apply/set0P => [[||x]] //; first by rewrite Sface.
by case: adjnF_ecpU => /= [_ EfF]; rewrite -EfF // (set0P Hbg).
Qed.

Lemma planar_ecpU : planar ecpU.
Proof.
have Hcp: fcard face ecpU = S (fcard face g).
  rewrite (n_compC (set1 ecpU)) -add1n; congr addn.
    rewrite -(eq_n_comp_r cface_ecpU) n_comp_connect //; apply: Sface.
  have EecpUF := adjunction_n_comp _ (Sface _) (Sface _) closedF_ecpU adjnF_ecpU.
  by apply: (etrans EecpUF); apply: eq_n_comp_r.
have HecpU: ucycle_plain_quasicubic_connected (rev (cpring ecpU)).
  split; [split; last exact: ucycle_rev_cpring | exact connected_ecpU].
  split; [exact plain_ecpU | exact cubic_ecpU].
rewrite (quasicubic_Euler HecpU).
rewrite [card ecpU](card_ecp g) Hcp size_rev size_cpring_ecpU.
rewrite head_cpring rev_adds headI mulnC /= !doubleS.
move: Hpg; rewrite (quasicubic_Euler Hg).
by rewrite size_rev head_cpring rev_adds headI mulnC /=; NatNorm.
Qed.

Lemma cface_ecpN : cface ecpN (icpN x0).
Proof. apply connect1; apply: set11. Qed.

Lemma adjnF_ecpN : fun_adjunction icpN face face ecpN.
Proof.
pose h u (_ : ecpN u) :=
  match u with Icp x => x | IcpX => x0 | IcpXe => edge (face (edge x0)) end.
apply: (intro_adjunction (Sface _) _ h)  => //.
  case=> [||x] /= _.
  - split; first by apply connect1; rewrite /eqdf /= !set11.
    case=> //= y _; rewrite {1}/eqdf {1}/eqd /=; move/eqP=> <-; exact: connect0.
  - split; first by rewrite (@cface1r ecpN) /= set11 connect0.
    case=> [||y] //= _; rewrite ?connect0 // {1}/eqdf /=;
      case Hx0: (long_cpring x0) => // Dy.
      by move/eqP: Hx0 => ->; rewrite cface1 Enode connect0.
  by rewrite cface1 ((_ =P y) Dy) connect0.
  split; first exact: connect0.
  case=> [||y] //= _; rewrite {1}/eqdf /=;
    case: (x =P edge (face (edge x0))) => [Dx|_] //; rewrite -?{}Dx ?connect0 //;
    case: (x =P edge (node x0)) => [Dx|_] //.
  - by rewrite -[x0]Enode -Dx fconnect1.
  by move/(_ =P y) => Dy; rewrite -Dy fconnect1.
move=> x /= _; split; first exact: connect0.
move=> y; move/eqP=> <- {y}; rewrite (@cface1 ecpN) /=.
case: (x =P edge (face (edge x0))) => [Dx|_].
  rewrite (@cface1 ecpN) /= -Dx.
  case Hx0: (long_cpring x0); first by rewrite connect0.
  by move/eqP: Hx0 => Dx0; rewrite (@cface1 ecpN) Dx Dx0 Enode /= connect0.
case: (x =P edge (node x0)) => [Dx|_]; last by rewrite connect0.
by rewrite (@cface1 ecpN) Dx Enode /= connect0.
Qed.

Lemma cface_icpN : forall x y, cface (icpN x) (icpN y) = cface x y.
Proof. by move: adjnF_ecpN => [_ H] x y; rewrite H. Qed.

Lemma adj_icpN : 
  let adjx0 x y := cface (edge (face (edge x0))) x && cface x0 y in
  forall x y, adj (icpN x) (icpN y) = or3b (adj x y) (adjx0 x y) (adjx0 y x).
Proof.
move=> /= x y; apply/adjP/or3P => [[[||z] Hxz Hzy]|].
- constructor 3; apply/andP; split.
    by rewrite -cface_icpN cface1 /= set11.
  by rewrite cface1r /= cface_icpN Sface in Hxz |- *.
- constructor 2; apply/andP; split.
    by rewrite -cface_icpN cface1 Sface /= set11.
  by rewrite /rlink cface1 /= cface_icpN in Hzy |- *.
- by constructor 1; apply/adjP; exists z; rewrite /rlink -cface_icpN.
case.
- by move/adjP=> [z Hxz Hzy]; exists (icpN z); rewrite /rlink /= cface_icpN.
- move/andP=> [Hzx Hzy]; exists (edge ecpN).
    by rewrite Sface -cface_icpN cface1r /= set11 in Hzx.
  by rewrite /rlink cface1 /= cface_icpN.
move/andP=> [Hzy Hzx]; exists (ecpN : ecpN).
  by rewrite Sface cface1 /= cface_icpN.
by rewrite -cface_icpN cface1 /= set11 in Hzy.
Qed.

Lemma sub_adj_icpN : forall x y, adj x y -> adj (icpN x) (icpN y).
Proof. by move=> x y Hxy; rewrite adj_icpN Hxy. Qed.

Lemma fband_icpN : forall u, {x : g | cface u (icpN x)}.
Proof.
case=> [||x].
- by exists x0; rewrite cface1 /= cface_icpN connect0.
- by exists (edge (face (edge x0))); rewrite cface1r /= set11 connect0.
by exists x; rewrite cface_icpN connect0.
Qed.

Lemma planar_ecpN : planar ecpN.
Proof.
have Hcp: fcard face ecpN = fcard face g.
  exact: (adjunction_n_comp _ (Sface _) (Sface _) _ adjnF_ecpN).
have HecpN: ucycle_plain_quasicubic_connected (rev (cpring ecpN)).
  split; [split; last exact: ucycle_rev_cpring | exact connected_ecpN ].
  split; [ exact plain_ecpN | exact cubic_ecpN ].
rewrite (quasicubic_Euler HecpN) [card ecpN](card_ecp g) Hcp size_rev.
rewrite size_cpring_ecpN head_cpring rev_adds headI /= !doubleS !addSn.
move: Hpg; rewrite (quasicubic_Euler Hg).
rewrite size_rev size_cpring head_cpring rev_adds headI /=.
case: (order node x0) (orderSpred node x0) (iter_order (Inode g) x0) => //.
by case=> [|n] /= _ Dnx0; [case/eqP: Hrg | rewrite !doubleS !addSn !addnS].
Qed.

End ExtConfig.

Lemma ecpR1_eq : forall (g : hypermap) x0, (ecpR 1 x0) = face (edge x0) :> g.
Proof. by move=> g x0; rewrite /ecpR /= subn1 -{3}(f_finv (Inode g) x0) Enode. Qed.

Section CompExtConfig.

Variables (n0 : nat) (g : hypermap) (x0 : g).

Hypotheses (Hpg : planar g) (Hbg : bridgeless g).
Hypotheses (HgE : plain g) (HgN : quasicubic (rev (cpring x0))).
Hypotheses (Hcg : connected g) (Hrg : proper_cpring x0).
Hypothesis Urg : simple (cpring x0).

Definition ecpR' := ecpR (pred (order node x0)) x0.

Definition icpR' : g -> ecpR' := icpR _ _.

Lemma ecpR'_eq : ecpR' = node x0 :> g.
Proof. by rewrite /ecpR' /ecpR /= -orderSpred /= subSnn. Qed.

Definition ecpK := ecpR 1 (ecpN ecpR').

Definition icpK x : ecpK := icpR 1 (ecpN ecpR') (icpN ecpR' (icpR' x)).

Lemma size_cpring_ecpK : size (cpring ecpK) = S (pred (pred (size (cpring x0)))).
Proof.
by rewrite /ecpK size_cpring_ecpR size_cpring_ecpN /ecpR' size_cpring_ecpR /=.
Qed.

Lemma icpK_inj : injective icpK. Proof. by move=> x y [Dx]. Qed.

Lemma icpK_edge : forall x, edge (icpK x) = icpK (edge x). Proof. done. Qed.

Lemma cpring_ecpK :
  cpring ecpK = Adds (node ecpK) (maps icpK (drop 2 (cpring x0))).
Proof.
rewrite /ecpK cpring_ecpR rot1_cpring_ecpN ecpR1_eq Eedge.
congr (Adds _ (maps _ (drop _ _))).
rewrite /ecpR' cpring_ecpR -subn1 -size_cpring; apply: rot_rotr.
Qed.

Lemma cface_icpK : forall x y, cface (icpK x) (icpK y) = cface x y.
Proof. exact (cface_icpN ecpR'). Qed.

Lemma adj_icpK :
  let adjx0 x y := cface (edge x0) x && cface (node x0) y in
  forall x y, adj (icpK x) (icpK y) = or3b (adj x y) (adjx0 x y) (adjx0 y x).
Proof.
by move=> *; apply: (etrans (adj_icpN ecpR' _ _)); rewrite ecpR'_eq Enode.
Qed.

Lemma sub_adj_icpK : forall x y, adj x y -> adj (icpK x) (icpK y).
Proof. by move=> x y Hxy; rewrite adj_icpK Hxy. Qed.

Lemma cface_node_ecpK : cface (node ecpK) (icpK (node x0)).
Proof. rewrite /ecpK ecpR1_eq Eedge ecpR'_eq; apply: cface_ecpN. Qed.

Lemma cface_ecpK : cface ecpK (icpK (face (edge x0))).
Proof.
rewrite /ecpK ecpR1_eq ecpR'_eq /= Enode.
case Hx0: (long_cpring (node x0)); first exact: connect0.
apply: connect1; apply/eqP => /=; move/eqP: Hx0 => Dx0.
by rewrite -[node x0]Enode -Dx0 Enode.
Qed.

Lemma fband_icpK : forall u, {x : g | cface u (icpK x)}.
Proof. exact: fband_icpN. Qed.

Definition ecpY := ecpN (ecpU x0).

Lemma plain_ecpY : plain ecpY.
Proof. by do 2 apply: plain_ecpN. Qed.

Lemma cubic_ecpY : quasicubic (rev (cpring ecpY)).
Proof. apply: cubic_ecpN => //; exact: cubic_ecpU. Qed.

Lemma size_cpring_ecpY : size (cpring ecpY) = S (size (cpring x0)).
Proof. by rewrite /ecpY size_cpring_ecpN size_cpring_ecpU /=. Qed.

Lemma planar_ecpY : planar ecpY.
Proof.
apply: planar_ecpN => //.
- exact: planar_ecpU.
- exact: plain_ecpU.
- exact: cubic_ecpU.
exact: connected_ecpU.
Qed.

Lemma connected_ecpY : connected ecpY.
Proof. apply: connected_ecpN; exact: connected_ecpU. Qed.

Definition icpY x : ecpY := icpN _ (icpU x0 x).

Lemma icpY_inj : injective icpY. Proof. by move=> x y [Dx]. Qed.

Lemma icpY_edge : forall x, edge (icpY x) = icpY (edge x). Proof. done. Qed.

Lemma icpY_node : forall x, negb (seq2 (node x0) x0 x) ->
  node (icpY x) = icpY (node x).
Proof.
move=> x; rewrite mem_seq2; move/norP=> [HxnX HxX].
rewrite /= (eqd_sym x) (negbE HxnX) /= (inj_eqd (Inode g)).
by rewrite (eqd_sym x) (negbE HxX).
Qed.

Lemma drop2_cpring_ecpY : drop 2 (cpring ecpY) = maps icpY (behead (cpring x0)).
Proof.
by rewrite /ecpY cpring_ecpN cpring_ecpU head_cpring /= !drop0 -maps_comp.
Qed.

Lemma cpring_ecpY :
  cpring ecpY = Seq (node ecpY) ecpY & (maps icpY (behead (cpring x0))).
Proof. by rewrite -drop2_cpring_ecpY -head_proper_cpring. Qed.

Lemma cface_icpY : forall x y, cface (icpY x) (icpY y) = cface x y.
Proof. by move=> x y; rewrite /icpY /ecpY cface_icpN cface_icpU. Qed.

Lemma adj_icpY : forall x y, adj (icpY x) (icpY y) = adj x y.
Proof.
by move=> *; rewrite /icpY /ecpY adj_icpN adj_icpU !cface_ecpU /= !andbF !orbF.
Qed.

Lemma cface_node_ecpY : cface (node ecpY) (icpY (node x0)).
Proof. rewrite cface1; apply: (etrans (cface_icpY _ _)); exact: connect0. Qed.

Lemma cface_ecpY : cface ecpY =1 seq2 ecpY (face ecpY).
Proof. exact: fconnect_cycle. Qed.

Lemma adj_ecpY : adj ecpY =1 fband (maps icpY (seq2 (node x0) x0)).
Proof.
move=> u; apply/adjP/hasP => [] [v Hv Huv].
  rewrite cface_ecpY mem_seq2 in Hv; case/orP: Hv Huv; move/eqP=> <- Hu.
    exists (icpY x0); first by rewrite (mem_maps icpY_inj) mem_seq2 set22.
    by rewrite /rlink cface1 Sface /= Enode (negbE Hrg) in Hu.
  exists (icpY (node x0)); first by rewrite (mem_maps icpY_inj) mem_seq2 set21.
  by rewrite /rlink cface1 Sface in Hu.
exists (node v); last by rewrite /rlink cface1 Enode Sface.
rewrite cface_ecpY mem_seq2 {Huv}; apply/orP.
repeat case/setU1P: Hv => [<-|Hv] //=; first by rewrite set11; right.
by left; rewrite (negbE Hrg) /= !set11.
Qed.

Lemma fband_icpY : forall u, {x : g | cface u (icpY x)} + {cface ecpY u}.
Proof.
move=> u; case: (fband_icpN u) => [v Huv].
case: (fband_icpU v) => [[x Hxv]|Hv]; [ left | right ].
  by exists x; rewrite (same_cface Huv) /icpY cface_icpN.
rewrite cface1 Sface (same_cface Huv) Sface.
by rewrite -(cface_icpN (ecpU x0)) in Hv.
Qed.

Lemma bridgeless_ecpY : bridgeless ecpY.
Proof.
have Hu0 := cface_ecpY (edge ecpY).
have Hfu0 := cface_ecpY (edge (face ecpY)); rewrite cface1 in Hfu0.
apply/set0P => [[||[||x]]] //; try by rewrite Sface.
by move: (set0P Hbg x); rewrite -cface_icpY.
Qed.

Definition ecpH := ecpN ecpY.

Lemma plain_ecpH : plain ecpH.
Proof. apply: plain_ecpN; exact plain_ecpY. Qed.

Lemma cubic_ecpH : quasicubic (rev (cpring ecpH)).
Proof. apply: cubic_ecpN => //; exact cubic_ecpY. Qed.

Lemma size_cpring_ecpH : size (cpring ecpH) = size (cpring x0).
Proof. by rewrite /ecpH size_cpring_ecpN size_cpring_ecpY head_cpring. Qed.

Lemma planar_ecpH : planar ecpH.
Proof.
apply: planar_ecpN => //.
- exact planar_ecpY.
- exact plain_ecpY.
- exact cubic_ecpY.
exact connected_ecpY.
Qed.

Lemma connected_ecpH : connected ecpH.
Proof. apply: connected_ecpN; exact connected_ecpY. Qed.

Definition icpH x : ecpH := icpN _ (icpY x).

Lemma icpH_inj : injective icpH. Proof. by move=> x y [Dx]. Qed.

Lemma icpH_edge : forall x, edge (icpH x) = icpH (edge x). Proof. done. Qed.

Lemma icpH_node : forall x, negb (seq3 (node x0) x0 (face (edge x0)) x) ->
  node (icpH x) = icpH (node x).
Proof.
move=> x; rewrite mem_seq3; case/norP=> [HxnX]; move/norP=> [HxX HxfeX].
rewrite /= (eqd_sym x) (negbE HxnX) /=.
do 2 rewrite (inj_eqd (Inode g)) (eqd_sym x) (negbE HxX) /=.
by rewrite (inj_eqd (Inode g)) (monic2F_eqd (Enode g)) (eqd_sym x) (negbE HxfeX).
Qed.

Lemma cface_icpH : forall x y, cface (icpH x) (icpH y) = cface x y.
Proof. by move=> x y; rewrite /icpH /ecpH cface_icpN cface_icpY. Qed.

Lemma adj_icpH : forall x y, adj (icpH x) (icpH y) = adj x y.
Proof.
move=> *; rewrite /icpH /ecpH adj_icpN adj_icpY !cface_ecpY.
by rewrite andbC orbC {1}[andb]lock andbC -lock.
Qed.

Lemma drop2_cpring_ecpH : drop 2 (cpring ecpH) = maps icpH (drop 2 (cpring x0)).
Proof.
rewrite /ecpH cpring_ecpN size_long_cpring size_cpring_ecpY.
rewrite (drop_behead 3) -f_iter -drop_behead drop2_cpring_ecpY.
by case: (cpring x0) => [|y1 [|y2 [|y3 r]]] //=; rewrite -maps_comp.
Qed.

Lemma cpring_ecpH :
  cpring ecpH = Seq (node ecpH) ecpH & (maps icpH (drop 2 (cpring x0))).
Proof.
rewrite -drop2_cpring_ecpH -head_proper_cpring //.
by rewrite size_proper_cpring size_cpring_ecpH -size_proper_cpring.
Qed.

Lemma cface_node_ecpH : cface (node ecpH) (icpH (node x0)).
Proof.
rewrite cface1 /= /long_cpring /=; do 2 rewrite Enode (negbE Hrg) /=.
apply: connect0.
Qed.

Lemma cface_ecpH : cface ecpH =1 seq3 ecpH (face ecpH) (face (face ecpH)).
Proof. by apply: fconnect_cycle; rewrite //= /eqdf /= Enode (negbE Hrg). Qed.

Lemma adj_ecpH :
 adj ecpH =1 fband (maps icpH (seq3 (node x0) x0 (face (edge x0)))).
Proof.
move=> u; rewrite adjF1; transitivity (adj (icpN ecpY ecpY) u); first done.
  case: (fband_icpN u) => [v Huv]; rewrite (adjFr Huv) adj_icpN connect0 andbT.
rewrite Sface !cface_ecpY (closed_connect (fbandF _) Huv) {u Huv}adj_ecpY.
have <-: icpY x0 = face (edge ecpY) by rewrite /= Enode (negbE Hrg).
rewrite /icpH /seq3 {1 4}/seq2 /seq1 /fband /maps /has !(cface_icpN ecpY) !orbF.
rewrite -(Sface _ v) icpY_edge; case: (fband_icpY v) => [[x Hvx]|Hv].
  by rewrite !(same_cface Hvx) !cface_icpY -cface1r -orbA.
by rewrite -!(same_cface Hv) !cface_ecpY.
Qed.

Lemma fband_icpH : forall u, {x : g | cface u (icpH x)} + {cface ecpH u}.
Proof.
move=> u; case: (fband_icpN u) => [v Huv].
case: (fband_icpY v) => [[x Hvx]|Hv]; [ left; exists x | right ].
  by rewrite (same_cface Huv) /icpH cface_icpN.
rewrite cface1 Sface (same_cface Huv) Sface.
by rewrite -(cface_icpN ecpY) in Hv.
Qed.

Lemma bridgeless_ecpH : bridgeless ecpH.
Proof.
have Hu0 := cface_ecpH (edge ecpH).
have Hfu0 := cface_ecpH (edge (face ecpH)); rewrite cface1 in Hfu0.
have Hffu0 := cface_ecpH (edge (face (face ecpH))); rewrite 2!cface1 in Hffu0.
apply/set0P => [[||[||[||x]]]] //; try by rewrite Sface.
by move: (set0P Hbg x); rewrite -cface_icpH.
Qed.

End CompExtConfig.

Lemma cpmap0P : monic3 negb negb id. Proof. by case. Qed.

Definition cpmap0_map := Hypermap cpmap0P.

Fixpoint cpmap (cp : cprog) : pointed_map :=
  match cp with
  | Adds (CpR n) cp' => ecpR n (cpmap cp')
  | Adds CpR' cp' => ecpR' (cpmap cp')
  | Adds CpY cp' => ecpY (cpmap cp')
  | Adds CpH cp' => ecpH (cpmap cp')
  | Adds CpU cp' => ecpU (cpmap cp')
  | Adds CpK cp' => ecpK (cpmap cp')
  | Adds CpA cp' => ecpA (cpmap cp')
  | seq0 => PointedMap cpmap0_map true
  end.

Definition cfmap cf := cpmap (cfprog cf).
Definition cfring cf := rev (cpring (cfmap cf)).

Lemma cpmap_proper : forall cp, cubic_prog cp -> proper_cpring (cpmap cp).
Proof.
move=> cp; rewrite size_proper_cpring; elim: cp => [|s cp Hrec] //=.
case: s => // [n|||]; move/Hrec=> Hrg.
- by rewrite size_cpring_ecpR.
- by rewrite size_cpring_ecpY ltnW.
- by rewrite size_cpring_ecpH.
by rewrite size_cpring_ecpU.
Qed.

Lemma cfmap_long : forall cp, config_prog cp -> long_cpring (cpmap cp).
Proof.
move=> cp; rewrite size_long_cpring; elim: cp => [|s cp Hrec] //=.
case: s => // [n||]; rewrite ?size_cpring_ecpR ?size_cpring_ecpH //.
case: cp Hrec => // [s cp] Hrec Hpc; rewrite size_cpring_ecpY ltnW ?ltnS; auto.
Qed.

Lemma cpmap_plain : forall cp, cubic_prog cp -> plain (cpmap cp).
Proof.
elim=> [|s cp Hrec] //=; case: s => // [||]; move/Hrec=> HgE.
- exact: plain_ecpY.
- exact: plain_ecpH.
exact: plain_ecpU.
Qed.

Lemma cpmap_cubic : forall cp, cubic_prog cp ->
  quasicubic (rev (cpring (cpmap cp))).
Proof.
elim=> [|s cp Hrec] //=; case: s => // [n|||]; move/Hrec {Hrec} => HgN.
- exact: cubic_ecpR.
- exact: cubic_ecpY.
- exact: cubic_ecpH.
exact: cubic_ecpU.
Qed.

Lemma cpmap_connected : forall cp, cubic_prog cp -> connected (cpmap cp).
Proof.
elim=> [|s cp Hrec] //=; case: s => // [||]; move/Hrec {Hrec} => Hcg.
- exact: connected_ecpY.
- exact: connected_ecpH.
exact: connected_ecpU.
Qed.

Lemma cpmap_bridgeless : forall cp, cubic_prog cp -> bridgeless (cpmap cp).
Proof.
elim=> [|s cp Hrec] //=; case: s => // Hcp.
- by apply: bridgeless_ecpY; auto.
- by apply: bridgeless_ecpH; auto; apply cpmap_proper.
by apply: bridgeless_ecpU; auto.
Qed.

Lemma cpmap_planar : forall cp, cubic_prog cp -> planar (cpmap cp).
Proof.
elim=> [|s cp Hrec] //=; case: s => // [||] Hcp;
  move: (Hrec Hcp) (cpmap_plain Hcp) (cpmap_cubic Hcp) (cpmap_connected Hcp);
  move=> Hpg HgE HgN Hcg.
- exact: planar_ecpY.
- exact: planar_ecpH.
exact: planar_ecpU.
Qed.

Fixpoint cpker (cp : cprog) : seq (cpmap cp) :=
  match cp as cp' return (seq (cpmap cp')) with
  | Adds (CpR _) cp' => cpker cp'
  | Adds CpY cp' => maps (icpY (cpmap cp')) (cpker cp')
  | Adds CpH cp' =>
      if cpring (cpmap cp') is Adds _ (Adds x _) then
         maps (icpH (cpmap cp')) (Adds x (cpker cp'))
      else seq0
  | _ => seq0
  end.

Lemma cpmap_simple : forall cp, config_prog cp ->
  simple (cat (cpring (cpmap cp)) (cpker cp)).
Proof.
elim=> [|s cp Hrec] //=; case: s => // [n||].
- by move/Hrec=> *; rewrite cpring_ecpR /rot -catA simple_catCA catA cat_take_drop.
- case Dcp: cp Hrec => // [s cp']; rewrite -{s cp'}Dcp => H; move/H {H} => Hrec.
  rewrite cpring_ecpY cat_adds simple_adds; set g := cpmap cp.
  rewrite (closed_connect (fbandF _) (cface_node_ecpY g)).
  rewrite -simple_adds -!cat1s -!catA simple_catCA !cat1s -cat_adds -maps_adds.
  rewrite -head_cpring -maps_cat simple_adds /fband.
  rewrite -(simple_maps (cface_icpY g)) in Hrec.
  by rewrite (eq_has (@cface_ecpY _ g)) has_maps /comp /= /setU1 /= has_set0.
move=> Hcp; move: {Hrec}(Hrec Hcp); set g := cpmap cp.
have Hgp := cpmap_proper (config_prog_cubic Hcp).
rewrite /g (head_proper_cpring Hgp) (cpring_ecpH Hgp) -/g; move=> Hrec.
rewrite cat_adds simple_adds (closed_connect (fbandF _) (cface_node_ecpH Hgp)).
rewrite -simple_adds -!cat1s -!catA simple_catCA !cat1s -!maps_adds -maps_cat.
rewrite -maps_adds simple_adds /fband (eq_has (cface_ecpH Hgp)) has_maps.
rewrite (simple_maps (cface_icpH g)) /comp /= /setU1 /= has_set0 /=.
by rewrite -!cat1s simple_catCA {1}[cat]lock catA -lock simple_catCA.
Qed.

Lemma cpmap_cover : forall cp, config_prog cp ->
  fband (cat (cpring (cpmap cp)) (cpker cp)) =1 cpmap cp.
Proof.
elim=> [|s cp Hrec] //=; case: s => // [n||].
- move=> Hcp x; apply: etrans (Hrec Hcp x).
  by rewrite cpring_ecpR !fband_cat fband_rot.
- case Dcp: cp Hrec => [|s cp']; first by do 2 clear; do 3 case=> //.
  move: Dcp => <- {s cp'}; set g := cpmap cp => H; move/H {H} => Hrec u.
  rewrite cpring_ecpY !cat_adds !fband_adds orbCA; apply/orP.
  case: (fband_icpY u) => [[x Hux]|Hu]; [ right | by left; rewrite Sface ].
  rewrite Sface (same_cface (cface_node_ecpY g)) Sface -fband_adds -maps_cat.
  rewrite -maps_adds -cat_adds -head_cpring /fband (eq_has (same_cface Hux)).
  rewrite has_maps (@eq_has _ (comp (cface _) _) _ (cface_icpY g x)); exact: Hrec.
move=> Hcp; move: {Hcp}(cpmap_proper (config_prog_cubic Hcp)) {Hrec}(Hrec Hcp).
set g := cpmap cp => Hgp; rewrite (head_proper_cpring Hgp) => Hrec u.
rewrite (cpring_ecpH Hgp) -/g -maps_adds !cat_adds.
rewrite !fband_adds Sface (same_cface (cface_node_ecpH Hgp)) Sface orbCA.
rewrite -maps_cat -fband_adds /setA -maps_adds; apply/orP.
case: (fband_icpH u) => [[x Hux]|Hu]; [ right | by left; rewrite Sface ].
rewrite /fband (eq_has (same_cface Hux)).
rewrite has_maps (@eq_has _ (comp (cface _) _) _ (cface_icpH g x)) /= has_cat /=.
rewrite orbA orbCA -!orbA orbCA -has_cat; exact (Hrec x).
Qed.

Fixpoint injcp (cp1 cp2 : cprog) (x : cpmap cp2) {struct cp1}
       : cpmap (catrev cp2 cp1) :=
  match cp1 as cp return cpmap (catrev cp2 cp) with
  | seq0 => x
  | Adds s cp1' =>
    injcp cp1' match s as s' return cpmap (Adds s' cp2) with
               | CpY => icpY (cpmap cp2) x
               | CpH => icpH (cpmap cp2) x
               | CpU => icpU (cpmap cp2) x
               | CpK => icpK (cpmap cp2) x
               | _ => x
               end
  end.

Lemma injcp_inj : forall cp1 cp2, injective (@injcp cp1 cp2).
Proof.
elim=> [|s cp1 Hrec] cp2 x y Exy //.
case: s {Hrec Exy}(Hrec _ _ _ Exy) => //.
- exact: icpY_inj.
- exact: icpH_inj.
- exact: icpU_inj.
exact: icpK_inj.
Qed.

Lemma sub_cface_injcp : forall cp1 cp2 (x y : cpmap cp2),
  cface x y -> cface (injcp cp1 x) (injcp cp1 y).
Proof.
elim=> [|s cp1 Hrec] cp2 x y Hxy //.
case: s => /= *; apply: Hrec => //.
- exact: etrans (cface_icpY _ _ _) _.
- exact: etrans (cface_icpH _ _ _) _.
- exact: etrans (cface_icpU _ _ _) _.
- exact: etrans (cface_icpK _ _ _) _.
exact: sub_cface_icpA.
Qed.

Lemma sub_adj_injcp : forall cp1 cp2 (x y : cpmap cp2),
   adj x y -> adj (injcp cp1 x) (injcp cp1 y).
Proof.
elim=> [|s cp1 Hrec] cp2 x y Hxy //.
case: s => /= *; apply: Hrec => //.
- exact: etrans (adj_icpY _ _ _) _.
- exact: etrans (adj_icpH _ _ _) _.
- exact: etrans (adj_icpU _ _ _) _.
- exact: sub_adj_icpK.
exact: sub_adj_icpA.
Qed.

Lemma cface_injcp : forall cp1 cp2 (x y : cpmap cp2), cubic_prog cp1 ->
  cface (injcp cp1 x) (injcp cp1 y) = cface x y.
Proof.
elim=> [|s cp1 Hrec] cp2 x y //=; case: s => // [n|||] Hcp; rewrite Hrec //.
- exact: cface_icpY.
- exact: cface_icpH.
exact: cface_icpU.
Qed.

Lemma edge_injcp : forall cp1 cp2 (x : cpmap cp2), cubic_prog cp1 ->
  edge (injcp cp1 x) = injcp cp1 (edge x).
Proof. by elim=> [|s cp1 Hrec] cp2 x //; case: s => //= *; rewrite Hrec. Qed.

Lemma adj_injcp : forall cp1 cp2 (x y : cpmap cp2),  cubic_prog cp1 ->
  adj (injcp cp1 x) (injcp cp1 y) = adj x y.
Proof.
elim=> [|s cp1 Hrec] cp2 x y //=; case: s => // [n|||] Hcp; rewrite Hrec //.
- exact: adj_icpY.
- exact: adj_icpH.
exact: adj_icpU.
Qed.

Lemma node_injcp : forall cp1 cp2 (x : cpmap cp2), cubic_prog cp1 ->
  negb (cpring (cpmap cp2) x) -> node (injcp cp1 x) = injcp cp1 (node x).
Proof.
elim=> [|[n||||||] cp1 Hrec] //= cp2 x Hcp1 Hx.
- by rewrite Hrec // /cpmap -/cpmap cpring_ecpR mem_rot.
- rewrite Hrec // -1?icpY_node //; first rewrite mem_cpring in Hx.
    rewrite mem_seq2; apply/orP; case; move/eqP=> Dx; case/idP: Hx; rewrite -{}Dx.
      exact: fconnect1.
    exact: connect0.
  rewrite /cpmap -/cpmap cpring_ecpY /= /setU1 /=.
  rewrite (mem_maps (@icpY_inj _ (cpmap cp2))).
  by apply/idP => Hx'; rewrite (mem_behead Hx') in Hx.
- rewrite Hrec // -1?icpH_node //; first rewrite mem_cpring in Hx.
    rewrite mem_seq3; apply/or3P; case; move/eqP=> Dx; case/idP: Hx; rewrite -{}Dx.
      exact: fconnect1.
    exact: connect0.
  by rewrite cnode1r Eedge connect0.
- rewrite /cpmap -/cpmap /ecpH cpring_ecpN cpring_ecpY.
  case Hgl: (long_cpring (ecpY (cpmap cp2))); last done.
  rewrite maps_drop !maps_adds -maps_comp.
  rewrite -[comp _ _]/(icpH (cpmap cp2)) /=.
  rewrite drop1 /setU1 /= behead_maps (mem_maps (@icpH_inj _ (cpmap cp2))).
  by apply/idP => [Hx']; case/idP: Hx; do 2 apply mem_behead.
rewrite Hrec // -1?icpU_node //.
  by rewrite head_cpring /= in Hx; rewrite mem_seq1; case/norP: Hx.
rewrite /cpmap -/cpmap cpring_ecpU /= /setU1 /=.
by rewrite (mem_maps (@icpU_inj _ (cpmap cp2))).
Qed.

Lemma cnode_injcp : forall cp1 cp2 (x y : cpmap cp2), cubic_prog cp1 ->
  negb (cpring (cpmap cp2) x) -> cnode (injcp cp1 x) (injcp cp1 y) = cnode x y.
Proof.
move=> cp1 cp2 x y Hcp1 Hx; apply/idP/idP; move/iter_findex.
elim: {x}(findex node (injcp cp1 x) (injcp cp1 y)) {-2}x Hx => [|n Hrec] x Hx.
- move/injcp_inj=> <-; exact: connect0.
- rewrite -iter_f node_injcp // cnode1; apply: Hrec.
  by rewrite mem_cpring -cnode1r -mem_cpring.
move <-; elim: {x y}(findex node x y) {-3}x Hx => [|n Hrec] x Hx.
  exact: connect0.
rewrite -iter_f cnode1 node_injcp //; apply: Hrec.
by rewrite mem_cpring -cnode1r -mem_cpring.
Qed.

Fixpoint cprsize (cp : cprog) : nat :=
  match cp with
  | seq0 => 2
  | Adds CpY cp' => S (cprsize cp')
  | Adds CpU cp' => S (S (cprsize cp'))
  | Adds CpK cp' => S (pred (pred (cprsize cp')))
  | Adds CpA cp' => sub2ifgt2 (cprsize cp')
  | Adds _ cp' => cprsize cp'
  end.

Lemma size_ring_cpmap : forall cp, size (cpring (cpmap cp)) = cprsize cp.
Proof.
elim=> [|s cp1 Hrec] //; case: s Hrec => [n||||||];
  rewrite /cprsize; move <-; rewrite /cpmap -/cpmap.
- exact: size_cpring_ecpR.
- exact: size_cpring_ecpR.
- by rewrite /ecpY size_cpring_ecpN size_cpring_ecpU.
- by rewrite /ecpH /ecpY !size_cpring_ecpN size_cpring_ecpU head_cpring.
- exact: size_cpring_ecpU.
- exact: size_cpring_ecpK.
rewrite cpring_ecpA size_long_cpring.
by case: (cpring (cpmap cp1)) => [|x [|y [|z p]]].
Qed.

Definition cpksize : cprog -> nat :=
  count (fun s => if s is CpH then true else false).

Lemma size_cpker : forall cp, config_prog cp -> size (cpker cp) = cpksize cp.
Proof.
elim=> [|s cp Hrec] //=; case: s => // [|].
  by rewrite size_maps; case: cp Hrec.
move=> Hcp; rewrite (head_proper_cpring (cpmap_proper (config_prog_cubic Hcp))).
by rewrite /= size_maps Hrec.
Qed.

Inductive cpmask : Set := Cpmask (mr mk : bitseq).

Definition proper_cpmask cp cm :=
  let: Cpmask mr mk := cm in (size mr =d cprsize cp) && (size mk =d cpksize cp).

Definition cpsieve cm cp :=
  let: Cpmask mr mk := cm in
  cat (sieve mr (cpring (cpmap cp))) (sieve mk (cpker cp)).

Definition cpmask1 cp i :=
  Cpmask (seqn (cprsize cp) false) (mkseq (set1 i) (cpksize cp)).

Lemma proper_cpmask1 : forall cp i, proper_cpmask cp (cpmask1 cp i).
Proof. by move=> *; rewrite /= size_seqn size_mkseq !set11. Qed.

Lemma cpsieve1 : forall cp i, i < cpksize cp -> config_prog cp ->
  cpsieve (cpmask1 cp i) cp = seq1 (sub (cpmap cp) (cpker cp) i).
Proof.
move=> cp i Hi Hcp /=; move: (cpmap cp : cpmap cp) Hi => x0.
rewrite sieve_false cat0s -size_cpker // -{2}[i]addn0 /mkseq {Hcp}.
elim: (cpker cp) 0 i => // [x p Hrec] j [|i] /= Hi.
  rewrite add0n set11 -addn1; congr Adds.
  elim: p 0 {x Hrec Hi} => //= [x p Hrec] i.
  by rewrite addnS eqn_leq ltnNge leq_addr andbF -!addnS.
rewrite addSn eqn_leq ltnNge leq_addl /= -addnS; auto.
Qed.

Fixpoint cpadj (cm : cpmask) (cp : cprog) {struct cp} : cpmask :=
  match cp, cm with
  | Adds (CpR n) cp', Cpmask mr mk =>
      let (mr', mk') := cpadj (Cpmask (rotr n mr) mk) cp' in
      Cpmask (rot n mr') mk'
  | Adds CpY cp', Cpmask (Seq b0 b1 b2 & mr) mk =>
    if cpadj (Cpmask (Seq b0 b2 & mr) mk) cp' is Cpmask (Seq a0 a2 & mr') mk'
    then Cpmask (Seq (a0 || b1) (b0 || b2) (a2 || b1) & mr') mk'
    else cm
  | Adds CpH cp', Cpmask (Seq b0 b1 & mr) (Seq b1' & mk) =>
    if cpadj (Cpmask (Seq b0 b1' & mr) mk) cp' is Cpmask (Seq a0 a1 & mr') mk'
    then Cpmask (Seq (a0 || b1) (or3b b0 b1' (head b0 mr))
                     & (if mr' is Adds a2 mr'' then Adds (a2 || b1) mr'' else mr'))
                (Adds (a1 || b1) mk')
    else cm
  | seq0, Cpmask (Seq b0 b1) seq0 => Cpmask (seq2 b1 b0) seq0
  | _, _ => cm (* can't happen *)
  end.

Lemma cpadj_proper : forall cp cm, proper_cpmask cp cm ->
  proper_cpmask cp (cpadj cm cp).
Proof.
elim=> [|s cp Hrec] [mr mk]; first by case: mr => [|b0 [|b1 [|b2 mr]]]; case mk.
case: s => //= [n||].
- move=> Hcm0; set cm := Cpmask (rotr n mr) mk.
  have Hcm: proper_cpmask cp cm by rewrite /= size_rotr.
  by case: (cpadj cm cp) (Hrec cm Hcm) => [mr' mk'] /=; rewrite size_rot.
- case: mr => [|b0 [|b1 [|b2 mr]]] //= Hcm; set cm := Cpmask _ mk.
  by case: (cpadj cm cp) (Hrec cm Hcm) => [[|a0 [|a2 mr']] mk'].
case: mr mk => [|b0 [|b1 mr]] //= [|b1' mk] //= Hcm; set cm := Cpmask _ mk.
by case: (cpadj cm cp) (Hrec cm Hcm) => [[|a0 [|a1 [|a2 mr']]] mk'].
Qed.

Lemma cpsieve_adj : forall cp cm, config_prog cp -> proper_cpmask cp cm ->
  fband (cpsieve (cpadj cm cp) cp) =1 (fun x => has (adj x) (cpsieve cm cp)).
Proof.
elim=> // [s cp Hrec] [mr mk] Hcp /=; case: s Hcp => // [n||] Hcp Hcm0.
- set cm := Cpmask _ mk.
  have Hcm: proper_cpmask cp cm by rewrite /= size_rotr.
  move: (cpadj_proper Hcm) {Hrec}(Hrec cm Hcp Hcm).
  move: (cpadj cm cp) => [mr' mk']; move/andP=> [Ecm _] Hrec.
  rewrite /cpsieve /cpmap -/cpmap cpring_ecpR /cpker -/cpker.
  move=> x; rewrite fband_cat has_cat /setU -(rot_rotr n mr).
  move/andP: Hcm0 => [Ecm0 _]; rewrite -(size_rotr n) -size_ring_cpmap in Ecm0.
  rewrite (eq_has_r (mem_sieve_rot n (eqP Ecm0))) -has_cat -Hrec /= fband_cat.
  congr orb; apply: eq_has_r; apply mem_sieve_rot.
  by rewrite size_ring_cpmap (eqP Ecm).
- have Urec := cpmap_simple Hcp; simpl in Hcp.
  case Dcp: cp Hcp Hcm0 => [|s cp']; last rewrite -{s cp'}Dcp.
    case: mr mk => [|b0 [|b1 [|b2 [|b3 mr]]]] // [|a1 mk] // _ _.
    by case b0; case b1; case b2; do 3 case=> //.
  move=> Hcp; have Hcpq := config_prog_cubic Hcp.
  move: (cpmap_proper Hcpq) (cpmap_plain Hcpq) Urec {Hrec}(Hrec _ Hcp).
  set g := cpmap cp => Hgp HgE Urec Hrec Hcm0; move: (andP Hcm0) => [Emr0 _].
  have Hmr0: 2 < size mr.
    by rewrite (eqP Emr0) -size_ring_cpmap ltnS -size_proper_cpring.
  case: mr Hmr0 Emr0 Hcm0 => [|b0 [|b1 [|b2 mr]]] // _ Emr0 Hcm0.
  set cm := Cpmask _ mk; have Hcm := Hcm0; rewrite /= eqdSS add0n in Hcm.
  move: (@cpadj_proper _ cm Hcm) {Hrec}(Hrec cm Hcm).
  case: (cpadj cm cp) => [mr' mk']; move/andP=> [Emr' _] Hrec.
  have Hmr': 1 < size mr'.
    by rewrite (eqP Emr') -size_ring_cpmap -size_proper_cpring.
  case: mr' Hmr' Emr' Hrec Urec => [|a0 [|a2 mr']] // _ Emr'.
  rewrite /cpsieve /cpmap -/cpmap /cpker -/cpker /g cpring_ecpY /cm -/g.
  rewrite (head_proper_cpring Hgp) /behead maps_adds.
  move=> Hrec Urec u; have HnYF := cface_node_ecpY g.
  rewrite cat_adds simple_adds (closed_connect (fbandF _) HnYF) in Urec.
  rewrite /fband !has_cat !has_sieve_adds (adjFr HnYF) Sface (same_cface HnYF).
  rewrite Sface -/g.
  case Hu: (cface u (ecpY g)).
    move: (adjF Hu) (adj_ecpY Hgp); rewrite [adj]lock => Eu EgY.
    rewrite !(eq_has Eu) !(eq_has EgY) !{}Eu !{}EgY.
    case b0; first by rewrite !orTb orbT {1}/seq2 maps_adds fband_adds connect0.
    rewrite andFb !orFb; case b2.
      by rewrite orbT !orTb {2}/seq2 /seq1 !maps_adds !fband_adds connect0 !orbT.
    rewrite andFb !orFb -!has_sieve_adds -!has_cat (eq_has (same_cface Hu)).
    apply/hasP/hasP; case=> v Hv Huv; elimtype False.
      rewrite -!maps_adds -!maps_sieve -maps_cat in Hv.
      by move/mapsP: Hv Huv => [y _ <-]; rewrite cface_ecpY.
    move: Urec; rewrite -(fband_rot 1) -(simple_rot 1) -simple_adds.
    rewrite cat_adds rot1_adds -add_last_adds -!cat1s cat1s -catA -!cat_adds.
    rewrite seq2I -cats1 -catA cats1 -rot1_adds simple_cat has_rot.
    case/and3P; clear; case/hasP; exists v; last done.
    rewrite -cat_adds !mem_cat /setU in Hv |- *; apply/orP.
    by case/orP: Hv; move/mem_sieve; auto.
  case: (fband_icpY u) {Urec} => [[x Hux]|Hu']; last by rewrite Sface Hu in Hu'.
  rewrite {Hu} andbF orFb !(same_cface Hux) !(adjF Hux) !cface_icpY !adj_icpY.
  rewrite (Sadj (plain_ecpY g HgE)) (adj_ecpY Hgp).
  rewrite /seq2 /seq1 {3}/maps /fband {3}/has !cface_icpY orbF.
  rewrite -!maps_sieve !has_find !size_maps !find_maps -!has_find.
  have Efu: comp (cface u) (icpY _) =1 cface x.
    by move=> y; rewrite /comp (same_cface Hux) cface_icpY.
  have Eau: comp (adj u) (icpY _) =1 adj x.
    by move=> y; rewrite /comp (adjF Hux) adj_icpY.
  rewrite {Hux} !{Efu}(eq_has Efu) !{u Eau}(eq_has Eau).
  move: {Hrec}(Hrec x); rewrite /fband !has_cat !has_sieve_adds.
  case b1; last by rewrite !orbF.
  case Hx0: (cface x (node g)); first by rewrite /= !orbT.
  by case Hx2: (cface x g); [ rewrite /= !orbT | rewrite !andbF ].
move: (andP Hcm0) (cpmap_simple Hcp) => [Emr Emk]; simpl in Hcp.
have Hcpq := config_prog_cubic Hcp.
move: (cpmap_plain Hcpq) (cpmap_proper Hcpq) (cfmap_long Hcp).
rewrite /cpmap -/cpmap; set g := cpmap cp => HgE Hgp Hgl.
have Hg0E := plain_ecpH g HgE.
have Hmr: 2 < size mr by rewrite (eqP Emr) -size_ring_cpmap -size_long_cpring.
case: mr Hmr Emr Hcm0 => [|b0 [|b1 [|b2 mr]]] // _ Emr.
case: mk Emk => [|b1' mk] // _ Hcm; rewrite /= add1n eqdSS in Hcm.
set cm := Cpmask _ mk.
move/andP: Hcm (@cpadj_proper _ cm Hcm) {Hrec}(Hrec cm Hcp Hcm) => [Ecp _].
move: (cpadj cm cp) => [mr' mk']; move/andP=> [Emr' _]; rewrite {}/cm.
rewrite -(eqP Ecp) in Emr'; case: mr' Emr' => [|a0 [|a1 [|a2 mr']]] // _.
rewrite /cpsieve /cpmap -/cpmap /cpker -/cpker -/g cpring_ecpH // drop_behead.
rewrite (head_long_cpring Hgl) /iter /head /behead !maps_adds.
have HnHF := cface_node_ecpH Hgp; move=> Hrec Urec u. 
rewrite !cat_adds simple_adds (closed_connect (fbandF _) HnHF) in Urec.
rewrite /fband !has_cat !has_sieve_adds (adjFr HnHF).
rewrite Sface (same_cface HnHF) Sface.
case Hu: (cface u (ecpH g)).
  move: (adjF Hu) (adj_ecpH Hgp); rewrite [adj]lock => Eu EgH.
  rewrite !(eq_has Eu) !(eq_has EgH) !{}Eu !{}EgH.
  case b0; first by rewrite !orbT orTb {1}/seq3 maps_adds fband_adds connect0.
  rewrite andFb !orFb; case b2.
    rewrite !orbT orTb {2}/seq3 /seq2 /seq1 !maps_adds !fband_adds connect0.
    by rewrite !orbT.
  rewrite andFb !orFb; case b1'.
    by rewrite !orbT orTb {3}/seq3 /seq2 !maps_adds !fband_adds connect0 !orbT.
  rewrite andFb !orFb -!has_sieve_adds -!has_cat (eq_has (same_cface Hu)).
  apply/hasP/hasP; case=> v Hv Huv; elimtype False.
    rewrite -!maps_adds -!maps_sieve -maps_cat in Hv.
    by case/mapsP: Hv Huv => [x _ <-]; rewrite cface_ecpH.
  have Urec': simple (cat (maps (icpH g) (seq3 (node g) g (face (edge g))))
                     (cat (Adds (ecpH g) (maps (icpH g) (drop 3 (cpring g))))
                          (maps (icpH g) (cpker cp)))).
    apply: etrans Urec; rewrite -simple_adds; apply simple_perm.
      move=> w; apply: {w}eq_has_r => w.
      by rewrite /= /setU1 !mem_cat /setU /= /setU1; repeat BoolCongr.
    by rewrite /= !size_cat /= !size_maps addnS.
  rewrite /cpker -/cpker simple_cat in Urec'; case/and3P: Urec' {Urec}; clear.
  case/hasP; exists v; last done.
  rewrite !mem_cat /setU in Hv |- *; apply/orP.
  by case/orP: Hv; move/mem_sieve; auto.
case: (fband_icpH u) {Urec} => [[x Hux]|Hu']; last by rewrite Sface Hu in Hu'.
rewrite {Hu} andbF orFb !(same_cface Hux) !(adjF Hux) !cface_icpH !adj_icpH.
rewrite (Sadj Hg0E) (adj_ecpH Hgp) /seq3 /seq2 /seq1 !maps_adds !fband_adds.
rewrite !cface_icpH {3}/maps /fband {3}/has !orbF.
rewrite -!maps_sieve !has_find !size_maps !find_maps -!has_find.
have Efu: comp (cface u) (icpH _) =1 cface x.
  by move=> y; rewrite /comp (same_cface Hux) cface_icpH.
have Eau: comp (adj u) (icpH _) =1 adj x.
  by move=> y; rewrite /comp (adjF Hux) adj_icpH.
rewrite {Hux} !{Efu}(eq_has Efu) !{u Eau}(eq_has Eau).
move: {Hrec}(Hrec x); rewrite /fband !has_cat !has_sieve_adds.
case b1; last by rewrite /= !orbF -!orbA -!(orbCA (a1 && _)) -!(orbCA (b1' && _)).
case Hx0: (cface x (node g)); first by rewrite /= !orbT.
case Hx1': (cface x g); first by rewrite /= !orbT.
case Hx2: (cface x (face (edge g))); first by rewrite /= !orbT.
by rewrite !andbF /= => ->; rewrite -!orbA; repeat BoolCongr.
Qed.


Unset Implicit Arguments.
