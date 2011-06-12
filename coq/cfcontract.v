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
Require Import cfcolor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Compute the contract of a configuration construction: a cprog whose ring  *)
(* colorings coincides with the contract colorings of the initial cprog.     *)
(* Also, check the validity of the contract (sparseness, and possibly the    *)
(* existence of a triad.                                                     *)
(* The darts in the contract sequence are represented by the index at which  *)
(* they are removed from the internal ring; each Y step (except the final    *)
(* one) has a single index, while each H step has three. The first index of  *)
(* the H step corresponds to the middle edge, which is actually never part   *)
(* of a ring; the next two are for the left and right feet of the H.         *)
(* The last Y does not have an index because it removes only one dart of the *)
(* central edge pair.                                                        *)

Section ConfigContract.

Fixpoint ctrmsize (cp : cprog) : nat :=
  match cp with
  | Adds (CpR _) cp' => ctrmsize cp'
  | Adds CpY seq0 => 0
  | Adds CpY cp' => S (ctrmsize cp')
  | Adds CpH cp' => S (S (S (ctrmsize cp')))
  | _ => 0
  end.

Fixpoint ctrmask_rec (cci : natseq) (i n : nat) {struct n} : bitseq :=
  if n is S n' then Adds (cci i) (ctrmask_rec cci (S i) n') else seq0.

Definition ctrmask (cp : cprog) (cci : natseq) : bitseq :=
  ctrmask_rec cci 0 (ctrmsize cp).

Lemma size_ctrmask : forall cp ms, size (ctrmask cp ms) = ctrmsize cp.
Proof.
by move=> cp ms; rewrite /ctrmask; elim: (ctrmsize cp) 0 => //= *; congr S.
Qed.

Fixpoint ctrenum (cp : cprog) : seq (cpmap cp) :=
  match cp as cp' return (seq (cpmap cp')) with
  | Adds (CpR _) cp' => ctrenum cp'
  | Adds CpY cp' => let g := cpmap cp' in
    if cp' is Seq0 then seq0 else maps (icpY g) (Adds (node g) (ctrenum cp'))
  | Adds CpH cp' => let g := cpmap cp' in
    Adds (face (ecpH g)) (maps (icpH g) (Seq (node g) g & (ctrenum cp')))
  | _ => seq0
  end.

Lemma size_ctrenum : forall cp, size (ctrenum cp) = ctrmsize cp.
Proof.
elim=> [|[n||||||] cp Hrec] //=; rewrite -{}Hrec ?size_maps //.
by case: cp => //= *; rewrite size_maps.
Qed.

Lemma insertE_icpY : forall (g : hypermap) (x : g) p,
 insertE (maps (icpY x) p) = maps (icpY x) (insertE p).
Proof. by move=> g x; elim=> // *; repeat congr Adds. Qed.

Lemma insertE_icpH : forall (g : hypermap) (x : g) p,
 insertE (maps (icpH x) p) = maps (icpH x) (insertE p).
Proof. by move=> g x; elim=> // *; repeat congr Adds. Qed.

Lemma uniq_ctrenum : forall cp,
 config_prog cp -> uniq (insertE (cat (cpring (cpmap cp)) (ctrenum cp))).
Proof.
elim=> //=; case=> // [n||] cp Hrec.
    move/Hrec=> {Hrec}; apply: etrans; set g := cpmap cp.
    rewrite cpring_ecpR /rot !insertE_cat -catA uniq_catCA catA.
    by rewrite -insertE_cat cat_take_drop.
case Dcp: cp => // [s cp']; move: Dcp => <- {c cp'} Hcp; move: {Hrec}(Hrec Hcp).
  set g := cpmap cp => Hrec; rewrite cpring_ecpY.
  rewrite -!cat1s !(@insertE_cat (ecpY g)) uniq_catCA.
  rewrite {1}[cat]lock -!catA catA -lock uniq_catCA -!insertE_cat -maps_cat.
  rewrite !cat1s -maps_adds -cat_adds -head_cpring insertE_cat.
  rewrite (insertE_icpY g) uniq_cat (uniq_maps (@icpY_inj _ g)) Hrec.
  by rewrite has_maps /comp /= /setU1 /= has_set0.
move=> Hcp; move: (cpmap_proper (config_prog_cubic Hcp)) {Hrec}(Hrec Hcp).
set g := cpmap cp => Hgp Hrec.
rewrite (cpring_ecpH Hgp) -!cat1s !(@insertE_cat (ecpH g)).
rewrite {1}[cat]lock !catA -lock uniq_catCA {2 6}[cat]lock -!catA uniq_catCA.
rewrite -!lock -!catA -3!insertE_cat !cat1s -maps_cat -!maps_adds.
rewrite -!cat_adds -(head_proper_cpring Hgp) (insertE_icpH g) !catA.
rewrite [insertE]lock /= /long_cpring /= Enode (negbE Hgp) /= -!lock.
rewrite uniq_cat (uniq_maps (@icpH_inj _ g)) Hrec has_maps /comp /= /setU1 /=.
by rewrite has_set0.
Qed.

Let nsp (b : bool) := if b then orb else andb.

Fixpoint cfctr (mr mc : bitseq) (cp : cprog) {struct cp} : option cprog :=
  match cp, mr, mc with
  | Adds (CpR i) cp', _, _ =>
    let mr' := rotr i mr in
    if cfctr mr' mc cp' is Some cpc then
      Some (Adds (CpR (count negb (take i mr'))) cpc)
    else None
  | Adds CpY seq0, (Seq b1 b2 b3 & _), _ =>
    if nsp b1 b2 b3 then None else
    Some (if b1 || (b2 || b3) then seq0 else seq1 CpY)
  | Adds CpY cp', (Seq b1 b2 & mr'), (Seq b3 & mc') =>
    if nsp b1 b2 b3 then None else
    if cfctr (Adds b3 mr') mc' cp' is Some cpc then
      Some (if b1 || b2 then cpc else Adds (if b3 then CpU else CpY) cpc)
    else None
  | Adds CpH cp', (Seq b1 b2 & mr'), (Seq b3 b4 b5 & mc') =>
    if nsp b3 b1 b4 || nsp b3 b2 b5 then None else
    if and3b b1 b2 (all (fun b => b) mr') then None else
    if cfctr (Seq b4 b5 & mr') mc' cp' is Some cpc then
      Some (if b3 then cpc else
            if b1 then
               if b2 then Adds CpA cpc else
               if b5 then cpc else Adds CpK cpc
             else
               if b2 then (if b4 then cpc else Adds CpK cpc) else
               if b4 then (if b5 then Adds CpU cpc else Adds CpY cpc) else
               if b5 then Adds CpY cpc else Adds CpH cpc)
     else None
  | _, _, _ => None
  end.

Lemma cfctr_config_prog : forall mr mc cp,
 if cfctr mr mc cp is Some _ then config_prog cp else true.
Proof.
move=> mr mc cp; elim: cp mr mc => //=; case=> // [n||] cp Hrec mr mc.
- by case: (cfctr (rotr n mr) mc cp) (Hrec (rotr n mr) mc).
- case Dcp: cp mr => [|s cp'] [|b1 [|b2 mr]] //.
    case: mr => [|b3 mr]; last by case (nsp b1 b2 b3).
    by case: mc => [|b3 mc] //; case: (nsp b1 b2 b3).
  rewrite -{}Dcp; case: mc => [|b3 mc] //; case: (nsp b1 b2 b3) => //.
  by case: (cfctr (Adds b3 mr) mc cp) (Hrec (Adds b3 mr) mc).
case: mr mc => [|b1 [|b2 mr]] [|b3 [|b4 [|b5 mc]]] //=.
case: (nsp b3 b1 b4 || nsp b3 b2 b5) => //.
case: (and3b _ _ _) => //.
by set mr' := Seq b4 b5 & mr; case: (cfctr mr' mc cp) (Hrec mr' mc).
Qed.

Lemma cfctr_correct : forall mr mc cp,
  size mr = cprsize cp -> size mc = ctrmsize cp ->
  let g := cpmap cp in let r := cpring g in
  let cc := cat (sieve mr r) (sieve mc (ctrenum cp)) in
  forall k : g -> color, cc_coloring cc k ->
  if cfctr mr mc cp is Some cpc then
    let r' := cpring (cpmap cpc) in
    exists2 k', coloring k' & maps k' r' = maps k (sieve (maps negb mr) r)
  else True.
Proof.
move=> /= mr mc cp; elim: cp mr mc => [|s cp Hrec] mr mc //.
move: (cfctr_config_prog mr mc (Adds s cp)).
case Dcpc: (cfctr mr mc (Adds s cp)) => // [cpc].
case: s Dcpc => // [n||] Dcpc Hcp' Emr Emc;
  have Hcp := config_prog_cubic Hcp'; simpl in Dcpc, Hcp, Emr, Emc;
  move: Hrec (cpmap_plain Hcp) (cpmap_proper Hcp); rewrite /cpmap -/cpmap;
  set g := cpmap cp => Hrec HgE Hgp.
- rewrite cpring_ecpR; rewrite -(size_rotr n) in Emr.
  move=> k [HkE HkF]; move: {Hrec}(Hrec _ _ Emr Emc k).
  case: (cfctr (rotr n mr) mc cp) cpc Dcpc => // [cpc] _ [<-].
  rewrite /cpmap -/cpmap; set gc := cpmap cpc.
  case; first split=> // x.
    rewrite HkE !(mem_insertE HgE); apply: {x}eq_has_r => x.
    rewrite !mem_cat; congr orb; rewrite -{1}(rot_rotr n mr).
    by apply: mem_sieve_rot; rewrite Emr -size_ring_cpmap.
  move=> k' Hk' Ek'; exists k'; first done.
  rewrite cpring_ecpR -{3}(rot_rotr n mr) !maps_rot {}Ek' sieve_rot.
    by rewrite maps_rot -maps_take count_maps.
  by rewrite size_maps /g size_ring_cpmap.
- rewrite /g.
  case Dcp: cp mc mr Emc Emr Dcpc => [|s cp'] [|b3 mc] [|b1 [|b2 mr]] //.
    case: mr {cp Dcp Hcp' Hcp g Hrec HgE Hgp} => [|b3 [|b4 mr]] // _ _.
    case Hb123: (nsp b1 b2 b3) => // [] [<-] {cpc}; rewrite cpring_ecpY.
    set x0 : cpmap seq0 := cpmap seq0.
    case: b1 Hb123; case: b2 => //; case: b3 => // _ k [HkE HkF].
    - exists (fun y => k (icpY x0 y)).
        by split; [ move=> y; case: y (HkE (icpY x0 y)) | case; apply/eqP ].
      congr Adds; move: (HkE (node (ecpY _))); rewrite /= /setU1 /=; move/eqcP.
      by rewrite /= -(eqcP (HkF _)) /=; move->; rewrite -(eqcP (HkF _)) /=.
    - exists (fun y => k (icpY x0 y)).
        by split; [ move=> y; case: y (HkE (icpY x0 y)) | case; apply/eqP ].
      by congr Adds; rewrite /= -(eqcP (HkF _)).
    - exists (fun y => k (if y is true then ecpY x0 else node (ecpY x0))) => //.
      split; last by case; apply/eqP.
      have HkEx0 := HkE (node (ecpY x0)).
      rewrite /invariant -(eqcP (HkF _)) Enode in HkEx0.
      by case=> //; rewrite /invariant eqd_sym.
    by exists k; split.
  rewrite -Dcp cpring_ecpY [size _]/= [size _ = _]/= => [] [Emc] [Emr].
  have Ecp: ctrenum (Adds CpY cp) = maps (icpY g) (Adds (node g) (ctrenum cp)).
    by rewrite /= /g Dcp.
  have Hg'E: plain (ecpY g) by apply: plain_ecpY.
  case Hb123: (nsp b1 b2 b3) {s cp' Dcp} => //.
  case: (cfctr (Adds b3 mr) mc cp) {Hrec Emr}(Hrec (Adds b3 mr) mc Emr Emc) => //.
  move: cpc => _ cpc Hrec [<-] k [HkE HkF].
  pose h x := k (icpY g x).
  have HhF: invariant face h =1 g.
    move=> x; apply/eqP; apply: (fconnect_invariant HkF).
    by rewrite cface_icpY Sface fconnect1.
  have HhE: invariant edge h =1
             insertE (cat (sieve (Adds b3 mr) (cpring g)) (sieve mc (ctrenum cp))).
    move=> x; rewrite /invariant /h -icpY_edge; apply: (etrans (HkE _)).
    rewrite !mem_insertE // /behead -/g head_cpring Ecp.
    rewrite (eq_has (plain_orbit HgE x)) (eq_has (plain_orbit Hg'E (icpY g x))).
    rewrite !has_cat icpY_edge maps_adds !has_sieve_adds !andbF !orFb.
    by rewrite orbCA -!orbA; congr orb; rewrite -!maps_sieve !has_maps.
  case: {Hrec}(Hrec h) {Emc}; first by split.
  set gc := cpmap cpc => h' Hh' Eh.
  move: Hh' (coloring_proper_cpring gc Hh') => [Hh'E Hh'F] Hgcp.
  case Hb12: (b1 || b2).
    exists h'; first by split.
    rewrite -/gc {h' HhE Hh'E Hh'F Eh'nX}Eh /behead head_cpring /h.
    rewrite !maps_sieve (maps_comp k (icpY _)) !maps_adds.
    rewrite -/g -(fconnect_invariant HkF (cface_node_ecpY g)).
    case: b1 b2 b3 Hb12 Hb123 HkE => [|] [|] [|] // _ _ HkE; congr Adds.
    move: (etrans (HkE _) (setU11 _ _)).
    by rewrite /invariant -(eqcP (HkF _)) Enode; move/eqP.
  have HrgE: all (invariant edge h) (sieve (Adds b3 mr) (cpring g)).
    apply/allP => [x Hx]; rewrite HhE mem_insertE //.
    apply/hasP; exists x; last by apply connect0.
    by rewrite mem_cat /setU Hx.
  have HrgN: fpath (finv node) (node g) (behead (cpring g)).
  move: (cycle_rev_cpring g); rewrite head_cpring lastI rev_add_last -lastI.
    by rewrite (cycle_path g) /= -(fpath_finv (Inode g)); case/andP.
  have Eh'nX: h' (node gc) = h (node g).
    rewrite head_cpring in Eh; move: HrgE Eh {HhE HkE}; rewrite head_cpring.
    elim: {mr}(Adds b3 mr) (node g) (behead (cpring g)) HrgN => // [b mr Hrec].
    case: b; last by move=> x p _ _ [Dx _].
    move=> x [|y p] //=; first by case mr.
    case/andP; move/eqP=> Dy Hp; case/andP; move/eqcP=> <-.
    rewrite -(eqcP (HhF (edge x))) -(f_finv (Inode g) x) Enode Dy; eauto.
  case: b1 b2 b3 Hb12 Eh HkE HhE HrgE {Hb123} => [|] [|] [|] // _ Eh HkE HhE HrgE.
    pose a u x := cface u (icpU gc x).
    have EaF: a =2 comp a face by move=> u x; exact: cface1.
    pose k' u := if pick (a u) is Some x then h' x else k (ecpY g).
    have Hk'F: invariant face k' =1 ecpU gc.
      by move=> u; apply/eqP; rewrite /k' (eq_pick (EaF u)).
    have Ek': forall x, k' (icpU gc x) = h' x.
      move=> x; rewrite /k'; case: pickP => [y Hy|Hx].
        by rewrite /a cface_icpU Sface in Hy; apply: (fconnect_invariant Hh'F).
      case/idP: (Hx x); exact: connect0.
    have Ek'X: k' (ecpU gc) = k (ecpY g).
      by rewrite /k'; case: pickP => // y; rewrite /a cface_ecpU.
    have Ek'nX: k' (node (ecpU gc)) = k (node (ecpY g)).
      rewrite /g (fconnect_invariant HkF (cface_node_ecpY _)).
      by rewrite -(eqcP (Hk'F _)) /= -/(icpU gc) Ek' -/gc Eh'nX.
    exists k'; first split=> //.
      have Hk'EX: invariant edge k' (ecpU gc) = false.
        apply/eqP => Hk'X; move: (esym (HkE (node (ecpY g)))).
        rewrite /invariant -Ek'nX -(eqcP (HkF _)) Enode -Ek'X -Hk'X set11.
        move: (uniq_ctrenum Hcp'); rewrite /cpmap -/cpmap -/g cpring_ecpY.
        move: {mc HkE HhE}(Adds true mc) (ctrenum (Adds CpY cp)) => mc p.
        move: (node (ecpY g)) => x /=; move/andP=> [H _]; move: H.
        do 3 case/norP => _; rewrite !(mem_insertE Hg'E).
        move=> H; move/hasP=> [y Hy Hxy]; case/hasP: H; exists y; auto.
        rewrite !mem_cat in Hy |- *; apply/orP; case/orP: Hy; move/mem_sieve; auto.
      move=> [||x] //; first by rewrite /invariant eqd_sym.
      rewrite -/cpmap -/gc in x |- *; rewrite -/(icpU gc x).
      rewrite /invariant -(icpU_edge gc) !Ek'; exact: Hh'E.
    rewrite /cpmap -/cpmap cpring_ecpU !maps_adds {1 2}/negb.
    rewrite -/gc Ek'nX !sieve_adds !maps_cat !maps_seqn Ek'X; do 2 congr Adds.
    rewrite -maps_sieve -!maps_comp /comp -/h.
    by rewrite (@eq_maps _ _ (comp k' (icpU _)) _ Ek') -/gc Eh head_cpring.
  pose a u x := cface u (icpY gc x).
  have EaF: a =2 comp a face by move=> u x; exact: cface1.
  pose k' u := if pick (a u) is Some x then h' x else k (ecpY g).
  have Hk'F: invariant face k' =1 ecpY gc.
    by move=> u; apply/eqP; rewrite /k' (eq_pick (EaF u)).
  have Ek': forall x, k' (icpY gc x) = h' x.
    move=> x; rewrite /k' -/gc; case: pickP => [y Hy|Hx].
      by rewrite /a cface_icpY Sface in Hy; apply: (fconnect_invariant Hh'F).
    case/idP: (Hx x); exact: connect0.
  have Ek'X: k' (ecpY gc) = k (ecpY g).
    by rewrite /k' -/gc; case: pickP => // y; rewrite /a cface_ecpY.
  have Ek'nX: k' (node (ecpY gc)) = k (node (ecpY g)).
    rewrite (fconnect_invariant Hk'F (cface_node_ecpY _)) Ek' Eh'nX.
    by rewrite /g (fconnect_invariant HkF (cface_node_ecpY _)).
  have Eh'X: h' gc = h g.
    rewrite head_proper_cpring // in Eh.
    move: HrgN Eh HrgE {HhE HkE}; rewrite head_proper_cpring //=.
    case/andP=> [_ H] [_ E]; move: H E.
    elim: mr (g : g) (drop 2 (cpring g)) => // [b mr Hrec].
    case: b; last by move=> x p _ [Dx _].
    move=> x [|y p] //=; first by case mr.
    case/andP; move/eqP=> Dy Hp Eh; case/andP; move/eqcP=> <-; move: Eh.
    by rewrite -(eqcP (HhF (edge x))) -(f_finv (Inode g) x) Enode Dy; eauto.
  exists k'; first split => //.
    have Hk'EX: forall u, cface u (ecpY gc) -> invariant edge k' u = false.
      move=> u HuX; rewrite /invariant (fconnect_invariant Hk'F HuX) Ek'X.
      have HeuX: adj (ecpY gc) (edge u) by rewrite -(adjF HuX) adjE.
      rewrite (adj_ecpY Hgcp) /fband in HeuX; case/hasP: HeuX {HuX} => v.
      case/mapsP=> [y Hy <-] {v} H; rewrite {u H}(fconnect_invariant Hk'F H) Ek'.
      move: (uniq_ctrenum Hcp') HkE; rewrite /cpmap -/cpmap -/g cpring_ecpY.
      move: {mc HkE HhE}(Adds false mc) (ctrenum (Adds CpY cp)) {x Hx} => mc p.
      move Dx: (ecpY g : ecpY g) => x; move Dnx: (node x) => nx.
      simpl; case/and4P=> [H _ H' _]; move: H H'; rewrite /setU1 /=.
      do 3 case/norP => _; rewrite !(mem_insertE Hg'E).
      move=> Hnx; move/norP=> [_ Hx] HkE.
      rewrite mem_seq2 in Hy; case/orP: Hy; move/eqP=> <- {y}.
        rewrite -[x]Enode Dnx Eh'nX /h eqd_sym.
        move: (eqcP (HkF (edge nx))) (fconnect_invariant HkF (cface_node_ecpY _)).
        rewrite -/g; move->; move <-; rewrite Dx Dnx.
        apply: (etrans (HkE nx)); rewrite (mem_insertE Hg'E).
        apply/hasP => [] [z Hz Hxz]; case/hasP: Hnx; exists z; last done.
        rewrite !mem_cat in Hz |- *; apply/orP; case/orP: Hz; move/mem_sieve; auto.
      have <-: k (edge x) = h' gc.
        by rewrite -(eqcP (HkF (edge x))) -/g Eh'X -Dx /= Enode (negbE Hgp) /=.
      apply: (etrans (HkE x)); rewrite (mem_insertE Hg'E).
      apply/hasP => [] [z Hz Hxz]; case/hasP: Hx; exists z; last done.
      rewrite !mem_cat in Hz |- *; apply/orP; case/orP: Hz; move/mem_sieve; auto.
    move=> u; case: (@fband_icpY _ gc u) => [[x Hx]|Hu].
      case: (@fband_icpY _ gc (edge u)) => [[y Hy]|Heu].
        rewrite /invariant (fconnect_invariant Hk'F Hx).
        rewrite (fconnect_invariant Hk'F Hy) !Ek'.
        have Hxy: adj x y.
          by rewrite -(adj_icpY gc); apply/adjP; exists u; rewrite // Sface.
        case/adjP: Hxy => [z Hxz Hzy]; rewrite (fconnect_invariant Hh'F Hxz).
        rewrite -(fconnect_invariant Hh'F Hzy); exact: Hh'E.
      have Deeu: edge (edge u) = u.
        by move: Heu {Hx}; rewrite cface_ecpY; case: u => [||[||z]].
      by rewrite /invariant eqd_sym -{1}Deeu; apply: Hk'EX; rewrite Sface.
    by apply: Hk'EX; rewrite Sface.
  rewrite /cpmap -/cpmap !cpring_ecpY !maps_adds {1 2}/negb -/gc.
  rewrite Ek'nX !sieve_adds !maps_cat !maps_seqn Ek'X; do 2 congr Adds.
  rewrite -maps_sieve -!maps_comp /comp -/gc -/h.
  rewrite (@eq_maps _ _ (comp k' (icpY gc)) _ Ek').
  by rewrite head_cpring (head_cpring g) in Eh; case: Eh.
case: mr mc Emc Emr Dcpc => [|b1 [|b2 mr]] // [|b3 [|b4 [|b5 mc]]] //.
case Hb: (nsp b3 b1 b4 || nsp b3 b2 b5); first done.
case HbA: (and3b _ _ _); first done.
rewrite [size _]/= [size _ = _]/= => [] [Emc] [Emr].
move: {Hrec}(Hrec (Adds b4 (Adds b5 mr)) mc Emr Emc).
case: (cfctr (Seq b4 b5 & mr) mc cp) cpc => // [cpc] _ Hrec [<-] k [HkE HkF].
pose h x := k (icpH g x).
have HhF: invariant face h =1 g.
  move=> x; apply/eqP; apply: (fconnect_invariant HkF).
  by rewrite cface_icpH Sface fconnect1.
have Hg'E := plain_ecpH g HgE.
have HhE: invariant edge h =1
   insertE (cat (sieve (Seq b4 b5 & mr) (cpring g)) (sieve mc (ctrenum cp))).
  move=> x; rewrite /invariant /h -icpH_edge; apply: (etrans (HkE _)).
  rewrite !mem_insertE // cpring_ecpH //.
  rewrite {2}head_proper_cpring //.
  rewrite (eq_has (plain_orbit HgE x)) (eq_has (plain_orbit Hg'E (icpH g x))).
  rewrite !has_cat icpH_edge [ctrenum _]/= !has_sieve_adds.
  rewrite !andbF !orFb orbCA -!orbA; congr 1 orb.
  rewrite [_ && _]/= /long_cpring [_ && _]/= Enode (negbE Hgp) andbF orFb orbCA.
  by do 2 congr orb; rewrite -maps_sieve has_maps; apply: eq_has.
case: {Hrec}(Hrec h); first by split.
set gc := cpmap cpc => h' Hh' Eh.
move: Hh' (coloring_proper_cpring gc Hh') => [Hh'E Hh'F] Hgcp.
have EkefX: k (edge (face (ecpH g))) = h g.
  apply: (fconnect_invariant HkF); apply connect1; apply/eqP.
  by rewrite /= Enode (negbE Hgp).
have HrgE: (all (invariant edge h) (sieve (Seq b4 b5 & mr) (cpring g))).
  apply/allP => [x Hx]; rewrite HhE mem_insertE //.
  apply/hasP; exists x; last exact: connect0.
  by rewrite mem_cat /setU Hx.
have HrgN: (fpath (finv node) (node g) (add_last (behead (cpring g)) (node g))).
  rewrite (fpath_finv (Inode g)) last_add_last belast_add_last -head_cpring.
  move: (cycle_rev_cpring g).
  by rewrite head_cpring (cycle_path g) rev_adds last_add_last.
case: b3 Hb HhE HrgE HkE Eh.
  case: b1 {HbA} => //; case: b2 => //; case: b4 b5 => [|] [|] // _ _ _ HkE Eh.
  exists h'; first by split.
  rewrite -/gc Eh head_proper_cpring // cpring_ecpH //.
  rewrite !maps_sieve !maps_adds -maps_comp.
  rewrite (fconnect_invariant HkF (cface_node_ecpH Hgp)) -/(h (node g)).
  do 2 congr Adds; apply: eqP; rewrite -(eqcP (HkF _)) -EkefX.
  apply: (etrans (HkE _)).
  by rewrite insertE_cat mem_cat; apply/orP; right; exact: setU11.
case Hb12: (b1 && b2).
  case: b1 Hb12 HbA => //; case: b2 => //  _ HbA.
  case: b4 => //; case: b5 => // _ HhE HrgE HkE Eh.
  have Hgcl: long_cpring gc.
    rewrite size_long_cpring -(size_maps h') Eh; move/(introT eqP): Emr HbA.
    rewrite -size_ring_cpmap -/g; case: (cpring g) => [|x0 [|x1 p]] {x0 x1}//=.
    by rewrite !ltnS !eqdSS; elim: (mr) p => [|[|] m Hrec] [|x p] //=; auto.
  rewrite (head_proper_cpring Hgp) head_proper_cpring //= in Eh.
  move: Eh => [EhnX EhX Eh].
  have EhfeX: h' (face (edge gc)) = h (face (edge g)).
    rewrite head_long_cpring //= in Eh; move: HrgN Eh HrgE.
    rewrite head_proper_cpring //= drop0; case/andP=> _.
    elim: (mr) {-2}(g : g) (drop 2 (cpring g)) => [|b m Hrec] // x [|y p] //=.
    case/andP; move/eqP=> Dy Hp; rewrite -(finv_eq_monic (Enode g) x) Dy.
    case: b; last by case.
    move=> /= Eh; case/andP; move/eqcP=> <- Hmp.
    by rewrite -(eqcP (HhF (edge y))); eauto.
  have Eh'A: h' (node gc) = h' (face (edge gc)).
    rewrite EhnX EhfeX (eqcP (HhF (edge g))).
    rewrite /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
    transitivity (k (face (edge (node (ecpH g))))); apply: eqP.
      rewrite eqd_sym (eqcP (HkF _)); apply: (etrans (HkE _)).
      rewrite head_cpring; exact: setU11.
    rewrite Enode eqd_sym -(eqcP (HkF _)) /= Enode (negbE Hgp) set11.
    apply: (etrans (HkE (ecpH g))).
    by rewrite cpring_ecpH //; do 2 apply: setU1r; apply: setU11.
  have Hh'FA: @invariant (ecpA gc) face _ h' =1 gc.
    rewrite /invariant /= /ecpA_face => x.
    case (cface (edge gc) (node gc)); first exact: Hh'F.
    case: (x =P edge gc) => [Dx|_].
      by rewrite /setA -(eqcP (Hh'F x)) Dx -Eh'A set11.
    case: (face x =P node gc) => [Dx|_]; last exact: Hh'F.
    by rewrite /setA -(eqcP (Hh'F x)) Dx -Eh'A set11.
  exists h'.
    split; last done; rewrite /invariant /= /ecpA_edge /= -/gc => x.
    case (cface (edge gc) (node gc)); last exact: Hh'E.
     case: (x =P gc) => /= [Dx|_].
       rewrite -(eqcP (Hh'F _)) Enode Eh'A (eqcP (Hh'F _)) Dx; exact: Hh'E.
     case: (x =P node (node gc)) => /= [Dx|_]; last exact: Hh'E.
     rewrite -(eqcP (Hh'F _)) -Eh'A -[node gc]Enode -Dx (eqcP (Hh'F _)).
     exact: Hh'E.
  rewrite /cpmap -/cpmap -/gc cpring_ecpA Hgcl cpring_ecpH //=.
  by rewrite -maps_sieve -maps_comp; rewrite drop_behead in Eh.
case: b1 b2 b4 b5 Hb12 {HbA} => [|] [|] // [|] [|] // _ _;
  rewrite /cpmap -/cpmap -/gc.
- move=> _ _ HkE Eh; exists h'; first by split.
  rewrite Eh (head_proper_cpring Hgp) cpring_ecpH // !maps_sieve !maps_adds.
  rewrite -maps_comp; congr Adds; apply: eqP.
  rewrite /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)) eqd_sym.
  rewrite -{1}[ecpH g : dart _]Enode (eqcP (HkF _)).
  by apply: (etrans (HkE _)); rewrite head_cpring; exact: setU11.
- move=> HhE HrgE HkE Eh.
  pose a u x := cface u (icpK gc x).
  have EaF: a =2 comp a face by move=> u x; exact: cface1.
  pose k' u := if pick (a u) is Some x then h' x else Color0.
  have Hk'F: invariant face k' =1 ecpK gc.
    by move=> u; apply/eqP; rewrite /k' (eq_pick (EaF u)).
  have Ek': forall x, k' (icpK _ x) = h' x.
    move=> x; rewrite /k' -/gc; case: pickP => [y Hy|Hx].
      by rewrite /a cface_icpK Sface in Hy; apply: (fconnect_invariant Hh'F).
    case/idP: (Hx x); exact: connect0.
  rewrite (head_proper_cpring Hgp) (head_proper_cpring Hgcp) /= in Eh.
  move: Eh => [EhnX EhX Eh].
  have EkX: (k (ecpH g) = h' (node gc)).
    apply: eqP; rewrite EhnX -[ecpH g : ecpH g]Enode (eqcP (HkF _)).
    rewrite /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
    apply: (etrans (HkE _)); rewrite head_cpring; exact: setU11.
  exists k'; first split=> //.
    set x0 : ecpK gc := ecpN (ecpR' gc).
    have Hk'EX: invariant edge k' x0 = false.
      rewrite /invariant; have <-: h' (face (edge gc)) = k' (edge x0).
        rewrite (eqcP (Hh'F _)) -Ek'; apply: (fconnect_invariant Hk'F).
        by apply connect1; apply/eqP; rewrite /ecpK /x0 ecpR'_eq /= Enode set11.
      have <-: k (ecpH g) = k' x0.
        symmetry; rewrite EkX -Ek'; apply: (fconnect_invariant Hk'F).
        by apply connect1; apply/eqP; rewrite /ecpK /x0 ecpR'_eq.
      have <-: (h (face (edge g)) = h' (face (edge gc))).
        move: HrgN HrgE (introT eqP Emr); rewrite -size_ring_cpmap -/g.
        rewrite (head_proper_cpring Hgp) /= !eqdSS; case/andP; clear.
        move: {-2}(g : g) (drop 2 (cpring g)) Eh.
        elim: (mr) => [|b m Hrec] x [|y p] //= Eh; case/andP;
         move/eqP=> Dy; rewrite -(finv_eq_monic (Enode g) x) {}Dy.
          have Hgcl: long_cpring gc = false; last by move/eqP: Hgcl => ->.
          by rewrite size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
        case: b Eh => [|] /= Eh Hp.
          by case/andP; move/eqcP=> <-; rewrite -(eqcP (HhF (edge y))); eauto.
        have Hgcl: long_cpring gc.
          by rewrite size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
        by rewrite head_long_cpring // in Eh; case: Eh.
      have <-: k (edge (ecpH g)) = h (face (edge g)).
        rewrite (eqcP (HhF (edge g))); symmetry; apply: (fconnect_invariant HkF).
        by apply: connect1; apply/eqP; rewrite /= Enode (negbE Hgp) set11.
      apply: (etrans (HkE _)).
      move: (uniq_ctrenum Hcp'); rewrite /cpmap -/cpmap -/g cpring_ecpH //.
      rewrite !cat_adds -2!cat1s 2!insertE_cat uniq_catC -catA uniq_cat.
      case/and3P=> [_ Ug _]; rewrite -rot_size_cat has_rot -insertE_cat in Ug.
      rewrite has_sym catA in Ug; move: {Ug}(hasPn Ug _ (setU11 _ _)).
      rewrite !mem_insertE //; move=> Ug; apply/hasP => [[v Hv Huv]].
      case/hasP: Ug; exists v; last done; move: Hv; rewrite !mem_cat.
      case/orP=> Hv; apply/orP; last by right; apply: (mem_sieve Hv).
      by left; apply: (@mem_sieve _ (Adds true mr)).
    move=> [||x] //; first by rewrite /invariant eqd_sym.
    rewrite -[Icp x]/(icpK gc x) /invariant icpK_edge !Ek'; exact: Hh'E.
  rewrite cpring_ecpK cpring_ecpH // maps_sieve !maps_adds -!maps_comp.
  rewrite (@eq_maps _ _ (comp k' (icpK gc)) _ Ek') Eh maps_sieve; congr Adds.
  by rewrite EkX (fconnect_invariant Hk'F (cface_node_ecpK _)) Ek'.
- move=> HhE _ _ Eh; exists h'; first by split.
  rewrite Eh (head_proper_cpring Hgp) cpring_ecpH // !maps_sieve !maps_adds.
  rewrite -maps_comp; congr Adds; apply: eqP.
  rewrite (fconnect_invariant HkF (cface_node_ecpH Hgp)).
  rewrite -{1}[g : g]Enode (eqcP (HhF _)).
  by apply: (etrans (HhE _)); rewrite head_cpring; apply: setU11.
- move=> HhE HrgE HkE Eh.
  pose a u x := cface u (icpK gc x).
  have EaF: a =2 comp a face by move=> u x; exact: cface1.
  pose k' u := if pick (a u) is Some x then h' x else Color0.
  have Hk'F: invariant face k' =1 ecpK gc.
    by move=> u; apply/eqP; rewrite /k' (eq_pick (EaF u)).
  have Ek': forall x, k' (icpK _ x) = h' x.
    move=> x; rewrite /k' -/gc; case: pickP => [y Hy|Hx].
      by rewrite /a cface_icpK Sface in Hy; apply: (fconnect_invariant Hh'F).
    case/idP: (Hx x); exact: connect0.
  rewrite (head_proper_cpring Hgp) (head_proper_cpring Hgcp) /= in Eh.
  move: Eh => [EhnX EhX Eh].
  exists k'; first split=> //.
    set x0 : ecpK gc := ecpN (ecpR' gc).
    have Hk'EX: invariant edge k' x0 = false.
      rewrite /invariant; have <-: h' (face (edge gc)) = k' (edge x0).
        rewrite (eqcP (Hh'F _)) -Ek'; apply: (fconnect_invariant Hk'F).
        by apply connect1; apply/eqP; rewrite /ecpK /x0 ecpR'_eq /= Enode set11.
      have <-: h (face (edge g)) = h' (face (edge gc)).
      move: HrgN HrgE (introT eqP Emr); rewrite -size_ring_cpmap -/g.
        rewrite (head_proper_cpring Hgp) /= !eqdSS; case/andP=> _.
        move: {-2}(g : g) (drop 2 (cpring g)) Eh.
        elim: (mr) => [|b m Hrec] x [|y p] //= Eh; case/andP;
          move/eqP=> Dy; rewrite -(finv_eq_monic (Enode g) x) {}Dy.
          have Hgcl: long_cpring gc = false.
            by rewrite size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
          by move/eqP: Hgcl; move->.
        case: b Eh => [|] /= Eh Hp.
          by case/andP; move/eqcP=> <-; rewrite -(eqcP (HhF (edge y))); eauto.
        have Hgcl: (long_cpring gc).
          by rewrite size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
        by rewrite head_long_cpring // in Eh; case: Eh.
      have <-: k (edge (ecpH g)) = h (face (edge g)).
        rewrite (eqcP (HhF (edge g))); symmetry; apply: (fconnect_invariant HkF).
        by apply: connect1; apply/eqP; rewrite /= Enode (negbE Hgp) set11.
      have <-: k (node (ecpH g)) = k' x0.
        rewrite (fconnect_invariant HkF (cface_node_ecpH Hgp)) -/(h (node g)).
        symmetry; rewrite -EhnX -Ek'; apply: (fconnect_invariant Hk'F).
        by apply connect1; apply/eqP; rewrite /ecpK /x0 ecpR'_eq.
      have <-: k (edge (node (ecpH g))) = k (edge (ecpH g)).
        rewrite -(eqcP (HkF _)) Enode; symmetry; apply: eqP.
        apply: (etrans (HkE _)); rewrite cpring_ecpH //; exact: setU11.
      apply: (etrans (HkE _)).
      move: (uniq_ctrenum Hcp'); rewrite /cpmap -/cpmap -/g cpring_ecpH //.
      rewrite !cat_adds -cat1s insertE_cat uniq_cat; case/and3P=> [_ Ug _].
      rewrite has_sym -cat_adds in Ug; move: {Ug}(hasPn Ug _ (setU11 _ _)).
      rewrite !mem_insertE // => Ug; apply/hasP => [] [v Hv Huv].
      case/hasP: Ug; exists v; last done; move: Hv; rewrite !mem_cat.
      case/orP=> Hv; apply/orP; last by right; apply: (mem_sieve Hv).
      by left; apply: (@mem_sieve _ (Adds true mr)).
    move=> [||x] //; first by rewrite /invariant eqd_sym.
    rewrite -[Icp x]/(icpK gc x) /invariant icpK_edge !Ek'; exact: Hh'E.
  rewrite cpring_ecpK cpring_ecpH // maps_sieve !maps_adds -!maps_comp.
  rewrite (@eq_maps _ _ (comp k' (icpK gc)) _ Ek') Eh maps_sieve; congr Adds.
  rewrite (fconnect_invariant Hk'F (cface_node_ecpK _)) Ek'.
  by rewrite (fconnect_invariant HkF (cface_node_ecpH Hgp)).
- move=> HhE HrgE HkE Eh.
  pose a u x := cface u (icpU gc x).
  have EaF: a =2 comp a face by move=> u x; exact: cface1.
  pose k' u := if pick (a u) is Some x then h' x else k (ecpH g).
  have Hk'F: invariant face k' =1 ecpU gc.
    by move=> u; apply/eqP; rewrite /k' (eq_pick (EaF u)).
  have Ek': forall x, k' (icpU _ x) = h' x.
    move=> x; rewrite /k' -/gc.
    case: pickP => [y Hy|Hx].
      by rewrite /a cface_icpU Sface in Hy; apply: (fconnect_invariant Hh'F).
    case/idP: (Hx x); exact: connect0.
  have Ek'X: k' (ecpU gc) = k (ecpH g).
    by rewrite /k'; case: pickP => // y; rewrite /a cface_ecpU.
  rewrite (head_proper_cpring Hgp) head_cpring /= in Eh.
  have Ek'eX: h (face (edge g)) = k' (edge (ecpU gc)).
    have <-: h' (node gc) = k' (edge (ecpU gc)).
      by rewrite -(eqcP (Hk'F _)) -Ek'.
    move: HrgN HrgE; rewrite (head_proper_cpring Hgp) /=.
    move/andP=> [_ H]; move/and3P=> [_ _ H']; move: H H'.
    move: {-2}(g : g) (drop 2 (cpring g)) Eh.
    elim: (mr) => [|b m Hrec] x [|y p] //= Eh.
    case/andP; move/eqP=> Dy; rewrite -(finv_eq_monic (Enode g) x) {}Dy.
    case: b Eh => [|] /= Eh Hp; last by case: Eh.
    by case/andP; move/eqcP=> <-; rewrite -(eqcP (HhF (edge y))); eauto.
  exists k'; first split=> //.
    have Hk'EX: invariant edge k' (ecpU gc) = false.
      rewrite /invariant Ek'X -Ek'eX.
      have <-: (k (edge (ecpH g)) = h (face (edge g))).
        rewrite (eqcP (HhF (edge g))); symmetry; apply: (fconnect_invariant HkF).
        by apply: connect1; apply/eqP; rewrite /= Enode (negbE Hgp) set11.
      apply: (etrans (HkE _)).
      move: (uniq_ctrenum Hcp'); rewrite /cpmap -/cpmap -/g cpring_ecpH //.
      rewrite !cat_adds -2!cat1s 2!insertE_cat !uniq_cat.
      case/and5P=> [_ _ _ Ug _]; rewrite has_sym in Ug.
      move: {Ug}(hasPn Ug _ (setU11 _ _)); rewrite !mem_insertE // => Ug.
      apply/hasP => [] [v Hv Huv]; case/hasP: Ug; exists v; last done.
      move: Hv; rewrite !mem_cat.
      case/orP=> Hv; apply/orP; last by right; apply: (mem_sieve Hv).
      by left; apply: (@mem_sieve _ mr).
    move=> [||x] //; first by rewrite /invariant eqd_sym.
    rewrite -[Icp x]/(icpU gc x) /invariant -icpU_edge !Ek'; exact: Hh'E.
  rewrite cpring_ecpU cpring_ecpH // maps_sieve !maps_adds -!maps_comp.
  rewrite (@eq_maps _ _ (comp k' (icpU gc)) _ Ek') head_cpring maps_adds Eh Ek'X.
  rewrite maps_sieve; congr Adds.
  rewrite (fconnect_invariant HkF (cface_node_ecpH Hgp)) -/(h (node g)).
  apply: (etrans (esym Ek'eX)); transitivity (h g); apply: eqP.
    rewrite (eqcP (HhF _)); apply: (etrans (HhE _)).
    rewrite head_proper_cpring //; do 2 apply: setU1r; exact: setU11.
  rewrite -{1}[g : g]Enode (eqcP (HhF _)); apply: (etrans (HhE _)).
  rewrite head_cpring; exact: setU11.
- move=> HhE HrgE HkE Eh.
  pose a u x := cface u (icpY gc x).
  have EaF: a =2 comp a face by move=> u x; exact: cface1.
  pose k' u := if pick (a u) is Some x then h' x else k (ecpH g).
  have Hk'F: invariant face k' =1 ecpY gc.
    by move=> u; apply/eqP; rewrite /k' (eq_pick (EaF u)).
  have Ek': forall x, k' (icpY _ x) = h' x.
    move=> x; rewrite /k' -/gc; case: pickP => [y Hy|Hx].
      by rewrite /a cface_icpY Sface in Hy; apply: (fconnect_invariant Hh'F).
    case/idP: (Hx x); exact: connect0.
  have Ek'X: k' (ecpY gc) = k (ecpH g).
    by rewrite /k'; case: pickP => // y; rewrite /a cface_ecpY.
  rewrite (head_proper_cpring Hgp) head_cpring /= in Eh; move: Eh => [EhnX Eh].
  have Ehng: h (node g) = h g.
    symmetry; rewrite -{1}[g : g]Enode (eqcP (HhF _)); apply: eqP.
    apply: (etrans (HhE _)); rewrite head_cpring; exact: setU11.
  have Ek'nX: k' (node (ecpY _)) = k (node (ecpH _)).
    rewrite (fconnect_invariant Hk'F (cface_node_ecpY _)) Ek' EhnX -Ehng.
    by rewrite (fconnect_invariant HkF (cface_node_ecpH Hgp)).
  have Eh'X: h' gc = h (face (edge g)).
    rewrite head_proper_cpring //= in Eh; move: HrgN HrgE {HhE HkE}.
    rewrite head_proper_cpring //=.
    case/andP=> [_ H]; case/andP=> [_ H']; move: H H'.
    elim: (mr) {-2}(g : g) (drop 2 (cpring g)) Eh => [|b m Hrec] x [|y p] //= Eh.
    case/andP; move/eqP=> Dy Hp; rewrite -(finv_eq_monic (Enode g) x) {}Dy.
    case: b Eh => [|] /= Eh; last by case: Eh.
    by case/andP; move/eqcP=> <-; rewrite -(eqcP (HhF _)); eauto.
  exists k'; first split=> //.
    have Hk'EX: forall u, cface u (ecpY _) -> invariant edge k' u = false.
      move=> u HuX; rewrite /invariant (fconnect_invariant Hk'F HuX) Ek'X.
      have HeuX: adj (ecpY _) (edge u) by rewrite -(adjF HuX) adjE.
      rewrite (adj_ecpY Hgcp) /fband in HeuX; case/hasP: HeuX {HuX} => v.
      case/mapsP=> [y Hy <-] {v} H; rewrite {u H}(fconnect_invariant Hk'F H) Ek'.
      move: HkE (uniq_ctrenum Hcp') {x Hx}.
      rewrite /cpmap -/cpmap -/g cpring_ecpH // => HkE.
      rewrite -!cat1s -!catA catA insertE_cat uniq_cat has_sym.
      case/and3P=> [_ Ug _].
      rewrite mem_seq2 in Hy; case/orP: Hy; move/eqP=> <- {y}.
        rewrite EhnX -Ehng /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
        rewrite eqd_sym -{1}[ecpH g : ecpH g]Enode (eqcP (HkF _)).
        apply: (etrans (HkE _)); rewrite mem_insertE // has_cat !has_sieve_adds.
        rewrite !andFb !orFb -has_cat; apply/hasP => [] [u Hu HuX].
        move: (hasPn Ug _ (setU11 _ _)); rewrite mem_insertE //; case/hasP.
        exists u; last done; rewrite mem_cat; apply/orP.
        by rewrite mem_cat in Hu; case/orP: Hu => Hu; move: (mem_sieve Hu); auto.
      rewrite Eh'X; have <-: k (edge (ecpH g)) = h (face (edge g)).
        rewrite (eqcP (HhF _)); symmetry; apply: (fconnect_invariant HkF).
        by apply: connect1; apply/eqP; rewrite /= Enode (negbE Hgp) /= set11.
      apply: (etrans (HkE _)); rewrite mem_insertE // has_cat !has_sieve_adds.
      rewrite !andFb !orFb -has_cat; apply/hasP => [[u Hu HuX]].
      move: (hasPn Ug _ (setU1r _ (setU1r _ (setU11 _ _)))).
      rewrite mem_insertE //; case/hasP.
      exists u; last done; rewrite mem_cat; apply/orP.
      by rewrite mem_cat in Hu; case/orP: Hu => Hu; move: (mem_sieve Hu); auto.
    move=> u; case: (@fband_icpY _ gc u) => [[x Hx]|Hu].
      case: (@fband_icpY _ gc (edge u)) => [[y Hy]|Heu].
        rewrite /invariant (fconnect_invariant Hk'F Hx).
        rewrite (fconnect_invariant Hk'F Hy) !Ek'.
        have Hxy: adj x y.
          by rewrite -(adj_icpY gc); apply/adjP; exists u; rewrite // Sface.
        case/adjP: Hxy => [z Hxz Hzy]; rewrite (fconnect_invariant Hh'F Hxz).
        rewrite -(fconnect_invariant Hh'F Hzy); exact: Hh'E.
      have Deeu: edge (edge u) = u.
        by move: Heu {Hx}; rewrite cface_ecpY; case: u => [||[||z]].
      by rewrite /invariant eqd_sym -{1}Deeu; apply: Hk'EX; rewrite Sface.
    by apply: Hk'EX; rewrite Sface.
  rewrite /cpmap -/cpmap cpring_ecpY cpring_ecpH // !maps_sieve !maps_adds.
  rewrite Ek'nX Ek'X -!maps_comp (@eq_maps _ _ (comp k' (icpY gc)) _ Ek') Eh.
  by rewrite maps_sieve.
- move=> HhE HrgE HkE Eh.
  pose a u x := cface u (icpY gc x).
  have EaF: a =2 comp a face by move=> u x; exact: cface1.
  pose k' u := if pick (a u) is Some x then h' x else k (ecpH g).
  have Hk'F: invariant face k' =1 ecpY gc.
    by move=> u; apply/eqP; rewrite /k' (eq_pick (EaF u)).
  have Ek': forall x, k' (icpY gc x) = h' x.
    move=> x; rewrite /k' -/gc; case: pickP => [y Hy|Hx].
      by rewrite /a cface_icpY Sface in Hy; apply: (fconnect_invariant Hh'F).
    by case/idP: (Hx x); exact: connect0.
  have Ek'X: k' (ecpY gc) = k (ecpH g).
    by rewrite /k'; case: pickP => // y; rewrite /a cface_ecpY.
  rewrite (head_proper_cpring Hgp) head_cpring /= in Eh; move: Eh => [EhnX Eh].
  have Ehfeg: h (face (edge g)) = h g.
    rewrite (eqcP (HhF _)); apply: eqP.
    by apply: (etrans (HhE _)); rewrite head_proper_cpring //; apply: setU11.
  have Ek'nX: k' (node (ecpY gc)) = k (node (ecpH g)).
    rewrite (fconnect_invariant Hk'F (cface_node_ecpY _)) Ek' EhnX.
    by rewrite (fconnect_invariant HkF (cface_node_ecpH Hgp)).
  have Eh'X: h' gc = h (face (edge g)).
    rewrite head_proper_cpring //= in Eh; move: HrgN HrgE {HhE HkE}.
    rewrite head_proper_cpring //=.
    case/andP=> [_ H]; case/andP=> [_ H']; move: H H'.
    elim: (mr) {-2}(g : g) (drop 2 (cpring g)) Eh => [|b m Hrec] x [|y p] //= Eh.
    case/andP; move/eqP=> Dy Hp; rewrite -(finv_eq_monic (Enode g) x) {}Dy.
    case: b Eh => [|] /= Eh; last by case: Eh.
    by case/andP; move/eqcP=> <-; rewrite -(eqcP (HhF _)); eauto.
  exists k'; first split=> //.
    have Hk'EX: forall u, cface u (ecpY gc) -> invariant edge k' u = false.
      move=> u HuX; rewrite /invariant (fconnect_invariant Hk'F HuX) Ek'X.
      have HeuX: adj (ecpY gc) (edge u) by rewrite -(adjF HuX) adjE.
      rewrite (adj_ecpY Hgcp) /fband in HeuX; case/hasP: HeuX {HuX} => v.
      case/mapsP=> [y Hy <-] {v} H; rewrite {u H}(fconnect_invariant Hk'F H) Ek'.
      move: HkE (uniq_ctrenum Hcp') {x Hx}.
      rewrite /cpmap -/cpmap -/g cpring_ecpH // => HkE.
      rewrite -!cat1s -!catA catA insertE_cat uniq_cat has_sym.
      case/and3P=> [_ Ug _].
      rewrite mem_seq2 in Hy; case/orP: Hy; move/eqP=> <- {y}.
        rewrite EhnX /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
        rewrite eqd_sym -{1}[ecpH g : ecpH g]Enode (eqcP (HkF _)).
        apply: (etrans (HkE _)); rewrite mem_insertE // has_cat !has_sieve_adds.
        rewrite !andFb !orFb -has_cat; apply/hasP => [] [u Hu HuX].
        move: (hasPn Ug _ (setU11 _ _)); rewrite mem_insertE //; case/hasP.
        exists u; last done; rewrite mem_cat; apply/orP.
        by rewrite mem_cat in Hu; case/orP: Hu => Hu; move: (mem_sieve Hu); auto.
      rewrite Eh'X; have <-: k (edge (ecpH g)) = h (face (edge g)).
        rewrite (eqcP (HhF _)); symmetry; apply: (fconnect_invariant HkF).
        by apply: connect1; apply/eqP; rewrite /= Enode (negbE Hgp) /= set11.
      apply: (etrans (HkE _)); rewrite mem_insertE // has_cat !has_sieve_adds.
      rewrite !andFb !orFb -has_cat; apply/hasP => [[u Hu HuX]].
      move: (hasPn Ug _ (setU1r _ (setU1r _ (setU11 _ _)))).
      rewrite mem_insertE //.
      case/hasP; exists u; last done; rewrite mem_cat; apply/orP.
      by rewrite mem_cat in Hu; case/orP: Hu => Hu; move: (mem_sieve Hu); auto.
    move=> u; case: (@fband_icpY _ gc u) => [[x Hx]|Hu].
      case: (@fband_icpY _ gc (edge u)) => [[y Hy]|Heu].
        rewrite /invariant (fconnect_invariant Hk'F Hx).
        rewrite (fconnect_invariant Hk'F Hy) !Ek'.
        have Hxy: adj x y.
          by rewrite -(adj_icpY gc); apply/adjP; exists u; rewrite // Sface.
        case/adjP: Hxy => [z Hxz Hzy]; rewrite (fconnect_invariant Hh'F Hxz).
        by rewrite -(fconnect_invariant Hh'F Hzy); apply: Hh'E.
      have Deeu: edge (edge u) = u.
        by move: Heu {Hx}; rewrite cface_ecpY; case: u => [||[||z]].
      by rewrite /invariant eqd_sym -{1}Deeu; apply: Hk'EX; rewrite Sface.
    by apply: Hk'EX; rewrite Sface.
  rewrite /cpmap -/cpmap cpring_ecpY cpring_ecpH // !maps_sieve !maps_adds Ek'nX.
  by rewrite Ek'X -!maps_comp (@eq_maps _ _ (comp k' _) _ Ek') Eh maps_sieve.
move=> HhE HrgE HkE Eh.
pose a u x := cface u (icpH gc x).
have EaF: a =2 comp a face by move=> u x; exact: cface1.
pose k' u := if pick (a u) is Some x then h' x else k (ecpH g).
have Hk'F: invariant face k' =1 ecpH gc.
  by move=> u; apply/eqP; rewrite /k' (eq_pick (EaF u)).
have Ek': forall x, k' (icpH _ x) = h' x.
  move=> x; rewrite /k' -/gc; case: pickP => [y Hy|Hx].
    by rewrite /a cface_icpH Sface in Hy; apply: (fconnect_invariant Hh'F).
  by case/idP: (Hx x); exact: connect0.
have Ek'X: k' (ecpH gc) = k (ecpH g).
  by rewrite /k'; case: pickP => // y; rewrite /a cface_ecpH.
rewrite (head_proper_cpring Hgp) head_proper_cpring //= in Eh.
move: Eh => [EhnX EhX Eh].
have Ek'nX: k' (node (ecpH gc)) = k (node (ecpH g)).
  rewrite (fconnect_invariant Hk'F (cface_node_ecpH Hgcp)) Ek' EhnX.
  by rewrite (fconnect_invariant HkF (cface_node_ecpH Hgp)).
have Eh'feX: h' (face (edge gc)) = h (face (edge g)).
move: HrgN HrgE (introT eqP Emr) {HhE HkE}; rewrite -size_ring_cpmap -/g.
  rewrite head_proper_cpring //= !eqdSS; case/andP=> _.
  elim: (mr) {-2}(g : g) (drop 2 (cpring g)) Eh => [|b m Hrec] x [|y p] //= Eh;
    case/andP; move/eqP=> Dy Hp; rewrite -(finv_eq_monic (Enode g) x) {}Dy.
    have Hgcl: long_cpring gc = false.
      by rewrite size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
    by rewrite -EhnX; move/eqP: Hgcl => <-.
  case: b Eh => [|] /= Eh.
    by case/andP; move/eqcP=> <-; rewrite -(eqcP (HhF _)); eauto.
  have Hgcl: long_cpring gc.
    by rewrite size_long_cpring -(size_maps h') head_proper_cpring //= Eh.
  by rewrite (head_long_cpring Hgcl) in Eh; case: Eh.
exists k'; first split=> //.
  have Hk'EX: forall u, cface u (ecpH gc) -> invariant edge k' u = false .
    move=> u HuX; rewrite /invariant (fconnect_invariant Hk'F HuX) Ek'X.
    have HeuX: (adj (ecpH _) (edge u)) by rewrite -(adjF HuX) adjE.
    rewrite (adj_ecpH Hgcp) /fband in HeuX; case/hasP: HeuX {HuX} => v.
    case/mapsP=> [y Hy <-] {v} H; rewrite {u H}(fconnect_invariant Hk'F H) Ek'.
    move: HkE (uniq_ctrenum Hcp') {x Hx}.
    rewrite /cpmap -/cpmap -/g cpring_ecpH //; move=> HkE.
    rewrite -!cat1s -!catA catA insertE_cat uniq_cat has_sym.
    case/and3P=> [_ Ug Ug']; rewrite insertE_cat uniq_catC -insertE_cat in Ug'.
    simpl in Ug'; case/andP: Ug' => [Ug' _]; rewrite /= /setU1 in Ug'.
    move: Ug'; repeat case/norP => _; move=> Ug'.
    rewrite mem_seq3 in Hy; case/or3P: Hy; move/eqP=> <-{y}.
    - rewrite EhnX /h -(fconnect_invariant HkF (cface_node_ecpH Hgp)).
      rewrite eqd_sym -{1}[ecpH g : ecpH g]Enode (eqcP (HkF _)).
      apply: (etrans (HkE _)); rewrite mem_insertE // has_cat !has_sieve_adds.
      rewrite !andFb !orFb -has_cat; apply/hasP => [] [u Hu HuX].
      move: (hasPn Ug _ (setU11 _ _)); rewrite mem_insertE //; case/hasP.
      exists u; last done; rewrite mem_cat; apply/orP.
      by rewrite mem_cat in Hu; case/orP: Hu => Hu; move: (mem_sieve Hu); auto.
    - rewrite EhX -(eqcP (HkF _)).
      have <-: k (edge (face (ecpH g))) = h g.
        apply: (fconnect_invariant HkF); apply: connect1; apply/eqP.
        by rewrite /= Enode (negbE Hgp).
      apply: (etrans (HkE _)); rewrite mem_insertE //=.
      apply/hasP => [[u Hu HuX]]; move: Ug'; rewrite (mem_insertE Hg'E).
      case/hasP; exists u; last done; rewrite mem_cat; apply/orP.
      by rewrite mem_cat in Hu; case/orP: Hu; move/mem_sieve; auto.
    rewrite Eh'feX; have <-: k (edge (ecpH g)) = h (face (edge g)).
      rewrite (eqcP (HhF _)); symmetry; apply: (fconnect_invariant HkF).
      by apply: connect1; apply/eqP; rewrite /= Enode (negbE Hgp) /= set11.
    apply: (etrans (HkE _)); rewrite mem_insertE // has_cat !has_sieve_adds.
    rewrite !andFb !orFb -has_cat; apply/hasP => [] [u Hu HuX].
    move: (hasPn Ug _ (setU1r _ (setU1r _ (setU11 _ _)))).
    rewrite mem_insertE //.
    case/hasP; exists u; last done; rewrite mem_cat; apply/orP.
    by rewrite mem_cat in Hu; case/orP: Hu; move/mem_sieve; auto.
  move=> u; case: (@fband_icpH _ gc u) => [[x Hx]|Hu].
    case: (@fband_icpH _ gc (edge u)) => [[y Hy]|Heu].
      rewrite /invariant (fconnect_invariant Hk'F Hx).
      rewrite (fconnect_invariant Hk'F Hy) !Ek'.
      have Hxy: adj x y.
        by rewrite -(adj_icpH gc); apply/adjP; exists u; rewrite // Sface.
      case/adjP: Hxy => [z Hxz Hzy]; rewrite (fconnect_invariant Hh'F Hxz).
      by rewrite -(fconnect_invariant Hh'F Hzy); apply: Hh'E.
    have Deeu: edge (edge u) = u.
      by move: Heu {Hx}; rewrite cface_ecpH; case: u => [||[||[||z]]].
    by rewrite /invariant eqd_sym -{1}Deeu; apply: Hk'EX; rewrite Sface.
  by apply: Hk'EX; rewrite Sface.
rewrite /cpmap -/cpmap !cpring_ecpH // !maps_sieve !maps_adds.
by rewrite Ek'nX Ek'X -!maps_comp (@eq_maps _ _ (comp k' _) _ Ek') Eh maps_sieve.
Qed.

Lemma sparse_cfctr : forall mr mc cp,
  size mr = cprsize cp -> size mc = ctrmsize cp ->
  let g := cpmap cp in let r := cpring g in
  let cc := cat (maps edge (sieve mr r)) (insertE (sieve mc (ctrenum cp))) in
  if cfctr mr mc cp is Some _ then sparse (Adds g cc) else true.
Proof.
move=> /= mr mc cp; elim: cp mr mc => [|s cp Hrec] mr mc //.
move: (cfctr_config_prog mr mc (Adds s cp)).
case Dcpc: (cfctr mr mc (Adds s cp)) => // [cpc].
case: s Dcpc => // [n||] Dcpc Hcp' Emr Emc;
  have Hcp := config_prog_cubic Hcp'; rewrite /= in Dcpc Hcp Emr Emc;
  move: Hrec (cpmap_plain Hcp) (cpmap_cubic Hcp) (cpmap_proper Hcp);
  rewrite /cpmap -/cpmap; set g := cpmap cp => Hrec HgE HgN Hgp.
- rewrite cpring_ecpR /= -(rot_rotr n mr).
  rewrite -(size_rotr n mr) in Emr; move: Dcpc (Hrec _ _ Emr Emc).
  case: (cfctr (rotr n mr) mc cp) => //= _ _ {cpc}; apply: etrans.
  apply: simple_perm.
    move=> y; congr orb.
      rewrite !(Sface (permF g) y); symmetry; apply: (@same_cnode g).
      exact: fconnect_iter.
    apply: eq_has_r => x {y}; rewrite !mem_cat; congr orb.
    rewrite -(Eface g x) !(mem_maps (Iedge g)).
    by apply: mem_sieve_rot; rewrite /g size_ring_cpmap.
  rewrite /= !size_cat !size_maps; congr S; congr addn; rewrite /rot sieve_cat.
    rewrite -rot_size_cat size_rot -sieve_cat ?cat_take_drop //.
    by rewrite !size_take Emr -size_ring_cpmap.
  by rewrite !size_drop Emr -size_ring_cpmap.
- rewrite /g.
  case Dcp: cp mc mr Emc Emr Dcpc => [|s cp'] [|b3 mc] // [|b1 [|b2 mr]] //.
    case: mr {cp Dcp g Hrec Hcp Hcp' HgE HgN Hgp} => [|b3 [|b4 mr]] //.
    by case: b1 b2 b3 => [|] [|] [|].
  rewrite -Dcp -/g; have Hg'E: plain (ecpY g) by apply: plain_ecpY.
  case Hb123: (nsp b1 b2 b3) => //.
  rewrite [size _]/= [size _ = _]/= => [] [Emc] [Emr].
  move: {Hrec}(Hrec (Adds b3 mr) mc Emr Emc).
  case: (cfctr (Adds b3 mr) mc cp) => // _ Hrec _ {cpc}.
  have <-: (maps (icpY g) (Adds (node g) (ctrenum cp)) = ctrenum (Adds CpY cp)).
    by rewrite /= /g Dcp.
  pose p := cat (maps edge (sieve (Adds b3 mr) (cpring (cpmap cp))))
                (insertE (sieve mc (ctrenum cp))).
  move: Hrec; rewrite /g -/p; rewrite -/g in p |- *.
  rewrite sparse_adds -(eq_has (mem_cpring g)); move/andP=> [Up Hp].
  have HpY: sparse (Adds (ecpY g) (maps (icpY g) (Adds (node g) p))).
    rewrite maps_adds !sparse_adds; apply/and3P; split.
    - rewrite -(eq_has (mem_cpring (ecpY g))) cpring_ecpY -maps_adds.
      apply/hasP => [] [u]; case/mapsP=> /= [y Hy <-] {u} Hry.
      rewrite /setU1 /= (mem_maps (@icpY_inj _ g)) in Hry.
        case/setU1P: Hy => [Dy|Hy].
          by move: (uniq_cpring g); rewrite head_cpring Dy /= Hry.
        by case/hasP: Up; exists y; last exact: mem_behead.
      apply/hasP => [] [u]; case/mapsP=> [y Hy <-] {u} Hry; rewrite Snode in Hry.
      have Hy' := hasPn Up y Hy; case/idP: (Hy').
      by rewrite mem_cpring cnode1 Snode -(@cnode_injcp (seq1 CpY) _ y).
    elim: p Up Hp => [|x p Hrec] //=; move/norP=> [Hx Up].
    rewrite sparse_adds (@sparse_adds (ecpY g)).
    move/andP=> [Hpx Hp]; apply/andP; split; last exact: Hrec.
    apply/hasP => [] [u]; case/mapsP=> [y Hy <- {u}] Hxy.
    case/hasP: Hpx; exists y; first done.
    by rewrite -(@cnode_injcp (seq1 CpY) _ x).
  move: HpY; rewrite -maps_sieve /p head_cpring cpring_ecpY -!cat1s !sieve_cat //.
  rewrite !maps_cat !insertE_cat -maps_sieve -!maps_comp -!catA.
  rewrite -rot_size_cat sparse_rot -!catA -/g => HpY.
  rewrite -rot_size_cat sparse_rot -!catA 2!catA sparse_catCA -!catA.
  move: (sieve mr (behead (cpring g))) (@sieve g mc (ctrenum cp)) HpY => r1 r2.
  set r1' := maps _ r1; set r2' := insertE (maps _ r2).
  have <-: r1' = maps (comp edge (icpY g)) r1 by done.
  have <-: r2' = maps (icpY g) (insertE r2).
    by rewrite {}/r2'; elim: r2 => // *; repeat congr Adds.
  move: {r1 r2 r1' r2'}(cat r1' (cat r2' (seq1 (ecpY g)))) => r Hrec.
  rewrite {1}[cat]lock catA -lock sparse_catCA -!catA {p Up Hp Emc Emr}.
(* Staging the identities avoids spurrious dependent type expansion *)
  move: r Hrec; set h := icpY g; set g' := ecpY g in h |- *.
  have: forall x, h (edge x) = edge (h x) by done.
  have: node (h (node g)) = edge (node g') by rewrite /= set11.
  have: node (edge (node g')) = edge g' by done.
  case: b1 b2 b3 Hb123 g' h => [|] [|] [|] //= _ g' h EhN2 EhN1 EhE r;
    rewrite !sparse_adds /comp ?EhE -?EhN2 -?EhN1 -?(eq_has (cnode1 _)) //.
  by case/andP.
case: mc mr Emc Emr Dcpc => [|b3 [|b4 [|b5 mc]]] [|b1 [|b2 mr]] //.
rewrite [size _]/= [size _ = _]/= => [] [Emc] [Emr].
case Hb: (nsp b3 b1 b4 || nsp b3 b2 b5); first done.
case: (and3b _ _ _); first done.
move: {Hrec}(Hrec (Seq b4 b5 & mr) mc Emr Emc).
case: (cfctr _ _ _) => // [_] Hrec _ {cpc}.
have Hg'E := plain_ecpH g HgE.
have <-: Adds (face (ecpH g)) (maps (icpH g) (Seq (node g) g & (ctrenum cp))) =
          ctrenum (Adds CpH cp) by done.
pose p := cat (maps edge (sieve (Seq b4 b5 & mr) (cpring (cpmap cp))))
              (insertE (sieve mc (ctrenum cp))).
move: Hrec; rewrite /g -/p; rewrite -/g in p |- *.
rewrite sparse_adds -(eq_has (mem_cpring g)); move/andP=> [Up Hp].
have Dng': node (ecpH g) = icpN _ (icpN _ (edge (ecpU g))).
  by rewrite /= /long_cpring /= Enode (negbE Hgp).
have Dn'g: node (icpH g g) = icpN _ (ecpY g).
  by rewrite /= (negbE Hgp) /eqd /= set11.
have Erg': forall x, cpring (ecpH g) (icpH g x) = drop 2 (cpring g) x.
  move=> x; rewrite cpring_ecpH // mem_adds /setU1 Dng'.
  by rewrite -(mem_maps (@icpH_inj _ g)).
have HpH: sparse (Adds (ecpH g) (maps (icpH g) (Seq (node g) g & p))).
  rewrite !maps_adds !sparse_adds; apply/and4P; split.
  - rewrite -(eq_has (mem_cpring (ecpH g))) -!maps_adds.
    apply/hasP; case=> u; case/mapsP=> y Hy <- {u}; rewrite Erg' => Hry.
    move: (uniq_cpring g); rewrite head_proper_cpring //=.
    case/setU1P: Hy => [Dy|Hy]; first by rewrite Dy /setU1 Hry orbT.
    case/setU1P: Hy => [Dy|Hy]; first by rewrite {5}Dy Hry /= andbF.
    by case/hasP: Up; exists y; last exact: (mem_drop Hry).
  - rewrite -maps_adds.
    apply/hasP; case=> u; case/mapsP=> y Hy <- {u} Hry; rewrite Snode in Hry.
    simpl in Hy; case/setU1P: Hy => [Dy|Hy].
      move: Hry; rewrite fconnect_orbit /orbit.
      have HyN: setC (rev (cpring (ecpH g))) (icpH g y).
        rewrite /setC mem_rev Erg' -Dy.
        move: (uniq_cpring g); rewrite head_proper_cpring //= drop0.
        by case/andP=> _; case/andP.
      (* staging computation prevents divergence on Qed. *)
      have ->: order node (icpH g y) = 3.
        apply: eqP; move: (ecpH g) (cubic_ecpH HgN) (icpH g y) HyN => g'.
        exact: subsetP.
      rewrite -Dy /traject /mem /setU1 Dn'g orbF; exact: negP.
    have Hy' := hasPn Up y Hy; case/idP: (Hy').
      by rewrite mem_cpring cnode1 Snode -(@cnode_injcp (seq1 CpH) _ y).
    apply/hasP => [] [u]; case/mapsP=> [y Hy <- {u}] Hry; rewrite Snode in Hry.
    have Hy' := hasPn Up y Hy; case/idP: (Hy').
    by rewrite mem_cpring Snode -(@cnode_injcp (seq1 CpH) _ y).
  elim: p Up Hp => [|x p Hrec] //=; move/norP=> [Hx Up].
  rewrite (@sparse_adds g) (@sparse_adds (ecpH g)).
  move/andP=> [Hpx Hp]; apply/andP; split; last exact: Hrec.
  apply/hasP => [] [u]; case/mapsP=> [y Hy <- {u}] Hxy.
  by case/hasP: Hpx; exists y; last by rewrite -(@cnode_injcp (seq1 CpH) _ x).
move: HpH {Up Hp}; rewrite {}/p head_proper_cpring // cpring_ecpH // -!cat1s.
rewrite !maps_cat !sieve_cat // -!maps_sieve -/g !sieve1 !maps_cat !maps_seqn.
move: (sieve mr (drop 2 (cpring g))) (@sieve g mc (ctrenum cp)) => r1 r2.
rewrite !insertE_cat !insertE_seqb -!maps_comp -!catA !icpH_edge.
set r1' := maps _ r1; set r2' := insertE (maps _ r2).
set r0 := seq1 (ecpH g); set x1 := icpH g (node g); set x2 := icpH g g.
set x5 := icpH g (edge g); set x4 := icpH g (edge (node g)).
have <-: r1' = maps (comp edge (icpH g)) r1 by done.
have <-: r2' = maps (icpH g) (insertE r2).
  by rewrite {}/r2'; elim: r2 => // *; repeat congr Adds.
rewrite /seq1 /maps !seq1I -/x1 -/x2; simpl in b1, b2, b3, b4, b5.
rewrite {1}[cat]lock catA -lock sparse_catCA -!catA; set r := cat r0 _ => HpH.
have Hrec: (sparse (cat (seqn b1 x1) (cat (seqn b3 x1) (cat (seqn b4 x1)
                   (cat (seqn b2 x2) (cat (seqn b3 x2) (cat (seqn b5 x2) r))))))).
  move: HpH; rewrite [sparse]lock; clearbody r.
  case: b3 b1 b2 b4 b5 Hb => [|] [|] [|] [|] [|] // _ /=.
  - rewrite -lock -!cat1s (@sparse_catCA (ecpH g)) /seq1 /cat.
    by rewrite (@sparse_adds (ecpH g)); case/andP.
  - by rewrite -lock (@sparse_adds (ecpH g)); case/andP.
  - rewrite -lock -!cat1s (@sparse_catCA (ecpH g)) /seq1 /cat.
    by rewrite (@sparse_adds (ecpH g)); case/andP.
  - by rewrite -lock (@sparse_adds (ecpH g)); case/andP.
  by rewrite -lock 2!(@sparse_adds (ecpH g)); case/and3P.
apply: etrans Hrec {HpH}; apply: simple_perm.
  move=> u; rewrite /r !(@fband_cat (permF (ecpH g))).
  set fb := @fband (permF (ecpH g)); case (fb r2' u); first by rewrite !orbT.
  case (fb r1' u); first by rewrite !orbT.
  case (fb r0 u); first by rewrite !orbT.
  case (fb (seqn b5 x5) u); first by rewrite !orbT.
  case (fb (seqn b4 x4) u); first by rewrite !orbT.
  case (fb (seqn b4 x1) u); first by rewrite !orbT.
  case (fb (seqn b5 x2) u); first by rewrite !orbT.
  rewrite !orbF !orFb; congr orb.
    case b1; rewrite // /nat_of_bool /seqn /addsn /iter /fb /fband /has.
    by rewrite 2!cface1r Dng' /= set11.
  rewrite orbA orbC; repeat congr orb.
  - case b3;  rewrite // /nat_of_bool /seqn /addsn /iter /fb /fband /has.
    by rewrite cface1r /= set11.
  - case b2; rewrite // /nat_of_bool /seqn /addsn /iter /fb /fband /has.
    by rewrite cface1r /= Enode (negbE Hgp) /=.
  case b3;  rewrite // /nat_of_bool /seqn /addsn /iter /fb /fband /has.
  by rewrite 2!cface1r /= Enode (negbE Hgp) /=.
by rewrite /r !size_cat !size_seqn; repeat NatCongr.
Qed.

Fixpoint ctrband (cm : bitseq) (cp : cprog) {struct cp} : cpmask :=
  match cp, cm with
  | Adds (CpR n) cp', _ =>
    let (mr, mk) := ctrband cm cp' in Cpmask (rot n mr) mk
  | Adds CpY seq0, _ =>
    Cpmask (seqn 3 false) seq0
  | Adds CpY cp', (Seq b1 & cm') =>
    if ctrband cm' cp' is Cpmask (Seq a0 a1 & mr) mk then
      Cpmask (cat (seq3 (b1 || a0) false (b1 || a1)) mr) mk
    else Cpmask seq0 seq0
  | Adds CpH cp', (Seq b1 b0 b2 & cm') =>
    if ctrband cm' cp' is Cpmask (Seq a0 a1 a2 & mr) mk then
      Cpmask (cat (seq3 (b0 || a0) b1 (b2 || a2)) mr)
             (Adds (b0 || (b1 || (b2 || a1))) mk)
    else Cpmask seq0 seq0
  | _, _ => Cpmask seq0 seq0
  end.


Lemma ctrband_correct : forall cm cp, size cm = ctrmsize cp -> config_prog cp ->
    proper_cpmask cp (ctrband cm cp)
 /\ fband (insertE (sieve cm (ctrenum cp))) =1 fband (cpsieve (ctrband cm cp) cp).
Proof.
move=> cm cp Ecm Hcp; elim: cp Hcp cm Ecm => // [s cp Hrec] Hcp.
move: Hcp (config_prog_cubic Hcp) Hrec => /=.
case: s => // [n||] Hcp Hcpq; move: (cpmap_plain Hcpq) (cpmap_proper Hcpq);
  rewrite /cpmap -/cpmap; set g := cpmap cp => HgE Hgp Hrec cm Ecm.
- case: (ctrband cm cp) {Hrec Ecm Hcp}(Hrec Hcp _ Ecm) => [mr mk].
  case; move/andP=> [Emr Emc] Erec.
  split; first by rewrite /= size_rot Emr.
  rewrite /cpsieve /cpmap -/cpmap -/g cpring_ecpR /=.
  move=> x; rewrite Erec -/g /= !fband_cat /=; congr orb.
  by rewrite sieve_rot ?fband_rot // (eqP Emr) -size_ring_cpmap.
- rewrite /g; case Dcp: cp cm Hcp Ecm => [|s cp'] // [|b1 cm] //.
  rewrite -Dcp -/g [size _]/= => Hcp [Ecm].
  case: (ctrband cm cp) {Hrec}(Hrec Hcp _ Ecm) => [mr mk].
  case; move/andP=> [Emr Emk].
  have Hmr: 1 < size mr by rewrite (eqP Emr) -size_ring_cpmap -size_proper_cpring.
  case: mr Hmr Emr => [|a0 [|a1 mr]] // _ Emr Erec.
  split; first by rewrite /= -(eqP Emr) /= set11.
  move=> u; rewrite -maps_adds /cpsieve /cpmap -/cpmap -/g.
  rewrite cpring_ecpY /behead (head_proper_cpring Hgp).
  rewrite /cpker -/cpker -!maps_sieve (insertE_icpY g) maps_adds.
  rewrite !sieve_adds insertE_cat insertE_seqb -!catA !fband_cat orFb /fband.
  rewrite !has_seqb -maps_sieve !has_maps -/g.
  case: (fband_icpY u) => [[x Hx]|Hu].
    have Eu: comp (cface u) (icpY g) =1 cface x.
      by move=> y; rewrite /comp (same_cface Hx) cface_icpY.
    rewrite !(eq_has Eu) !(same_cface Hx) cface_icpY !has_cat !has_seqb.
    rewrite orbCA cface1r Enode; symmetry.
    rewrite Sface (same_cface (cface_node_ecpY g)) cface_icpY Sface.
    rewrite /fband in Erec; rewrite Erec /cpsieve -/g has_cat.
    rewrite {2}(head_proper_cpring Hgp) !has_sieve_adds !orbA.
    by do 2 congr orb; rewrite !demorgan2 -!orbA; repeat BoolCongr.
  have Eu: comp (cface u) (icpY g) =1 set0.
    by move=> y; rewrite /comp -(same_cface Hu) (@cface_ecpY _ g).
  by rewrite !(eq_has Eu) !has_set0 -!(same_cface Hu) !(@cface_ecpY _ g) !andbF.
case: cm Ecm => [|b1 [|b0 [|b2 cm]]] //; rewrite [size _]/= => [] [Ecm].
case: (ctrband cm cp) {Hrec}(Hrec Hcp _ Ecm) => [mr mk].
case; move/andP=> [Emr Emk].
have Hgl: long_cpring g by apply: cfmap_long.
have Hmr: 2 < size mr by rewrite (eqP Emr) -size_ring_cpmap -size_long_cpring.
case: mr Hmr Emr => [|a0 [|a1 [|a2 mr]]] // _ Emr Erec; simpl in Emr.
split; first by rewrite /= -(eqP Emr) /= set11.
move=> u; rewrite /cpsieve /cpmap -/cpmap -/g.
rewrite cpring_ecpH // /drop /cpker -/cpker -/g (head_long_cpring Hgl).
rewrite sieve_adds -!maps_adds -!maps_sieve (@insertE_cat (ecpH g)).
rewrite (@insertE_seqb (ecpH g)) (insertE_icpH g).
set fX := face (ecpH g); have EfX := erefl fX; rewrite {2}/fX /= in EfX.
rewrite -EfX; have <-: face (icpH g (edge (node g))) = edge fX.
  rewrite /= Enode (negbE Hgp) /=; rewrite /eqd /= set11 /eqd /=.
  by rewrite (inj_eqd (Iedge g)) eqd_sym (negbE Hgp).
rewrite !sieve_adds -!catA -maps_sieve -maps_cat /fband !has_cat !has_seqb.
rewrite /fX -!cface1r !has_maps; symmetry; rewrite orbCA; congr orb.
rewrite Sface (same_cface (cface_node_ecpH Hgp)) Sface.
case: (fband_icpH u) => [[x Hx]|Hu].
  have Eu: comp (cface u) (icpH g) =1 cface x.
    by move=> y; rewrite /comp (same_cface Hx) cface_icpH.
  rewrite !(same_cface Hx) !cface_icpH !(eq_has Eu); rewrite /fband in Erec.
  rewrite !insertE_cat !insertE_seqb !has_cat !has_seqb Erec.
  rewrite /cpsieve -/g {2}(head_long_cpring Hgl) has_cat.
  rewrite !has_sieve_adds -cface1r (cface1r (edge (node g))) Enode.
  by rewrite !demorgan2 -!orbA; repeat BoolCongr.
have Eu: comp (cface u) (icpH g) =1 set0.
  by move=> y; rewrite /comp -(same_cface Hu) cface_ecpH.
by rewrite !(eq_has Eu) !has_set0; rewrite /comp in Eu; rewrite !Eu !andbF.
Qed.

Definition cfcontract_mask cf := ctrmask (cfprog cf) (cfcontract_ref cf).

Definition cfcontract cf := sieve (cfcontract_mask cf) (ctrenum (cfprog cf)).

Fixpoint cptriad (ccm : cpmask) (cp : cprog) (i : nat) {struct i} : bool :=
  if i is S i' then
    let (mrt, mkt) := cpadj (cpmask1 cp i') cp in
    let (mrc, mkc) := ccm in
    let mct := cat (sieve mrc mrt) (sieve mkc mkt) in
    if has negb mct && (2 < count id mct) then true else cptriad ccm cp i'
  else false.

Definition valid_ctrm (cm : bitseq) cp :=
  let n := count id cm in
  if n =d 4 then cptriad (ctrband cm cp) cp (cpksize cp) else set3 1 2 3 n.

Definition contract_ctree cf :=
  let cp := cfprog cf in
  let cm := cfcontract_mask cf in
  if cfctr (seqn (cprsize cp) false) cm cp is Some cpc then
    if valid_ctrm cm cp then Some (cpcolor cpc) else None
  else None.

Lemma contract_ctreeP : forall cf,
 if contract_ctree cf is Some ct then
   let r := cfring cf in let cc := cfcontract cf in
      valid_contract r cc
   /\ (forall et, cc_ring_trace cc (rev r) et -> ctree_mem ct (etrace (behead et)))
 else True.
Proof.
move=> [sym ccr cp]; rewrite /contract_ctree /cfcontract /cfcontract_mask /=.
rewrite /cfring rev_rev /cfmap {sym}/= -size_ring_cpmap.
set g := cpmap cp; set r := cpring g.
set cm := ctrmask cp ccr; set mr0 := seqn (size r) false.
have Emr0: size mr0 = cprsize cp by rewrite -size_ring_cpmap /mr0 size_seqn.
have Ecm: size cm = ctrmsize cp by apply: size_ctrmask.
move: (sparse_cfctr Emr0 Ecm) (cfctr_correct Emr0 Ecm).
case: (cfctr mr0 cm cp) (cfctr_config_prog mr0 cm cp) => //= [cpc] Hcp.
have HgE := cpmap_plain (config_prog_cubic Hcp).
set cc := sieve cm (ctrenum cp); rewrite -/g -/r in cc |- * => UccN Hcc.
case Hcm: (valid_ctrm cm cp); last done.
rewrite /mr0 sieve_false /= in UccN; split.
  move: Hcm; rewrite /valid_ctrm eqd_sym.
  have <-: size cc = count id cm.
  apply: eqP; move: (introT eqP Ecm); rewrite -size_ctrenum /cc.
  elim: (cm) (ctrenum cp) => [|[|] m Hrec] [|x p] //; apply: Hrec.
  move=> Hcm; split; try by case/andP: UccN.
  move: (uniq_ctrenum Hcp); rewrite -/g -/r insertE_cat uniq_cat disjoint_has.
  - move/and3P=> [_ Ur _]; apply/hasP => [[x Hxc Hxr]]; case/hasP: Ur.
    exists x; rewrite !mem_insertE // in Hxr |- *; apply/hasP.
      by case/hasP: Hxr => [y Hy Hxy]; exists y; first exact (mem_sieve Hy).
    by exists x; [ rewrite -mem_rev | exact: connect0 ].
  - by rewrite -/cc /set4; case: (4 =d size cc) Hcm; rewrite ?orbT ?orbF.
  rewrite -/cc; move=> Dcc; move: Hcm; rewrite Dcc /=.
  move=> H; apply/set0P => [Hccr]; case/negPf: H; move: Hccr.
  elim: {-2}(cpksize cp) (leqnn (cpksize cp)) => //= [i Hrec] Hi.
  move: (cpsieve1 Hi Hcp) (proper_cpmask1 cp i).
  set x := sub (cpmap cp) (cpker cp) i.
  move: (cpmask1 cp i) => cmx Hx Hcmx.
  case: (cpadj cmx cp) (cpadj_proper Hcmx) (cpsieve_adj Hcp Hcmx) => [mrt mkt].
  case: {-4}(ctrband cm cp) (ctrband_correct Ecm Hcp) => [mrc mkc].
  rewrite -/cc /= -/g -/r; case; move/andP=> [Emrc Emkc] Hmc.
  move/andP=> [Emrt Emkt] Hmt Hccr.
  apply: cases_of_if; last by clear; apply: Hrec => //; apply ltnW.
  move/andP=> [Hmtc Hmtc']; rewrite -size_ring_cpmap -/g -/r in Emrc Emrt.
  set mt := cat mrt mkt; set mc := cat mrc mkc; set q := cat r (cpker cp).
  have Emtq: size mt =d size q.
    by rewrite /mt /q !size_cat (eqP Emrt) (eqP Emkt) /g (size_cpker Hcp) set11.
  have Emcq: size mc =d size q.
    by rewrite /mc /q !size_cat (eqP Emrc) (eqP Emkc) /g (size_cpker Hcp) set11.
  have Uq: simple q by apply: cpmap_simple.
  rewrite -sieve_cat -/mt -/q ?(eqP Emrt) // {}Hx in Hmt.
  rewrite -sieve_cat -/mc -/q ?(eqP Emrc) // in Hmc.
  rewrite -sieve_cat -/mt -/mc ?(eqP Emrt) ?(eqP Emrc) // in Hmtc Hmtc'.
  case/andP: {Hccr}(Hccr x) {Hrec}; split.
    apply/hasP => [] [y Hy Hyx].
    rewrite /q simple_cat in Uq; case/and3P: Uq; clear; case/hasP; exists x.
      by apply: mem_sub; rewrite /g (size_cpker Hcp).
    by apply/hasP; exists y; first by rewrite -mem_rev.
  apply/andP; split.
    apply: {Hmtc'}(leq_trans Hmtc').
    apply: (@leq_trans (fcard face (setI (adj x) (fband (insertE cc))))).
      rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      transitivity (fcard face (fband (filter (fband (sieve mt q)) (sieve mc q)))).
        rewrite simple_fcard_fband.
          move: (mc) (mt) Emcq Emtq Uq; rewrite simple_recI.
          elim: (q) => [|y q' Hrec] [|b m] // [|b' m'] //= Emq Em'q.
          move/andP=> [Hy Uq']; set q1 := sieve m q'; set q2 := sieve m' q'.
          have Hy': forall m'', fband (sieve m'' q') y = false.
            move=> m''; apply/hasP => [] [z Hz Hyz].
            by case/hasP: Hy; exists z; first exact (mem_sieve Hz).
          have Ebq': filter (fband (Adds y q2)) q1 = filter (fband q2) q1.
            move/idPn: (Hy' m); rewrite -/q1.
            elim: q1 {Hrec} => [|z q1 Hrec] //=; move/norP=> [Hz Hq1].
            by rewrite Sface (negbE Hz) Hrec.
          case: b; rewrite /= Hrec //; case: b';
            by rewrite //= ?connect0 ?Ebq' // /q2 Hy'.
        have Uq1: simple (sieve mc q).
          elim: (mc) (q) Uq => [|[|] m Hrec] [|y q'] //=;
            rewrite !simple_adds; move/andP=> [Hy Uq']; auto.
          rewrite Hrec // andbT; apply/hasP => [[z Hz Hyz]].
          by case/hasP: Hy; exists z; first exact (mem_sieve Hz).
        elim: (sieve mc q) Uq1 => [|y q1 Hrec] //=.
        rewrite !simple_adds; move/andP=> [Hy Uq'].
        case: (fband (sieve mt q) y); auto.
        rewrite simple_adds Hrec // andbT; apply/hasP => [] [z Hz Hyz].
        by rewrite mem_filter in Hz; case/hasP: Hy; case/andP: Hz; exists z.
      apply: eq_n_comp_r => y; apply/idP/idP.
        move/hasP=> [z Hz Hyz]; rewrite mem_filter in Hz; case/andP: Hz.
        rewrite Hmt /= orbF -(adjF Hyz) Sadj //; move=> Hxy Hccz.
        by rewrite /setI -/g Hxy Hmc; apply/hasP; exists z.
      move/andP=> [Hxy Hccy]; rewrite Hmc in Hccy.
      case/hasP: Hccy => [z Hz Hyz]; apply/hasP; exists z; auto.
      by rewrite mem_filter /setI Hz andbT Hmt /= orbF -(adjF Hyz) Sadj.
    rewrite count_filter -(size_maps (fun y => froot face (edge y))).
    apply: leq_trans (card_size _); apply: subset_leq_card.
    apply/subsetP => y; move/and3P=> [Dy Hxy Hyc]; case/adjP: Hxy => [z Hxz Hzy].
    rewrite -(eqP Dy) -/g -((rootP (Sface g)) Hzy); apply: maps_f.
    rewrite mem_filter /setI -fconnect_orbit /g Hxz andbT.
    by move: (closed_connect (fbandF (insertE cc)) Hzy); rewrite -/g => ->.
  apply/subsetP => Hccx.
  have Hct: sub_set (fband (sieve mc q)) (fband (sieve mt q)).
    move=> y Hy; rewrite -Hmc in Hy; case/hasP: Hy => [z Hz Hyz].
    rewrite (closed_connect (fbandF (sieve mt q)) Hyz) Hmt /= orbF Sadj //; auto.
  move: (mc) (mt) Emcq Emtq Uq Hct Hmtc; rewrite simple_recI.
  elim: (q) => [|y q' Hrec] [|b m] // [|b' m'] //= Emq Em'q; move/andP=> [Hy Uq'].
  have Hy': forall m'', fband (sieve m'' q') y = false.
    move=> m''; apply/hasP => [] [z Hz Hyz]; case/hasP: Hy.
    by exists z; first exact (mem_sieve Hz).
  case: b; case: b'; move=> Hct; try apply: (Hrec m m'); auto.
  move=> z Hz; move: (Hct z) => /=.
  case Hzy: (cface z y) => /=; auto.
  - by rewrite (closed_connect (fbandF (sieve m q')) Hzy) Hy' in Hz.
  - by move: (Hct y); rewrite /= connect0 !Hy' => H; move: (H (erefl _)).
  move=> z Hz; move: (Hct z) => /=; case Hzy: (cface z y) => /=; auto.
  by rewrite (closed_connect (fbandF (sieve m q')) Hzy) Hy' in Hz.
move=> et [k Hk Det]; rewrite {et}Det.
rewrite {1}/mr0 sieve_false in Hcc; case: {Hk Hcc}(Hcc _ Hk).
have <-: r = sieve (maps negb mr0) r.
  by rewrite /mr0; elim: (r) => [|x r' Hrec] //=; congr Adds.
move: k => _ k Hk <-; apply/(ctree_mem_cpcolor _ _).
split; first exact: even_etrace.
set et := trace (maps k (cpring (cpmap cpc))).
rewrite /etrace; pose h := etrace_perm (behead et).
exists (comp h k); first by apply: coloring_inj => //; apply permc_inj.
rewrite sumt_permt (maps_comp h k) -/(permt h) trace_permt -/et.
rewrite /permt -maps_adds; congr (maps h).
have Het: sumt et = Color0 by apply: sumt_trace.
case Det: et (introT eqP Het) {h} => [|e et'] /=.
  by move: (congr1 size Det); rewrite /et size_trace size_maps head_cpring.
by rewrite -eq_addc0; move/eqcP=> <-.
Qed.

End ConfigContract.

Set Strict Implicit.
Unset Implicit Arguments.

