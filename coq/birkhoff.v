(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import paths.
Require Import finset.
Require Import connect.
Require Import hypermap.
Require Import jordan.
Require Import geometry.
Require Import color.
Require Import chromogram.
Require Import coloring.
Require Import patch.
Require Import snip.
Require Import sew.
Require Import revsnip.
Require Import kempe.
Require Import ctree.
Require Import initctree.
Require Import gtree.
Require Import initgtree.
Require Import ctreerestrict.
Require Import gtreerestrict.
Require Import cfmap.
Require Import cfcolor.
Require Import kempetree.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The birkhoff theorem: a minimal coloring counter-example must be *)
(* internally 5-connected. *)

Section BirkhoffCheck.

Variable h m : nat.

Fixpoint ctree_pick_rev_rec (et : colseq) (e : color) (t' t : ctree) {struct t}
                          : colseq :=
  match t with
  | Ctree_leaf _ =>
    if ctree_mem t' (etrace (belast e et)) then Adds e et else seq0
  | Ctree_node t1 t2 t3 =>
    if ctree_pick_rev_rec (Adds Color1 et) (e +c Color1) t' t1 is Adds e' et' then
      Adds e' et' else
    if ctree_pick_rev_rec (Adds Color2 et) (e +c Color2) t' t2 is Adds e' et' then
      Adds e' et' else
    ctree_pick_rev_rec (Adds Color3 et) (e +c Color3) t' t3
  | _ => seq0
  end.

Definition ctree_pick_rev : ctree -> ctree -> colseq :=
  ctree_pick_rev_rec seq0 Color0.

Lemma sumt_ctree_pick_rev : forall t t', sumt (ctree_pick_rev t t') = Color0.
Proof.
move=> t' t; rewrite /ctree_pick_rev; set cs0 : colseq := seq0.
have: Color0 +c sumt cs0 = Color0 by done.
elim: t cs0 {1 3}Color0 => [t1 Ht1 t2 Ht2 t3 Ht3|lf _|] et e //.
  move=> Het /=; set cprr := ctree_pick_rev_rec.
  case Det1: (cprr _ _ _ t1) => [|e1 et1].
    case Det2: (cprr _ _ _ t2) => [|e2 et2].
      by apply: Ht3; rewrite [Color3]lock /= -addcA addc_inv.
    by rewrite -Det2; apply: Ht2; rewrite [Color2]lock /= -addcA addc_inv.
  by rewrite -Det1; apply: Ht1; rewrite [Color1]lock /= -addcA addc_inv.
by move=> Het /=; case (ctree_mem t' (etrace (belast e et))).
Qed.

Lemma size_ctree_pick_rev : forall t t',
  ctree_proper h t' -> set2 0 (S h) (size (ctree_pick_rev t t')).
Proof.
move=> t' t; rewrite /ctree_pick_rev; set cs0 : colseq := seq0.
have Ecs0: size cs0 + h = h by done.
elim: {1 3}h t cs0 {1}Color0 Ecs0 => [|n Hrec] [t1 t2 t3|lf|] et e //=.
rewrite addn0; case: (ctree_mem t' (etrace (belast e et))) => // Het.
  by rewrite /set2 /= Het set11.
rewrite -addSnnS; move=> Het [_ Ht1 Ht2 Ht3].
set cprr := ctree_pick_rev_rec.
case Det1: (cprr _ _ _ t1) => [|e1 et1]; last by rewrite -Det1; auto.
by case Det2: (cprr _ _ _ t2) => [|e2 et2]; last rewrite -Det2; auto.
Qed.

Section BirkhoffTree.

Variable check_basis : ctree -> bool.

Definition do_bkf_check2 et ctu gtu chk :=
  let ctr := ctree_of_ttail (etrace et) in
  if et Color0 then false else
  let (ctu', gtru') := kempe_tree_closure (pred h) h ctu ctr gtu in
  if gtru' is Gtree_pair Gtree_empty gtu' then
    check_basis ctu' || chk ctu' gtu'
  else false.

Fixpoint bkf_check2 (ctu1 : ctree) (gtu1 : gtree) (n : nat)
                    (ctu2 : ctree) (gtu2 : gtree) {struct n} : bool :=
  if n is S n' then
    if ctree_pick_rev ctu1 ctu2 is Adds e et then
         do_bkf_check2 (belast e et) ctu1 gtu1 (bkf_check2 ctu2 gtu2 n')
      && do_bkf_check2 (rev et) ctu2 gtu2 (bkf_check2 ctu1 gtu1 n')
    else false
  else false.

End BirkhoffTree.

Definition bkf_check1 cp :=
  and3b (cubic_prog cp) (S (card (cpmap cp)) < 6 * m + 4 * h) (cprsize cp =d S h).

Inductive birkhoff_check : Prop :=
    BkfCheck: forall niter cps,
      let ctu := ctree_init_tree h in let gtu := gtree_init_tree h in
      let basis := maps cpcolor cps in
      let chkb t := has (ctree_disjoint t) basis in
      all bkf_check1 cps -> bkf_check2 chkb ctu gtu niter ctu gtu ->
    birkhoff_check.

End BirkhoffCheck.

Module BirkhoffCheckLemmas.

Import ConfigSyntax.

Lemma birkhoff2 : birkhoff_check 1 0.
Proof. by exists 1 (Seq (Cprog)). Qed.

Lemma birkhoff3 : birkhoff_check 2 0.
Proof. by exists 1 (Seq (Cprog Y)). Qed.

Lemma birkhoff4 : birkhoff_check 3 0.
Proof. by exists 4 (Seq (Cprog U) (Cprog 1 U)). Qed.

Lemma birkhoff5 : birkhoff_check 4 1.
Proof.
by exists 10 (Seq (Cprog U Y) (Cprog 1 U Y) (Cprog 2 U Y) (Cprog 3 U Y)
                  (Cprog 4 U Y) (Cprog H 4 Y Y Y)).
Qed.

End BirkhoffCheckLemmas.

Import BirkhoffCheckLemmas.

Section Birkhoff.

Variable g : hypermap.
Hypothesis Hg : minimal_counter_example g.

Let Hpg : planar g := Hg.
Let Hbg : bridgeless g := Hg.
Let HgE : plain g := Hg.
Let HgN : cubic g := Hg.
Let Hcg : connected g := Hg.
Let Hkg := minimal_counter_example_is_noncolorable Hg.
Let Hmg := minimal_counter_example_is_minimal Hg.
Let De2 := plain_eq Hg.
Let He1 := plain_neq Hg.
Let Dn3 := cubic_eq Hg.

Section BirkhoffValid.

Variable n : nat.
Hypothesis Hn : forall r : seq g, scycle rlink r -> size r <= n ->
   nontrivial_ring 0 r = false.

Lemma birkhoff_valid : forall m, birkhoff_check n m ->
 forall r : seq g, scycle rlink r -> size r = S n -> nontrivial_ring m r = false.
Proof.
move=> m [nm cps ctu0 gtu0 basis chkb Hbk1 Hbk2].
have Hchkb: forall (r : seq g) (HUr : scycle rlink r),
    size r = S n -> nontrivial_ring m r ->
    forall ctu, chkb ctu ->
    exists2 et, ring_trace (snipd_ring Hpg HUr) (ctrace et)
             &  negb (ctree_mem ctu (etrace et)).
  move=> r HUr Hrn Hrm ctu; move: Hbk1 {Hbk2}; rewrite {}/chkb {}/basis.
  elim: cps => [|cp cps Hrec] //=; case/andP; move/and3P=> [Hqcp Hkcp Hrcp] Hbk1.
  case/orP; auto; move{cps Hbk1 Hrec} => Hctu.
  have Hcp := cpmap_proper Hqcp.
  pose gr := cpmap cp; pose bgr : seq gr := rotr 1 (rev (cpring gr)).
  have Hbgr: ufcycle node bgr.
    rewrite /ucycle /bgr /rotr uniq_rot uniq_rev uniq_cpring.
    by rewrite cycle_rot cycle_rev_cpring.
  pose gd := snip_disk Hpg HUr; pose bgd : seq gd := snipd_ring Hpg HUr.
  have Hbgd: sfcycle edge bgd by apply: scycle_snipd_ring.
  have Hbgdr: size bgd = size bgr.
    rewrite /bgr /rotr size_rot size_rev /gr size_ring_cpmap (eqP Hrcp) -Hrn.
    by rewrite -(maps_snipd_ring Hpg HUr) size_maps.
  have Hpp := sew_map_patch Hbgd Hbgr Hbgdr.
  have Hppr := snip_patch Hpg HUr; rewrite -/bgd in Hppr.
  pose g' := sew_map Hbgd Hbgr Hbgdr.
  move: HgE HgN; rewrite (plain_patch Hppr) (cubic_patch Hppr).
  move/andP=> [HgdE HgrrE]; move/andP=> [HgdN HgrrN].
  have Hpg': planar g'.
    rewrite /planar /g' (genus_patch Hpp).
    rewrite /gr ((_ =P 0) (cpmap_planar Hqcp)) addn0; exact: planar_snipd.
  have Hg'E: plain g'.
    by rewrite /g' (plain_patch Hpp); apply/andP; split; last exact: cpmap_plain.
  have Hg'N: cubic g'.
    rewrite /g' (cubic_patch Hpp); apply/andP; split; first done.
    apply: (etrans (eq_subset _ _) (cpmap_cubic Hqcp)) => x.
    by rewrite /setC /bgr mem_rotr.
  have Hbg': bridgeless g'.
    apply: (bridgeless_patch Hpp _ (cpmap_bridgeless Hqcp) _).
      by case (patch_bridgeless Hppr Hbg).
    apply/idPn => [Hch].
    case: (ring_disk_chord Hg Hrm Hch) => [r' HUr' [Hr' Hrr']].
    by rewrite Hrn ltnS in Hrr'; case/idP: (Hn HUr' Hrr').
  have Hkg': four_colorable g'.
    apply Hmg; try by repeat split; try apply cubic_precubic.
    rewrite ltnNge -(leq_add2l (size bgd)).
    move: (card_patch Hpp) (card_patch Hppr); rewrite !size_maps -/g'.
    rewrite -/gd -/bgd => <- <-; rewrite leq_add2l -ltnNge -ltnS.
    apply: (leq_trans Hkcp); pose bgrr := snipr_ring Hpg HUr.
    have Ebgrr: size bgrr = S n.
      by rewrite -Hrn -(size_rev r) -(maps_snipr_ring Hpg HUr) size_maps.
    case Dbgrr: bgrr (Ebgrr) => // [bgrr0 bgrr'] _.
    have Hbgrr: ucycle_plain_quasicubic_connected bgrr.
      split; first by split; [ split | apply: ucycle_snipr_ring ].
      by apply: (patch_connected_r Hppr Hcg); apply/set0Pn; exists bgrr0.
    move: (planar_snipr Hpg HUr); rewrite -/bgrr (quasicubic_Euler Hbgrr) Ebgrr.
    rewrite (patch_fcard_face_r Hppr) /outer -/gr.
    move: (card (snip_rem Hpg HUr)) => ngrr.
    pose arF := setU (diskFC r) (fband r).
    have HarF: fcard face arF = S n + fcard face (diskFC r).
      symmetry; rewrite -Hrn -(scycle_fcard_fband HUr) /n_comp -cardUI addnC.
      rewrite -(@eq_card g set0) ?card0.
        apply: eq_card => x; rewrite /setI /arF /diskFC /setU /setD.
        by case (fband r x); rewrite /= andbF ?orbF.
      move=> x; rewrite /setI /diskFC /setD.
      by case (fband r x); rewrite /= !andbF.
    rewrite Dbgrr -(@eq_n_comp_r _ arF) [muln]lock /=; unlock.
      rewrite HarF double_mul2 -(add1n n) !muln_addr !muln1 !addnA -addnA addnC.
      rewrite eqn_addr -{1}[6]/(2 + 4) muln_addl -addnA addnC eqn_addr addnS addn1.
      rewrite -ltnS; move/eqP=> <-; rewrite -addSn addnC leq_add2l.
      by rewrite ltnNge leq_mul2l orFb -ltnNge; case/andP: Hrm.
    have Ddgr := codom_snipr Hpg HUr; move=> x; apply/idP/set0Pn.
    rewrite /arF /diskFC /setU /setD; case Hx: (fband r x).
      case: (hasP Hx) => [y Hy Hxy] _; exists y.
        by rewrite /setI Hxy Ddgr /setC /diskE /setD Hy.
      move=> HxN; rewrite /= orbF in HxN; exists x; rewrite /setI connect0.
      by rewrite Ddgr /setC /diskE /setD (negbE HxN) andbF.
    case; move=> y; move/andP=> [Hxy Hy]; rewrite Ddgr in Hy.
    rewrite /arF /diskFC /setU /setD.
    case Hx: (fband r x); [ by rewrite orbT | rewrite /= orbF ].
    case HxF: (diskF r x).
      rewrite (closed_connect (diskF_face r) Hxy) in HxF.
      case: (andP HxF) => [H HyN]; case: {H}(elimN hasP H).
      rewrite /setC /diskE /setD HyN andbT negb_elim in Hy.
      by exists y; last by apply connect0.
    by rewrite /diskF /setD Hx /= in HxF; rewrite /setC HxF.
  case: (colorable_patch Hpp) => [H _]; case: {H}(H Hkg').
  case/lastP=> [|et e] Hetd Hetr.
  case: Hetr => [k _ Det]; move: (congr1 size Det).
    by rewrite /bgr size_trace size_maps size_rotr size_rev head_cpring.
  have De: sumt et = e.
    case: Hetd => [k _ Det]; move: (congr1 sumt Det); rewrite sumt_trace /=.
    rewrite -{2}[e]add0c => <-; elim: et {Hetr Det} => [|e' et Hrec] /=.
      by rewrite addcC addc_inv.
    by rewrite Hrec addcA.
  exists et; first by rewrite /ctrace De.
  apply: (negbI (ctree_mem_disjoint Hctu _)) {Hetd}.
  apply/(ctree_mem_cpcolor _ _); split; first by apply even_etrace.
  rewrite /etrace; set (h := etrace_perm et); rewrite sumt_permt De.
  case: Hetr => [k Hk Det]; exists (comp h k).
    apply: (coloring_inj (h := h)) Hk => //; apply permc_inj.
  rewrite -/gr (maps_comp h k) -/(permt h) trace_permt.
  rewrite -(rev_rev (cpring gr)) maps_rev trace_rev.
  rewrite -(rot_rotr 1 (rev (cpring gr))) maps_rot trace_rot -/bgr -Det.
  by rewrite -rev_rotr rotr_rot -rev_rotr rev_rev rotr1_add_last.
move=> r HUr Hrn; apply/idP => Hrm; case Dn: n => [|n'].
  case: (r) Hrn (andP HUr) => [|x [|x' r']]; try by rewrite Dn.
  by move=> _ [H _]; case: {H}(andP H); rewrite /rlink Sface (set0P Hbg x).
have HUr2 := scycle_rev_ring Hg HUr.
pose kv P := kempe_valid n' (fun et => ~ P et) ctu0 Ctree_empty Gtree_empty gtu0.
have Hkv0: kv (ring_trace (snipd_ring Hpg HUr)) /\
           kv (ring_trace (snipd_ring Hpg HUr2)).
  split; rewrite /kv /ctu0 /gtu0 Dn; exact: kempe_valid_init.
case/negPf: Hbk2; move: Hrn Hrm HUr HUr2 Hkv0; rewrite {}/kv.
elim: nm r ctu0 gtu0 {2 4}ctu0 {2 4}gtu0 => [|nm Hrec]; auto.
move=> r1 ctu1 gtu1 ctu2 gtu2 Hr1n Hr1m HUr1; set r2 := rev_ring r1.
move=> HUr2 [Hk1 Hk2] /=.
have Hr2n: size r2 = S n by rewrite /r2 /rev_ring size_rev size_maps.
have Hr2m: nontrivial_ring m r2 by apply: (nontrivial_rev_ring Hg).
have Hcl1 := @ring_disk_closed _ Hg Hpg _ HUr1 _ Hr1m HgN.
have Hcl2 := @ring_disk_closed _ Hg Hpg _ HUr2 _ Hr2m HgN.
case Det: (ctree_pick_rev ctu1 ctu2) => [|e et] //=.
apply/andP => [[Hck1 Hck2]]; case Hkg.
apply (@colorable_from_ring _ Hg Hpg _ HUr1 _ Hr1m (Adds e et)).
  case (decide_ring_trace (snipd_ring Hpg HUr1) (Adds e et)); auto.
  move=> Het; move: Hck1 {Hck2}; rewrite /do_bkf_check2 {1}Dn /pred.
  set ctr := ctree_of_ttail _.
  case Het0: (belast e et Color0); first done.
  pose P et' := ~ ring_trace (snipd_ring Hpg HUr1) et'.
  case (@kempe_tree_closure_correct n' P n ctu1 ctr gtu1).
    apply: kempe_valid_restrict Hk1 => et' Het'.
    rewrite {Het'}(ctree_of_ttail_mem _ _ Het');
      last by rewrite /etrace memc0_permt Het0.
    rewrite /etrace ctrace_permt {2}/permt size_maps; split.
      move: (etrace_perm _) => ge.
      move/(Hcl1 _)=> [Het' _]; case: Het; move: (Het' (inv_eperm ge)).
      have <-: Adds e et = ctrace (belast e et).
        have Hets := sumt_ctree_pick_rev ctu1 ctu2.
        rewrite Det in Hets; rewrite -(trace_untrace Color0 Hets) /trace /=.
        by rewrite (pairmap_scanl addc_inv).
      by rewrite /permt (monic_maps (inv_permc ge)).
    case: (Hk2) => [Hctu2 _]; move: (size_ctree_pick_rev ctu1 Hctu2).
    by rewrite -Dn size_belast Det /set2 /= eqdSS; move/eqP=> ->.
  case: (kempe_tree_closure n' n ctu1 ctr gtu1) => [ctu' [gtr gtu']].
  case: gtr => // Hctu' _; case/orP=> Hck.
    move: {Hchkb Hrec Hck}(Hchkb _ HUr1 Hr1n Hr1m _ Hck) => [et1 Het1 Hctu1].
    have Hset1: size et1 = S n'.
      symmetry; rewrite -Dn -[n]/(pred (S n)) -Hr1n.
      rewrite -(maps_snipd_ring Hpg HUr1) size_maps.
      case: Het1 => [k _ Det1]; rewrite -(size_maps k) -size_trace -Det1.
      by rewrite /ctrace size_add_last.
    case: (kempe_validP Hctu' Hset1 Hctu1 Hcl1 Het1) => s H; case/H {P H}.
  rewrite {Hk1 Hcl1 Het}/P in Hctu'.
  rewrite -(rev_rev_ring Hg r1) -/r2 in HUr1 Hctu' |- *.
  case/negPf: Hck; eapply (Hrec r2); auto; split; eauto.
case (decide_ring_trace (snipd_ring Hpg HUr2) (rev (Adds e et))).
  rewrite /rev_snipd_ring /rev_snipd_disk.
  by rewrite (bool_eqT (scycle_rev_ring Hg HUr1) HUr2).
move=> Het; move: Hck2 {Hck1}; rewrite /do_bkf_check2 {1}Dn /pred.
set ctr := ctree_of_ttail (etrace (rev et)).
case Het0: (rev et Color0); first done.
pose P et' := ~ ring_trace (snipd_ring Hpg HUr2) et'.
case (@kempe_tree_closure_correct n' P n ctu2 ctr gtu2).
  apply: kempe_valid_restrict (Hk2) => et' Het'.
  rewrite {Het'}(ctree_of_ttail_mem _ _ Het');
    last by rewrite /etrace memc0_permt Het0.
  rewrite /etrace ctrace_permt {2}/permt size_maps; split.
    move: (etrace_perm (rev et)) => ge; move/(Hcl2 _)=> [Het' _].
    case: Het; move: (Het' (inv_eperm ge)).
    have <-: rev (Adds e et) = ctrace (rev et).
      have Hrets: sumt (rev (Adds e et)) = Color0.
        rewrite -(rotr_rot 1 (rev (Adds e et))).
        have Hets := (sumt_ctree_pick_rev ctu1 ctu2).
        rewrite Det in Hets; rewrite -(trace_untrace Color0 Hets) -trace_rev.
        rewrite -(rot_rotr 1 (rev (untrace Color0 (Adds e et)))).
        by rewrite trace_rot rotr_rot sumt_trace.
      rewrite -(trace_untrace Color0 Hrets) rev_adds /untrace /=.
      by rewrite belast_add_last /trace /= (pairmap_scanl addc_inv).
    by rewrite /permt (monic_maps (inv_permc ge)).
  case: (Hk2) => [Hctu2 _]; move: (size_ctree_pick_rev ctu1 Hctu2).
  by rewrite -Dn size_rev Det /set2 /= eqdSS; move=> H; rewrite (eqP H).
move: (kempe_tree_closure n' n ctu2 ctr gtu2) => [ctu' [gtr gtu']].
rewrite {}/P; case: gtr=> // Hctu' _; case/orP=> Hck.
 case: {Hchkb Hrec Hck}(Hchkb _ HUr2 Hr2n Hr2m _ Hck) => [et2 Het2 Hctu2].
  have Hset2: size et2 = S n'.
    symmetry; rewrite -Dn -[n]/(pred (S n)) -Hr2n.
    rewrite -(maps_snipd_ring Hpg HUr2) size_maps.
    case: Het2 => [k _ Det2]; rewrite -(size_maps k) -size_trace -Det2.
    by rewrite /ctrace size_add_last.
  case: (kempe_validP Hctu' Hset2 Hctu2 Hcl2 Het2) => s H; case/H.
by case/negPf: Hck; eapply (Hrec r1); auto; split; eauto.
Qed.

End BirkhoffValid.

Theorem birkhoff : forall r : seq g,
  size r <= 5 -> scycle rlink r -> nontrivial_ring (size r =d 5) r = false.
Proof.
elim: {1 3}5 (leqnn 5) => [|n Hrec] Hn.
  move=> [|x r] // _ _; rewrite /nontrivial_ring /n_comp eq_card0 //.
  by move=> x; rewrite /setI andbC.
move: {Hrec}(Hrec (ltnW Hn)) => Hrec.
move=> r Hrn; rewrite leq_eqVlt in Hrn; case/orP: Hrn; auto.
move=> Hrn Hr; apply: (birkhoff_valid _ _ Hr (eqP Hrn)).
  move {r Hrn Hr} => r Hr Hrn; rewrite -(Hrec r Hrn Hr).
  by rewrite -ltnS in Hrn; rewrite eqn_leq andbC leqNgt (leq_trans Hrn Hn).
rewrite (eqP Hrn); case: n Hrn Hn {Hrec} => [|n].
  case: r Hr => [|x [|x' r']] //=.
  by rewrite /scycle /= /rlink Sface (set0P Hbg x).
case: n => [|[|[|[|n]]]] _ // _.
- exact birkhoff2.
- exact birkhoff3.
- exact birkhoff4.
exact birkhoff5.
Qed.

Lemma nontrivial_cycle2 : forall x y : g, let r := seq2 x y in
 scycle rlink r -> negb (edge x =d y) -> nontrivial_ring 0 r.
Proof.
move=> x y r HUr Hexy; apply/(nontrivial0P _); split.
  exists (node x); rewrite /diskF /setD -(fclosed1 (diskN_node r)).
  rewrite diskN_E /setU /= setU11 /= -{2}[x]Enode -cface1r (set0P Hbg) /=.
  case: (andP HUr); move/and3P=> [Hxy Hyx _] _.
  rewrite Sface -(same_cface Hxy) -[node x]Enode -{1}[x]Dn3.
  by rewrite cface1 Enode -cface1r (set0P Hbg).
pose nex := node (edge x); case Hnex: (fband r nex).
  rewrite /fband in Hnex; case: (hasP Hnex) => [z Hz Hnexz].
  rewrite /= /setU1 orbF in Hz; case/orP: Hz => Dz.
    rewrite -{1}[nex]Enode /nex -{1}[x]Eface De2 Dn3 -cface1 Sface in Hnexz.
    by rewrite -(eqP Dz) cface1 (set0P Hbg) in Hnexz.
  case: (andP HUr); move/andP=> [Hxy _].
  rewrite Sface -(eqP Dz) -(same_cface Hxy) in Hnexz.
  by rewrite -[edge x]Enode -/nex -cface1 Sface (set0P Hbg) in Hnexz.
exists nex; rewrite /diskFC /setD Hnex /= /setC /nex.
rewrite -(fclosed1 (diskN_node r)) diskN_E /setU.
rewrite -(fclosed1 (diskE_edge Hpg HUr)) /diskE /setD /= setU11 /= /setU1.
by rewrite eqd_sym He1 eqd_sym (negbE Hexy).
Qed.

Lemma double_dart : forall x y : g,
  cface x y -> cface (edge x) (edge y) -> x = y.
Proof.
move=> /= x y HxyF Hexey; apply: eqP; apply/idPn => [Hxy].
have HUp: scycle rlink (seq2 x (edge y)).
  by rewrite srcycleI //= Hexey De2 Sface.
rewrite -(inj_eqd (Iedge g)) in Hxy.
by apply: (elimF idP (birkhoff _ HUp) (nontrivial_cycle2 HUp Hxy)).
Qed.

Section SpokeRing.

Variable x : g.

Let p : seq g := orbit face x.

Remark SpokeRing_Hpx : p x. Proof. by rewrite /p -fconnect_orbit connect0. Qed.
Let Hpx := SpokeRing_Hpx.

Remark SpokeRing_HUp : ufcycle face p.
Proof. by rewrite /p /ucycle uniq_orbit (cycle_orbit (Iface g)). Qed.
Let HUp := SpokeRing_HUp.

Remark SpokeRing_Ep : cface x =1 p. Proof. by apply: fconnect_orbit. Qed.
Notation Ep := SpokeRing_Ep.

Definition spoke (y : g) : g := face (edge y).

Lemma inj_spoke : injective spoke.
Proof. apply: (monic_inj (g := node)); apply: Eedge. Qed.

Definition spoke_ring : seq g := maps spoke (rev p).

Lemma mem_spoke_ring : forall y : g, spoke_ring y = cface x (node y).
Proof.
move=> y; rewrite /spoke_ring -{1}[y]Enode -/(spoke (node y)).
by rewrite (mem_maps inj_spoke) mem_rev Ep.
Qed.

Notation r := spoke_ring.
Notation Er := mem_spoke_ring.

Lemma next_spoke_ring : forall y : g, r y -> next r y = face (spoke y).
Proof.
case: (andP HUp) => [Hp Up] y Hy.
rewrite /r -{1}[y]Enode -/(spoke (node y)).
rewrite (next_maps inj_spoke); last by rewrite uniq_rev.
rewrite (next_rev Up) -(Eface g (prev p (node y))) /spoke De2.
by rewrite Er Ep in Hy; rewrite (eqP (prev_cycle Hp Hy)) -{1}[y]Eedge Dn3.
Qed.

Lemma scycle_spoke_ring : scycle rlink r.
Proof.
case: (andP HUp) => [Hp Up]; apply/andP; split.
  apply cycle_from_next; first by rewrite /r (uniq_maps inj_spoke) ?uniq_rev.
  move=> y Hy; rewrite (next_spoke_ring Hy) /rlink -cface1r; exact: fconnect1.
rewrite /simple /r !maps_rev uniq_rev -maps_comp /comp.
have HpF: sub_set p (cface x) by move=> y Hy; rewrite Ep.
elim: (p) HpF {Hp} Up => [|y q Hrec] Hq //=; move/andP=> [Hqy Uq].
rewrite {Hrec Uq}(Hrec (fun z Hz => Hq z (setU1r _ Hz)) Uq) andbT.
apply/mapsP => [] [z Hz Hyz]; case/idP: Hqy.
rewrite (@double_dart y z) //.
  rewrite -(same_cface (Hq _ (setU11 _ _))); exact (Hq _ (setU1r _ Hz)).
by rewrite cface1 cface1r; apply/(rootP (Sface _)).
Qed.
Let HUr := scycle_spoke_ring.

Lemma diskF_spoke_ring : diskF r =1 cface x.
Proof.
move=> y; symmetry; apply/idP/idP.
  move=> Hxy; apply/andP; split.
    apply/hasP => [] [z1 Hz1 Hyz1]; rewrite Er in Hz1.
    case/idP: (set0P Hbg (node z1)).
    rewrite cface1r Enode -(same_cface Hz1); exact (connect_trans Hxy Hyz1).
  by rewrite /= -{1}[y]Eedge -(fclosed1 (diskN_node r)) diskN_E /setU Er Eedge Hxy.
case/andP=> Hy; move/hasP=> [z Hz Hzy]; case/connectP: Hzy Hy.
set z' := finv node z; rewrite Er in Hz.
have Hz': r (face z').
  by rewrite -(De2 z') Er Eedge -(Dn3 z') /z' (f_finv (Inode g)) cface1r Enode.
case=> [|z'' q] Hq <-.
  by case/hasP=> /=; exists (face z'); last by apply fconnect1.
move: Hq; rewrite /= {1}/dlink; case (r z'); first done.
case/andP; case/clinkP=> [Dz'|Dz''] Hq.
  rewrite -(f_finv (Inode g) z) -/z' (Inode g (etrans (Dn3 _) Dz')) in Hz.
  elim: q z'' {y z z' Hz' Dz'}Hz Hq => [|z q Hrec] y Hy //=.
  rewrite {1}/dlink; case: (r y) => //; case/andP; case/clinkP=> [Dy|Dz].
    have Hz: r z by rewrite Er -Dy.
    case: q {Hrec} => [|z' q]; last by rewrite /= /dlink Hz.
    by rewrite /= (subsetP (ring_fband r) _ Hz).
  by apply: Hrec; rewrite -Dz -cface1r.
rewrite Dz'' in Hz'; case: q Hq => [|z''' q]; last by rewrite /= /dlink Hz'.
by rewrite /= (subsetP (ring_fband r) _ Hz').
Qed.

Lemma chordless_spoke_ring : chordless r.
Proof.
apply/subsetP => [y1 Hy1]; apply/set0Pn => [] [y2]; case/andP.
move/adjP=> [z Hz1 Hz2]; rewrite /rlink in Hz2; move/and3P=> [Hry12 Hry21 Hy2].
pose q := seq3 (node y2) (edge z) (edge (node y1)).
have HUq: scycle rlink q.
  rewrite srcycleI //= !De2 cface1 Enode Sface Hz2 /= andbC.
  rewrite cface1r Enode Sface Hz1 /= Sface; rewrite !Er in Hy1 Hy2.
  by rewrite -!(same_cface Hy2) !(same_cface Hy1) connect0 (set0P Hbg).
apply: (elimF idP (birkhoff _ HUq) _); first done.
apply/(nontrivial0P _); split.
  pose t := node (edge (node y1)); exists t; rewrite /diskF /setD /=.
  have Dt: t = prev r y1.
    move: (andP HUr) => [_ Ur]; rewrite /t -{1}[y1](next_prev (simple_uniq Ur)).
    by rewrite next_spoke_ring ?mem_prev // Eface /spoke Eedge.
  rewrite Er in Hy2; rewrite Sface -(same_cface Hy2).
  have Ht: cface x (node t) by rewrite -Er Dt mem_prev.
  rewrite (same_cface Ht) -{2}[t]Enode -cface1r (set0P Hbg).
  rewrite Sface (same_cface Hz2) Sface /= orbC.
  rewrite -[edge (node y1)]Enode -cface1r (set0P Hbg).
  rewrite {2}/t -(fclosed1 (diskN_node q)) diskN_E /setU /= /setU1 set11.
  rewrite /= !orbT andbT; apply/idP => [Hy2t]; case/eqP: Hry21.
  by rewrite -Dt; apply (scycle_cface HUr); rewrite ?Er.
exists (node (node y1)); rewrite /diskFC /setD /= /setC.
rewrite andbC -(fclosed1 (diskN_node q)) -{1}[node y1]De2.
rewrite (diskN_edge_ring Hg) /= /setU1 ?set11 /= ?orbT //; rewrite !Er in Hy1 Hy2.
rewrite Sface -(same_cface Hy2) (same_cface Hy1) -{1}[node y1]Enode -cface1.
rewrite Sface (set0P Hbg) /= orbF orbC -[node (node y1)]Enode Dn3.
rewrite -cface1 Sface cface1 Enode (set0P Hbg) /= cface1 -/(spoke y1).
rewrite -next_spoke_ring; last by rewrite Er.
apply/idP => [Hy2t]; case/eqP: Hry12.
by apply (scycle_cface HUr); rewrite ?mem_next ?Er // (same_cface Hy2t).
Qed.

Lemma size_spoke_ring : size r = order face x.
Proof. by rewrite /r size_maps size_rev /p /orbit size_traject. Qed.

Lemma min_arity : 4 < order face x.
Proof.
rewrite /= -size_spoke_ring ltnNge; apply/idP => HrF.
case HrFC: (negb (set0b (diskFC r))).
  apply: (elimF idP (birkhoff _ HUr) _); first by apply ltnW.
  case: (size r =P 5) => [Hr5|_]; first by rewrite Hr5 in HrF.
  apply/(nontrivial0P _); split; last by exact (set0Pn HrFC).
  by exists x; rewrite diskF_spoke_ring connect0.
move: {HrFC}(set0P (negbEf HrFC)) => HrFC.
case Hkg;  exists (fun y =>
  if cface x y then Color0 else
  let i := find (cface y) r in
  if (i =d 2) && (size r =d 3) then Color3 else
  if set2 0 2 i then Color1 else Color2).
split=> y; rewrite /invariant;
  last by rewrite -cface1r -(eq_find (cface1 y)) set11.
set i1 := find (cface y) _; set i2 := find (cface (edge y)) _.
case Hxy: (cface x y).
  rewrite (same_cface Hxy) (set0P Hbg).
  by case: (_ && _); last by case (set2 0 2 i2).
case Hxey: (cface x (edge y)); first by case: (_ && _); last by case (set2 0 2 i1).
case Hy: (fband r y);
  last by rewrite -diskF_spoke_ring /diskF /setD Hy /= in Hxy;
          move: (HrFC y); rewrite /diskFC /setD Hy /setC Hxy.
case Hey: (fband r (edge y));
  last by rewrite -diskF_spoke_ring /diskF /setD Hey /= in Hxey;
          move: (HrFC (edge y)); rewrite /diskFC /setD Hey /setC Hxey.
pose z1 := sub x r i1; pose z2 := sub x r i2.
have Hz12: adj z1 z2.
  apply/adjP; exists y; first rewrite Sface; exact: sub_find.
rewrite /fband has_find -/i1 in Hy; rewrite /fband has_find -/i2 in Hey.
have Hz1: r z1 by rewrite /z1 (mem_sub x Hy).
have Hz2: r z2 by rewrite /z2 (mem_sub x Hey).
move: {Hz1}(set0P (subsetP chordless_spoke_ring _ Hz1) z2).
case: (andP HUr) => Hr; move/simple_uniq=> Ur.
rewrite /setI /setD1 {}Hz12 {}Hz2 (monic2F_eqd (prev_next Ur)) -(eqd_sym z2).
have Hpri: forall i i', i < size r -> i' < size r ->
  (sub x r i' =d prev r (sub x r i)) = (i' =d pred (if i =d 0 then size r else i)).
- move=> i i' Hi Hi'; set z := sub x r i.
  suffice <-: index (prev r z) r = pred (if i =d 0 then size r else i).
    apply/eqP/eqP=> [<- | ->]; first by rewrite (index_uniq x Hi' Ur).
    by rewrite sub_index // mem_prev /z mem_sub.
  rewrite prev_sub {}/z mem_sub // {i' Hi'}.
  case Dr: r Ur Hi => [|x0 r'] Ur //.
  rewrite index_uniq //; last by rewrite /= ltnS index_size.
  simpl in Ur; case/andP: Ur => [Hx0 Ur'].
  case: i => [|i] Hi; rewrite /= ?index_uniq //.
  by rewrite -{1}[r']cats0 index_cat (negbE Hx0) /= addn0.
rewrite {}/z1 {}/z2 !{}Hpri //.
case Dn: (size r) HrF Hy Hey => [|[|n]] //.
  case: r HUr Dn => [|x0 [|x1 r']] //.
  by rewrite /scycle /= andbT /rlink Sface (set0P Hbg).
by case: i1 i2 n {Dn} => [|[|[|[|i1]]]] [|[|[|[|i2]]]] [|[|[|n]]].
Qed.

Lemma fband_spoke_ring : fband r =1 adj x.
Proof.
move=> y; apply/hasP/adjP => [] [z Hxz Hzy].
  by exists (node z); [rewrite -Er | rewrite /rlink cface1 Enode Sface].
by exists (face (edge z)); [rewrite Er Eedge | rewrite -cface1r Sface].
Qed.

Lemma adj11_edge : forall y, adj x y -> adj x (edge y) -> r y || r (edge y).
Proof.
move=> y; rewrite -!fband_spoke_ring.
move/hasP=> [z Hrz Hyz]; move/hasP=> [z' Hrz' Heyz']; apply/norP => [] [Hry Hrey].
case/andP: (set0P (subsetP chordless_spoke_ring _ Hrz) z'); split.
  by apply/adjP; exists y; first by rewrite Sface.
case: (andP HUr) => _; move/simple_uniq=> Ur.
rewrite /setD1 Hrz' andbT (monic2F_eqd (next_prev Ur)) !next_spoke_ring //.
apply/andP; split; apply/eqP => Dz.
  rewrite -Dz /spoke -!cface1r in Heyz'.
  by rewrite (double_dart Hyz Heyz') Hrz in Hry.
rewrite Dz /spoke -!cface1r -{1}[y]De2 in Hyz.
by rewrite (double_dart Heyz' Hyz) Hrz' in Hrey.
Qed.

Lemma fcard_adj_adj : forall y, adj x y -> fcard face (setI (adj y) (adj x)) = 2.
Proof.
move=> y Hy; have Hry := Hy; rewrite -fband_spoke_ring in Hry.
move/hasP: Hry => [y' Hy' Hyy'].
rewrite /n_comp (cardD1 (froot face (next r y'))).
rewrite (cardD1 (froot face (prev r y'))).
rewrite {1}/setD1 {1 2 3 4}/setI !(roots_root (Sface g)).
have Hra: forall z, r z -> adj x z.
  by move=> z; rewrite Er; move=> Hnxz; rewrite (adjF Hnxz) adjN.
set z := prev r y'; have Hz: r z by rewrite /z mem_prev.
set z' := next r y'; have Hz': r z' by rewrite /z' mem_next.
rewrite -!(adjFr (connect_root _ _)) !Hra //.
case: (andP HUr) => Hr; move/simple_uniq=> Ur.
rewrite !(adjF Hyy') /z' (rlink_adj (next_cycle Hr Hy')) -/z'.
rewrite Sadj // /z (rlink_adj (prev_cycle Hr Hy')) -/z /=.
rewrite (sameP eqP (rootPx (Sface g) z' z)).
case Hz'z: (cface z' z).
  case: (rot_to Hz) min_arity (cycle_next Ur) (Ur) => [i r' Dr].
  rewrite -size_spoke_ring -(size_rot i) -(cycle_rot i) -(uniq_rot i) Dr.
  case: r' {Dr} => [|y'' [|z'' r']] // _; move/and3P=> [Dy'' Dz'' _].
  case/andP; case/orP; right; apply/setU1P; left.
  rewrite -(eqP Dz'') -(eqP Dy'') {1}/z (next_prev Ur) -/z'.
  exact: (scycle_cface HUr).
apply: eqP; apply/set0Pn => [] [t]; move/and5P=> [Hzt Hz't Ht Hyt Hxt].
rewrite -(eqP Ht) (sameP eqP (rootPx (Sface _) z t)) in Hzt.
rewrite -{Ht}(eqP Ht) (sameP eqP (rootPx (Sface _) z' t)) in Hz't.
rewrite -fband_spoke_ring in Hxt; case/hasP: Hxt => [t' Ht' Htt'].
case/andP: (set0P (subsetP chordless_spoke_ring _ Hy') t'); split.
  by rewrite -(adjF Hyy') -(adjFr Htt').
rewrite /setD1 Ht' andbT; apply/andP; split; apply/eqP => [Dt'].
  by rewrite Sface (same_cface Htt') -Dt' -/z' connect0 in Hz't.
by rewrite Sface (same_cface Htt') -Dt' -/z connect0 in Hzt.
Qed.

Definition adj01 (y z : g) := cface y z || adj y z.

Lemma adj12_edge : forall y z,
  adj x y -> adj x z -> adj z (edge y) -> adj01 z y || adj01 x (edge y).
Proof.
move=> y z0; rewrite -2!fband_spoke_ring.
move/hasP=> [y' Hry' Hyy']; move/hasP=> [z Hrz Hz0z].
move/adjP=> [z' Hzz' Heyz']; rewrite /rlink Sface in Heyz'.
apply/norP; case; move/norP=> [Hzy Hazy]; move/norP=> [Hxey Haxey].
rewrite !(same_cface Hz0z) in Hzy Hzz'; rewrite {z0 Hz0z}(adjF Hz0z) in Hazy.
pose q := Adds y (seq3 (edge z') (edge (node z)) (node y')).
have HUq: scycle rlink q.
  rewrite srcycleI //= Heyz' cface1r Enode Sface Hzy !De2 /=.
  rewrite (same_cface Hyy') Sface (adj_no_cface Hbg (adjN y')) /=.
  rewrite !Er in Hry' Hrz.
  rewrite cface1r Enode Sface Hzz' -(same_cface Heyz') Sface -(same_cface Hry').
  by rewrite Hxey -(same_cface Hrz) Hry' cface1 Enode Sface Hyy'.
apply: (elimF (nontrivial0P _) (birkhoff _ HUq) _); [ done | split ].
  exists (node (node y')); rewrite /diskF /setD -(fclosed1 (diskN_node q)).
  rewrite diskN_E /setU /= /setU1 set11 /= !orbT andbT.
  rewrite Sface (same_cface Hyy') -{2 4}[y']Eedge Dn3.
  rewrite -cface1r (set0P Hbg) Sface -(same_cface Heyz') (no_adj_adj Haxey).
    rewrite -cface1 Sface cface1 Enode; rewrite Sadj // in Hazy.
    rewrite (no_adj_adj Hazy); first by rewrite adj_no_cface ?adjN.
    by rewrite (adjF Hyy') adjE.
  by rewrite Er in Hry'; rewrite (adjF Hry') Sadj ?adjN.
exists (node (node z)).
rewrite /diskFC /setD /setC -(fclosed1 (diskN_node q)).
rewrite -{2}[node z]De2 (diskN_edge_ring Hg) //= /setU1 ?set11 ?orbT //.
rewrite andbT orbF -{1 3}[z]Eedge Dn3 -cface1 Sface (no_adj_adj Hazy (adjE z)).
rewrite !Er in Hry' Hrz.
rewrite Sface -(same_cface Heyz') (no_adj_adj Haxey).
  rewrite -cface1 Sface cface1 Enode (set0P Hbg) Sface -(same_cface Hry').
  by rewrite (same_cface Hrz) -{1}[node z]Enode -cface1 Sface (set0P Hbg).
by rewrite (adjF Hrz) Sadj ?adjN.
Qed.

Lemma fcard_adj_max : forall y,
  negb (cface x y) -> fcard face (setI (adj y) (adj x)) <= 2.
Proof.
move=> y Hxy0; case Hxy: (adj01 x y).
  by rewrite /adj01 (negbE Hxy0) in Hxy; rewrite (fcard_adj_adj Hxy).
rewrite {Hxy0}leqNgt /n_comp; apply/idP => Hy3.
have Hy1 := (ltnW (ltnW Hy3)); rewrite ltnNge leqn0 in Hy1.
case/set0Pn: Hy1 => [z1 Hz1]; rewrite (cardD1 z1) Hz1 /= in Hy3.
have Hy2 := (ltnW Hy3); rewrite add1n ltnS ltnNge leqn0 in Hy2.
case/set0Pn: Hy2 => [z2 Hz2]; rewrite (cardD1 z2) Hz2 /= in Hy3.
rewrite !add1n !ltnS ltnNge leqn0 in Hy3; case/set0Pn: Hy3 => [z3 Hz3].
case/and3P: Hz1 => [Hz1 Hyz1 Hxz1].
case/and4P: Hz2 => [Hz12 Hz2 Hyz2 Hxz2].
case/and5P: Hz3 => [Hz23 Hz13 Hz3 Hyz3 Hxz3].
have Hyz: forall z z', negb (z =d z') -> froots face z -> froots face z' ->
    adj x z -> adj x z' -> adj y z -> adj y z' -> adj z z'.
- move=> z z' Hzz' Hz Hz' Hxz Hxz' Hyz; move/adjP=> [z'' Hyz'' Hz''z'].
  rewrite -(adjFr Hz''z') in Hxz'; rewrite (adjF Hyz'') Sadj // -[z'']De2 in Hyz.
  move: (adj12_edge Hxz' Hxz Hyz).
  rewrite De2 orbC /adj01 -(adjFr Hyz'') (Sface _ x) -(same_cface Hyz'') Sface.
  rewrite -/(adj01 x y) Hxy Sface (same_cface Hz''z') Sface.
  rewrite (sameP (rootPx (Sface _) z z') eqP) (eqP Hz) (eqP Hz') (negbE Hzz').
  by rewrite (adjFr Hz''z').
have Hz123: and3 (adj z1 z2) (adj z1 z3) (adj z2 z3) by split; auto.
move: {y Hxy Hz1 Hyz1 Hz12 Hz2 Hyz2 Hz13 Hz23 Hz3 Hyz3 Hyz}Hxz1 Hxz2 Hxz3.
rewrite -!fband_spoke_ring; move/hasP=> [t1 Ht1 Hzt1].
move/hasP=> [t2 Ht2 Hzt2]; move/hasP=> [t3 Ht3 Hzt3].
move: Hz123; rewrite !(adjF Hzt1) (adjF Hzt2) (adjFr Hzt2) !(adjFr Hzt3).
move {z1 z2 z3 Hzt1 Hzt2 Hzt3} => [Ht12 Ht13 Ht23].
case: (andP HUr) => _; move/simple_uniq=> Ur.
have Hrt: forall t t', adj t t' -> r t -> r t' ->
    next r t <> next r t' /\ (next r t = t' \/ next r t' = t).
- move=> t t' Htt' Ht Ht'; split.
  move=> Dt'; move: (adj_no_cface Hbg Htt').
    by rewrite (monic_inj (prev_next Ur) Dt') connect0.
  move: (set0P (subsetP chordless_spoke_ring _ Ht) t').
  rewrite /setI /setD1 Htt' Ht' andbT -negb_orb.
  by case/orP; move/eqP=> <-; auto; right; apply next_prev.
move: {Ht12}(Hrt _ _ Ht12 Ht1 Ht2) => [Ht12 Dt12].
move: {Ht13}(Hrt _ _ Ht13 Ht1 Ht3) => [Ht13 Dt13].
move: {Hrt Ht23}(Hrt _ _ Ht23 Ht2 Ht3) => [Ht23 Dt23].
move: (rot_to Ht1) (min_arity) (cycle_next Ur) (Ur) => [i r' Dr].
rewrite -size_spoke_ring -(size_rot i) -(cycle_rot i) -(uniq_rot i) Dr.
case: r' {Dr} => [|u2 [|u3 [|u4 r']]] //= _; move/and4P=> [Du2 Du3 Du4 _].
case/andP; do 2 case/norP=> _; case/norP; case/eqP.
rewrite -{u4 Du4}(eqP Du4) -{u3 Du3}(eqP Du3) -{u2 Du2}(eqP Du2).
case: Dt12 => [Dt2|Dt1].
  case: Dt23 => [Dt3|Dt2']; last by case Ht13; rewrite Dt2 Dt2'.
  case: Dt13 => [Dt3'|Dt1]; first by case Ht12; rewrite Dt3 Dt3'.
  by rewrite Dt2 Dt3 Dt1.
case: Dt13 => [Dt3|Dt1']; last by case Ht23; rewrite Dt1 Dt1'.
case: Dt23 => [Dt3'|Dt2]; first by case Ht12; rewrite Dt3 Dt3'.
by rewrite Dt3 Dt2 Dt1.
Qed.

End SpokeRing.

Definition minimal_counter_example_is_plain_cubic_pentagonal :=
  PlainCubicPentagonal Hg min_arity.

End Birkhoff.

Prenex Implicits spoke spoke_ring.

Coercion minimal_counter_example_is_plain_cubic_pentagonal :
  minimal_counter_example >-> plain_cubic_pentagonal.

Unset Implicit Arguments.