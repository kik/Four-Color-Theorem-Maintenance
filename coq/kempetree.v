(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import funs.
Require Import ssrbool.
Require Import dataset.
Require Import ssrnat.
Require Import dyck.
Require Import seq.
Require Import paths.
Require Import connect.
Require Import hypermap.
Require Import geometry.
Require Import color.
Require Import chromogram.
Require Import coloring.
Require Import cfmap.
Require Import cfcolor.
Require Import ctree.
Require Import initctree.
Require Import gtree.
Require Import initgtree.
Require Import gtreerestrict.
Require Import ctreerestrict.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Here we put all the reducibility steps together, to compute the   *)
(* Kempe closure tree of a configuration, which we can use to test   *)
(* directly for D-reducibility. A bit more work will be required for *)
(* C-reducibility.                                                   *)

Fixpoint ctree_size (t : ctree) : nat :=
  match t with
  | Ctree_node t1 t2 t3 => ctree_size t1 + (ctree_size t2 + ctree_size t3)
  | Ctree_leaf _ => 1
  | Ctree_empty => 0
  end.

Lemma ctree_size_partition : forall t t' t'',
    ctree_partition t (Ctree_pair t' t'') ->
  ctree_size t = ctree_size t' + ctree_size t''.
Proof.
have Epp := addnCA (ctree_size _).
have Esz0: forall t, (forall et, ctree_mem t et = false) -> ctree_size t = 0.
  elim=> [t1 Hrec1 t2 Hrec2 t3 Hrec3|lf Hr|] Ht //=.
    have Hte := Ht (Adds _ _); rewrite (Hrec1 (Hte Color1)).
    by rewrite (Hrec2 (Hte Color2)) (Hrec3 (Hte Color3)).
  by move: (Ht seq0).
simpl; elim.
  move=> t1 Hrec1 t2 Hrec2 t3 Hrec3 t' t'' Ht.
  move: {Ht}(Ht seq0) (Ht (Adds _ _)).
    case: t' => [t1' t2' t3'|lf|] //.
      case: t'' => [t1'' t2'' t3''|lf|] // _ Hte.
        rewrite /= (Hrec1 _ _ (Hte Color1)).
        rewrite (Hrec2 _ _ (Hte Color2)) (Hrec3 _ _ (Hte Color3)).
        by rewrite -!addnA (Epp t1'') (Epp t2'') (Epp t1'').
      rewrite /= (Hrec1 _ Ctree_empty (Hte Color1)).
      rewrite (Hrec2 _ Ctree_empty (Hte Color2)).
      by rewrite (Hrec3 _ Ctree_empty (Hte Color3)) /= !addn0.
    case: t'' => [t1'' t2'' t3''|lf|] // _ Hte.
      rewrite /= (Hrec1 Ctree_empty _ (Hte Color1)).
      rewrite (Hrec2 Ctree_empty _ (Hte Color2)).
      by rewrite (Hrec3 Ctree_empty _ (Hte Color3)).
    rewrite /= (Hrec1 Ctree_empty Ctree_empty (Hte Color1)).
    rewrite (Hrec2 Ctree_empty Ctree_empty (Hte Color2)).
    by rewrite (Hrec3 Ctree_empty Ctree_empty (Hte Color3)).
  move=> lf _ t' t'' Ht.
    case Dt': t' Ht => [t1' t2' t3'|lf'|] Ht.
     move: {Ht}(Ht seq0) (Ht (Adds _ _)).
      case: t'' => [t1'' t2'' t3''|lf''|] Htn //.
      rewrite -Dt'; move=> Hte; rewrite (Esz0 t') //.
      by move=> [|e et]; [ rewrite Dt' | rewrite -(Hte e et) /= orbC ].
     rewrite addnC (Esz0 t'') //; move=> et; rewrite -(Ht et).
      by case (ctree_mem t'' et); case et.
    by case: t'' {Ht}(Ht seq0).
move=> /= t' t'' Ht; rewrite (Esz0 t') ?(Esz0 t'') //;
 by move=> et; apply: negbE; case/norP: (Ht et).
Qed.

Lemma ctree_size_proper : forall h t,
  ctree_proper h t -> ctree_size t = 0 -> t = Ctree_empty.
Proof.
elim=> [|h Hrec] [t1 t2 t3|lf|] //= [Hne Ht1 Ht2 Ht3] Hzt; move: Hzt Hne.
case Hzt1: (ctree_size t1); [ rewrite (Hrec _ Ht1 Hzt1) | done ].
case Hzt2: (ctree_size t2); [ rewrite (Hrec _ Ht2 Hzt2) | done ].
by case Hzt3: (ctree_size t3); first by rewrite (Hrec _ Ht3 Hzt3).
Qed.

Fixpoint exp3 (n : nat) : nat := if n is  S n' then 3 * exp3 n' else 1.

Lemma ctree_max_size_proper : forall h t,
  ctree_proper h t -> ctree_size t <= exp3 h.
Proof.
elim=> [|h Hrec] [t1 t2 t3|lf|] //= [_ Ht1 Ht2 Ht3]; rewrite addn0.
by move: leq_add2; auto.
Qed.

Section KempeTreeClosure.

Variable h : nat.

Let ktc_fun := ctree -> ctree -> gtree -> ctree * gtree_pair.

Definition ktc_step closure kr :=
  let: (ctu, gtp) := kr in
  if ctree_empty ctu then kr else
  let: Gtree_pair gtr gtu := gtp in
  if gtree_empty gtr then kr else
  if gtree_empty gtu then (Ctree_empty, empty_gtree_pair) else
  let: Ctree_pair ctu' ctr :=
    ctree_restrict h ctu (Ctr_some Bstack0 gtr Ctr_none) in
  closure ctu' (ctree_rotlr ctr) gtu.

Definition ktc_step2c step (closure : ktc_fun) ctu ctr gtu :=
  step (step (closure ctu ctr gtu)).

Definition ktc_dostep2c closure := ktc_step2c (ktc_step closure) closure.

Fixpoint kempe_tree_closure (d : nat) : ktc_fun :=
  if d is S d' then ktc_dostep2c (kempe_tree_closure d') else
  fun ctu ctr gtu => (ctu, gtree_restrict gtu (Gtr_some Bstack0 ctr Gtr_none)).

Variable P : colseq -> Prop.

Definition kempe_valid ctu ctr gtr gtu :=
     ctree_proper (S h) ctu
  /\ ctree_sub ctu =1
       (fun et => if negb (even_trace et) then 0 else
                  gtree_sub gtr Bstack0 et + gtree_sub gtu Bstack0 et)
  /\ (forall et, ctree_mem ctr et ->
      kempe_coclosure P (ctrace et) /\ size et = S h)
  /\ (forall w, gtree_mem gtr w -> ~ gtree_mem gtu w /\ init_gtree_spec (S h) w)
  /\ (forall w, ~ gtree_mem gtu w -> init_gtree_spec (S h) w ->
      exists2 et, kempe_coclosure P (ctrace et) & matchpg Bstack0 et w)
  /\ (forall w, gtree_mem gtu w -> init_gtree_spec (S h) w).

Definition kempe_complete sz ctu ctr gtr gtu :=
     (ctree_size ctu < sz \/ ctr = Ctree_empty /\ (forall w, ~ gtree_mem gtr w))
  /\ (forall et, let norm_et e := permt (edge_rot e) (etrace et) in
        (P (ctrace et) \/ (exists e, ~ ctree_mem ctu (norm_et e))) ->
      ctree_mem ctr (etrace et) \/ gtree_sub gtu Bstack0 et = 0).

Let ktr_prop ktr Q : Prop :=
  let: (ctu, Gtree_pair gtr gtu) := ktr in Q (ctu : ctree) Ctree_empty gtr gtu.

Theorem kempe_tree_closure_correct : forall d ctu ctr gtu,
  let ktr0 Q := Q ctu ctr Gtree_empty gtu in
  let ktrp := ktr_prop (kempe_tree_closure d ctu ctr gtu) in
  ktr0 kempe_valid ->
    ktrp kempe_valid
 /\ forall sz, ktr0 (kempe_complete (exp3 d + sz)) -> ktrp (kempe_complete (S sz)).
Proof.
elim=> [|d Hrec].
  move=> ctu ctr gtu; hnf; move=> [Hctu [Ectu [Hctr [Hgte [Hgtu Hclg]]]]] /=.
  move Dctrr:(Gtr_some Bstack0 ctr Gtr_none) => ctrr.
  move: (gtree_restrict_partition gtu ctrr) (gtree_mem0_restrict gtu ctrr).
  case: (gtree_restrict gtu ctrr) => [gtr gtu'] /=.
  move=> Hgtp Hgtr; split.
    split; [ done | split ].
      move=> et; rewrite (Ectu et); case: (even_trace et) => //=.
      by rewrite gtree_sub_empty; apply: match_count_partition.
    split; [ done | split ].
      move=> w Hwr; move: Hwr (esym (Hgtr w)) {Hgtp}(elimF idP (Hgtp w)) => ->.
      case/andP=> [Hwu _]; rewrite Hwu /=.
      by case: (gtree_mem gtu' w); [ case | split; last by apply: Hclg ].
    split; [ move=> w Hwu' Hcw | idtac ].
      case Hwu: (gtree_mem gtu w) (Hgtp w); last by move/idP: Hwu; auto.
      case Hwr: (gtree_mem gtr w); last by rewrite (introF idP Hwu').
      clear; rewrite {}Hgtr {}Hwu -{ctrr}Dctrr /= orbF in Hwr.
      move/xmatchP: Hwr => [et Het Hm]; move/andP: Hcw => [Hsw Hbw].
      by case: (Hctr _ Het); exists et.
    move=> w Hw; apply Hclg; apply/negPf => [Hwu].
    by case/idP: (Hgtp w); rewrite Hw Hwu orbC.
  move=> sz [Hsz Hcl]; split.
    case: Hsz => [Hsz|[Dctr Egte]]; [ left | right; split ]; trivial.
    move=> w; rewrite Hgtr andb_comm -Dctrr Dctr /=.
    by rewrite (introF (has_matchP _ _ w)) //; case.
  move=> et; hnf; move=> Het; right; symmetry; apply: (eqP (negbEf _)).
  apply/nmatchP => [[w Hw Hm]]; case/idP: (Hgtp w); rewrite Hw Hgtr -Dctrr /=.
  case Hwu: (gtree_mem gtu w); rewrite //= orbF eqbE.
  case: {Hcl Het}(Hcl _ Het) => [Het|Het].
    rewrite -matchpg_etrace in Hm.
    by apply/eqP; apply/xmatchP; exists (etrace et).
  case (elimF (match_countP (gtree_mem gtu) Bstack0 et)); last by exists w.
  by rewrite /gtree_sub in Het; rewrite Het.
  simpl; move: (kempe_tree_closure d) Hrec => ktc' Hktc'.
suffice: forall ktr, let ktrp := ktr_prop ktr in
                 let ktrp' := ktr_prop (ktc_step ktc' ktr) in
  ktrp kempe_valid ->
     ktrp' kempe_valid
  /\ forall sz,
     ktrp (kempe_complete (exp3 d + S sz)) -> ktrp' (kempe_complete (S sz)).
  move=> Hstep ctu ctr gtu Hv; case: (Hktc' _ _ _ Hv) => [Hv1 Hcl1].
  case: (Hstep _ Hv1) => [Hv2 Hcl2]; case: (Hstep _ Hv2) => [Hv3 Hcl3].
  split; first done; move=> sz Hkc; apply: Hcl3; rewrite addnS.
  by apply Hcl2; rewrite addnS; rewrite -!addnA in Hkc; auto.
move=> ktr; move Dktr': (ktc_step ktc' ktr) => ktr'; move: Dktr'.
move: ktr => [ctu [gtr gtu]] /= Dktr' [Hctu [Ectu [Hcte [Hgtr [Hgtu Hclg]]]]].
case Hctue: (ctree_empty ctu) Dktr'.
  move <-; split; first by repeat (split; trivial).
  by move=> sz [Hsz Hcl]; split; rewrite // (ctree_empty_eq Hctue); left.
case Hgtre: (gtree_empty gtr).
  move <-; split; first by repeat (split; trivial).
  move=> sz [Hsz Hcl]; split; last done; right; split; trivial.
  by move=> w; rewrite (gtree_empty_empty Hgtre) gtree_mem_empty.
case Hgtue: (gtree_empty gtu); move <-.
  split; last by move=> sz _; split; [ left | right; rewrite gtree_sub_empty ].
  do 2 split; first by move=> et; rewrite /= gtree_sub_empty /= addn0 if_same.
  split; first done; split; first by move=> w; rewrite gtree_mem_empty.
  split; last by move=> w; rewrite gtree_mem_empty.
  by rewrite (gtree_empty_empty Hgtue) in Hgtu |- *.
clear ktr' Hctue Hgtre Hgtue.
move: (ctree_restrict_correct (Ctr_some Bstack0 gtr Ctr_none) Hctu).
move: (ctree_restrict _ _ _) => [ctu' ctr] /= [Hctru' Hctp Ectu'r].
suffice [Hv Hc]: kempe_valid ctu' (ctree_rotlr ctr) Gtree_empty gtu
  /\ forall sz,
       kempe_complete (S sz) ctu Ctree_empty gtr gtu ->
     kempe_complete sz ctu' (ctree_rotlr ctr) Gtree_empty gtu.
- by case: (Hktc' _ _ _ Hv); split; auto=> sz; rewrite addnS; auto.
have Ectu': ctree_sub ctu' =1
       (fun et => if negb (even_trace et) then 0 else gtree_sub gtu Bstack0 et).
  move=> et; rewrite Ectu'r Ectu addn0.
  by case (even_trace et); first exact: subn_addr.
clear Ectu'r Hktc' Hcte; split.
  split; [ exact (Hctru' false) | split ].
    move=> et; rewrite /= gtree_sub_empty; exact (Ectu' et).
  split; [ move=> et Het | by split; [ case | split ] ].
  have [g Het']: exists g, ctree_mem ctr (permt g et).
    rewrite (ctree_mem_rotlr (Hctru' true)) in Het.
    by case (orP Het); [ exists Eperm312 | exists Eperm231 ].
  pose et' := permt g et; rewrite -/et' in Het'.
  have [g' Eg']: exists g', ctrace et = permt g' (ctrace et').
    exists (inv_eperm g); rewrite /et' ctrace_permt.
    exact (monic_move (monic_maps (inv_permc g)) (erefl _)).
  have Elg: size et' = size et by apply: size_maps.
  case Het'u: (ctree_mem ctu et') (Hctp et'); case Hetu': (ctree_mem ctu' et');
    rewrite Het'; move=> Hep {Hep Het'}//.
  move: Hetu' Het'u; rewrite /ctree_mem Ectu Ectu'.
  case: (even_trace et') => [|] //= Het'.
  rewrite -(eqP (negbEf Het')) addn0; move=> Het'g.
  case: {Het'g}(nmatchP Het'g) => [w Hw Hm].
  move: {Hgtr}(Hgtr w Hw) => [Hwu H]; case/andP: H (Hgtu _ Hwu H).
  move=> Hlw Hcw [et1 _ Het1w].
  move: (esym (matchpg_size Hm)); rewrite (eqP Hlw) Elg.
  move=> Hetl; split; last done; move=> P' HP' HP'et.
  have HP'et': P' (ctrace et') by rewrite /et' ctrace_permt; case: (HP' _ HP'et).
  case: (HP' _ HP'et') => [_ [w1 Hetw1 HP'w1]].
    move: (take (pred (size w1)) w1) (matchg_cgram Hetw1) => w2 Dw1.
    case: (matchg_balanced Hetw1) => [_ Hw2]; rewrite Dw1 sumt_ctrace /= in Hw2.
    move: (Hetw1); rewrite Dw1 !matchg_pg //; move=> Hetw2.
    case: (Hgtu w2).
      by move=> Hgtuw2; case/idPn: Het'; apply/nmatchP; exists w2.
    by rewrite /init_gtree_spec Hw2 (matchpg_size Hetw2) Elg Hetl set11.
  move=> et2 Het2 Het2w; apply: (Het2 _ HP' (HP'w1 _ _)).
  by rewrite Dw1 matchg_pg.
move=> sz [Hsz Hcl]; split.
  case: Hsz => [Hsz|[_ Egtr]].
    move: Hsz; rewrite (ctree_size_partition Hctp) addnC.
    case Dctr: (ctree_size ctr) => [|m] Hsz.
      right; rewrite (ctree_size_proper (Hctru' true) Dctr).
      by repeat split; move=> *; rewrite gtree_mem_empty.
    by left; apply: (@leq_trans _ (S (S _))) Hsz; apply: leq_addl.
  right; split; last by move=> *; rewrite gtree_mem_empty.
  replace ctr with Ctree_empty; first done; symmetry.
  apply (ctree_size_proper (Hctru' true)).
  apply (@addn_injl (ctree_size ctu')); rewrite -(ctree_size_partition Hctp).
  rewrite (@ctree_size_partition ctu ctu' Ctree_empty) //.
  move=> et; move: (Hctp et).
  case Hetu': (ctree_mem ctu' et); case Hetu: (ctree_mem ctu et); trivial.
  case/idPn: Hetu'; move: Hetu.
  by rewrite /ctree_mem Ectu Ectu' {1}/gtree_sub match_count_0.
move=> et; hnf; case=> [Het|[e Hrot]]; try (case: (Hcl et) => //; tauto).
 case Hetu': (ctree_mem ctu' (etrace et)).
 case Hrotu: (ctree_mem ctu (permt (edge_rot e) (etrace et))).
 left; move: {Hctp}(Hctp (permt (edge_rot e) (etrace et))).
    rewrite {}Hrotu (introF idP Hrot) /=.
    case Hrotr: (ctree_mem ctr (permt (edge_rot e) (etrace et))) => // _.
    rewrite (ctree_mem_rotlr (Hctru' true)).
    case: e {Hrot}(introF idP Hrot) Hrotr; simpl;
      by first [ rewrite permt_id Hetu' | move=> _ H; rewrite H ?orb_b_true ].
  by case: (Hcl et); auto; first by right; exists e; rewrite Hrotu.
right; symmetry; apply: eqP; apply: (introTn nmatchP) => [[w Hw Hetw]].
rewrite /ctree_mem Ectu' even_etrace /= in Hetu'.
by case (elimF nmatchP Hetu'); exists w; rewrite ?matchpg_etrace.
Qed.

Lemma kempe_validP : forall ctu ctr gtr gtu, kempe_valid ctu ctr gtr gtu ->
                     forall et, size et = S h ->
  negb (ctree_mem ctu (etrace et)) -> kempe_coclosure P (ctrace et).
Proof.
move=> ctu ctr gtr gtu [Hctu [Ectu [Hctr [Hgtr [Hgtu Hclg]]]]] et0 Het0l.
move=> Het0 P' HP' HP'et0; have HP'eet0: (P' (ctrace (etrace et0))).
  by rewrite /etrace ctrace_permt; case: (HP' _ HP'et0).
case: (HP' _ HP'eet0) => [_ [cw Hwet0 HP'cw]].
  move: (take (pred (size cw)) cw) (matchg_cgram Hwet0) => w Dcw.
  case: (matchg_balanced Hwet0) => [_ Hbw]; rewrite sumt_ctrace /= Dcw in Hbw.
rewrite Dcw matchg_pg // in Hwet0.
case: (Hgtu w).
- move=> Hgtuw; case: (negP Het0).
  rewrite /ctree_mem Ectu even_etrace /= eqd_sym -leqn0 -ltnNge.
  apply: (leq_trans _ (leq_addl _ _)); rewrite ltnNge leqn0 eqd_sym.
  by apply: (introT nmatchP _); exists w.
- rewrite /init_gtree_spec Hbw (matchpg_size Hwet0) /etrace /permt size_maps.
  by rewrite Het0l set11.
by move=> et' Het' Het'w; apply: (Het' _ HP' (HP'cw _ _)); rewrite Dcw matchg_pg.
Qed.

Lemma kempe_completeP : forall ctu ctr gtr gtu, kempe_valid ctu ctr gtr gtu ->
                                           kempe_complete 1 ctu ctr gtr gtu ->
                        forall et, size et = S h ->
  reflect (kempe_coclosure P (ctrace et)) (negb (ctree_mem ctu (etrace et))).
Proof.
move=> ctu ctr gtr gtu Hv [Hsz Hcl] et0 Het0l.
case Het0: (ctree_mem ctu (etrace et0)); constructor;
 last by apply (kempe_validP Hv Het0l); rewrite Het0.
case: Hv => [Hctu [Ectu [Hctr [Hgtr [Hgtu Hclg]]]]] Hk.
apply: {Het0}(elimF idP _ Het0); case: Hsz => [Hsz0|[Dctr Egtr]].
  rewrite ltnS leqn0 in Hsz0.
  by rewrite (ctree_size_proper Hctu (eqP Hsz0)).
have Hctug: forall et, gtree_sub gtu Bstack0 et = 0 -> ~ ctree_mem ctu et.
  move=> et Het; rewrite /ctree_mem Ectu Het /gtree_sub.
  by rewrite match_count_0 /= ?if_same.
have Hgtu23: forall et, gtree_sub gtu Bstack0 et = 0 ->
              gtree_sub gtu Bstack0 (permt Eperm132 et) = 0.
  move=> et Het; apply: esym; apply: eqP; apply/nmatchP => [[w Hw Hm]].
  rewrite matchpg_flip in Hm.
  by case/idPn: (introT eqP (esym Het)); apply/nmatchP; exists w.
have Hctu23: forall et, ctree_mem ctu (permt Eperm132 (etrace et)) ->
                        ctree_mem ctu (etrace et).
  move=> et; rewrite {2}/ctree_mem Ectu even_etrace {1}/gtree_sub.
  rewrite match_count_0 //=; move=> Het.
  by apply/eqP => [Hwet]; apply: Hctug Het; auto.
have Hctue: forall et, ctree_mem ctu (etrace et) =
                         ctree_mem ctu et || ctree_mem ctu (permt Eperm132 et).
  have Hio: forall b b' : bool, (b -> b') -> b' = b || b'.
    by rewrite /is_true; case; auto.
  move=> et; move: (Hctu23 et); rewrite /etrace /etrace_perm.
  case (even_trace et); rewrite ?permt_id ?etrace_id; auto.
  rewrite orbC; auto.
  move Dcet0: (ctrace et0) Hk => cet0 Hk; apply/negPf => [Het0].
  case (Hk (fun cet => exists2 et, cet = ctrace et & ctree_mem ctu (etrace et))).
  move=> cet [et Dcet Het]; split.
   move=> g; exists (permt g et); first by rewrite Dcet ctrace_permt.
    set et' := etrace et.
    have [g' <-]: exists g', permt g' et' = permt g et.
      case: (compose_permt g (etrace_perm et) (etrace et)) => [g' Eg'].
      exists g'; rewrite /et' Eg' /etrace /etrace_perm.
      by case (even_trace et); rewrite ?permt_id ?etrace_id.
    rewrite Hctue; apply/norP => [[Hg'et Hpg'et]].
    have Hrot: exists e, ~ ctree_mem ctu (permt (edge_rot e) et').
      case: g' {Hg'et Hpg'et}(negP Hg'et) (negP Hpg'et);
      try first [ by exists Color1 | by exists Color2 | by exists Color3
                | by rewrite etrace_id; exists Color1; rewrite permt_id ];
      move=> _ Het'; rewrite /permt -maps_comp in Het';
      [ exists Color2 | exists Color3 ]; move=> He;
      by apply: (Het' (etrans (congr1 _ (eq_maps _ _)) He)); case.
    case (Hcl et); [ by right | by rewrite Dctr | idtac ].
    rewrite Hctue in Het; case/orP: Het => Het Het';
      by apply: (elimF idP (negbIf Het) (introT negP _)); auto.
   case Hgtuet: (0 =d gtree_sub gtu Bstack0 (etrace et)).
      case (Hctug _ (esym (eqP Hgtuet)) Het).
    case/nmatchP: Hgtuet => [w Hw Hwet].
    case/andP: (Hclg _ Hw) => [Hsw Hbw].
    exists (cgram 0 false w).
      by rewrite matchpg_etrace -matchg_pg // -Dcet in Hwet |- *.
    move=> cet' Hcet'w; have [et' Dcet']: exists et', cet' = ctrace et'.
    move: (balanced_sumt0 Hbw Hcet'w).
      elim/last_ind: cet' Hcet'w => [|et' e _]; first by case w.
      move=> _ He; rewrite -cats1 /sumt foldr_cat /= addc0 in He.
      exists et'; congr add_last; apply: (@inj_addc e); rewrite addcc -{}He.
      elim: et' e => [|e' et' Erec] e /=; first by rewrite addc0.
      by rewrite Erec !addcA (addcC e').
    exists et'; auto; rewrite Dcet' matchg_pg // in Hcet'w.
    rewrite /ctree_mem Ectu even_etrace /= eqd_sym -leqn0 -ltnNge.
    apply: leq_trans _ (leq_addl _ _); rewrite ltnNge leqn0 eqd_sym.
    by apply: (introT nmatchP _); exists w; rewrite ?matchpg_etrace.
  by exists et0; rewrite // /ctree_mem Het0.
move=> cet Hpet [et Dcet Het]; case (Hcl et); rewrite ?Dctr // -?Dcet; auto.
move=> Hgtuet; case (negP Het); rewrite Ectu even_etrace /=.
have Hgtueet: gtree_sub gtu Bstack0 (etrace et) = 0.
  by rewrite /etrace /etrace_perm; case (even_trace et); rewrite ?permt_id; auto.
by rewrite Hgtueet addn0; apply/nmatchP => [] [w' Hw' _]; case (Egtr _ Hw').
Qed.

Lemma kempe_valid_restrict : forall ctr ctu gtu gtr,
   (forall et, ctree_mem ctr et -> P (ctrace et) /\ size et = S h) ->
  kempe_valid ctu Ctree_empty gtr gtu -> kempe_valid ctu ctr gtr gtu.
Proof.
move=> ctr ctu gtu gtr Hctr [Hctu [Ectu [_ Hgtur]]]; do 3 (split; trivial).
by move=> et Het; case: (Hctr _ Het); split; first by exists (ctrace et).
Qed.

Lemma kempe_valid_init :
  let ctu := ctree_init_tree (S h) in let gtu := gtree_init_tree (S h) in
  kempe_valid ctu Ctree_empty Gtree_empty gtu.
Proof.
move: (ctree_init_tree_proper (S h)) (ctree_sub_init_tree (S h)).
move Dctu: (ctree_init_tree (S h)) => ctu Hctu Ectu.
move Dgtu: (gtree_init_tree (S h)) (gtree_mem_init_tree (S h)) => gtu Egtu.
split; first done; split.
  move=> et; rewrite Ectu gtree_sub_empty andbA andbC.
  case Hete: (even_trace et); last done.
  by rewrite /= /gtree_sub (match_count_eq Egtu) match_count_balanced.
split; first done; split; first by move=> w; rewrite gtree_mem_empty.
by split; move=> w; rewrite Egtu; first by move=> H; case/H.
Qed.

Lemma kempe_complete_init : forall ctr,
   (forall et, P (ctrace et) -> ctree_mem ctr (etrace et)) ->
  let ctu := ctree_init_tree (S h) in
  let gtu := gtree_init_tree (S h) in
  forall gtr, kempe_complete (exp3 (S (S h))) ctu ctr gtr gtu.
Proof.
move=> ctr Hctr; split.
  left; have Hexp: exp3 (S h) < exp3 (S (S h)).
    move: (S h) => n; rewrite -addn1 /= leq_add2l addn0.
    elim: n => [|n Hrec] //=; rewrite -!addnA addnA.
    exact: leq_trans Hrec (leq_addr _ _).
  apply: leq_trans Hexp; rewrite ltnS; apply ctree_max_size_proper.
  apply ctree_init_tree_proper.
move=> et; hnf; case=> [Het|[e Hrot]]; auto.
right; apply: (esym (eqP (negbEf (introF nmatchP _)))).
move=> [w Hw Hetw]; case: Hrot; rewrite /ctree_mem ctree_sub_init_tree.
rewrite gtree_mem_init_tree in Hw; case: {Hw}(andP Hw) => [Hsw Hbw].
rewrite {1 2}/etrace {1 2}/permt !size_maps -(matchpg_size Hetw) Hsw.
rewrite -matchg_pg // in Hetw.
rewrite !ctrace_permt !memc0_permt (matchg_memc0 Hetw).
set pre := permt (edge_rot e); have Hreet: even_trace (pre (etrace et)).
  rewrite /is_true -(even_etrace et) /even_trace /ttail /pre proper_permt.
  case: (etrace et) => [|[|||] ett]; rewrite // /permt /= -maps_comp;
    by apply: (congr1 even_tail (eq_maps _ _)); move=> [|||]; case e.
have Hbit: forall et', odd (count_cbit1 et') = cbit1 (sumt et').
  move=> et'; elim: et' => [|c et' Hrec] //=.
  by rewrite odd_addn Hrec cbit1_addc; case c.
rewrite Hreet /= -(odd_double_half (count_cbit1 _)) Hbit /pre.
rewrite sumt_permt sumt_ctrace permc0 /= add0n eqd_sym -leqn0 -ltnNge.
exact: even_dyck_pos.
Qed.

End KempeTreeClosure.

Definition kempe_tree (cp : cprog) : ctree :=
  if cprsize cp is S (S h) then
    let ctu := ctree_init_tree (S h) in
    let gtu := gtree_init_tree (S h) in
    let ctr := cpcolor cp in
    fst (kempe_tree_closure h (S (S h)) ctu ctr gtu)
  else Ctree_empty.

Theorem kempe_treeP : forall cp et, size et = pred (cprsize cp) ->
 reflect (kempe_coclosure (ring_trace (rot 1 (cpring (cpmap cp))))  (ctrace et))
         (negb (ctree_mem (kempe_tree cp) (etrace et))).
Proof.
move=> cp; set Pcol := ring_trace _; rewrite /kempe_tree.
move: (cpcolor cp) (ctree_mem_cpcolor cp) => ctr Dctr.
case Dh: (cprsize cp) => [|[|h]].
 by rewrite -size_ring_cpmap head_cpring in Dh.
 by case=> // _; left; move=> P H; case/H=> [_ [[|s w] Hw _]].
set ctu := ctree_init_tree _; set gtu := gtree_init_tree _.
case: (@kempe_tree_closure_correct h Pcol (S (S h)) ctu ctr gtu).
  apply: (kempe_valid_restrict _ (kempe_valid_init _ _)).
  move=> et'; move/(Dctr _)=> [Heet' [k Hk Det']]; split.
    by rewrite /Pcol /ctrace -rot1_adds Det' -trace_rot -maps_rot; exists k.
  move: (congr1 size Det'); rewrite size_trace size_maps size_ring_cpmap Dh.
  by case.
case: (kempe_tree_closure h (S (S h)) ctu ctr gtu) => [ctu' [gtr gtu']].
move=> Hv Hcl; apply: {Hcl}(kempe_completeP Hv (Hcl _ _)).
rewrite addn0; apply: kempe_complete_init {et Het} => [et Het]; apply/(Dctr _).
split; first by apply even_etrace.
case: Het => [k Hk Det]; rewrite /Pcol maps_rot trace_rot in Det.
rewrite /etrace; set g := etrace_perm et; exists (comp g k).
  by apply: (@coloring_inj _ g) Hk => //; apply permc_inj.
rewrite (maps_comp g k) -/(permt g) trace_permt sumt_permt.
by rewrite (monic_move (@rotr_rot 1 _) (esym Det)) /ctrace rotr1_add_last.
Qed.

Unset Implicit Arguments.
