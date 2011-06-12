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
Require Import color.
Require Import geometry.
Require Import coloring.
Require Import patch.
Require Import cfmap.
Require Import quiz.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Compile the quiz that tests for the occurrence of a configuration. Since *)
(* this requires to compute arities, we also check that the arity of ring   *)
(* regions are in the [3,6] range along the way. The procedure here is      *)
(* valid, but not complete, e.g., it assumes that skews only occur at       *)
(* articulations. The configuration data has been carefully knobbed to meet *)
(* those constraints.                                                       *)
(*   The algorithm proceeds by walking the map construction program         *)
(* backwards, keeeping track of kernel faces and of arities on the submap   *)
(* ring. During the traversal a list of questions is kept, that covers      *)
(* exactly the kernel faces that are disjoint from the current submap ring. *)
(* Each of these question is rooted at (node (ic x)) for some dart x of the *)
(* submap ring, where ic is the injection from the current submap to the    *)
(* full configuration map (crucially, this implies that "node" is computed  *)
(* in the full map). As the ring shrinks, questions are linked to form      *)
(* trees, until we arrive at the initial two-dart graph, where we have just *)
(* questions, which form a proper quiz.                                     *)
(*   H-type steps could be somewhat of a problem for this algorithm, but it *)
(* turns out that (with a little fiddling) in all the programs we consider, *)
(* we never need to join trees in an H step, so the code below doesn't      *)
(* cater to that case (we'd need to generate more LL and RR questions).     *)

(* We use a single sequence of records rather that three parallel sequences. *)

Record ring_question : Set := RingQuestion {
  ring_question_is_kernel : bool;
  ring_question_outer_arity :> nat;
  ring_question_node_question :> question
}.

Section ConfigQuiz.

Notation isk := ring_question_is_kernel.

Remark ringQuestionDataP : comparable ring_question.
Proof. rewrite /comparable; decide equality; apply: comparable_data. Qed.
Definition ringQuestionData := Eval compute in compareData ringQuestionDataP.
Canonical Structure ringQuestionData.
Let rqseq : Set := seq ringQuestionData.

(* We only compile questions for maps with kernel arities between 5 an 11; in *)
(* fact only the most central face (the one to which the "true" dart of the   *)
(* central submap belongs) can have more that 8 sides. We check and use this  *)
(* fact during the compilation. We also check that the ring arities are in    *)
(* the 3..6 range; this property allows us to lift the preembedding           *)
(* constructed in quiz.v into an actual embedding (see embed.v).              *)
(* All the functions below work with the arities offset by two, because each  *)
(* time a face is detached from the submap, if had at least two neighbors in  *)
(* that submap.                                                               *)

Definition small_qarity a :=
  match a with
  | 3 => Qa5
  | 4 => Qa6
  | 5 => Qa7
  | 6 => Qa8
  | 7 => Qa10
  | _ => Qa9
  end.

Definition bad_small_arity qa :=
  match qa with
  | Qa9 => true
  | Qa10 => true
  | Qa11 => true
  | _ => false
  end.

Lemma small_qarityP : forall a,
  let qa := small_qarity a in bad_small_arity qa = negb ((qa : nat) =d S (S a)).
Proof. do 8 case=> //. Qed.

Definition large_qarity a :=
  match a with
  | 7 => Qa9
  | 8 => Qa10
  | 9 => Qa11
  | _ => small_qarity a
  end.

Definition bad_ring_arity a :=
  match a with
  | O => true
  | S (S (S (S (S _)))) => true
  | _ => false
  end.

Lemma not_bad_ring_arity : forall (g : hypermap) (x : g),
  bad_ring_arity (pred (pred (arity x))) = false -> good_ring_arity x.
Proof. move=> g x; rewrite /good_ring_arity; move: (arity x); do 7 case=> //. Qed.

(* Error value. *)
Let noquiz := Quiz Qask0 Qask0.

(* The quiz construction proper.                                               *)

Definition rqs_Y rq1 rq3 (qs : rqseq) q1' : rqseq :=
  let: RingQuestion k1 a1 _ := rq1 in
  let: RingQuestion k3 a3 q3 := rq3 in
  Seq (RingQuestion k1 (S a1) q1') (RingQuestion k3 (S a3) q3) & qs.

Definition cfquiz_Y rq1 rq2 rqs' : rqseq :=
  let: RingQuestion _ _ q1 := rq1 in
  let: RingQuestion k2 a2 q2 := rq2 in
  if k2 then
    let qa2 := small_qarity a2 in
    if bad_small_arity qa2 then seq0 else
    rqs' match q1, q2 with
        | Qask0, Qask0 => Qask1 qa2
        | Qask0, _ => QaskL qa2 q2
        | _, Qask0 => QaskR qa2 q1
        | _, _ => QaskLR qa2 q2 q1
        end
   else
    if bad_ring_arity a2 then seq0 else
    match q1, q2 with
    | Qask0, Qask0 => rqs' Qask0
    | QaskR qa1 q1r, Qask0 => rqs' (QaskRR qa1 q1r)
    | Qask0, QaskL qa1 q1l => rqs' (QaskLL qa1 q1l)
    | _, _ => seq0
    end.

Definition rqs_H rq1 rq3 (qs : rqseq) q1' q2' : rqseq :=
  let: RingQuestion k1 a1 _ := rq1 in
  let: RingQuestion k3 a3 q3 := rq3 in
  Seq (RingQuestion k1 (S a1) q1')
      (RingQuestion true 1 q2')
      (RingQuestion k3 (S a3) q3)
   & qs.

Definition cfquiz_H rq1 rq2 rqs' : rqseq :=
  let: RingQuestion k1 _ q1 := rq1 in
  let: RingQuestion k2 a2 q2 := rq2 in
  if k2 then
    let qa2 := small_qarity (S a2) in
    if bad_small_arity qa2 then seq0 else
    match q1, q2, k1 with
    | Qask0, Qask0, true => rqs' (Qask1 qa2) q2
    | Qask0, Qask0, _ => rqs' q1 (Qask1 qa2)
    | Qask0, _, _ => rqs' q1 (QaskL qa2 q2)
    | _, Qask0, _ => rqs' (QaskR qa2 q1) q2
    | _, _, _ => seq0
    end
  else
    if bad_ring_arity (S a2) then seq0 else
    match q1, q2 with
    | Qask0, Qask0 => rqs' q1 q2
    | _, _ => seq0
    end.

Fixpoint cfquiz_rec (qs : rqseq) (cp : cprog) {struct cp} : quiz :=
  match cp, qs with
  | seq0, (Seq rq1 rq2 & _) =>
    let: RingQuestion k1 a1 q1 := rq1 in
    let: RingQuestion k2 a2 q2 := rq2 in
    if negb (k1 && k2) then noquiz else
    let qa1 := large_qarity (pred a1) in
    let qa2 := small_qarity (pred a2) in
    if negb ((qa1 : nat) =d S a1) || bad_small_arity qa2 then noquiz else
    Quiz (QaskR qa1 q2) (QaskR qa2 q1)
  | Adds s cp', (Seq rq1 rq2 rq3 & qs') =>
    match s with
    | CpR n => cfquiz_rec (rotr n qs) cp'
    | CpY => cfquiz_rec (cfquiz_Y rq1 rq2 (rqs_Y rq1 rq3 qs')) cp'
    | CpH => cfquiz_rec (cfquiz_H rq1 rq2 (rqs_H rq1 rq3 qs')) cp'
    | _ => noquiz
    end
  | _, _ =>
    noquiz
  end.

Section RqsWalk.

Variables (g0 g : pointed_map) (h : g -> g0).

Fixpoint rqs_fit (qs : rqseq) (p : seq g) {struct p} : bool :=
  match qs, p with
  | Adds rqd qs', Adds x p' =>
    let rq := rqd : ring_question in
    and3b (arity (h x) =d rq + arity x) (fitq (node (h x)) rq) (rqs_fit qs' p')
  | seq0, seq0 => true
  | _, _ => false
  end.

Lemma rqs_fit_adds : forall (rq : ring_question) qs x p,
 rqs_fit (Adds rq qs) (Adds x p) =
   and3b (arity (h x) =d rq + arity x) (fitq (node (h x)) rq) (rqs_fit qs p).
Proof. done. Qed.

Lemma rqs_fit_size : forall qs p, rqs_fit qs p -> size qs = size p.
Proof. elim=> [|rq qs Hrec] [|x p] //=; case/and3P=> *; congr S; auto. Qed.

Fixpoint rqs_walk (qs : rqseq) (p : seq g0) {struct p} : seq g0 :=
  match qs, p with
  | Adds rqd qs', Adds u p' =>
    let rq := rqd : ring_question in
    cat (cat (seqn (isk rq) u) (walkq (node u) rq)) (rqs_walk qs' p')
  | _, _ => seq0
  end.

Lemma rqs_walk_adds : forall (rq : ring_question) qs u p,
 rqs_walk (Adds rq qs) (Adds u p) =
   cat (cat (seqn (isk rq) u) (walkq (node u) rq)) (rqs_walk qs p).
Proof. done. Qed.

Definition rqs_ok (qs : rqseq) :=
  let r0 := cpring g0 in let r := cpring g in let hr := maps h r in
  and4 (rqs_fit qs r)
       (sub_set (setD r0 (setU (codom h) (fband hr))) good_ring_arity)
       (simple (cat (rqs_walk qs hr) r0))
       (fband (cat (rqs_walk qs hr) r0) =1 setU (setC (codom h)) (fband hr)).

End RqsWalk.

(* We check separately the radius of the configuration (the initial face *)
(* of the quiz might not be at the center of the kernel).                *)

Fixpoint cpradius2 (cp : cprog) (i : nat) {struct i} : bool :=
  if i is S i' then
    let cm0 := cpmask1 cp i' in
    let: Cpmask mr1 _ := cm0 in
    let: Cpmask _ mk1 := cpadj cm0 cp in
    let: Cpmask _ mk2 := cpadj (Cpmask mr1 mk1) cp in
    if all id mk2 then true else cpradius2 cp i'
  else false.

Variable cf : config.

Let cp : cprog := cfprog cf.

Definition cfquiz : quiz :=
  if cpradius2 cp (cpksize cp) then
    cfquiz_rec (seqn (cprsize cp) (RingQuestion false 0 Qask0)) cp
  else noquiz.

Hypothesis Hqz : isQuizR cfquiz.

Remark Cfquiz_Hcfk2 : cpradius2 cp (cpksize cp).
Proof. by move: Hqz; rewrite /cfquiz; case (cpradius2 cp (cpksize cp)). Qed.
Notation Hcfk2 := Cfquiz_Hcfk2.

Remark Cfquiz_qs0_notR : forall cp' : cprog, isQuizR (cfquiz_rec seq0 cp') = false.
Proof. by elim=> //; case. Qed.
Notation qs0_notR := Cfquiz_qs0_notR.

Remark Cfquiz_Hcp : config_prog cp.
Proof.
pose qs := seqn (cprsize cp) (RingQuestion false 0 Qask0).
have Hcp: setC1 seq0 cp by case: cp Hcfk2.
have Eqs: size qs = cprsize cp by rewrite /qs size_seqn.
move: Hcp Eqs Hqz; rewrite /cfquiz Hcfk2 -/qs.
elim: cp qs => // [s cp' Hrec] [|rq1 [|rq2 [|rq3 qs]]] //= _.
case: s cp' Hrec => //= [n||] [|s cp'] // H Eqs Hqs; apply: H (Hqs) => //.
- by rewrite -Eqs size_rotr.
- move: Hqs; rewrite /cfquiz_Y -(eq_add_S _ _ Eqs).
  case: rq1 rq2 rq3 => [k1 a1 q1] [[|] a2 q2] [k3 a3 q3].
    by case: (bad_small_arity (small_qarity a2)); first by rewrite qs0_notR.
  case: (bad_ring_arity a2); first by rewrite qs0_notR.
  by case: q1; rewrite ?qs0_notR //; case: q2; rewrite ?qs0_notR.
move: Hqs; rewrite /cfquiz_H -Eqs.
case: rq1 rq2 rq3 => [k1 a1 q1] [[|] a2 q2] [k3 a3 q3].
case: (bad_small_arity (small_qarity (S a2))); first by rewrite qs0_notR.
  by case: q1; rewrite ?qs0_notR //; case: q2; rewrite ?qs0_notR //; case k1.
  case: (bad_ring_arity (S a2)); first by rewrite qs0_notR.
by case: q1; rewrite ?qs0_notR //; case: q2; rewrite ?qs0_notR.
Qed.
Let Hcp := Cfquiz_Hcp.

Remark Cfquiz_Hrad2 : radius2 (kernel (cfring cf)).
Proof.
rewrite /cfring /cfmap -/cp.
elim: {-2}(cpksize cp) (leqnn (cpksize cp)) Hcfk2 => //= [i Hrec] Hi.
move: (proper_cpmask1 cp i) (cpsieve1 Hi Hcp); set g := cpmap cp.
set cm0 := cpmask1 cp i; set x0 := sub g (cpker cp) i => Hcm0 Ecm0.
case: (cpadj cm0 cp) (cpadj_proper Hcm0) (cpsieve_adj Hcp Hcm0) => mr1 mk1.
move/andP=> [_ Hmk1] Ecm1 /=; rewrite {}Ecm0 in Ecm1; set cm1 := Cpmask _ mk1.
have Hcm1: proper_cpmask cp cm1 by rewrite /= size_seqn set11.
case: (cpadj cm1 cp) (cpadj_proper Hcm1) (cpsieve_adj Hcp Hcm1) => mr2 mk2.
move/andP=> [_ Emk2] Ecm2.
case Hmk2: (all (@id bool) mk2); last by apply: Hrec; apply ltnW.
clear; clear Hrec; set kg := kernel _.
have Dkg: kg =1 fband (cpker cp).
  move=> x; move: (cpmap_simple Hcp) (cpmap_cover Hcp x).
  rewrite simple_cat fband_cat -/g orbC; move/and3P=> [_ Ug _].
  rewrite /kg /kernel /setC fband_rev.
  case Hx: (@fband g (cpker cp) x); last by move=> *; apply/idP.
  case/hasP: Hx => [y Hy Hxy] _;  rewrite (closed_connect (fbandF _) Hxy) -/g.
  by apply: (hasPn Ug).
have Hx0: kg x0.
  rewrite Dkg; apply: (subsetP (ring_fband _)); apply: mem_sub.
  by rewrite (size_cpker Hcp).
apply/(radius2P _); exists x0; first done.
move=> x Hx; apply/(at_radius2P (g := g) (a := kg) (kernelF _) _ _).
have Hx': has (adj x) (cpsieve cm1 cp).
  rewrite -Ecm2 /= fband_cat; apply/orP; right.
  suffice <-: cpker cp = sieve mk2 (cpker cp) by rewrite -Dkg.
  move: Hmk2 Emk2; rewrite -(size_cpker Hcp).
  by elim: (mk2) (cpker cp) => [|[|] m Hrec] [|y p] //= Hm Em; rewrite -Hrec.
case/hasP: Hx' => [y Hy]; case/adjP=> [z Hxz Hzy].
rewrite /cm1 /= sieve_false /= in Hy.
have Hez: (has (adj (edge z)) (seq1 x0)).
  by rewrite -Ecm1 /= fband_cat; apply/orP; right; apply/hasP; exists y.
rewrite has_seq1 Sadj in Hez; last by apply: cpmap_plain; apply config_prog_cubic.
case/adjP: Hez => [t Hx0t Htz]; exists t; exists z; split; auto; rewrite Dkg.
by apply/hasP; exists y; [ exact (mem_sieve Hy) | rewrite (same_cface Htz) ].
Qed.
Notation Hrad2 := Cfquiz_Hrad2.

Lemma cfquizP :
      sub_set (cpring (cpmap cp)) good_ring_arity
  /\ (exists x0, valid_quiz (cpring (cpmap cp)) x0 cfquiz).
Proof.
move: Hqz; rewrite /cfquiz Hcfk2 -[cpmap cp]/(cpmap (catrev cp seq0)).
set qs := seqn (cprsize cp) _; set cp1 : cprog := seq0; set cp2 := cp.
have Hcp1: cubic_prog cp1 by done.
have Hcp2: setU1 seq0 config_prog cp2 by apply setU1r.
have Arec: rqs_ok (@injcp cp1 cp2) qs.
  rewrite /cp2; set g := cpmap cp; set r := cpring g.
  have Dq0: rqs_walk qs r = seq0.
    by rewrite /qs -size_ring_cpmap -/g -/r; elim: r => //= *.
  have Hd0: codom (fun x : g => x) =1 g.
     by move=> x; apply/set0Pn; exists x; apply/eqP.
  split; rewrite //= ?maps_id -/g -/r ?{}Dq0 /qs //=.
  - by rewrite -size_ring_cpmap -/g -/r; elim: r => //= *; rewrite set11.
  - by move=> x; rewrite /setD /setU Hd0.
  - by move: (cpmap_simple Hcp); rewrite -/g -/r simple_cat; case/andP.
  by move=> x; rewrite /setU /setC Hd0.
elim: cp2 Hcp2 cp1 Hcp1 qs Arec => [|s cp2 Hrec] Hscp2 cp1 Hcp1 qs Arec Hqz'.
  case: Arec Hqz'; set g := cpmap seq0; set g0 := cpmap (catrev seq0 cp1).
  set r := cpring g; set r0 := cpring g0; set h := @injcp cp1 seq0.
  have EhE: forall x, edge (h x) = h (edge x) by move=> x; apply: edge_injcp.
  move=> Hr Hr0F Uq Eq; case Dqs: qs Hr => [|[[|] a1 q1] [|[[|] a2 q2] qs']] //=.
  case/and5P; rewrite addnC (addnC a2) /addn /= small_qarityP.
  set qa1 := large_qarity (pred a1); case: ((qa1 : nat) =P S a1) => //.
  case: a2 Dqs => [|a2] Dqs //; rewrite /pred; set qa2 := small_qarity a2.
  case: ((qa2 : nat) =P S (S a2)) => // [<-] <- Eqa1 Hq1 Eqa2 Hq2.
  case: qs' Dqs => //= Dqs _ _; split.
    move=> u Hu; apply: Hr0F; rewrite /setD Hu andbT /setU orbC /g0 /g.
    case Hu': (fband (maps h r) u); rewrite /fband -/g0 -/g in Hu' |- *.
      move: Uq; rewrite simple_cat; case/and3P; clear; case/hasP.
      exists u; first done; rewrite Dqs /= fband_cat /=; case/hasP: Hu' => v.
      by case/mapsP=> [[|] _ <-] Hu'; rewrite Hu' ?orbT.
    apply/set0Pn => [] [x Du]; case/hasP: Hu'; exists u; last exact: connect0.
    by rewrite (eqP Du); apply maps_f; case x.
  set qz := Quiz _ _.
  have Eqz: fband (walkqz (h false) qz) =1 fband (rqs_walk qs (maps h r)).
    move=> u; rewrite /qz Dqs /= /qstepR !EhE /= !fband_cat /= cats0.
    by repeat BoolCongr.
  exists (h false); repeat split.
  - rewrite /fitqz /qz /= eqseq_adds fitq_cat /qstepR !EhE /= eqseq_adds.
    by rewrite eqd_sym Eqa1 Hq2 eqd_sym Eqa2.
  - rewrite /g0 (simple_perm Eqz).
      by move: Uq; rewrite simple_cat; case/and3P.
    by rewrite /qz Dqs /= cats0 !size_cat /= !addnS addnC /qstepR !EhE.
  move=> u; rewrite Eqz; apply/idP/idP => Hu.
    move: Uq; rewrite simple_cat; case/and3P=> [_ Uq _].
    apply/hasP => [[v Hv Huv]]; case/hasP: Uq; exists v; first done.
    by rewrite -(fun q0 => closed_connect (fbandF q0) Huv).
  move: (Eq u); rewrite fband_cat (negbE Hu) orbF /setU /setC /g0 /g => ->.
  case Hu': (codom h u); last done; apply/hasP; exists u; last exact: connect0.
  by case/set0Pn: Hu' => [x Du]; rewrite (eqP Du); apply maps_f; case x.
have [Hcp2 Hscp1]: setU1 seq0 config_prog cp2 /\ cubic_prog (Adds s cp1).
  by case: (s) Hscp2 Hqz' => //=; case cp2; split.
move: {Hrec Hscp1}(Hrec Hcp2 _ Hscp1) => Hrec; simpl in Hrec; move: Hrec Arec Hqz'.
case Dqs: qs => [|rq1 [|rq2 [|rq3 qs']]] //; rewrite -Dqs.
set h := @injcp cp1 _; set g' := cpmap (Adds s cp2).
set g := cpmap cp2; set r := cpring g.
have Hh: injective h by apply: injcp_inj.
have EhE: forall x, edge (h x) = h (edge x) by move=> x; apply: edge_injcp.
have EhN: forall x, negb (cpring g' x) -> node (h x) = h (node x).
  by move=> x; apply: node_injcp.
have EhF: forall x y, cface (h x) (h y) = cface x y.
  by move=> x y; apply: cface_injcp.
move: (cpmap (catrev (Adds s cp2) cp1)) h Hh EhE EhN EhF {Hcp1} => g0.
set r0 := cpring g0; rewrite {}/g'; rewrite /setU1 orFb in Hscp2.
have Ur: simple r.
  rewrite /r /g; case/setU1P: Hcp2 => [<-|Hcp2] //.
  by move: (cpmap_simple Hcp2); rewrite simple_cat; case/and3P.
pose simq q q' (u : g0) := flatq q = flatq q' /\ walkq u q = walkq u q'.
pose selq q q' q'' : question := if q is Qask0 then q' else q''.
case: s Hscp2 (config_prog_cubic Hscp2) {Hcp2} => // [n||] Hscp2 Hcp2;
  rewrite /cpmap -/cpmap -/g -/r; move=> h Hh EhE EhN EhF Hrec [].
- rewrite cpring_ecpR -/r -/r0 /= !maps_rot; simpl in h; set hr := maps h r.
  rewrite Dqs -Dqs => Hr Hr0 Uq Eq; apply: Hrec.
  pose r1 := take n r; pose r2 := drop n r.
  rewrite /rotr (rqs_fit_size Hr) size_rot -size_drop -/r2 /rot.
  set qs1 := drop _ qs; set qs2 := take _ qs.
  have [Hqs1 Hqs2]: rqs_fit (fun x => h x) qs1 r1 /\ rqs_fit (fun x => h x) qs2 r2.
    apply: andP; move: Hr; rewrite /rot -/r1 -/r2 /qs1 /qs2 andbC.
    elim: (r2) (qs) {qs' Dqs} => [|x r2' Hrec] [|rq qs']; rewrite // ?cats0 //=.
    by move/and3P=> [Ha Hq Hqs]; rewrite Ha Hq /=; auto.
  pose pq2 := rqs_walk qs2 (maps h r2); pose m2 := size pq2.
  pose pq1 := rqs_walk qs1 (maps h r1); pose qs12 := cat qs1 qs2.
  have Dpq': rqs_walk qs12 hr = rot m2 (rqs_walk qs (rot n hr)).
    transitivity (cat pq1 pq2).
      rewrite /hr -(cat_take_drop n r) -/r1 -/r2 {}/qs12 {}/pq1.
      elim: (r1) qs1 Hqs1 => [|x r1' Hrec] [|rq qs1] //=.
      by move/and3P=> [_ _ Hqs]; rewrite Hrec ?catA.
    rewrite -rot_size_cat {}/m2; congr rot.
    move: Hqs2; rewrite /hr -maps_rot /rot /pq1 /pq2 /qs1 /qs2 -/r1 -/r2.
    elim: (r2) (qs) {qs' Dqs} => [|x r' Hrec] [|rq qs'] //=.
    by case/and3P=> *; rewrite -Hrec ?catA.
  have Ehr: maps (fun x => h x) r = hr by apply: eq_maps.
  split; auto; rewrite -/r -/r0 ?Ehr -/qs12.
  + rewrite -(cat_take_drop n r) -/r1 -/r2 /qs12.
    elim: (r1) (qs1) Hqs1 => [|x r1' Hrec] [|rq qs1'] //=.
    by move/and3P=> [Ha Hq Hqs]; rewrite Ha Hq /=; auto.
  + move=> u Hu; apply: Hr0; apply: etrans Hu; congr andb.
    by rewrite /setU fband_rot.
  + by rewrite Dpq' {1}/rot -catA simple_catCA catA cat_take_drop.
  by move=> u; rewrite fband_cat Dpq' fband_rot -fband_cat Eq /setU fband_rot.
- simpl in Hcp2; have Hgp := cpmap_proper Hcp2; rewrite -/g in Hgp.
  have HgE := cpmap_plain Hcp2; have Hg'E := plain_ecpY g HgE.
  rewrite -/r0; set rY := maps h _; set pY := cat _ r0.
  set u0 : ecpY g := ecpY g; set nu0 := node u0.
  have Hnu0: cface nu0 (icpY g (node g)) by apply: cface_node_ecpY.
  pose h' x := h (icpY g x); pose rY' := maps h' r.
  have ErY: fband rY =1 fband (Adds (h u0) rY').
    move=> u; rewrite /rY' /r head_cpring /rY cpring_ecpY -/u0 -/nu0 /= orbCA.
    rewrite -maps_comp; do 2 congr orb.
    by rewrite /h' !(Sface _ u); apply: same_cface; rewrite EhF.
  rewrite -/r; pose r' := drop 2 r; pose au0 := seq2 (node g) g.
  have Eau0: arity u0 = 2 by apply: (@order_cycle _ _ (traject face u0 2)).
  have Eag: forall x, arity (icpY g x) = fband au0 x + arity x.
    pose bu0 := maps edge (orbit face u0).
    have Ebu0: fband bu0 =1 fband (maps (icpY g) au0).
      move=> u; rewrite /au0 -adj_ecpY // /bu0 /fband has_maps.
      by apply: eq_has => v; rewrite /comp Sface.
    move=> x; rewrite /order -(cardIC bu0); congr addn.
      rewrite setI_cface_simple.
        congr nat_of_bool; rewrite Ebu0 /fband has_maps; apply: eq_has.
        exact: cface_icpY.
      rewrite (simple_perm Ebu0); last by rewrite /bu0 !size_maps size_orbit.
      rewrite (simple_maps (cface_icpY g)).
      rewrite /r (head_proper_cpring Hgp) -(cat1s g) -cat_adds seq2I in Ur.
      by rewrite simple_cat in Ur; case/and3P: Ur.
    rewrite -(card_image (@icpY_inj _ g)); apply: eq_card => u.
    apply/andP/set0Pn => [[Hux Hu]|[y]].
      have Hu0u: negb (cface u0 u).
        by rewrite Sface -(same_cface Hux) Sface /u0 cface_ecpY.
      rewrite /u0 cface_ecpY -/u0 in Hu0u.
      rewrite /bu0 /orbit -/(arity u0) Eau0 in Hu.
      case: u Hu Hu0u Hux => //; case=> // [y] _ _ Hxy; exists y.
      by rewrite /setI /preimage set11 -(cface_icpY g).
    case/andP; rewrite /preimage; move/eqP=> Du; rewrite Du cface_icpY.
    by split; first done; rewrite /bu0 /orbit -/(arity u0) Eau0.
  rewrite Dqs => Hqs Hr0 UpY EpY /=.
  move DcqY: (rqs_Y _ _ _) => cqY; move DqsY: (cfquiz_Y _ _ _) => qsY.
  case: rq1 rq2 rq3 DcqY DqsY Hqs Dqs => [k1 a1 q1] [k2 a2 q2] [k3 a3 q3].
  move=> DcqY DqsY Hqs Dqs HqY; apply: Hrec (HqY).
  rewrite /u0 cpring_ecpY /behead (head_proper_cpring Hgp) -/u0 -/nu0 in Hqs.
  rewrite maps_adds !rqs_fit_adds Eau0 (arity_cface Hnu0) in Hqs.
  rewrite -EhF in Hnu0; rewrite (arity_cface Hnu0) !Eag /= !connect0 in Hqs.
  rewrite addnS orbT /= !addnA !addn1 -/r -/r' in Hqs.
  case/and5P: Hqs => [Ea1 Hq1 Ea2 Hq2]; move/and3P=> [Ea3 Hq3 Hqs].
  have Hqs': rqs_fit (fun x => h (icpY g x)) qs' r'.
    move Dea: (fun x => arity (icpY g x) =d arity x) => ea.
    have Hr': all ea r'.
      apply/allP => [x Hx]; rewrite -Dea Eag //; apply/eqP.
      rewrite /r (head_proper_cpring Hgp) -/r' -(cat1s g) -cat_adds seq2I in Ur.
      rewrite simple_cat -/r -/r' -/au0 in Ur; case/and3P: Ur => [_ Ur _].
      by rewrite (negbE (hasPn Ur _ Hx)).
    elim: r' (qs') Hr' Hqs {Dqs Hr0} => [|x r' Hrec] [|rq qs''] //=.
    move/andP=> [Ear' Hr']; move/and3P=> [Ea Hq Hqs]; rewrite -Dea /= in Ear'.
    by rewrite -(eqP Ear') Ea Hq Hrec.
  pose v1 := icpY g (node g); have Uv1: negb (cpring u0 v1).
    rewrite /u0 /v1 cpring_ecpY /= /setU1 /= (mem_maps (@icpY_inj _ g)).
    by move: (simple_uniq Ur); rewrite {1}[r](head_cpring g); case/andP.
  have Eenv1: edge (node (h v1)) = h nu0 by rewrite (EhN _ Uv1) EhE /= set11.
  have Eennv1: edge (node (node (h v1))) = h u0.
    by rewrite !EhN // ?EhE ?cpring_ecpY /= /setU1 ?set11 //=; apply/mapsP; case.
  have EpY': fband pY =1 setU (setC (codom h')) (fband rY').
    have HrY'F: fclosed face (setU (setC (codom h')) (fband rY')).
      apply: (intro_closed (Sface _)) => [u v]; move/eqP=> <- {v} Hu.
      apply/norP; rewrite /setC negb_elim; move=> [Hfu HfuF]; move: Hu;
        rewrite /setU (fclosed1 (fbandF rY')) (negbE HfuF) orbF; case/set0Pn.
      move: (iinv Hfu) (f_iinv Hfu) => x Dx; rewrite /h' in Dx.
      exists (edge (node x)); apply/eqP; rewrite /h'-icpY_edge -icpY_node.
        rewrite -EhE -EhN; first by rewrite Dx Eface.
        rewrite cpring_ecpY /= /setU1 /=; apply/idP => HxF.
        case/hasP: HfuF; exists (face u); last exact: connect0.
        rewrite /rY' -Dx; apply mem_behead.
        by rewrite /h' (maps_comp h (icpY g)) !behead_maps; apply maps_f.
      apply/idP => [HxF]; case/hasP: HfuF; exists (face u); last exact: connect0.
      rewrite /rY' -Dx; apply: maps_f.
      rewrite /r (head_proper_cpring Hgp) -(cat1s g) -cat_adds seq2I.
      by rewrite mem_cat /setU HxF.
    move=> u; rewrite EpY {1}/setU {1}/setC ErY; case Hu: (codom h u).
      case: (fband_icpY (iinv Hu)) => [[x Hx]|Hu'].
        rewrite -EhF f_iinv in Hx; rewrite (closed_connect HrY'F Hx).
        rewrite (fun p => closed_connect (fbandF p) Hx) /setU /setC /= EhF Sface.
        by rewrite /u0 cface_ecpY -/(h' x) codom_f.
      simpl; congr orb; rewrite -EhF f_iinv in Hu'.
      rewrite Sface /u0 Hu'; apply: esym; apply/idP => Hx.
      by rewrite -(f_iinv Hx) /h' EhF cface_ecpY in Hu'.
    apply: esym; apply/orP; left; apply/idP => [Hu'].
    by rewrite -(f_iinv Hu') /h' codom_f in Hu.
  have Hr0': sub_set (setD r0 (setU (codom h') (fband rY'))) good_ring_arity.
    move=> u; case/andP; move/norP=> [Hh'u Hr'u] Hr0u.
    case Hu: (cface (h u0) u).
      rewrite /good_ring_arity -(arity_cface Hu); apply: not_bad_ring_arity.
      rewrite (eqP Ea2) /=; apply/idP => [Ha2].
      rewrite /pY simple_cat in UpY; case/and3P: UpY; clear; case/hasP.
      exists u; first done; apply/hasP; exists (h u0); last by rewrite Sface.
      rewrite Dqs /rY cpring_ecpY -/u0 -/nu0 /= mem_cat; apply/orP; right.
      do 2 (rewrite mem_cat; apply/orP; left); move: HqY; rewrite -DqsY.
      by case k2; [ rewrite /= setU11 | rewrite /= Ha2 qs0_notR ].
    apply: Hr0; rewrite /setD Hr0u /setU ErY fband_adds Sface Hu (negbE Hr'u).
    have HuY: fband pY u by rewrite EpY' /setU /setC Hh'u.
    rewrite EpY /setU /setC ErY fband_adds Sface Hu (negbE Hr'u) orbF in HuY.
    by rewrite orbF HuY.
  move: HqY; rewrite -/h' -DqsY; case Dk2: k2.
    rewrite /= small_qarityP; set qa2 := small_qarity a2.
    case: ((qa2 : nat) =P S (S a2)) => [Dqa2|_]; last by rewrite qs0_notR.
    clear; rewrite -{}Dqa2 in Ea2; rewrite -/v1 in Ea1.
    set q1' := QaskLR qa2 q2 q1.
    pose q1'' := selq q1 (selq q2 (Qask1 qa2) (QaskL qa2 q2))
                         (selq q2 (QaskR qa2 q1) q1').
    change (rqs_ok h' (cqY q1'')).
    have [Eq1 Eq1v1]: simq q1'' q1' (node (h v1)).
      by rewrite /q1'' /q1' /simq; case q1; case: (q2) => //= *; rewrite !cats0.
    rewrite /= /qstepR /qstepL Eennv1 Eenv1 in Eq1v1.
    have Eq1''F: fband (cat (rqs_walk (cqY q1'') rY') r0) =1 fband pY.
      rewrite /rY' /pY /rY cpring_ecpY /r /behead (head_proper_cpring Hgp).
      rewrite -/r -/r' !maps_adds -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
      rewrite !rqs_walk_adds {1 2}/h' -/v1 -maps_comp !catA.
      move=> u; rewrite !fband_cat; do 4 congr orb.
      rewrite (fband_seqn Hnu0) -!orbA; congr orb.
      rewrite /= Eq1v1 /= fband_cat orbA orbC orbF; do 2 congr orb.
      by rewrite (cface1r (h u0)) -Eennv1 Enode.
    split; auto; rewrite -/r -/rY' -/r0; last by move=> u; rewrite Eq1''F EpY'.
      rewrite /r (head_proper_cpring Hgp) -/r -DcqY /=.
      apply/and5P; split; auto.
      rewrite /h' -/v1 /fitq Eq1 Eq1v1 /= eqseq_adds fitq_cat.
      by rewrite -arity_face -Eennv1 Enode in Ea2; rewrite eqd_sym Ea2 Hq2.
    rewrite (simple_perm Eq1''F) // /rY' /pY /rY cpring_ecpY.
    rewrite /r /behead (head_proper_cpring Hgp) -/r -/r' !maps_adds.
    rewrite -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_adds {1 2}/h' -/v1.
    rewrite -maps_comp !size_cat /= Eq1v1 /= !size_cat !addnA; do 4 congr addn.
    by rewrite !size_seqn -!addnA; congr addn; symmetry; rewrite addnC.
  rewrite /=; case: (bad_ring_arity a2); first by rewrite qs0_notR.
  case: (q1) Dqs Hq1 Hq2; rewrite ?qs0_notR //.
    case: (q2); rewrite ?qs0_notR //.
      move=> Dqs _ _ _.
      have EqsF: fband (cat (rqs_walk (cqY Qask0) rY') r0) =1 fband pY.
        rewrite /rY' /pY /rY cpring_ecpY /r /behead (head_proper_cpring Hgp).
        rewrite -/r -/r' !maps_adds -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
        rewrite !rqs_walk_adds {1 2}/h' -/v1 -maps_comp !catA.
        move=> u; rewrite !fband_cat !orbF; do 4 congr orb.
        by rewrite (fband_seqn Hnu0).
      split; auto; rewrite -/r -/rY' -/r0; last by move=> u; rewrite EqsF EpY'.
        by rewrite /r (head_proper_cpring Hgp) -/r -DcqY /=; apply/and4P; split.
      rewrite (simple_perm EqsF) // /rY' /pY /rY cpring_ecpY.
      rewrite /r /behead (head_proper_cpring Hgp) -/r -/r' !maps_adds.
      rewrite -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_adds {1 2}/h' -/v1.
      rewrite -maps_comp !size_cat /= !addnA; do 4 congr addn.
      by rewrite !size_seqn !addn0.
    move=> qa2l q2l Dqs _ Hq2 _.
    have EqsF: fband (cat (rqs_walk (cqY (QaskLL qa2l q2l)) rY') r0) =1 fband pY.
      rewrite /rY' /pY /rY cpring_ecpY /r /behead (head_proper_cpring Hgp).
      rewrite -/r -/r' !maps_adds -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
      rewrite !rqs_walk_adds {1 2}/h' -/v1 -maps_comp !catA.
      move=> u; rewrite !fband_cat !orbF; do 4 congr orb.
      rewrite (fband_seqn Hnu0); congr orb; simpl.
      by rewrite /qstepL Eennv1 cface1r Enode.
    split; auto; rewrite -/r -/rY' -/r0; last by move=> u; rewrite EqsF EpY'.
      rewrite /r (head_proper_cpring Hgp) -/r -DcqY /=; apply/and5P; split; auto.
      move: Hq2; rewrite /fitq /= !eqseq_adds /h' -/v1 /qstepL Eennv1.
      by rewrite -{1}[node (h u0)]Enode arity_face.
    rewrite (simple_perm EqsF) // /rY' /pY /rY cpring_ecpY.
    rewrite /r /behead (head_proper_cpring Hgp) -/r -/r' !maps_adds.
    rewrite -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_adds {1 2}/h' -/v1.
    rewrite -maps_comp !size_cat /= !addnA; do 4 congr addn.
    by rewrite !size_seqn !addn0 /qstepL Eennv1.
  case q2; try by rewrite qs0_notR.
  move=> qa1r q1r Dqs Hq1 _ _.
  have EqsF: fband (cat (rqs_walk (cqY (QaskRR qa1r q1r)) rY') r0) =1 fband pY.
    rewrite /rY' /pY /rY cpring_ecpY /r /behead (head_proper_cpring Hgp).
    rewrite -/r -/r' !maps_adds -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
    rewrite !rqs_walk_adds {1 2}/h' -/v1 -maps_comp !catA.
    move=> u; rewrite !fband_cat !orbF; do 4 congr orb.
    rewrite (fband_seqn Hnu0); congr orb; simpl.
    by rewrite /qstepR Eenv1.
  split; auto; rewrite -/r -/rY' -/r0; last by move=> u; rewrite EqsF EpY'.
    rewrite /r (head_proper_cpring Hgp) -/r -DcqY /=; apply/and5P; split; auto.
    by move: Hq1; rewrite /fitq /= !eqseq_adds /h' -/v1 /qstepR Eenv1.
  rewrite (simple_perm EqsF) // /rY' /pY /rY cpring_ecpY.
  rewrite /r /behead (head_proper_cpring Hgp) -/r -/r' !maps_adds.
  rewrite -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_adds {1 2}/h' -/v1.
  rewrite -maps_comp !size_cat /= !addnA; do 4 congr addn.
  by rewrite !size_seqn !addn0 /qstepR Eenv1.
simpl in Hcp2; have Hgp := cpmap_proper Hcp2; rewrite -/g in Hgp.
simpl in Hscp2; have Hgl := cfmap_long Hscp2; rewrite -/g in Hgl.
have HgE := cpmap_plain Hcp2; have Hg'E := plain_ecpH g HgE.
rewrite -/r0; set rH := maps h (cpring (ecpH g)); set pH := cat _ r0.
set u0 : ecpH g := ecpH g; set nu0 := node u0.
pose v1 := icpH g (node g); pose v2 := icpH g g.
pose v3 := icpH g (face (edge g)).
have Hnu0: cface nu0 v1 by apply: cface_node_ecpH.
pose h' x := h (icpH g x); pose rH' := maps h' r.
pose r' := drop 3 r; pose au0 := seq3 (node g) g (face (edge g)).
have Dr: r = cat au0 r' by rewrite /r head_long_cpring.
have DrH: rH = Adds (h nu0) (Adds (h u0) (Adds (h v3) (maps h' r'))).
  by rewrite /rH cpring_ecpH // -/r -/u0 -/nu0 Dr /= -maps_comp.
have DrH': rH' = Adds (h v1) (Adds (h v2) (Adds (h v3) (maps h' r'))).
  by rewrite /rH' Dr.
have ErH: fband (Adds (h v2) rH) =1 fband (Adds (h u0) rH').
  move=> u; rewrite DrH DrH' !fband_adds; BoolCongr.
  rewrite orbCA; BoolCongr; congr orb.
  by rewrite !(Sface _ u); apply: same_cface; rewrite EhF.
have Eau0: arity u0 = 3.
  have Df3u0: face (face (face u0)) = u0 by rewrite /= Enode (negbE Hgp).
  apply: (@order_cycle _ _ (traject face u0 3)) => //.
  by rewrite (cycle_path u0) /traject /eqdf /last /path Df3u0.
have Eag: forall x, arity (icpH g x) = fband au0 x + arity x.
  pose bu0 := maps edge (orbit face u0).
  have Ebu0: fband bu0 =1 fband (maps (icpH g) au0).
    move=> u; rewrite /au0 -adj_ecpH // /bu0 /fband has_maps.
    by apply: eq_has => v; rewrite /comp Sface.
  move=> x; rewrite /order -(cardIC bu0); congr addn.
    rewrite setI_cface_simple.
      congr nat_of_bool; rewrite Ebu0 /fband has_maps; apply: eq_has.
      exact: cface_icpH.
    rewrite (simple_perm Ebu0); last by rewrite /bu0 !size_maps size_orbit.
    rewrite (simple_maps (cface_icpH g)).
    by rewrite Dr simple_cat in Ur; case/and3P: Ur.
  rewrite -(card_image (@icpH_inj g g)); apply: eq_card => u.
  apply/andP/set0Pn => [[Hux Hu]|[y]].
    have Hu0u: negb (cface u0 u).
      by rewrite Sface -(same_cface Hux) Sface /u0 cface_ecpH.
    rewrite /u0 cface_ecpH // -/u0 in Hu0u; rewrite /bu0 /orbit Eau0 in Hu.
    case: u Hu Hu0u Hux => //; case=> //; case=> // [y] _ _ Hxy; exists y.
    by rewrite /setI /preimage set11 -(cface_icpH g).
  case/andP; rewrite /preimage; move/eqP=> Du; rewrite Du cface_icpH.
  by split; first done; rewrite /bu0 /orbit Eau0.
rewrite Dqs; move=> Hqs Hr0 UpH EpH /=.
move DcqH: (rqs_H _ _ _) => cqH; move DqsH: (cfquiz_H _ _ _) => qsH.
case: rq1 rq2 rq3 DcqH DqsH Hqs Dqs => [k1 a1 q1] [k2 a2 q2] [k3 a3 q3].
move=> DcqH DqsH Hqs Dqs HqH; apply: Hrec (HqH).
rewrite /u0 cpring_ecpH -/u0 -/nu0 // -/r Dr /au0 /seq3 /seq2 !cat_adds in Hqs.
rewrite cat1s /drop maps_adds -/v3 !rqs_fit_adds Eau0 (arity_cface Hnu0) in Hqs.
rewrite -EhF in Hnu0; rewrite (arity_cface Hnu0) in Hqs.
rewrite {2}/v1 {2}/v3 !Eag /= !connect0 in Hqs.
rewrite 2!addnS !orbT /= !addnA !addn1 in Hqs.
case/and5P: Hqs => Ea1 Hq1 Ea2 Hq2; move/and3P=> [Ea3 Hq3 Hqs].
have Hqs': rqs_fit (fun x => h (icpH g x)) qs' r'.
  move Dea: (fun x => arity (icpH g x) =d arity x) => ea.
  have Hr': all ea r'.
    apply/allP => [x Hx]; rewrite -Dea Eag //; apply/eqP.
    rewrite Dr simple_cat in Ur; case/and3P: Ur => [_ Ur _].
    by rewrite (negbE (hasPn Ur _ Hx)).
  elim: (r') (qs') Hr' Hqs {Dqs Hr0} => [|x r'' Hrec] [|rq qs''] //=.
  move/andP=> [Ear'' Hr'']; move/and3P=> [Ea Hq Hqs]; rewrite -Dea /= in Ear''.
  by rewrite -(eqP Ear'') Ea Hq Hrec.
have UrH: forall x, cpring u0 (icpH g x) = drop 2 r x.
  move=> x; rewrite /u0 cpring_ecpH //= /setU1 /= (mem_maps (@icpH_inj _ g)).
  by rewrite /long_cpring /= Enode (negbE Hgp).
have Uv1: negb (cpring u0 v1).
  move: (simple_uniq Ur).
  by rewrite {1}[r](head_proper_cpring Hgp) /v1 UrH; case/andP; case/norP.
have Uv2: negb (cpring u0 v2).
  move: (simple_uniq Ur).
  by rewrite {1}[r](head_proper_cpring Hgp) /v2 UrH; case/and3P.
have Eenv1: edge (node (h v1)) = h nu0.
  rewrite (EhN _ Uv1) EhE; congr h; apply Iface; rewrite Enode.
  have ->: nu0 = icpN _ (icpN _ (edge (ecpU g)));
    by rewrite /nu0 /= /long_cpring /= Enode (negbE Hgp).
have Hnv1: cface (node (h v1)) (h u0).
  by rewrite EhN // EhF Sface /u0 cface_ecpH //= !set11 /= /setU1 !orbT.
have Eennv2: edge (node (node (h v2))) = h u0.
  have Env2: node v2 = face u0 by rewrite /v2 /= (negbE Hgp) /= 2!set11.
  rewrite EhN // Env2 EhN; [by rewrite EhE Eface | rewrite cpring_ecpH //].
  repeat (apply/norP; split => //); last by apply/mapsP; case.
  by rewrite /= /long_cpring /= Enode (negbE Hgp).
have EpH': fband (Adds (h v2) pH) =1 setU (setC (codom h')) (fband rH').
  have HrH'F: fclosed face (setU (setC (codom h')) (fband rH')).
    apply: (intro_closed (Sface _)) => [u v]; move/eqP=> <- {v} Hu.
    apply/norP; rewrite /setC negb_elim; move=> [Hfu HfuF]; move: Hu;
      rewrite /setU (fclosed1 (fbandF rH')) (negbE HfuF) orbF; case/set0Pn.
    move: (iinv Hfu) (f_iinv Hfu) => x Dx; rewrite /h' in Dx.
    exists (edge (node x)); apply/eqP; rewrite /h'.
    rewrite -icpH_edge -icpH_node.
      rewrite -EhE -EhN; first by rewrite Dx Eface.
      rewrite -/u0 UrH; apply/idP => HxF.
      case/hasP: HfuF; exists (face u); last exact: connect0.
      by rewrite /rH' -Dx; apply: (@mem_drop 2); rewrite -maps_drop; apply: maps_f.
    apply/idP => [HxF]; case/hasP: HfuF; exists (face u); last exact: connect0.
    by rewrite /rH' -Dx; apply: maps_f; rewrite Dr mem_cat /au0 /setU HxF.
  move=> u; rewrite fband_adds EpH {1}/setU {1}/setC orbCA -fband_adds ErH.
  case Hu: (codom h u).
    case: (fband_icpH (iinv Hu)) => [[x Hx]|Hu'].
      rewrite -EhF f_iinv in Hx; rewrite (closed_connect HrH'F Hx).
      rewrite (fun p => closed_connect (fbandF p) Hx) /setU /setC /= EhF Sface.
      by rewrite /u0 cface_ecpH // -/(h' x) codom_f.
    simpl; congr orb; rewrite -EhF f_iinv in Hu'.
    rewrite Sface /u0 Hu'; apply: esym; apply/idP => Hx.
    by rewrite -(f_iinv Hx) /h' EhF cface_ecpH in Hu'.
  symmetry; apply/orP; left; apply/idP => Hu'.
  by rewrite -(f_iinv Hu') /h' codom_f in Hu.
have Hr0': sub_set (setD r0 (setU (codom h') (fband rH'))) good_ring_arity.
  move=> u; case/andP; move/norP=> [Hh'u Hr'u] Hr0u.
  case Hu: (cface (h u0) u).
    rewrite /good_ring_arity -(arity_cface Hu); apply: not_bad_ring_arity.
    rewrite (eqP Ea2) {3}[S]lock /= -lock; apply/idP => Ha2; simpl in Ha2.
    rewrite /pH simple_cat in UpH; case/and3P: UpH => _; case/hasP.
    exists u; first done; apply/hasP; exists (h u0); last by rewrite Sface.
    rewrite Dqs DrH !rqs_walk_adds mem_cat; apply/orP; right.
    do 2 (rewrite mem_cat; apply/orP; left); move: HqH; rewrite -DqsH.
    by case k2; rewrite /= ?setU11 // Ha2 /= qs0_notR.
  apply: Hr0; rewrite /setD Hr0u /setU.
  have HuH: fband (Adds (h v2) pH) u by rewrite EpH' /setU /setC Hh'u.
  have Hur: negb (fband (Adds (h v2) rH) u).
    by rewrite ErH fband_adds Sface Hu.
  rewrite fband_adds EpH /setU /setC orbCA -fband_adds (negbE Hur) orbF in HuH.
  rewrite fband_adds in Hur; case/norP: Hur => _ Hur.
  by rewrite (negbE Hur) orbF HuH.
have HrHv2: negb (fband rH (h v2)).
  rewrite DrH !fband_adds Sface (same_cface Hnu0) Sface !EhF /h' /fband.
  rewrite (maps_comp h (icpH g)) has_maps (@eq_has _ (comp _ h) _ (EhF v2)).
  rewrite orbCA Sface /u0 cface_ecpH // orFb.
  rewrite /v1 /v2 /v3 !cface_icpH has_maps.
  rewrite (@eq_has _ (comp _ (icpH g)) _ (cface_icpH g g)).
  move: Ur; rewrite Dr simple_recI /= Sface; case/and3P.
  by move/norP=> [Ung _] Ug _; apply/norP; split.
have HpHv2: negb (fband pH (h v2)) by rewrite EpH /setU /setC codom_f.
have Uv2pH: simple (Adds (h v2) pH) by rewrite simple_adds HpHv2.
have Eav2: arity (h v2) = S (arity g).
  transitivity (arity v2); last by rewrite /v2 Eag /= connect0 orbT.
  rewrite /order -(card_image Hh); apply: eq_card => [u].
  apply/idP/idP => [Hu|];
   last by case/set0Pn=> [x]; case/andP; move/eqP=> Du; rewrite Du EhF.
  rewrite (closed_connect (fbandF pH) Hu) EpH /setU /setC in HpHv2.
  rewrite -(closed_connect (fbandF rH) Hu) (negbE HrHv2) orbF negb_elim in HpHv2.
  by rewrite -(f_iinv HpHv2) (image_f Hh) -EhF f_iinv.
move: HqH; rewrite -/h' -DqsH; case Dk2: k2.
  rewrite /cfquiz_H small_qarityP; set qa2 := small_qarity (S a2).
  case: ((qa2 : nat) =P S (S (S a2))) => [Dqa2|_]; last by rewrite qs0_notR.
  rewrite -{}Dqa2 in Ea2; rewrite if_negb.
  set q1' := QaskR qa2 q1; set q2' := QaskL qa2 q2.
  have Hq1': forall q, q2 = Qask0 -> simq q q1' (node (h v1)) ->
      rqs_ok h' (cqH q q2).
    move=> q Dq2 [Eq Eqv1]; rewrite /= /qstepR Eenv1 in Eqv1.
    have EqsF: fband (cat (rqs_walk (cqH q q2) rH') r0) =1 fband (Adds (h v2) pH).
      move=> u; rewrite /pH Dqs Dk2 DrH' DrH -DcqH Dq2 /= Eqv1.
      rewrite !fband_cat !fband_adds !fband_cat !orbA; do 4 congr orb.
      rewrite (fband_seqn Hnu0) -!orbA !(Sface _ u) (same_cface Hnv1).
      by repeat BoolCongr.
    split; auto; rewrite -/r -/r0 -/rH'; last by move=> u; rewrite EqsF EpH'.
      rewrite Dr -DcqH Dq2 /= {-6}/h' -/v1 -/v2 -/v3 Hq3 Eav2 set11.
      apply/and5P; split; auto.
      by rewrite /fitq Eq Eqv1 /= eqseq_adds (arity_cface Hnv1) eqd_sym Ea2.
    rewrite (simple_perm EqsF) // DrH' /pH DrH Dqs Dq2 Dk2 -DcqH /=.
    rewrite !size_cat /= !size_cat !size_seqn Eqv1 /=.
    by NatNorm; repeat NatCongr.
  have Hq2': forall q, q1 = Qask0 -> simq q q2' (node (h v2)) ->
     rqs_ok h' (cqH q1 q).
    move=> q Dq1 [Eq Eqv2]; rewrite /= /qstepL Eennv2 in Eqv2.
    have EqsF: fband (cat (rqs_walk (cqH q1 q) rH') r0) =1 fband (Adds (h v2) pH).
      move=> u; rewrite /pH Dqs Dk2 DrH' DrH -DcqH Dq1 /= Eqv2 !cats0.
      rewrite !fband_cat !fband_adds !fband_cat fband_adds !orbA; do 5 congr orb.
      rewrite (fband_seqn Hnu0) -!orbA orbCA; do 2 congr orb.
      by rewrite (cface1r (h u0)) -Eennv2 Enode.
    split; auto; rewrite -/r -/r0 -/rH'; last by move=> u; rewrite EqsF EpH'.
      rewrite Dr -DcqH Dq1 /= {-6}/h' -/v1 -/v2 -/v3 Hq3 Eav2 set11.
      apply/and5P; split; auto.
      rewrite /fitq Eq Eqv2 /= eqseq_adds -[node (h v2)]Enode Eennv2.
      by rewrite arity_face eqd_sym Ea2.
    rewrite (simple_perm EqsF) // DrH' /pH DrH Dqs Dq1 Dk2 -DcqH /=.
    rewrite !size_cat /= !size_cat !size_seqn Eqv2 /=.
    by NatNorm; repeat NatCongr.
  have Hsimq: forall q (u : g0), simq q q u by split.
  case Dq1: q1 Hq1' Hq2'; case Dq2: q2; auto; try by rewrite qs0_notR.
  by rewrite {}/q1' {}/q2' {}Dq1 {}Dq2; case: (k1) => [H _|_ H] _; apply: H.
rewrite /cfquiz_H; case: (bad_ring_arity (S a2)); first by rewrite qs0_notR.
case Dq1: q1; rewrite ?qs0_notR //; case Dq2: q2; rewrite ?qs0_notR //.
have EqsF:
     fband (cat (rqs_walk (cqH Qask0 Qask0) rH') r0) =1 fband (Adds (h v2) pH).
  move=> u; rewrite /pH Dqs Dk2 DrH' DrH -DcqH Dq1 Dq2 /= !cats0.
  rewrite !fband_cat !fband_adds !fband_cat !orbA; do 4 congr orb.
  by rewrite (fband_seqn Hnu0) orbC.
split; auto; rewrite -/r -/r0 -/rH'; last by move=> u; rewrite EqsF EpH'.
  rewrite Dr -DcqH /= {-5}/h' -/v1 -/v2 -/v3 Hq3 Eav2 set11 /=.
  by apply/and3P; split.
rewrite (simple_perm EqsF) // DrH' /pH DrH Dqs Dq1 Dq2 Dk2 -DcqH /=.
rewrite !size_cat /= !size_cat !size_seqn /=.
by NatNorm; repeat NatCongr.
Qed.

Lemma embeddable_cfquiz : embeddable (cfring cf).
Proof.
split; try exact Hrad2.
  have Hcpq := config_prog_cubic Hcp; repeat split.
  - exact: cpmap_plain.
  - exact: cpmap_cubic.
  - exact: ucycle_rev_cpring.
  - exact: cpmap_connected.
  - by move: (cpmap_simple Hcp); rewrite simple_cat -simple_rev; case/and3P.
  - exact: cpmap_planar.
  exact: cpmap_bridgeless.
by apply/allP => x Hx; case: cfquizP => H _; apply: H; rewrite -mem_rev.
Qed.

Lemma valid_cfquiz : exists u, valid_quiz (cfring cf) u cfquiz.
Proof.
case: cfquizP => _ [u [Hcqz Hu Uqz Eqz]]; exists u; split; auto.
by move=> v; rewrite {u Hcqz Hu Uqz}Eqz /kernel /setC -fband_rev.
Qed.

End ConfigQuiz.

Unset Implicit Arguments.