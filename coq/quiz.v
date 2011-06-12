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
Require Import geometry.
Require Import coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* A quiz is a pair of binary trees that covers the inner regions of a    *)
(* configuration and store their arity. The embedding lemmas allow us to  *)
(* use questions to actually test for an isomorphic embedding of the      *)
(* configuration in a minimal uncolorable cubic map.                      *)

(* We are only interested in arities between 5 and 11 (in fact 9, 10, and 11 *)
(* only occur at the hub).                                                   *)

Inductive qarity : Set :=
  | Qa5 : qarity
  | Qa6 : qarity
  | Qa7 : qarity
  | Qa8 : qarity
  | Qa9 : qarity
  | Qa10 : qarity
  | Qa11 : qarity.

Definition nat_of_qarity (qa : qarity) : nat :=
  match qa with
  | Qa5 => 5
  | Qa6 => 6
  | Qa7 => 7
  | Qa8 => 8
  | Qa9 => 9
  | Qa10 => 10
  | Qa11 => 11
  end.

Coercion nat_of_qarity : qarity >-> nat.

Definition qarity_of_nat (n : nat) : qarity :=
  match n with
  | S (S (S (S (S O)))) => Qa5
  | S (S (S (S (S (S O))))) => Qa6
  | S (S (S (S (S (S (S O)))))) => Qa7
  | S (S (S (S (S (S (S (S O))))))) => Qa8
  | S (S (S (S (S (S (S (S (S O)))))))) => Qa9
  | S (S (S (S (S (S (S (S (S (S O))))))))) => Qa10
  | _ => Qa11
  end.

Lemma qarity_of_qarity : forall qa : qarity, qarity_of_nat qa = qa.
Proof. by case. Qed.

Lemma qarityDataP : comparable qarity.
Proof. rewrite /comparable; decide equality. Qed.

(* We specialize the question tree constructor according to the presence    *)
(* of left and right branches. We also need skewed left and right branches, *)
(* for configurations whose interior has an articulation.                   *)

Inductive question : Set :=
  | Qask0 : question
  | Qask1 : qarity -> question
  | QaskL : qarity -> question -> question
  | QaskR : qarity -> question -> question
  | QaskLR : qarity -> question -> question -> question
  | QaskLL : qarity -> question -> question
  | QaskRR : qarity -> question -> question.

Lemma questionDataP : comparable question.
Proof. rewrite /comparable; decide equality; apply qarityDataP. Qed.
Definition questionData : dataSet := Eval compute in
  compareData questionDataP.
Canonical Structure questionData.

Definition isQaskR q := if q is QaskR _ _ then true else false.

Fixpoint flatq (q : question) : natseq :=
  match q with
  | Qask0 => seq0
  | Qask1 qa => seq1 (qa : nat)
  | QaskL qa ql => Adds (qa : nat) (flatq ql)
  | QaskR qa qr => Adds (qa : nat) (flatq qr)
  | QaskLR qa ql qr => Adds (qa : nat) (cat (flatq ql) (flatq qr))
  | QaskLL qa qll => Adds (qa : nat) (flatq qll)
  | QaskRR qa qrr => Adds (qa : nat) (flatq qrr)
  end.

(* Mirror image questions. *)

Fixpoint flipq (q : question) : question :=
  match q with
  | QaskL qa ql => QaskR qa (flipq ql)
  | QaskR qa qr => QaskL qa (flipq qr)
  | QaskLR qa ql qr => QaskLR qa (flipq qr) (flipq ql)
  | QaskLL qa qll => QaskRR qa (flipq qll)
  | QaskRR qa qrr => QaskLL qa (flipq qrr)
  | _ => q
  end.

Definition qstepL (g : hypermap) (x : g) := node (edge (node x)).
Definition qstepR (g : hypermap) (x : g) := node (edge x).

Inductive quiz : Set := Quiz : forall q0 q1 : question, quiz.

Definition isQuizR qz := let: Quiz q0 q1 := qz in isQaskR q0 && isQaskR q1.

Definition flatqz qz := let: Quiz q0 q1 := qz in cat (flatq q0) (flatq q1).

Definition flipqz qz :=
  if qz is Quiz (QaskR qa0 q01) (QaskR qa1 q10) then
    Quiz (QaskR qa0 (flipq q10)) (QaskR qa1 (flipq q01))
  else qz.

Section FitQuiz.

Variable g : hypermap.

Fixpoint walkq (x : g) (q : question) {struct q} : seq g :=
  match q with
  | Qask0 => seq0
  | Qask1 qa => seq1 x
  | QaskL qa ql => Adds x (walkq (qstepL x) ql)
  | QaskR qa qr => Adds x (walkq (qstepR x) qr)
  | QaskLR qa ql qr => Adds x (cat (walkq (qstepL x) ql) (walkq (qstepR x) qr))
  | QaskLL qa qll =>
    let xl := qstepL x in Adds (edge (node xl)) (walkq (qstepL xl) qll)
  | QaskRR qa qrr => let xr := qstepR x in Adds xr (walkq (qstepR xr) qrr)
  end.

Definition fitq (x : g) q := (flatq q : seq _) =d maps arity (walkq x q).

Lemma size_walkq : forall (x : g) q, size (walkq x q) = size (flatq q).
Proof. move=> x q; elim: q x => //= *; rewrite ?size_cat; congr S; auto. Qed.

Lemma fitq_cat : forall x q s s',
 (cat (flatq q) s =d maps arity (cat (walkq x q) s'))
    = fitq x q && (s =d maps arity s').
Proof.
move=> x q s s'; rewrite /fitq; move: (introT eqP (size_walkq x q)).
elim: {q x}(walkq x q) (flatq q) => [|x s1 Hrec] [|n s2] //= Es12.
rewrite !eqseq_adds -andbA; congr andb; auto.
Qed.

Lemma size_flipq : forall q, size (flatq (flipq q)) = size (flatq q).
Proof. elim=> //= *; rewrite ?size_cat 1?addnC; congr S; auto. Qed.

Definition walkqz x qz :=
  let: Quiz q0 q1 := qz in cat (walkq x q0) (walkq (edge x) q1).

Lemma size_walkqz : forall x qz, size (walkqz x qz) = size (flatqz qz).
Proof. by move=> x [q0 q1]; rewrite /= ?size_cat ?size_walkq. Qed.

Definition fitqz x qz := flatqz qz =d maps arity (walkqz x qz).

End FitQuiz.

Lemma fitqz_flip : forall g x qz, plain_cubic g -> isQuizR qz ->
  @fitqz g x (flipqz qz) = @fitqz (mirror g) (face x) qz.
Proof.
move=> g x [q0 q1] [HgE HgN]; case: q0 => //=; case: q1 => //=.
move=> qa1 q10 qa0 q01 _; move Dh: (fun y : g => y : mirror g) => h.
rewrite (congr1 (fun f => f (face x)) Dh); move: x.
have De2: forall x : g, edge (edge x) = x by apply plain_eq.
have Dn3: forall x : g, node (node (node x)) = x by apply cubic_eq.
have Hh1: forall x : g, arity (h x) = arity x.
 by move=> x; rewrite -Dh arity_mirror.
have HhL: forall x : g, qstepL (h x) = h (qstepR x).
move=> x; rewrite -Dh /= /comp (f_finv (Inode g)) -{1}[x]De2 -{1}[edge x]Dn3.
  by rewrite Enode (finv_f (Inode g)).
have HhR: forall x : g, qstepR (h x) = h (qstepL x).
  move=> x; apply: (etrans _ (HhL _)).
  by rewrite -Dh /qstepL /qstepR /= (finv_f (Inode g)).
have HhE: forall x : g, edge (h (face x)) = h (face (edge x)).
  by move=> x; rewrite -Dh /= -{1}[x]De2 /comp Eedge.
have EaEN: forall x, arity (edge (node x)) = arity x.
  by move=> g' x; rewrite -arity_face Enode.
  move: (mirror g) h {Dh}Hh1 HhL HhR HhE => g' h Hh1 HhL HhR HhE.
have Eqs1: forall (n n' : nat) s s',
  (Adds n s =d Adds n' s') = (n =d n') && (s =d s') by done.
have Hq: forall q x, fitq x (flipq q) = fitq (h x) q.
  rewrite /fitq; elim=> //= *; rewrite ?HhL ?HhR ?EaEN Hh1 //;
    rewrite ?Eqs1 ?fitq_cat /fitq; try congr andb; auto.
  by rewrite andbC; congr andb.
move=> x; rewrite /fitqz /= !Eqs1 !fitq_cat /= !Eqs1 HhE !Hh1 !arity_face !HhR.
congr andb; rewrite !(andbC ((qa1 : nat) =d _)) !andbA; congr andb; rewrite andbC.
congr andb; apply: (etrans (Hq _ _) (congr1 (fun y => fitq (h y) _) _)).
  by rewrite /qstepL -{2}[x]De2 Eedge.
by rewrite /qstepL Eedge.
Qed.

Section QuizEmbedding.

Variables (gm gc : hypermap) (rc : seq gc).

Notation ac := (kernel rc).
Notation bc := (setC rc).
Let Hacbc := subsetP (kernel_off_ring rc).
Let HacF := kernelF rc.

Hypotheses (Hgm : plain_cubic gm) (Hgc : plain_quasicubic rc).
Let De2m := plain_eq Hgm.
Let Dn3m := cubic_eq Hgm.
Let De2c := plain_eq Hgc.
Let Dn3c := quasicubic_eq Hgc.

(* Adds the (disjoint) domain covered by the question to a previously covered *)
(* domain. The empty set is returned if the question is invalid (wrong arity, *)
(* cover overlap).                                                            *)

Variables (x0m : gm) (x0c : gc) (qz : quiz).
Let s0c : seq gc := walkqz x0c qz.
Let s0m : seq gm := walkqz x0m qz.

Definition valid_quiz :=
  and4 (isQuizR qz) (fitqz x0c qz) (simple s0c) (fband s0c =1 ac).

Hypotheses (Hqzc : valid_quiz) (Hqzm : fitqz x0m qz).

Definition embedqz x :=
  let i := find (cface x) s0c in
  let j := findex face (sub x0c s0c i) x in
  iter j face (sub x0m s0m i).

Notation h := embedqz.
Notation hc := (edge_central h).
Let HhcE := edge_central_edge h Hgc Hgm.

Remark Embedqz_Dhx0 : h x0c = x0m.
Proof.
rewrite /h /s0c /s0m; case: Hqzc => [H _ _ _]; case: qz H => [q0 q1].
by case q0; rewrite //= connect0 /= findex0.
Qed.
Notation Dhx0 := Embedqz_Dhx0.

Remark Embedqz_Dhs0 : forall i : nat, h (sub x0c s0c i) = sub x0m s0m i.
Proof.
move=> i; case Hi: (size s0c <= i).
  by rewrite !sub_default ?Dhx0 //; move: Hi; rewrite /s0c /s0m !size_walkqz.
rewrite leqNgt in Hi; move/idP: Hi => Hi.
set x := sub x0c s0c i; rewrite /h.
suffice ->: find (cface x) s0c = i by rewrite -/x findex0.
case: Hqzc => [_ _ Uq _]; move: Uq.
rewrite -(cat_take_drop i s0c) (drop_sub x0c Hi) -/x.
rewrite /simple maps_cat uniq_cat /=; move/and3P=> [_ Uq _].
rewrite find_cat /= connect0 (size_takel (ltnW Hi)) addn0.
case: (hasPx (cface x) (take i s0c)) => // [[y Hy Hxy]].
case/norP: Uq; case/mapsP; exists y; first done.
symmetry; exact: (rootP (Sface _)).
Qed.
Notation Dhs0 := Embedqz_Dhs0.

Remark Embedqz_Dhex0 : h (edge x0c) = edge x0m.
Proof.
case: Hqzc => [H _ _ _]; move: Dhs0 H; rewrite /s0c /s0m; case qz.
move=> /= q0 q1 H; move: {H}(H (size (flatq q0))).
by rewrite !sub_cat !size_walkq /= ltnn subnn andbC; case q1.
Qed.
Notation Dhex0 := Embedqz_Dhex0.

Lemma embedqz_arity : forall x, ac x -> arity (h x) = arity x.
Proof.
case: Hqzc => [_ Haqc _ Dac] x; rewrite -{}Dac /h; move=> Hx.
set i := find (cface x) s0c; set y := sub x0c s0c i.
set j := findex face y x.
have Hi: i < size s0c by rewrite /i -has_find.
have Hy: s0c y by exact: mem_sub Hi.
have Hxy: cface x y by exact: sub_find.
move: Haqc Hqzm; rewrite /fitqz -/s0c -/s0m => Eaqc Eqzm.
rewrite (arity_cface Hxy) /y -(sub_maps x0c 0) // -(eqP Eaqc) (eqP Eqzm).
rewrite (sub_maps x0m 0); first by elim j=> *; rewrite /= ?arity_face.
by move: Hi; rewrite /s0c /s0m !size_walkqz.
Qed.

Lemma embedqz_face : forall x, ac x -> h (face x) = face (h x).
Proof.
case: Hqzc => [_ _ _ Dac] x; rewrite -Dac => Hx.
set i := find (cface x) s0c; rewrite /h -(eq_find (cface1 x)) -/i.
set yc := sub x0c s0c i.
have Hxyc: cface yc x by rewrite Sface /yc /i sub_find.
rewrite -Dhs0 -/yc -{1}(iter_findex Hxyc).
move: (findex face yc x) (@findex_max _ face yc x) => j Hj.
rewrite leq_eqVlt in Hj; case/orP: {Hj}(Hj Hxyc) => [Dj|Hj].
  rewrite -[j]/(pred (S j)) (eqP Dj) -/(finv face yc) (f_finv (Iface gc)).
  rewrite findex0 /= -/(arity yc) -embedqz_arity.
    by rewrite -/(finv face (h yc)) (f_finv (Iface gm)).
  by rewrite -Dac (closed_connect (fbandF s0c) Hxyc).
by rewrite f_iter findex_iter.
Qed.

Lemma embedqz_central : sub_set s0c hc.
Proof.
have Hq: forall x q, ac x -> ac (edge x) -> hc x -> let s := walkq (node x) q in
    all ac s -> (maps h s =d walkq (node (h x)) q) -> all hc s.
  move=> x q; elim: q x => //= _.
  - move=> x HxF _ HxE _; case/andP; move/eqP=> Dhnx _.
    rewrite /edge_central Dhnx -{2}[x]Enode embedqz_face ?Eface ?set11 //.
    by rewrite (fclosed1 HacF) Enode.
  - move=> q Hrec x HxF HexF HxE; move/andP=> [HnxF HsF].
    rewrite eqseq_adds; case/andP; move/eqP=> Dhnx Hs.
    have HenxF: ac (edge (node x)) by rewrite (fclosed1 HacF) Enode.
    have HennxF: ac (edge (node (node x))) by rewrite (fclosed1 HacF) Enode.
    have HnxE: hc (node x).
      by rewrite /edge_central Dhnx -{2}[x]Enode embedqz_face ?Eface ?set11.
    have HennxE: hc (edge (node (node x))).
      rewrite /edge_central De2c -{1}[node (node x)]Enode (Dn3c (Hacbc HxF)).
      rewrite (embedqz_face HexF) (eqP HxE) -{1}[h x]Dn3m Enode.
      by rewrite -[h (edge _)]Eface -embedqz_face // De2m Enode Dhnx set11.
    rewrite HnxE /= /qstepL Hrec //.
    rewrite De2c -[node (node x)]Enode (Dn3c (Hacbc HxF)).
      by rewrite -(fclosed1 HacF).
    by rewrite -[h (edge _)]Eface -embedqz_face // Enode Dhnx.
  - move=> q Hrec x HxF HexF HxE; move/andP=> [HnxF HsF].
    rewrite eqseq_adds; case/andP; move/eqP=> Dhnx Hs.
    have HenxF: ac (edge (node x)) by rewrite (fclosed1 HacF) Enode.
    have HennxF: ac (edge (node (node x))) by rewrite (fclosed1 HacF) Enode.
    have HnxE: hc (node x).
      by rewrite /edge_central Dhnx -{2}[x]Enode embedqz_face ?Eface ?set11.
    by rewrite HnxE /= /qstepR Hrec ?De2c 1?HhcE // (eqP HnxE) Dhnx.
  - move=> ql Hrecl qr Hrecr x HxF HexF HxE /=.
    rewrite !all_cat eqseq_adds maps_cat eqseq_cat ?size_maps ?size_walkq //.
    move/and3P=> [HnxF HslF HsrF]; case/and3P; move/eqP=> Dhnx Hsl Hsr.
    have HenxF: ac (edge (node x)) by rewrite (fclosed1 HacF) Enode.
    have HennxF: ac (edge (node (node x))) by rewrite (fclosed1 HacF) Enode.
    have HnxE: hc (node x).
      by rewrite /edge_central Dhnx -{2}[x]Enode embedqz_face ?Eface ?set11.
    have HennxE: hc (edge (node (node x))).
    rewrite /edge_central De2c -{1}[node (node x)]Enode (Dn3c (Hacbc HxF)).
    rewrite (embedqz_face HexF) (eqP HxE) -{1}[h x]Dn3m Enode.
    rewrite -[h (edge _)]Eface -embedqz_face //.
      by rewrite De2m Enode Dhnx set11.
    rewrite HnxE /= /qstepL /qstepR Hrecl // ?Hrecr // ?De2c ?HhcE //.
    + by rewrite (eqP HnxE) Dhnx.
    + by rewrite -[node (node x)]Enode (Dn3c (Hacbc HxF)) -(fclosed1 HacF).
    by rewrite -[h (edge _)]Eface -embedqz_face // Enode Dhnx.
  - move=> q Hrec x HxF HexF HxE; move/andP=> [HenLnxF HsF].
    rewrite eqseq_adds; case/andP; move/eqP=> DhenLnx Hs.
    have HfexF: ac (face (edge x)) by rewrite -(fclosed1 HacF).
    have HffexF: ac (face (face (edge x))) by rewrite -(fclosed1 HacF).
    have HenLnxE: hc (edge (node (qstepL (node x)))).
      rewrite /edge_central De2c DhenLnx /qstepL De2m.
      rewrite -{1}[x]Eedge (Dn3c (Hacbc HfexF)).
      rewrite -{1}[face (edge x)]Eface De2c (Dn3c (Hacbc HffexF)).
      rewrite !embedqz_face // (eqP HxE) -{2}[h x]Eedge Dn3m.
      by rewrite -{2}[face (edge _)]Eface De2m Dn3m set11.
    rewrite HenLnxE /= {1}/qstepL Hrec ?DhenLnx //.
    rewrite De2c -{1}[x]Eedge /qstepL (Dn3c (Hacbc HfexF)).
    by rewrite -{1}[face (edge x)]Eface De2c (Dn3c (Hacbc HffexF)).
  - move=> q Hrec x HxF HexF HxE; move/andP=> [HRnxF HsF].
    rewrite eqseq_adds; case/andP; move/eqP=> DhRnx Hs.
    have HenxF: ac (edge (node x)) by rewrite (fclosed1 HacF) Enode.
    have HenenxF: ac (edge (node (edge (node x)))).
      by rewrite (fclosed1 HacF) Enode.
    have HRnxE: hc (qstepR (node x)).
      rewrite /edge_central DhRnx /qstepR -(monic2F_eqd (Eface gm)).
      rewrite -embedqz_face // Enode.
      by rewrite -(monic2F_eqd (Eface gm)) -embedqz_face // Enode set11.
    by rewrite HRnxE /= {1}/qstepR Hrec ?De2c ?HhcE // (eqP HRnxE) DhRnx.
have Hx0E: hc x0c by rewrite /edge_central Dhx0 Dhex0 set11.
have Hex0E: hc (edge x0c) by rewrite HhcE.
move: Hqzc => [Hqz _ _ Dac].
have Hs0F: subset s0c ac by rewrite -(eq_subset_r Dac); apply ring_fband.
have Ehs0: maps h s0c =d s0m.
  apply/eqP; pose n := size (flatqz qz).
  have Dnc: size s0c = n by rewrite /s0c size_walkqz.
  have Dnm: size s0m = n by rewrite /s0m size_walkqz.
  rewrite -(take_size s0c) -(take_size s0m) Dnc Dnm.
  elim: {-2}n (leqnn n) => [|i Hrec] Hi; first by rewrite !take0.
  rewrite (take_sub x0c) ?Dnc // maps_add_last Dhs0 (Hrec (ltnW Hi)).
  by rewrite -take_sub // Dnm.
apply: subsetP; move: Hs0F Ehs0 {Dac}; rewrite /s0c /s0m !subset_all.
case: qz Hqz => [q0 q1] /=.
rewrite !all_cat maps_cat eqseq_cat; last by rewrite size_maps !size_walkq.
case: q0 => //= [_ q01]; case: q1 => //= [_ q10] _; rewrite Hx0E Hex0E /=.
case/and3P; case/andP; move=> Hx0cF Hs01F Hex0cF Hs10F; rewrite !eqseq_adds.
case/and3P; case/andP; move/eqP=> <- Hs01; move/eqP=> <- Hs10.
rewrite /qstepR !Hq // ?De2c // ?(eqP Hx0E) //.
by rewrite /qstepR (eqP Hx0E) De2c De2m in Hs10 |- *.
Qed.

Lemma embedqz_rlinked : rlink_connected (setI ac hc).
Proof.
have Hq1: forall x a, fband a x ->
    rlink_connected (setI (fband a) hc) -> hc (node x) ->
    rlink_connected (setI (fband (add_last a (node x))) hc).
  move=> x a Hx Ha Hnx y z; rewrite {1 2}/setI -cats1 !fband_cat /= !orbF.
  have Henx: setI (fband a) hc (edge (node x)).
    by rewrite /setI (fclosed1 (fbandF a)) Enode Hx HhcE.
  case Hynx: (cface y (node x)).
    case Hznx: (cface z (node x)).
      move=> _ _; exists (Seq0 gc); last done.
      by rewrite /= /rlink Eface (same_cface Hynx) Sface andbT.
    rewrite orbF; move{Hznx} => _ Hz.
    case: {Ha}(Ha _ _ Henx Hz) => [p Hp Hap]; exists (Adds (node x) p).
      by move: Hp; rewrite Eedge /= {2}/rlink Eface Hynx.
    rewrite /= /setI fband_cat Hnx /= connect0 orbT.
    apply/allP => [t Ht]; rewrite fband_cat demorgan2; apply/orP; left.
    by apply: (allP Hap).
  case Hznx: (cface z (node x)) {Hynx}; rewrite !orbF.
    move=> Hy; case: {Ha}(Ha _ _ Hy Henx) => [p Hp Hap].
    exists (add_last p (edge (node x))).
      by rewrite -cats1 path_cat Hp last_add_last /= /rlink De2c Sface Hznx.
    apply/allP => [t Ht]; rewrite /setI fband_cat demorgan2; apply/orP; left.
    rewrite mem_add_last in Ht; case/setU1P: Ht => [<-|Ht] //.
    by apply: (allP Hap).
  move=> Hy Hz; case: {Ha}(Ha _ _ Hy Hz) => [p Hp Hap]; exists p; auto.
  apply/allP => [t Ht]; rewrite /setI fband_cat demorgan2; apply/orP; left.
  by apply: (allP Hap).
have Hq: forall x a q, fband a x -> fband a (edge x) -> all ac a ->
    rlink_connected (setI (fband a) hc) -> let s := walkq (node x) q in
    all (setI ac hc) s -> rlink_connected (setI (fband (cat a s)) hc).
  move=> x a q; elim: q x a => /=; try by move=> *; rewrite cats0.
  - by move=> _ x a Hx _ _ HaE; rewrite cats1 andbT; case/andP; auto.
  - move=> _ ql Hrec x a Hx Hex Ha HaE; case/andP; move/andP=> [Hnx HnxE] Hql.
    rewrite -cat_add_last /qstepL; apply Hrec; auto.
    + by rewrite -cats1 fband_cat /= cface1 Enode connect0 orbT.
    + rewrite De2c -2!(Enode gc (node (node _))) (Dn3c (Hacbc Hnx)) Enode.
      by rewrite -cats1 fband_cat -(fclosed1 (fbandF a)) Hex.
    by rewrite -cats1 all_cat Ha /= andbT.
  - move=> _ qr Hrec x a Hx _ Ha HaE; case/andP; move/andP=> [Hnx HnxE] Hqr.
    rewrite -cat_add_last /qstepR; apply Hrec; auto.
    + by rewrite -cats1 fband_cat (fclosed1 (fbandF a)) Enode Hx.
    + by rewrite De2c -cats1 fband_cat /= connect0 orbT.
    by rewrite -cats1 all_cat Ha /= andbT.
  - move=> _ ql Hrecl qr Hrecr x a Hx Hex Ha HaE; rewrite all_cat; case/and3P.
    move/andP=> [Hnx HnxE] Hql Hqr.
    rewrite -cat_add_last catA /qstepR; apply Hrecr; auto.
    + by rewrite cat_add_last fband_cat /= (fclosed1 (fbandF a)) Enode Hx.
    + by rewrite De2c cat_add_last fband_cat /= connect0 orbT.
    + rewrite cat_add_last all_cat Ha /= Hnx /=.
      by rewrite all_setI in Hql; case/andP: Hql.
    rewrite /qstepL; apply Hrecl; auto.
    + by rewrite -cats1 fband_cat /= cface1 Enode connect0 orbC.
    + rewrite De2c -2!(Enode gc (node (node _))) (Dn3c (Hacbc Hnx)) Enode.
      by rewrite -cats1 fband_cat -(fclosed1 (fbandF a)) Hex.
    by rewrite -cats1 all_cat Ha /= andbT.
  - move=> _ qll Hrec x a _ Hex Ha HaE; case/andP.
    move/andP=> [HneLnx HneLnxE] Hqll.
    have Hfex: ac (face (edge x)).
      case/hasP: Hex => [y Hy Hexy]; rewrite cface1 in Hexy.
      by rewrite (closed_connect HacF Hexy); apply (allP Ha).
    have Hffex: ac (face (face (edge x))) by rewrite -(fclosed1 HacF).
    have Dffex: node (qstepL (node x)) = face (face (edge x)).
      rewrite /qstepL -{1}[x]Eedge (Dn3c (Hacbc Hfex)).
      by rewrite -{1}[face (edge x)]Eface De2c (Dn3c (Hacbc Hffex)).
    rewrite -cat_add_last {2}/qstepL; apply Hrec; auto.
    + by rewrite -cats1 fband_cat /= connect0 orbT.
    + by rewrite De2c Dffex -cats1 fband_cat -!(fclosed1 (fbandF a)) /= Hex.
    + by rewrite -cats1 all_cat Ha /= andbT.
    rewrite Dffex -{1}[face (face (edge x))]Eface De2c; apply Hq1; auto.
      by rewrite -!(fclosed1 (fbandF a)).
    by rewrite -[face (face (edge x))]De2c Eedge -Dffex.
  move=> _ qrr Hrec x a Hx _ Ha HaE; case/andP; move/andP=> [HRnx HRnxE] Hqrr.
  have Henx: ac (edge (node x)).
    case/hasP: Hx => [y Hy Hxy]; rewrite -[x]Enode -cface1 in Hxy.
    by rewrite (closed_connect HacF Hxy); apply (allP Ha).
  rewrite -cat_add_last {2}/qstepR; apply Hrec; auto.
  - by rewrite 2!(fclosed1 (fbandF _)) /qstepR !Enode -cats1 fband_cat Hx.
  - by rewrite De2c -cats1 fband_cat /= connect0 orbT.
  - by rewrite -cats1 all_cat Ha /= andbT.
  by rewrite /qstepR; apply Hq1; auto; rewrite (fclosed1 (fbandF a)) Enode.
case: Hqzc => [Hqz _ _ Dac].
have Hs: all (setI ac hc) s0c.
  apply/allP => [y Hy].
  by rewrite /setI -Dac (embedqz_central Hy) (subsetP (ring_fband _) _ Hy).
move: Hqz Dac Hs; rewrite /s0c; case: qz => [q0 q1] /=; rewrite all_cat /=.
case: q0 => //= [_ q01]; case: q1 => //= [_ q10] _ Dac; case/and3P; case/andP.
move/andP=> [Hx0F Hx0E] Hq01; move/andP=> [Hx1F Hx1E] Hq10.
pose a := cat (seq2 x0c (edge x0c)) (walkq (qstepR x0c) q01).
pose a' := cat a (walkq (qstepR (edge x0c)) q10).
have Ha': rlink_connected (setI (fband a') hc).
  rewrite /a' /qstepR; apply Hq; auto; rewrite ?De2c.
  - by apply (subsetP (ring_fband a)); rewrite /a /= /setU1 set11.
  - by apply (subsetP (ring_fband a)); rewrite /a /= /setU1 set11 /= orbT.
  - apply/allP => [x Hx]; rewrite /= in Hx.
    by do 2 case/setU1P: Hx => [<-|Hx] //; case/andP: (allP Hq01 _ Hx).
  rewrite /a /qstepR; apply Hq; auto; rewrite ?De2c /= ?connect0 ?orbT //.
    by rewrite Hx0F Hx1F.
  rewrite /seq2 -cat1s cats1 -{2}[x0c]Eface De2c; apply Hq1; auto.
  - by rewrite /= Sface fconnect1.
  - move=> x y; rewrite /setI /= !orbF; move/andP=> [Hx _]; move/andP=> [Hy _].
    by exists (Seq0 gc); rewrite //= /rlink Eface (same_cface Hx) Sface andbT.
  by rewrite -{1}[x0c]De2c Eedge.
have Dac': ac =1 fband a'.
  move=> x; rewrite -Dac /fband /= !has_cat /=; congr orb.
  by rewrite !orbA; congr orb; rewrite orbC.
move=> x y Hx Hy; rewrite /setI !Dac' in Hx Hy.
case: (Ha' _ _ Hx Hy) => [p Hp Hpa]; exists p; first done.
by apply/allP => [z Hz]; rewrite /setI Dac'; apply: (allP Hpa).
Qed.

Lemma quiz_preembedding : preembedding ac h.
Proof.
split.
- exact embedqz_face.
- exact embedqz_arity.
- case: Hqzc => [_ _ _ Dac]; apply/subsetP => x; rewrite -Dac.
  move/hasP=> [y Hy Hxy]; apply/set0Pn; exists y; rewrite /setI Hxy.
  exact: embedqz_central.
exact embedqz_rlinked.
Qed.

End QuizEmbedding.

Unset Implicit Arguments.