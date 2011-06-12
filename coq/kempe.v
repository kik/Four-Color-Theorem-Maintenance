(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import dataset.
Require Import ssrnat.
Require Import seq.
Require Import color.
Require Import chromogram.
Require Import finset.
Require Import paths.
Require Import connect.
Require Import hypermap.
Require Import walkup.
Require Import jordan.
Require Import geometry.
Require Import coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The proof of the kempe closure property of planar quasitriangulations.  *)
(* This is the main link between the reflected combinatorial reducibility  *)
(* proofs, and the mathematical theory of planar graphs developed in the   *)
(* rest of the proof. The result is also reused to validate the reduction  *)
(* to internally 5-connected triangulations.                               *)
(* We start by showing a side result that if a color sequence's edge trace *)
(* can be matched by a coloring, then in fact the color sequence can be    *)
(* matched exactly.                                                        *)
(* The file also contains a three small functions on chromograms that      *)
(* mangle chromograms by flipping brackets in various ways. These are used *)
(* to match changes in the perimeter as edges are removed in the main      *)
(* theorem, which proceeds by induction on the graph size, much as the     *)
(* proof of the euler formula; indeed, it uses the `euler_tree' lemma from *)
(* that proof to do the edge selection.                                    *)

Section KempeMap.

(* Negate the bit of the first unmatched pop. *)

Fixpoint gram_neg_rec (n : nat) (w : chromogram) {struct w} : chromogram :=
  match w, n with
  | Adds Gpush w', _ => Adds Gpush (gram_neg_rec (S n) w')
  | Adds Gskip w', _ => Adds Gskip (gram_neg_rec n w')
  | Adds s w', S n => Adds s (gram_neg_rec n w')
  | Adds Gpop0 w', O => Adds Gpop1 w'
  | Adds Gpop1 w', O => Adds Gpop0 w'
  | seq0, _ => w
  end.

Definition gram_neg := gram_neg_rec 0.

Lemma match_gram_neg : forall b0 et w,
  matchg (Seq b0) et (gram_neg w) = matchg (Seq (negb b0)) et w.
Proof.
move=> b0 et w; set sb : bitseq := seq0.
have Esb: forall b : bool, Adds b sb = add_last sb b by done.
rewrite /gram_neg -[0]/(size sb) 2!{}Esb.
elim: w et sb => [|s w Hrec] et lb; first by case lb.
case Ds: s; (case: et => [|e et]; first by case lb);
 first [ by case: e (Hrec et (Adds _ lb)) => /=
       | by case: e; case: lb => [|b lb]; rewrite /= ?if_negb ?Hrec ].
Qed.

(* Flip the next unmatched pop into a push, and adjust the bit of the next *)
(* pop so that the total parity is inverted. This rebalances a chromogram  *)
(* that has two extra pops.                                                *)

Fixpoint gram_flip_rec (n : nat) (w : chromogram) {struct w} : chromogram :=
  match w, n with
  | Adds Gpush w', _ => Adds Gpush (gram_flip_rec (S n) w')
  | Adds Gskip w', _ => Adds Gskip (gram_flip_rec n w')
  | Adds s w', S n => Adds s (gram_flip_rec n w')
  | Adds Gpop0 w', O => Adds Gpush (gram_neg w')
  | Adds Gpop1 w', O => Adds Gpush w'
  | seq0, _ => Adds Gpush w
  end.

Definition gram_flip := gram_flip_rec 0.

Lemma match_gram_flip : forall et w,
  matchg seq0 et (gram_flip w) =
    matchg (Seq true false) et w || matchg (Seq false true) et w.
Proof.
move=> et w; set lb0 := Seq true false; set lb0' := Seq false true.
rewrite /gram_flip -(cat0s lb0) -(cat0s lb0').
set sb := seq0 : bitseq; rewrite -[0]/(size sb).
elim: w et sb => [|s w Hrec] et lb.
  by case: et lb => [|[|||] [|e et]] [|b lb].
case s; (case: et => [|e et]; first by case lb); first
 [ by case: e (Hrec et (Adds _ lb)) => /=
 | by case: e; case: lb => [|[|] lb];
     rewrite /= ?if_negb ?Hrec // /= ?orbF ?match_gram_neg ].
Qed.

(* Rotate a chromogram by moving the first symbol at the end, and flipping *)
(* it if it's a push. We check for imbalanced chromograms first, to ensure *)
(* that matchg is always preserved.                                        *)

Definition gram_rot w :=
  if set0b (fun b => gram_balanced 0 b w) then w else
   match w with
   | Adds Gpush w' => gram_flip (add_last w' Gpop1)
   | Adds Gskip w' => add_last w' Gskip
   | _ => w
   end.

Lemma match_gram_rot : forall et w,
  matchg seq0 (rot 1 et) (gram_rot w) = matchg seq0 et w.
Proof.
move=> et w; rewrite /gram_rot; case Hw0: (set0b _).
  by apply/idP/idP; case/matchg_balanced; rewrite (set0P Hw0).
move/set0Pn: Hw0 => [b0]; case: et w => [|e et]; first by do 4 case=> //.
rewrite rot1_adds; move=> [|[|||] w] /= Hw;
 try by case: e et; do 2 try case.
  suffice Ew: forall b lb, gram_balanced (size lb) b0 w ->
    matchg (Adds b lb) (add_last et e) (add_last w Gpop1) =
      (e =d ccons true (negb (last b lb))) && matchg (belast b lb) et w.
    by rewrite match_gram_flip !Ew //; case e; rewrite ?orbF.
  move=> b lb; rewrite andbC; elim: w lb b b0 et {Hw} => [|s w Hrec] lb b b0 et.
    by case: lb => // [] _; case: b; (case: et; [ case: e | do 2 try case ]).
  case: et => [|e' et]; first by case: s; case: e {Hrec} => //; case: b; case: w.
  case: s; case: e' => //=; first
   [ apply: Hrec
   | apply: (Hrec (Adds b lb))
   | case: b; case: lb => [|b' lb] //=; apply: Hrec ].
   elim: w (seq0 : bitseq) et {b0 Hw} => [|s w Hrec] lb et.
  by case e; case: et; do 2 try case.
case: et => [|e' et]; first by case e; case: s lb => [|||] [|[|] lb] //; case w.
by case: s; case: e' => //=; try apply: (Hrec (Adds _ lb));
  case: lb => [|[|] lb'] //=; case e.
Qed.

(* The main theorem, in one big piece.                                      *)

Theorem kempe_map : forall g r,
  @ucycle_planar_plain_quasicubic g r -> kempe_closed (ring_trace r).
Proof.
move=> g r; do 3 case; move=> HgE HgN; move/andP=> [Hr Ur] Hpg.
move=> et [k Hk Det]; split.
  move=> h; exists (comp h k).
  move: (iso_inj (iso_permc h)) Hk => Ih [HkE HkN].
    by split; move=> x; rewrite (fun f => invariant_inj f Ih k).
  by rewrite (maps_comp h k) -/(permt h) trace_permt -Det.
suffice: forall r, fcycle node r -> uniq r -> quasicubic r ->
    exists2 w, matchg seq0 (urtrace (maps k r)) w
            & forall et, matchg seq0 et w ->
              exists2 k', coloring k' & et = urtrace (maps k' r).
  case/(fun H => H (rot 1 r)); rewrite ?cycle_rot ?uniq_rot //.
    by apply: subset_trans HgN; apply/subsetP => [x]; rewrite /setC mem_rot.
  move=> w Hw Hpc; rewrite maps_rot urtrace_trace -Det in Hw.
  exists w; first done; move=> et' Het'; case: (Hpc _ Het') => [k' Hk' Det'].
  by rewrite maps_rot urtrace_trace in Det'; exists k'.
move{r et Hr Ur HgN Det} => r Hr Ur HgN; move: r Hr Ur Hpg HgE HgN k Hk.
elim: {g}(S (card g)) {-3 4}g (ltnSn (card g)) => [|n Hrec] g Hn //.
move=> r Hr Ur Hpg HgqE HgqN k [HkE HkF]; case Dr: r Hr Ur HgqN => [|r0 r'].
  do 3 clear; exists (seq0 : chromogram); first done.
  by case; first by exists k; split.
move: {HgqE}(plain_eq HgqE) (plain_neq HgqE) => Dee HgE.
rewrite -Dr /=; move=> Hr Ur HgqN.
have HkN: forall x, k (node x) <> k x.
  move=> x Hkx; case/eqcP: (HkE (node x)).
  by rewrite -(eqcP (HkF (edge (node x)))) Enode.
have HgN: forall x : g, (x =d node x) = false.
  by move=> x; apply/eqP => [Dnx]; case (HkN x); congr k.
case Hgpi: (negb (has (fun z => setU1 z (setC r) (face z)) r)).
  have HgNp: planar (permN g) by rewrite planar_permN.
  case/set0Pn: (euler_tree (planarP _ HgNp) r0) => /= [] x; move/andP=> [Hrx Hx].
  have Hr0: r r0 by rewrite Dr /= setU11.
  have Er := fconnect_cycle Hr Hr0.
  case/hasP: Hgpi; exists x; first by rewrite -Er.
  case/orP: Hx => [Hx|Hfx].
    case/clinkP: Hx => /=; first by move<-; rewrite setU11.
    by move=> *; case/eqP: (HgE x).
  by rewrite /cross_edge /= -(same_cnode Hrx) Er in Hfx; apply: setU1r.
case/hasP: Hgpi {r0 r' Dr} => z.
move Di: (if index z r is S i then size r - S i else 0) => i.
elim: i r Di Hr Ur HgqN => [|i Hreci] r Di Hr Ur HgqN Hrz.
  case Dr: {1 2 3}r (Hrz) {Di}(introT eqP Di) => [|z' p]; first done.
  rewrite /= /setU1; case Hz': (negb (z =d z')).
    by rewrite eqd_sym (negbE Hz') subSS eqn_sub0 leqNgt /= index_mem => ->.
  do 2 clear; move/eqP: Hz' Dr => <- {z'} Dr.
  move: {Hrz}(fconnect_cycle Hr Hrz) => EpN.
  rewrite Dr /= -cats1 path_cat /= {2}/eqdf andbT in Hr Ur.
  move/andP: Hr => [Hp Ep]; move/andP: Ur => [Hpz Up].
  case Dp: p Hp => [|nz p'] /=; first by rewrite Dp /= eqd_sym HgN in Ep.
  case/andP; move/eqP=> Dnz Hp'; set fz := face z; set ez := edge z.
  have Hez: (setC1 z ez) by rewrite /setC1 /ez eqd_sym HgE.
  set ez' := subdI Hez : walkupN z; set g' := walkupE ez'.
  have Deez': edge ez' = ez'.
    by apply: subdE_inj; rewrite /= /skip1 /= /ez Dee set11.
  have Hg'n: card g' < n.
    move: (card_sub_dom (setC1 ez')) => /= ->; rewrite -ltnS.
    apply: leq_trans Hn; rewrite -(cardC (eqd z)) card1 add1n !ltnS.
    apply: (leq_trans (max_card _)).
    by move: (card_sub_dom (setC1 z)) => /= ->; rewrite leqnn.
  pose h (x' : g') : g := subdE (subdE x').
  have Hh: forall x, negb (z =d x) -> negb (ez =d x) -> {x' : g' | h x' = x}.
    move=> x Hzx Hezx.
    by exists (subdI (Hezx : setC1 ez' (subdI (Hzx : setC1 z x))) : g').
  have Ehd: forall x' y', (x' =d y') = (h x' =d h y') by done.
  have Ih: injective h by move=> x' y' Ex'y'; do 2 apply: subdE_inj.
  have Hzh: (z =d h _) = false by move=> [[x Hx] Hx']; apply negbE.
  have Hezh: (ez =d h _) = false by move=> [x' Hx']; apply negbE.
  have DhE: forall x', h (edge x') = edge (h x').
    move=> [[x Hzx] Hezx]; rewrite /setC1 /eqd /= in Hezx |- *.
    rewrite /h /= /skip_edge1 /= /eqd /= /skip1 /= /ez Dee !set11 /=.
    by rewrite /skip1 /= -(Dee z) -/ez (inj_eqd (Iedge g)) (negbE Hezx).
  set nez := node ez.
  have DhN: forall x', h (node x') = let nx := node (h x') in
                                     if z =d nx then nez else
                                     if ez =d nx then nz else nx.
    move=> [[x Hzx] Hezx]; rewrite /setC1 {2}/eqd /= in x Hzx Hezx |- *.
    rewrite /h /= /skip1 /= (fun_if (subdE (a := setC1 z))) {1}/eqd /=.
    rewrite /skip_edge1 /= -{3 6 9 15}[z]Dee Eedge -/ez.
    rewrite !(inj_eqd (Iedge g)) !HgN.
    case Hznx: (z =d node x).
      rewrite -(eqP Hznx) !(eqd_sym ez) (negbE Hez) set11.
      by rewrite {1}(eqP Hznx) (inj_eqd (Inode g)) eqd_sym (negbE Hezx).
    case Heznx: (ez =d node x); last by rewrite Heznx.
    by rewrite (eqP Heznx) (inj_eqd (Inode g)) eqd_sym (negbE Hzx).
  have Hpg' := planar_walkupE _ (planar_walkupN _ Hpg) : planar g'.
  clearbody h g'; move=> Hz.
  have Hg'qE: plain g'.
    apply/plainP => [x' _].
    by split; [ apply Ih; rewrite !DhE Dee | rewrite Ehd DhE HgE ].
  have Hg'k: coloring (comp k h).
    split; move=> x'; rewrite /invariant /comp; first by rewrite DhE; apply: HkE.
    rewrite -{2}[x']Eface DhE DhN /setA; move: {x'}(h (face x')) => y.
    rewrite -{1}[y]Enode; case: (z =P node y) => [<-|_].
      by rewrite (eqcP (HkF (edge z))) -[edge z]Enode; apply: HkF.
    case: (ez =P node y) => [<-|_]; last by apply: HkF.
    by rewrite /ez Dee (eqcP (HkF z)) -[z]Enode Dnz; apply: HkF.
  have [r' Hr' Dr']: exists2 r', fcycle node r'
                              & maps h r' = if z =d fz then p' else Seq nez fz & p.
    have Hup: forall x' q, fpath node (h x') q -> negb (q z) -> negb (q (edge z))
              -> exists2 q', maps h q' = q & fpath node x' q'.
      move{Hrec} => x' q; elim: q x' => [|y q Hrec] x'; first by exists (Seq0 g').
      rewrite /= {1}/eqdf /setU1 !(eqd_sym y); move/andP=> [Dnx Hq].
      move/norP=> [Hzy Hqz]; move/norP=> [Hezy Hqez].
      case: {Hzy Hezy}(Hh _ Hzy Hezy) => y' Dy.
      rewrite -Dy in Hq; case: {Hrec Hq Hqz Hqez}(Hrec y' Hq Hqz Hqez).
      move=> q' Dq Hq'; exists (Adds y' q'); first by rewrite /= Dy Dq.
      by rewrite /= Hq' /eqdf Ehd DhN (eqP Dnx) -Dy /= Hzh Hezh set11.
    rewrite Dp /= in Hpz; move/norP: Hpz => [Hznz Hpz].
    case Hfz: (z =d fz) Hz => [|] /= Hz.
      have Eez: ez = nz by rewrite /ez -(Eface g z) Dee -/fz -(eqP Hfz).
      case: p' Dp Hpz Hp' => [|nnz p'] Dp; first by exists (Seq0 g').
      rewrite Dp /= -Eez /setU1 !(eqd_sym nnz) in Up |- *; case/andP: Up.
      move/norP=> [Heznnz Hp'ez] _; move/norP=> [Hznnz Hp'z]; case/andP.
      move/eqP=> Dnnz Hp'; move: (Hh _ Hznnz Heznnz) => [nnz' Ennz].
      rewrite -Ennz in Hp'; case: (Hup _ _ Hp' Hp'z Hp'ez) => [q' Dp' Hq'].
      exists (Adds nnz' q'); last by rewrite /= Ennz Dp'.
      rewrite /= -cats1 path_cat Hq' /eqdf /= Ehd DhN.
      rewrite Dp -Dp' /= -Ennz last_maps in Ep.
      by rewrite (eqP Ep) Ennz /= set11 -Dnnz -/nez set11.
    rewrite eqd_sym in Hznz; case: (Hh _ Hznz).
      by rewrite -Dnz eqd_sym (monic2F_eqd (Enode g)) /ez Dee -/fz Hfz.
    move=> nz' Dnz'; rewrite -Dnz' in Hp'; case: (Hup _ _ Hp' Hpz).
      apply/idP => [Hpez]; case/idP: Hz; rewrite -EpN Snode cnode1.
      by rewrite /fz -{1}[z]Dee Eedge Snode EpN Dr Dp /= /setU1 Hpez !orbT.
    move=> q' Dq' Hq'; case (Hh nez).
        apply/eqP => [Dnez]; case/idP: Hz; rewrite -EpN Snode.
        by rewrite /fz {2}Dnez /nez /ez -{2}[z]Eface Dee -cnode1r fconnect1.
      by rewrite /nez HgN.
      move=> nez' Dnez'; move: (cubicP HgqN _ Hz) => [Dfz _].
    have Hezfz: (ez =d fz) = false.
      by rewrite eqd_sym /ez -(Eface g z) -/fz Dee HgN.
      case: (Hh fz (negbI Hfz) (negbI Hezfz)) => [fz' Dfz'].
    exists (Adds nez' (Adds fz' (Adds nz' q')));
     last by rewrite /= Dfz' Dnez' Dnz' Dq' -Dp.
    rewrite /= -cats1 path_cat Hq' /eqdf /= !Ehd !DhN.
    rewrite Dp -Dq' /= -Dnz' last_maps in Ep.
    rewrite Dnez' Dfz' Dnz' (eqP Ep) /= !set11 {2 3}/fz -{3 4}[z]Dee Eedge -/ez.
    rewrite set11 (negbE Hez) /nez {1 4 5}/ez -{2 3 4}[z]Eface Dee -/fz Dfz /=.
    by rewrite Hfz Hezfz !set11.
  have Hg'qN: quasicubic r'.
    apply/cubicP => [y' Hy']; set (y := h y'); case Hy: (maps h r' y).
      by rewrite /y (mem_maps Ih) in Hy; case (negP Hy').
    rewrite Dr' in Hy; case Hry: (r y).
      rewrite Dr /= /setU1 {1}/y Hzh /= in Hry.
      case: (z =P fz) Hy => [Dfz|_] Hy.
        rewrite Dp /= /setU1 Hy orbF in Hry.
        by rewrite -Dnz Dfz /fz -(Dee z) Eedge -/ez /y Hezh in Hry.
      by rewrite /= /setU1 Hry !orbT in Hy.
    case: (cubicP HgqN _ (negbI Hry)) => [Dnnny _].
    case Hzny: (z =d node y).
      by rewrite -EpN Snode (eqP Hzny) fconnect1 in Hry.
    have Dny': h (node y') = node y.
    rewrite DhN -/y /= Hzny; case: (ez =P node y); last done.
      move=> Dez; rewrite /fz -{2 3}[z]Dee -/ez Dez Enode {1}/y Hzh in Hy.
      by rewrite /= /setU1 set11 /= !orbT in Hy.
    have Dnny': h (node (node y')) = node (node y).
      rewrite DhN Dny' /=; case: (z =P node (node y)) => [Dz|_].
        by rewrite -EpN -Dnnny -Dz fconnect1 in Hry.
        case: (ez =P node (node y)) => [Dez|_]; last done.
      rewrite {1}/fz -{2}[z]Dee -/ez /nez Dez Enode Dnnny Hzny in Hy.
      by rewrite /= /setU1 set11 in Hy.
    split; first by apply Ih; rewrite DhN Dnny' -/y Dnnny /= /y Hzh Hezh.
    by rewrite Ehd Dny' -/y eqd_sym HgN.
  have Ur': uniq r'.
    rewrite -(uniq_maps Ih) Dr'.
    case Hfz: (eqd z fz) Hz; first by rewrite Dp in Up; case/andP: Up.
    rewrite /= Up; move=> Hpfz; move: (cubicP HgqN _ Hpfz) => [Efz _].
    rewrite /setC Dr /= /setU1 Hfz /= in Hpfz.
    rewrite {1}/fz -[z]Dee Eedge -/ez -/nez in Efz.
    rewrite /setU1 (negbE Hpfz) -Efz eqd_sym HgN /= andbT.
    apply/idP => [Hpnez]; move: (EpN nez).
    rewrite Dr /= (setU1r z Hpnez) Snode cnode1.
    by rewrite Efz Snode EpN Dr /= /setU1 Hfz (negbE Hpfz).
  case: {n Hrec Hn Hg'n Hr' Ur'}(Hrec _ Hg'n _ Hr' Ur' Hpg' Hg'qE Hg'qN _ Hg'k).
  rewrite {Hpg' Hg'qE Hg'qN Hg'k}(maps_comp k h) Dr'; move=> w Hw Hwet.
  have Huk: forall k', coloring k' -> forall e1,
               (if z =d fz then negb (e1 =d Color0) else
                proper_trace (ptrace (urtrace (maps k' r')))) ->
           {k'' : g -> color | coloring k''
              & k' =1 comp k'' h /\ (z =d fz -> k'' z +c k'' nz = e1)}.
    move=> k'; have [k1 Dk1]: {k1 : g -> color | k' =1 comp k1 h}.
      exists (fun x => if pick (fun x' => x =d (h x')) is Some x' then k' x'
                       else Color0).
      move=> x'; rewrite /comp; case: (pickP _) => [y' Dy' | Hx'].
        by rewrite (Ih _ _ (eqP Dy')).
      by case/eqP: (Hx' x').
    move=> [Hk'E Hk'F] e1 He1.
    have Hk1fz: (z =d fz) = false -> k1 fz <> k1 (last z p).
      move=> Hfz Dk1nz; move: He1; rewrite (eq_maps Dk1) (maps_comp k1 h).
      rewrite Dr' Hfz /proper_trace /= Dk1nz Dp /= last_maps.
      by rewrite {1}[addc]lock addcC -lock addcc.
    exists (fun x =>
        if z =d x then if z =d fz then e1 +c k1 (last z p) else k1 fz else
        if ez =d x then k1 (last z p) else k1 x).
      split; move=> x; apply/eqP.
        rewrite -{1}[z]Dee -/ez {2}/ez !(inj_eqd (Iedge g)).
        rewrite -(addc_inv (k1 (last z p)) e1) -(addcC e1) in He1.
        case Hezx: (ez =d x).
          rewrite -(eqP Hezx) (negbE Hez); case Hfz: (eqd z fz) He1; auto.
          by move=> He1 De1; rewrite De1 addcc in He1.
        case Hzx: (z =d x).
          case Hfz: (z =d fz) He1 => [|] He1; last by apply: nesym; auto.
          by move=> De1; rewrite -De1 addcc in He1.
        case: (Hh _ (negbI Hzx) (negbI Hezx)) => [x' <-].
        by move/eqcP: (Hk'E x'); rewrite !Dk1 -DhE.
      case Hzx: (z =d x) => /=.
        rewrite -(eqP Hzx) -/fz (eqd_sym ez) /ez -{4}[z]Eface Dee -/fz HgN.
        by case (z =d fz).
      case Hezx: (ez =d x).
        rewrite (eqd_sym z) -{1}[z]Eedge -/ez (eqP Hezx) HgN.
        by rewrite -{3}(eqP Hezx) /ez -{2}(eqP Ep) Enode if_same.
      case: (Hh _ (negbI Hzx) (negbI Hezx)) => x' Dx'; move/eqcP: (Hk'F x') (Dx').
      rewrite /= -{3}[x']Eface !Dk1 /comp DhE DhN Dx' /= => <-.
      set y := h (face x'); case Hzny: (z =d node y).
        move=> Dx; rewrite -{1 2}Dx /nez Enode (negbE Hez) set11.
        by rewrite -(eqP Ep) in Hzny; rewrite (Inode _ (eqP Hzny)).
      case Hezny: (ez =d node y).
        move=> Dx; rewrite -{1}Dx -Dnz Enode set11.
        rewrite -{1}[z]Enode Dnz Dx /fz (inj_eqd (Iface g)) eqd_sym Hzx.
        by rewrite -(Dee z) -/ez (eqP Hezny) Enode.
      by move <-; rewrite Enode {1 2}/y Hzh Hezh.
    split; first by move=> y; rewrite /comp Hzh Hezh Dk1.
    move=> Hfz; rewrite Hfz set11 -Dnz {3 5}(eqP Hfz) /fz -{3 5}[z]Dee Eedge.
    by rewrite -/ez (negbE Hez) set11 -addcA addcc addc0.
  case Hfz: (z =d fz) Dr' Hw Huk => [|] /= Dr' Hw Huk.
    have He1k: forall k', coloring k' -> exists2 e1, negb (e1 =d Color0)
                       & urtrace (maps k' r) = Seq e1 e1 & (urtrace (maps k' p')).
      move=> k' [Hk'E Hk'F]; pose e1 := k' z +c k' nz; exists e1.
      rewrite /e1 -eq_addc0; apply/eqP => [De1]; case/eqcP: (Hk'E nz).
        by rewrite -De1 -[z]Enode Dnz (eqcP (Hk'F _)).
      move: Ep; rewrite Dr Dp /urtrace /= addcC last_maps.
      case: (p') => [|nnz q] Dz //=.
      rewrite /= -[z]Eedge -[z]Eface -/fz Dee -(eqP Hfz) Dnz in Dz.
      by rewrite last_maps (Inode g (eqP Dz)) (eqcP (Hk'F nz)).
    case (He1k k); [ by split | move=> e1 He1 Dkr; rewrite Dkr ].
    exists (if e1 =d Color1 then Seq Gskip Gskip & w else Seq Gpush Gpop0 & w).
      by case De1: e1 He1.
    move=> et Het.
    have [e1' He1' [et' Het' Det]]: exists2 e1', negb (e1' =d Color0)
                         & exists2 et', matchg seq0 et' w & et = Seq e1' e1' & et'.
      by case: (e1 =d Color1) Het; case: et => [|e1' et] //;
        case De1': e1' => //; move=> Hetw; exists e1';
        rewrite De1' //; case: et Hetw => [|[|||] et] //; exists et.
    case: (Hwet _ Het') => [k1 Hk1 Det'].
    case: (Huk _ Hk1 _ He1') => [k' Hk' [Dk' Dk'x]]; exists k'; first done.
    rewrite (eq_maps Dk') (maps_comp k' h) Dr' in Det'.
    case: (He1k _ Hk') => [e1'' _ Dk'r]; rewrite Det Dk'r -Det' -Dk'x //.
    by rewrite Dr Dp /= in Dk'r; case: Dk'r => [_ -> _].
  move: Hw; rewrite {1}Dp /urtrace /= last_maps.
  set e1 := k (last nz p') +c k z; set e2 := k (last nz p') +c k nez.
  have <-: e2 +c e1 = k nez +c k fz.
    rewrite /fz (eqcP (HkF z)) /e2 {1}[addc]lock addcC -lock -addcA.
    by rewrite /e1 addc_inv.
  case: w Hwet => [|s1 [|s2 w]] Hwet //; first by case s1; case e2.
  rewrite /fz (eqcP (HkF z)) => Hw.
  have He1: negb (e1 =d Color0).
    rewrite Dp /= (monic2F_eqd (Enode g)) in Ep.
    rewrite /e1 -eq_addc0 (eqP Ep) (eqcP (HkF (edge z))).
    apply negbI; apply: HkE.
  have Hs12: match s1, s2 with
             | Gpush, Gpop0 => False
             | Gpush, _ => True
             | Gskip, Gpush => True
             | _, _ => False
             end.
    by case: s1 Hw {Hwet} => //; case: e2 => //; case: e1 He1 => //; case s2.
  exists match s1, s2 with
        | Gpush, Gpush => Adds Gskip (gram_flip w)
        | Gpush, Gskip => Adds Gpush (gram_neg w)
        | Gskip, _ => Adds Gpush (gram_neg w)
        | _, _ => Adds Gskip w
        end.
    rewrite Dr /= Dp /urtrace /= last_maps -/e1; move: Hw {Hwet}.
    move: (Adds (k z +c k nz) (pairmap addc (k nz) (maps k p'))) => et.
    by case: s1 Hs12 => //; case: e2 => //; case: s2 => // _; case: e1 He1;
      rewrite //= ?match_gram_neg //; move=> _ Hw';
      rewrite match_gram_flip Hw' ?orbT.
  move=> [|e et]; first by case: (s1) Hs12; case s2.
  move=> Het; pose m01etw := matchg (Seq false true) et w.
  pose e' :=  match s1, s2, m01etw with
              | Gpush, Gpush, true => Color3
              | Gpush, Gskip, _ => addc Color1 e
              | Gskip, Gpush, _ => Color1
              | _, _, _ => Color2
              end.
  case: {Hw Hwet}(Hwet (Seq e' (e' +c e) & et)).
    by rewrite {}/e'; case: s1 Hs12 Het => //; case: s2 => //; case: e => //=;
      rewrite ?match_gram_neg // ?match_gram_flip orbC -/m01etw; case Hw: m01etw.
  move=> k1 Hk1 Det; case (Huk _ Hk1 Color0).
    rewrite -{}Det /ptrace /proper_trace /= addc_inv {e'}.
    by case: e Het => //; case: s1 {Hs12} => //; case s2.
  move=> k' [Hk'E Hk'F] [Dk' _]; exists k'; first by split.
  move: Det; rewrite (eq_maps Dk') (maps_comp k' h) Dr' Dr /urtrace /=.
  rewrite /fz (eqcP (Hk'F z)); case=> [De' De <-]; congr Adds.
  by rewrite -(addc_inv e' e) De De' -addcA addc_inv.
have [r' Dr]: exists r', r = rot 1 r' by exists (rotr 1 r); rewrite rot_rotr.
rewrite Dr cycle_rot in Hr; rewrite Dr uniq_rot in Ur.
rewrite Dr mem_rot in Hrz.
move=> Hz; rewrite Dr /setU1 /setC mem_rot in Hz.
case: {Hreci}(Hreci r'); auto.
 apply eq_add_S; move: Di.
  case Dj: (index z r) => [|j] //; rewrite -{j}Dj; case.
    rewrite Dr; case: (r') Hrz Ur => [|y q]; first done.
    rewrite size_rot /rot index_cat /= drop0 take0 /setU1 eqd_sym.
    case: (z =P y) => [Dz|_].
      by clear; move/andP=> [Hqy _]; rewrite Dz (negbE Hqy) addn0 subSnn.
    move=> /= Hqz _; rewrite Hqz.
    by rewrite -index_mem in Hqz; rewrite (leq_subS (ltnW Hqz)).
  apply: (subset_trans (introT subsetP (fun x => _)) HgqN).
  by rewrite Dr /setC mem_rot.
move=> w Hw Hwet; exists (gram_rot w).
  by rewrite Dr maps_rot urtrace_rot match_gram_rot.
move=> et; rewrite -(rot_rotr 1 et) match_gram_rot Dr.
move=> Hw'; case: (Hwet _ Hw') => [k' Hk' Duet]; exists k'; auto.
by rewrite maps_rot urtrace_rot -Duet.
Qed.

End KempeMap.

Unset Implicit Arguments.