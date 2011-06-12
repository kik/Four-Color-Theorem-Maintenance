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
Require Import walkup.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Planarity.

Theorem even_genusP : forall g, even_genus g.
Proof.
move=> g; elim: {g}(card g) {-3 4}g (erefl (card g)) => [|n Hrec] g Dn.
  have Hc0: forall a : set g, card a = 0.
    move=> a; apply: eqP; rewrite -leqn0 -Dn; apply max_card.
  by rewrite /even_genus /genus /genus_rhs /genus_lhs /n_comp Dn !Hc0.
case: (set0Pnx g _); first by rewrite /set0b Dn.
move=> z _; apply: (@even_genus_walkup g z); apply Hrec.
by rewrite card_walkup Dn.
Qed.

Theorem genus_le : forall g, genus_rhs g <= genus_lhs g.
Proof. move=> g; rewrite even_genusP; apply leq_addl. Qed.

Remark node_is_last : forall g  x p,
 exists2 y : dart g, node y = last x p & y = finv node (last x p).
Proof.
by move=> g x p; exists (finv node (last x p)); rewrite ?(f_finv (Inode g)).
Qed.

Theorem planar_jordan : forall g, planar g -> jordan g.
Proof.
move=> g Hg; elim: {g}(card g) {-4 5}g Hg (erefl (card g)) => [|n Hrec] g Hg Dn.
  by move=> [|x p]; last by move: (max_card (eqd x)); rewrite card1 Dn.
have HcE: forall z : g, jordan (walkupE z).
  by move=> z; apply: (Hrec _ (planar_walkupE z Hg)); rewrite card_walkup Dn.
have HcN: forall z : g, jordan (walkupN z).
  move=> z; apply: (Hrec _ (planar_walkupN z Hg)).
  by apply: (etrans (card_walkup _)); rewrite /= Dn.
have HcF: forall z : g, jordan (walkupF z).
  move=> z; apply: (Hrec _ (planar_walkupF z Hg)).
  by apply: (etrans (card_walkup _)); rewrite /= Dn.
clear n Dn Hrec.
have HpE: forall (z x : g) p, path clink x p ->
      negb (Adds x p z) ->
    let pg : walkupE z -> g := @subdE _ _ in
    exists2 x', pg x' = x & exists2 p', path clink x' p' & maps pg p' = p.
  move=> z x p; rewrite /= /setU1 eqd_sym; move=> Hp; move/norP=> [Hx Hpz].
  exists (@subdI g (setC1 z) x Hx); trivial.
  elim: p x Hx Hp Hpz => [|y p Hrec] x Hx; first by exists (Seq0 (walkupE z)).
  rewrite /= /setU1 eqd_sym; move/andP=> [Hxy Hp]; move/norP=> [Hy Hpz].
  case: {Hrec Hp Hpz}(Hrec y Hy Hp Hpz) => [p' Hp' Dp].
  exists (Adds (@subdI g (setC1 z) y Hy) p'); last by rewrite /= Dp.
  apply/andP; split; [ apply/clinkP | done ].
  case/clinkP: Hxy => [Dny|Dfx]; [ left | right ]; apply: subdE_inj.
    by rewrite /= /skip1 -Dny (negbE Hx).
  by rewrite /= /skip1 Dfx (negbE Hy).
have HpN: forall (z x : g) p, path clink x p ->
      negb (Adds x p z) -> negb (p (face z)) ->
    let pg : walkupN z -> g := @subdE _ _ in
    exists2 x', pg x' = x & exists2 p', path clink x' p' & maps pg p' = p.
  move=> z x p; rewrite /= /setU1 eqd_sym; move=> Hp; move/norP=> [Hx Hpz] Hpfz.
  exists (@subdI g (setC1 z) x Hx); trivial.
  elim: p x Hx Hp Hpz Hpfz => [|y p Hrec] x;
   first by exists (Seq0 (walkupN z)).
  rewrite /= /setU1 !(eqd_sym y); move=> Hx; move/andP=> [Hxy Hp].
  move/norP=> [Hy Hpz]; move/norP=> [Hyfz Hpfz].
  case: {Hrec Hp Hpz Hpfz}(Hrec y Hy Hp Hpz Hpfz) => [p' Hp' Dp].
  exists (Adds (@subdI g (setC1 z) y Hy) p'); last by congr Adds.
  apply/andP; split; [ apply/clinkP | done ].
  case/clinkP: Hxy => [Dny|Dfx]; [ left | right ]; apply: subdE_inj.
    rewrite /= /skip_edge1 /= -(monic2F_eqd (Eface g)) -Dny (negbE Hx).
    by rewrite (negbE Hyfz) if_same.
  by rewrite /= /skip1 /= Dfx (negbE Hy).
have HpF: forall (z x : g) p, path clink x p ->
      negb (Adds x p z) -> negb (p (face (edge z))) ->
    let pg : walkupF z -> g := @subdE _ _ in
    exists2 x', pg x' = x & exists2 p', path clink x' p' & maps pg p' = p.
  move=> z x p; rewrite /= /setU1 eqd_sym; move=> Hp; move/norP=> [Hx Hpz] Hpfez.
  exists (@subdI g (setC1 z) x Hx); trivial.
  elim: p x Hx Hp Hpz Hpfez => [|y p Hrec] x; first by exists (Seq0 (walkupF z)).
  rewrite /= /setU1 (eqd_sym y); move=> Hx; move/andP=> [Hxy Hp].
  move/norP=> [Hy Hpz]; move/norP=> [Hyfez Hpfez].
  case: {Hrec Hp Hpz Hpfez}(Hrec y Hy Hp Hpz Hpfez) => [p' Hp' Dp].
  exists (Adds (@subdI g (setC1 z) y Hy) p'); last by congr Adds.
  apply/andP; split; [ apply/clinkP | done ].
  case/clinkP: Hxy => [Dny|Dfx]; [ left | right ]; apply: subdE_inj.
    by rewrite /= /skip1 /= -Dny (negbE Hx).
  rewrite /= /skip_edge1 /= Dfx (negbE Hy) !(eqd_sym z).
  by rewrite (monic2F_eqd (Enode g)) (negbE Hyfez) if_same.
move=> [|x p]; [ done | apply/and3P ].
case: (node_is_last x p) => [y Dny <-] [Hp2 Up Hp].
have HeI := @subdE_inj g (setC1 _).
case: (pickP (setC (Adds x p))) => [z Hz|Hpg].
case: {Hp}(HpE _ _ _ Hp Hz) => [x' Dx [p' Hp' Dp]].
simpl in Dp; case/and3P: (HcE z (Adds x' p')); split; auto.
case: (node_is_last x' p') => [[y' Hy'] Dny' <-]; simpl in Dny'.
 rewrite -(mem2_maps (HeI z)) /= Dp Dx /skip1.
  rewrite -Dp -Dx last_maps /= -Dny' /= /skip1 in Dny.
  case: (z =P node x) => [Dz|_].
    by rewrite Dz /setC /= (setU1r x (mem2r Hp2)) in Hz.
    case: (z =d node y') Dny => [|] Dny; last by rewrite -(Inode g Dny).
    by rewrite -(Inode g Dny) /setC /= (setU1r x (mem2l Hp2)) in Hz.
  by rewrite -(uniq_maps (HeI z)) /= Dx Dp.
move: (cardC (Adds x p)); rewrite (card_uniqP Up) (eq_card Hpg) card0 addn0.
case: p x {Hp2}(mem2l Hp2) Hp Up (Hp2) Dny Hpg => [|x1 p] x0 //=.
case Hx0y: (x0 =d y); first by move=> H _; rewrite (eqP Hx0y) H.
clear; move/andP=> [Hx01 Hp]; move/andP=> [Hpx0 Up] Hp2 Dny.
rewrite mem2_adds in Hp2.
case/clinkP: Hx01 => [Dnx1|Dfx0].
  case: {Hp}(HpE _ _ _ Hp Hpx0) => [x' Dx1 [p' Hp' Dp]].
  case/and3P: (HcE x0 (Adds x' p')); split; auto.
    case: (x1 =P y) Hp2 => [Dy|_] Hp2.
      by rewrite Dnx1 {2}Dy Dny mem_lastU in Hpx0.
    case: (node_is_last x' p') => [[y' Hy'] Dny' <-].
    rewrite -(mem2_maps (HeI x0)).
    rewrite [maps _ _]Dp /= /skip1 Dx1 -Dnx1 set11.
    rewrite -Dp -Dx1 last_maps -Dny' /= /skip1 in Dny.
    case: (x0 =d node y') Dny => [|] Dny; last by rewrite -(Inode g Dny).
    by rewrite (Inode g Dny) set11 in Hx0y.
  by rewrite -Dp -Dx1 in Up; rewrite -(uniq_maps (HeI x0)).
case: p Hp Hp2 Dny Up Dfx0 Hpx0 => [|x2 p].
  simpl; case (x1 =d y); rewrite // /setU1 orbF /=.
  by move=> _ H Dny; rewrite -(inj_eqd (Inode g)) Dny eqd_sym H in Hx0y.
simpl; move/andP=> [Hx1p Hp] Hp2 Dny; move/andP=> [Hpx1 Up] Dfx0.
move/norP=> [Hx10 Hpx0]; set (u01 := subdI (a := setC1 x1) Hx10).
case/clinkP: Hx1p => [Dnx2|Dfx1].
  case: {Hp}(HpF _ _ _ Hp Hpx1); first by rewrite Dnx2 Enode; case/andP: Up.
  case Hx1nx0: (x1 =d node x0).
    by rewrite (eqP Hx1nx0) in Dnx2; rewrite (Inode g Dnx2) setU11 in Hpx0.
  move=> x' Dx2 [p' Hp' Dp].
  case/and3P: (HcF x1 (Adds u01 (Adds x' p'))); split.
   rewrite last_adds -(mem2_maps (HeI x1)).
    case: (node_is_last x' p') => [[y' Hy'] Dny' <-]; simpl in y', Hy'.
    rewrite -Dp -Dx2 last_maps -Dny' /= /skip1 /= in Dny; simpl in Dp, Dx2.
    rewrite /= Dp Dx2 /skip1 /= Hx1nx0.
    case: (x1 =P node y') Dny => [Dx1|_] Dny.
      rewrite Dx1 in Dnx2; rewrite (Inode g Dnx2) mem2_adds set11.
      by rewrite (Inode g Dny) set11 /setU1 Hx1nx0 in Hp2.
    by rewrite (Inode g Dny) (negbE Hy') in Hp2 |- *.
   by simpl in Dp, Dx2; rewrite -(uniq_maps (HeI x1)) /= Dp Dx2 Hpx0.
  apply/andP; split; [ apply/clinkP; right; apply: subdE_inj | done ].
  rewrite Dx2 /= /skip_edge1 /= -{1}Dfx0 (inj_eqd (Iface g)).
  rewrite (eqd_sym x0) (negbE Hx10) Dfx0 set11.
  case: (x1 =P node x1) => [Dx1|_]; last by rewrite Dnx2 Enode.
  by rewrite Dx1 in Dnx2; rewrite (Inode g Dnx2) setU11 in Hpx1.
rewrite -if_negb in Hp2; case Hx1y: (negb (eqd x1 y)) Hp2.
  case: {Hp}(HpE _ _ _ Hp Hpx1) => [x' Dx2 [p' Hp' Dp]] Hp2.
  case/and3P: (HcE x1 (Adds u01 (Adds x' p'))); split.
   rewrite -(mem2_maps (d':=walkupE x1) (HeI x1)) last_adds.
    case: (node_is_last x' p') => [[y' Hy'] Dny' <-]; simpl in y', Hy'.
    rewrite -Dp -Dx2 last_maps -Dny' /= /skip1 in Dny; simpl in Dp, Dx2.
    rewrite /= Dp Dx2 /skip1 /=.
    case: (x1 =P node x0) => [Dx1|_].
      by rewrite -Dx1 in Hp2; rewrite -mem_adds (mem2r Hp2) in Hpx1.
      case: (eqd x1 (node y')) Dny => [|] Dny; last by rewrite -(Inode g Dny).
    by rewrite (Inode g Dny) set11 in Hx1y.
   by simpl in Dp, Dx2; rewrite -(uniq_maps (HeI x1)) /= Dp Dx2 Hpx0.
  apply/andP; split; [ apply/clinkP; right; apply: subdE_inj | done ].
  by rewrite Dx2 /= /skip1 Dfx0 set11 Dfx1.
move/eqP: Hx1y Dny => <- Dnx1 Hp2.
case Hnx1: (x1 =d node x1).
  by rewrite (eqP Hnx1) Dnx1 mem_lastU in Hpx1.
case Hx1nx0: (negb (eqd x1 (node x0))).
  rewrite /setU1 (negbE Hx1nx0) /= in Hp2; case: {Hp}(HpN _ _ _ Hp Hpx1).
    by rewrite Dfx1; case: (andP Up).
  move=> x' Dx2 [p' Hp' Dp].
  case/and3P: (HcN x1 (Adds u01 (Adds x' p'))); split.
  - rewrite -(mem2_maps (HeI x1)) last_adds.
    case: (node_is_last x' p') => [[y' Hy'] Dny' <-]; simpl in y', Hy'.
    rewrite -Dp -Dx2 last_maps -Dny' /= /skip_edge1 /= in Dnx1.
    simpl in Dp, Dx2; rewrite /= Dp Dx2 /skip_edge1 /=; move: Dnx1.
    rewrite (negbE Hx1nx0) -!(monic2F_eqd (Eface g)) Hnx1 Dfx1.
    case: (x2 =P x0) => [Dx0|_]; first by rewrite -Dx0 setU11 in Hpx0.
    case: (x2 =P y') => [Dy'|_]; first by rewrite -Dy' mem2_adds set11.
    case: (x1 =d node y') {Dny'} => [|] Dnx1.
      by rewrite (Inode g Dnx1) setU11 in Hpx1.
   - by rewrite /setC1 (Inode g Dnx1) set11 in Hy'.
   by simpl in Dp, Dx2; rewrite -(uniq_maps (HeI x1)) /= Dp Dx2 Hpx0.
  apply/andP; split; [ apply/clinkP; right; apply: subdE_inj | done ].
  by rewrite Dx2 /= /skip1 /= Dfx0 set11 Dfx1.
move: {Hx1nx0}(esym (eqP (negbEf Hx1nx0))) {Hnx1 Hp2} => Dnx0.
case: p Hp Up Hpx0 Hpx1 Dfx1 Dnx1 => [|x3 p].
  rewrite /= /setU1 !orbF; move=> _ _ Hx20 Hx21 Dfx1 Dnx1 Hpg Hcg.
  have Hge1: forall e, connect_sym e -> e x0 x1 -> e x1 x2 -> n_comp e g = 1.
    move=> e He He01 He12; rewrite -(card1 (root e x1)); apply: eq_card => [x].
    rewrite /setI andbT; congr (@eqd g); apply: (rootP He).
    case/or3P: (Hpg x); rewrite ?orbF; case/eqP=> <-.
    - by apply connect1.
    - by rewrite connect0.
    by rewrite He; apply connect1.
  have Dex0: edge x0 = x1.
    apply: eqP; rewrite (monic2F_eqd (Eedge g)) Dfx1;
    move/idP: (Hpg (node x2)).
    rewrite /setU1 -Dnx0 -{3}Dnx1 !(inj_eqd (Inode g)) -!(eqd_sym x2).
    by rewrite (negbE Hx20) (negbE Hx21) !orbF.
  have Dex1: edge x1 = x2.
    apply: (Iface g (eqP _)); rewrite -Dnx0 Enode; move/idP: (Hpg (face x2)).
    rewrite /setU1 -Dfx0 -{3}Dfx1 !(inj_eqd (Iface g)) -!(eqd_sym x2).
    by rewrite (negbE Hx20) (negbE Hx21) !orbF.
  move: Hg; rewrite /planar /genus /genus_lhs /genus_rhs.
  rewrite -Hcg !Hge1 //; try by apply/eqP.
  - exact (Sface g).
  - exact (Snode g).
  - exact (Sedge g).
  - exact (Sglink g).
  - by rewrite -Dfx0 glinkF.
  by rewrite -Dfx1 glinkF.
simpl; move/andP=> [Hx2p Hp]; move/andP=> [Hpx2 Up].
move/norP=> [Hx20 Hpx0]; move/norP=> [Hx21 Hpx1] Dfx1 Dnx1.
pose u02 := @subdI g (setC1 x2) x0 Hx20.
pose u12 := @subdI g (setC1 x2) x1 Hx21.
case/clinkP: Hx2p => [Dnx3|Dfx2].
  case: {Hp}(HpF _ _ _ Hp Hpx2); first by rewrite Dnx3 Enode; case (andP Up).
  move=> x' Dx3 [p' Hp' Dp].
  case/and3P: (HcF x2 (Adds u02 (Adds u12 (Adds x' p')))); split.
  - rewrite -(mem2_maps (HeI x2)) !last_adds.
    case: (node_is_last x' p') => [[y' Hy'] Dny' <-]; simpl in y', Hy'.
    rewrite -Dp -Dx3 last_maps -Dny' /= /skip1 /= in Dnx1; simpl in Dp, Dx3.
    rewrite /= Dp Dx3 /skip1 /= Dnx0 (negbE Hx21).
    case: (x2 =d node y') Dnx1 => [|] Dnx1.
      by case/eqP: (Hx21); apply Inode.
    by rewrite (Inode g Dnx1) mem2_adds set11 setU11.
  - simpl in Dp, Dx3; rewrite -(uniq_maps (HeI x2)) /= Dp Dx3.
    by rewrite {1}/setU1 negb_orb Hx10 Hpx0 Hpx1.
  apply/and3P; split; auto; apply/clinkP; right; apply: subdE_inj.
    rewrite /= /skip_edge1 /= Dfx0 (negbE Hx21) Dnx3 (inj_eqd (Inode g)).
    case: (x3 =P x1) => [Dx1|_]; first by rewrite -Dx1 setU11 in Hpx1.
    by rewrite if_same.
  rewrite Dx3 /= /skip_edge1 /= Dfx1 set11 -{1}Dfx1 (inj_eqd (Iface g)).
  rewrite (eqd_sym x1) (negbE Hx21) {1}Dnx3 (inj_eqd (Inode g)).
  case: (x3 =P x2) => [Dx2|_]; first by rewrite -Dx2 setU11 in Hpx2.
  by rewrite Dnx3 Enode.
case: {Hp}(HpE _ _ _ Hp Hpx2) => [x' Dx3 [p' Hp' Dp]].
  case/and3P: (HcE x2 (Adds u02 (Adds u12 (Adds x' p')))); split.
    rewrite -(mem2_maps (HeI x2)) !last_adds.
    case: (node_is_last x' p') => [[y' Hy'] Dny' <-]; simpl in y', Hy'.
    rewrite -Dp -Dx3 last_maps -Dny' /= /skip1 in Dnx1; simpl in Dp, Dx3.
    rewrite /= Dp Dx3 /skip1 /= Dnx0 (negbE Hx21).
    case: (x2 =d node y') Dnx1 => [|] Dnx1.
      by case/eqP: (Hx21); apply Inode.
    by rewrite (Inode g Dnx1) mem2_adds set11 setU11.
  simpl in Dp, Dx3; rewrite -(uniq_maps (HeI x2)) /= Dp Dx3.
  by rewrite {1}/setU1 negb_orb Hx10 Hpx0 Hpx1.
apply/and3P; split; auto; apply/clinkP; right; apply: subdE_inj.
  by rewrite /= /skip1 /= Dfx0 (negbE Hx21).
by rewrite /= /skip1 Dfx1 set11 Dfx2.
Qed.

Lemma euler_tree : forall g, jordan g -> forall x : g,
  negb (disjoint (cedge x) (fun y => clink y y || negb (cross_edge y))).
Proof.
move=> g Hj x0; apply/set0P => [Hx0].
move: (@root g (eqdf face)) (rootPx (Sface g)) => rf rfP.
suffice []: ~ (exists2 x, cedge x0 x
          & exists2 p, fpath edge x p /\ uniq (maps rf (Adds x p))
          & rf (node (face x)) = rf (last x p)).
  have Hp' := fconnect1 edge x0; rewrite Sedge in Hp'.
  case/connectP: Hp' => [p' Hp' Ep']; pose p := Adds (edge x0) p'.
  have: negb (uniq (maps rf (Adds x0 p))).
    by rewrite /= -{2}Ep' -(last_maps rf) mem_lastU.
  have: last x0 p = x0 by done.
  have: fpath edge x0 p by rewrite /= /eqdf set11.
  elim Dp: p {1 2 4}x0 => {p' Hp' Ep'} [|ex p' Hrec] // x.
  rewrite -{3}Dp /=; move/andP=> [Dex Hp] Ep.
  case Up: (uniq (maps rf p)); last by move: (negbI Up); rewrite Dp; eauto.
  rewrite andbT negb_elim Dp {Hrec}; move/mapsP=> [y Hpy Drfy].
  have Hx0x': cedge x0 ex by rewrite Sedge; apply/connectP; exists p'.
  case/splitPl: {p' Ep}Hpy Dp Hp => [p1 p2 Ep1]; rewrite -cat_adds; move=> Dp Hp.
  rewrite path_cat in Hp; case/andP: Hp => [Hp1 _].
  rewrite Dp maps_cat uniq_cat in Up; case/andP: Up => [Up1 _].
  by exists ex; last by exists p1; [ split | rewrite Ep1 -(eqP Dex) Eedge ].
case; move=> x Hx0x; set fx := face x; set nfx := node fx.
move=> [pe [Hpe Upe] Erpe].
have [pc [Hpc Epc] [Upc _ Hnpc]]:
    exists2 pc, path clink fx pc /\ last fx pc = nfx
         & let xpc := Adds fx pc in
           and3 (uniq xpc) (maps rf xpc =1 maps rf (Adds x pe))
            (forall y, xpc (face y) -> negb (belast fx pc y) -> last x pe = y).
  have Hfpcp: forall y (p : seq g), fpath face y p -> path clink y p.
    move=> y p; elim: p y => [|y' p Hrec] y //=; move/andP=> [Dy Hp].
    by rewrite (Hrec _ Hp) -(eqP Dy) clinkF.
  move: Hpe Upe Erpe {Hx0x}; clearbody nfx; rewrite {}/fx.
  elim: pe x => [|ex p Hrec] x /=.
    do 2 clear; rewrite (rfP x _ (fconnect1 _ _)).
    move/esym; move/(introT (rfP _ _)); case/connectP; move=> pc0.
    case/shortenP=> [pc Hpc Upc _] Epc; exists pc; split; auto=> {pc0 Epc}.
      move=> z; rewrite /setU1 orbF; case (rf (face x) =P z); first done.
      move=> H; apply/mapsP => [] [y Hy Dz]; case: H; rewrite -{z}Dz.
      exact (rfP _ _ (path_connect Hpc (setU1r _ Hy))).
    move=> y; rewrite /setU1 (inj_eqd (Iface g)).
    case: (x =P y) => [Dx|_] // H; case/splitPr: H Hpc {Upc} => [p1 p2].
    rewrite path_cat belast_cat mem_cat /= /setU /setU1.
    rewrite {2}/eqdf (inj_eqd (Iface g)) eqd_sym.
    by case (y =d last (face x) p1); rewrite /= ?orbT ?andbF.
  move/andP=> [Dex Hp]; move/andP=> [Hpx Up] Ep.
  case: {Hrec Hp Up}(Hrec _ Hp Up Ep) => [q2 [Hq2 Eq2] [Uq2 Hrq2 Hfq2]].
  case/connectP: (etrans (Sface _ _ x) (fconnect1 _ _)).
  move=> q0; case/shortenP=> q1 Hq1 Uq1 _ Eq1 {q0}.
  have Hrq1: forall y, Adds (face x) q1 y -> rf y = rf x.
    move=> y Hq1y; symmetry; apply: rfP; rewrite cface1.
    exact (path_connect Hq1 Hq1y).
  exists (cat q1 (Adds (face ex) q2)).
    rewrite path_cat last_cat Eq1 /=; split; last done.
    by rewrite (Hfpcp _ _ Hq1) -(Eedge g x) (eqP Dex) clinkN.
  split.
    rewrite -uniq_adds -cat_adds uniq_cat Uq1 Uq2 andbT.
    apply/hasP => [[y Hq2y Hq1y]]; case/idP: Hpx.
    apply: (etrans (esym (Hrq2 _))); apply/mapsP; exists y; auto.
    move=> y; rewrite maps_cat {1 2}/setU1 mem_cat /setU Hrq2 orbA; congr orb.
    apply/(mapsPx _ (Adds _ _) _)/eqP => [[z Hq1z <-]|<-]; first by symmetry; auto.
    by exists x; first by rewrite -{2}Eq1 mem_last.
  move=> y; rewrite -cat_add_last belast_cat belast_add_last last_add_last.
  rewrite -mem_adds cat_add_last -cat_adds !mem_cat /setU.
  have Hcq1: fcycle face (Adds (face x) q1).
    by rewrite /= -cats1 path_cat Eq1 Hq1 /= /eqdf set11.
  rewrite -!(fconnect_cycle Hcq1 (mem_last _ _)) Eq1 !(Sface g x) -cface1.
  by case Hyx: (cface y x); last by exact (Hfq2 y).
have Hnfx: cedge x nfx by rewrite Sedge -(Eface g x) /nfx fconnect1.
have Hfx: cedge x fx.
  suffice Hnx: (fclosed node (cedge x)) by rewrite (fclosed1 Hnx).
  apply: (intro_closed (Snode g)) => [y1 y2 Dy2 Hy1].
  apply: (connect_trans Hy1).
  move: (negbI (Hx0 y1)); rewrite -(eqP Dy2) /setI (connect_trans Hx0x Hy1).
  by rewrite /= negb_orb negb_elim /cross_edge; case/andP.
have Hpefx: negb (Adds x pe fx).
  move/andP: Upe => [Hpx _]; apply/orP=> [] [Dx|Hpfx].
    by case/andP: (Hx0 x); split; rewrite // {2}(eqP Dx) /fx clinkF.
  by case/mapsP: Hpx; exists fx; last by exact (esym (rfP _ _ (fconnect1 _ _))).
    case: (fx =P nfx) => [Dfx|Hfxn].
    case/andP: (Hx0 nfx); split; first by exact (connect_trans Hx0x Hnfx).
  by rewrite -{2}Dfx /nfx clinkN.
clear x0 Hx0 rf rfP Hx0x Upe Erpe.
have [qe [Hqe Eqe] Hqepe]: exists2 qe, fpath edge fx qe /\ last fx qe = nfx
                                     & negb (Adds fx qe (last x pe)).
  case: (connectP Hnfx); rewrite Sedge in Hnfx.
  move=> q0; case/shortenP=> q Hq Uq _ {q0} Eq.
  have Hqfx: Adds x q fx.
    apply: (etrans (esym _) Hfx); apply: fconnect_cycle; rewrite /= ?setU11 //.
    by rewrite -cats1 path_cat Hq Eq /= /eqdf /nfx /fx Eface set11.
  case/splitPl: {q Hnfx Hfx Hnpc}Hqfx Hq Uq Eq => [q1 qe Eq1].
  rewrite path_cat last_cat Eq1; move/andP=> [Hq1 Hqe] Uq Eqe.
  exists qe; [ by split | simpl; apply/norP; split ].
    by apply/eqP => [Dfx]; rewrite Dfx mem_last in Hpefx.
  move: {nfx npc Hpc Upc Epc Hfxn Eq1 Eqe Hqe}Eq1 Hpefx Hpe => <- {fx}.
  elim: q1 pe x Hq1 Uq => [|y q1 Hrec] pe x /=; first by rewrite setU11.
  move/andP=> [Dy Hq1]; move/andP=> [Hqx Uq]; case/norP.
  case: pe => [|y' pe] _ Hpeq1 /=.
    by rewrite /setU1 mem_cat /setU orbA in Hqx; case/norP: Hqx.
  move/andP=> [Dy' Hpe]; rewrite /eqdf (eqP Dy) in Dy'.
  by rewrite -(eqP Dy') in Hpeq1 Hpe |- *; auto.
suffice [qc [_ Eqc] Hqpc]:
    exists2 qc, path clink nfx qc /\ last nfx qc = fx & negb (has (Adds fx pc) qc).
  case/idP: Hqpc; rewrite has_sym /=.
  case: qc Eqc => [|y qc] Eqc; first by case Hfxn.
  by simpl in Eqc; rewrite -Eqc mem_last.
elim: qe {-5}fx Eqe Hqe Hqepe => [|y' qe Hrec] /=; first by exists (Seq0 g); auto.
move=> y Eqe; move/andP=> [Dy' Hqe]; move/norP=> [_ Hqepe].
case: {Hrec Hqe Eqe}(Hrec _ Eqe Hqe Hqepe) => [qc [Hqc Eqc] Hqcpc].
have Hny := fconnect1 node (face (edge y)); rewrite Snode Eedge in Hny.
case/connectP: Hny => [p Hp Ep]; apply (@proj2 (y <> nfx)).
elim: p {-3}y Hp Ep => [|z' p Hrec] z /=.
  move=> _ Dz; case Hpcz: (Adds fx pc z).
    case/idP: Hqepe; rewrite Dz in Hpcz; rewrite (Hnpc _ Hpcz).
      by rewrite (eqP Dy') setU11.
    apply/idP => [Hey]; case/hasP: Hqcpc.
    exists (edge y); [ move: (mem_last nfx qc) | by apply mem_belast ].
  rewrite Eqc (eqP Dy') /= /setU1; case: (nfx =P y') => [Dnfx|H] //.
    by rewrite lastI Epc Dnfx -(eqP Dy') -cats1 uniq_cat /= Hey andbC in Upc.
  split; first by move=> Dnfx; rewrite Dnfx -Epc mem_last in Hpcz.
  exists (add_last qc z).
    split; last by rewrite last_add_last.
    by rewrite -cats1 path_cat Hqc Eqc -(eqP Dy') Dz /= clinkF.
  by rewrite -cats1 has_cat /= -mem_adds Hpcz orbF.
move/andP=> [Dz' Hp] Ep {Hnpc y' qe Dy' Hqepe qc Hqc Ehqc Eqc Hqcpc}.
case: {y Hrec Hp Ep}(Hrec _ Hp Ep); move=> Hz'nfx [qc0 []].
case/shortenP=> [qc Hqc Uqc Hqc0] Eqc.
case Hpcqc: (has (Adds fx pc) qc).
  case/hasP; case/hasP: Hpcqc => [y Hqcy Hpcy]; exists y; auto.
  clear; case Hpcz: (Adds fx pc z) {qc0 Hqc0}.
  case/and3P: (Hj (Adds fx (cat pc qc))); split.
  - rewrite last_cat Epc Eqc -(eqP Dz') (finv_f (Inode g)) -/nfx -Epc.
    rewrite mem2_cat -orbA; apply/orP; left; simpl in Hpcz; case/orP: Hpcz.
      by move=> Dfx; case Hz'nfx; rewrite /nfx (eqP Dfx) (eqP Dz').
    case: pc Epc {Upc Hpcqc Hpc} => [|fx' pc] *; first by case Hfxn.
   - by rewrite /= mem2_last.
   by rewrite -cat_adds uniq_cat Upc Hpcqc; case/andP: Uqc.
  by rewrite path_cat Hpc Epc.
split; first by move=> Dz; rewrite Dz -Epc mem_last in Hpcz.
exists (add_last qc z).
  split; last by rewrite last_add_last.
  by rewrite -cats1 path_cat Hqc Eqc -(eqP Dz') /= clinkN.
by simpl in Hpcqc; rewrite -cats1 has_cat /= -mem_adds Hpcqc Hpcz.
Qed.

Theorem jordan_planar : forall g, jordan g -> planar g.
Proof.
move=> g Hg; elim: {g}(card g) {-4 5}g Hg (erefl (card g)) => [|n Hrec] g Hg Dn.
  have Hc0: forall a : set g, card a = 0.
    move=> a; apply: eqP; rewrite -leqn0 -Dn; apply max_card.
  by rewrite /planar /genus /genus_rhs /genus_lhs /n_comp Dn !Hc0.
  case Hg0: (set0b g); first by rewrite (eqnP Hg0) in Dn.
case/set0Pn: Hg0 => [x _].
case/set0Pn: (euler_tree Hg x); move=> z; move/andP=> [_ Hz].
rewrite /planar -(@genus_walkupE_eq _ z).
  by apply: (Hrec _ (jordan_walkupE Hg)); rewrite card_walkup Dn.
case/orP: Hz; [ case/clinkP=> Dz; left | by right ].
  by rewrite {2}Dz glinkN.
by rewrite -{2}Dz glinkF.
Qed.

Theorem planarP : forall g, reflect (jordan g) (planarb g).
Proof. move=> g; exact (iffP idP (@planar_jordan g) (@jordan_planar g)). Qed.

End Planarity.

Unset Implicit Arguments.

