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
Require Import part.
Require Import quiz.
Require Import quiztree.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Reducibility check for parts. We use a zipper structure to navigate the *)
(* part while searching for a reducible config. Once we detect a match for *)
(* the top arity range values, we walk the config quiz again to look for a *)
(* match for the other values (most of the time, though, the match spans   *)
(* only singleton ranges).                                                 *)
(*   We work here under the assumption that the map is plain and cubic,    *)
(* and that the quiz tree does not directly fit the map. We show that this *)
(* lifts to parts for which redpart returns true (for a fixed hub size).   *)

Section Redpart.

(* The function is only applied to the main quiz tree, but it is treated   *)
(* as a parameter here, to prevemt unwanted expansions.                    *)
Variables (qt : quiz_tree) (g : hypermap).

Hypothesis Hg : plain_cubic_pentagonal g.
Let HgF : pentagonal g := Hg.
Let De2 := plain_eq Hg.
Let Dnf := plain_eq' Hg.
Let Dn3 := cubic_eq Hg.
Let Dn2 := cubic_eq' Hg.

Remark Redpart_Dfn : forall n (x : g), n =d arity x -> x = iter n face x.
Proof. by move=> n x Dn; rewrite (eqP Dn) iter_face_arity. Qed.
Notation Dfn := Redpart_Dfn.

Hypothesis Hqt : forall y : g, negb (qzt_fit y qt).

Section RedpartRec.

(* The hub size must be in the qarity range.                               *)
Variable ahub : qarity.
Let nhub : nat := ahub.

Section Zpart.

(* A zipper part is a pair of a left and right part, with the left part  *)
(* reversed (not mirrored!), plus an index which identifies the dart     *)
(* represented by the part (there is also a nil index). These darts are  *)
(* the following:                                                        *)
(*  - the two node cycles that fall between the left and  right parts,   *)
(*    that is, that contain a dart from both the left spoke and right    *)
(*    spoke face. Their third dart is either the hub dart or a hat dart  *)
(*    the right part.                                                    *)
(*  - the (disjoint) qstepL and qstepR chains that run around the left   *)
(*    spoke face, counter-clockwise and clockwise, respectively, and end *)
(*    with hat darts (the left chain ends with the hat of the right part *)
(*    and conversely).                                                   *)
(* Note that this excludes the darts on the spoke face itself, which are *)
(* unreachable using quiz steps (they can only match the center triangle *)
(* and therefore don't occur in the recursive traversal).                *)
(*  We have to be careful with double steps, which may cross over a non  *)
(* existent dart in a corner case (the articulation has degree 6 and     *)
(* matches a spoke with range [5, 6])).                                  *)
(*  The two parts wrap around the hub exactly twice; the initial parts   *)
(* are available as parameters in this section, in case additional wrap  *)
(* around is needed.                                                     *)

Variable red_rec : part -> bool.

Hypothesis Hred_rec : forall (x : g) p,
  arity x = nhub -> exact_fitp x p -> negb (red_rec p).

Variables (p0l p0r : part) (x0 : g).
Hypothesis Dp0l : p0l = rev_part p0r.

Hypotheses (Hp0r : exact_fitp x0 p0r) (Hx0n : arity x0 = nhub).
Remark Zpart_Ep0r : size_part p0r = nhub.
Proof. by case/andP: Hp0r; move/eqP; rewrite Hx0n. Qed.
Notation Ep0r := Zpart_Ep0r.

Inductive zpart_loc : Set :=
  | Znil
  | Zhub   (* hub-side node cycle *)
  | Zhubl
  | Zhubr
  | Zhat   (* hat-side node cycle *)
  | Zhatl
  | Zhatr
  | Zfan0l (* the left step chain; Zfan0l is the last (hat) dart *)
  | Zfan1l
  | Zfan2l
  | Zfan3l
  | Zfan0r (* the right step chain *)
  | Zfan1r
  | Zfan2r
  | Zfan3r.

Definition zmove_def zi (x : g) :=
  match zi with
  | Znil => x
  | Zhub => x
  | Zhubl => node x
  | Zhubr => node (node x)
  | Zhat => node (edge (node (node x)))
  | Zhatl => edge (node (node x))
  | Zhatr => face (node (node x))
  | Zfan0l => face (edge (iter 2 (fun y => edge (node y)) (node x)))
  | Zfan1l => face (edge (iter 3 (fun y => edge (node y)) (node x)))
  | Zfan2l => face (edge (iter 4 (fun y => edge (node y)) (node x)))
  | Zfan3l => face (edge (iter 5 (fun y => edge (node y)) (node x)))
  | Zfan0r => edge (iter 2 face (node x))
  | Zfan1r => edge (iter 3 face (node x))
  | Zfan2r => edge (iter 4 face (node x))
  | Zfan3r => edge (iter 5 face (node x))
  end.

Definition zmove := nosimpl zmove_def.

Inductive zpart : Set := Zpart (zi : zpart_loc) (pl pr : part).

Definition zvalid pl pr := catrev_part pl pr = cat_part p0r p0r.

Definition zpvalid zp := let: Zpart _ pl pr := zp in zvalid pl pr.

Lemma zvalid_init : zvalid p0l p0r.
Proof. by rewrite /zvalid catrev_part_eq Dp0l rev_rev_part. Qed.

Definition shift_part p1 p2 := cat_part (take_part 1 p1) p2.

Notation p0ll := (drop_part 1 p0l) (only parsing).
Notation p0lr := (shift_part p0l p0r) (only parsing).
Notation p0rr := (drop_part 1 p0r) (only parsing).
Notation p0rl := (shift_part p0r p0l) (only parsing).

Lemma zvalid_initl : zvalid p0ll p0lr.
Proof.
move: Ep0r; rewrite -size_rev_part -Dp0l -Hx0n -orderSpred /zvalid -zvalid_init.
by case p0l.
Qed.

Lemma zvalid_initr : zvalid p0rl p0rr.
Proof.
by move: Ep0r; rewrite -Hx0n -orderSpred /zvalid -zvalid_init; case p0r.
Qed.

Lemma zvalid_fit : forall pl pr, zvalid pl pr -> fitp x0 (catrev_part pl pr).
Proof.
move=> pl pr Dplr; rewrite {pl pr}Dplr fitp_cat.
by case/andP: Hp0r; move/eqP=> <-; rewrite /= (iter_face_arity x0) andbb.
Qed.

Definition zproper zp := if zp is Zpart Znil _ _ then false else true.


Definition zporg zp := let: Zpart _ pl _ := zp in iter (size_part pl) face x0.

Definition zdart zp := let: Zpart zi _ _ := zp in zmove zi (zporg zp).

Definition zpfit x zp := zproper zp -> zdart zp = x.

Definition hub_range :=
  match ahub with
  | Qa5 => Pr55
  | Qa6 => Pr66
  | Qa7 => Pr77
  | Qa8 => Pr88
  | _   => Pr99
  end.

Definition zrange zp :=
  match zp with
  | Zpart Znil   _  _ => Pr59
  | Zpart Zhub   _  _ => hub_range
  | Zpart Zhubl  pl _ => get_spoke pl
  | Zpart Zhubr  _ pr => get_spoke pr
  | Zpart Zhatl  pl _ => get_spoke pl
  | Zpart Zhat   _ pr => get_hat pr
  | Zpart Zhatr  _ pr => get_spoke pr
  | Zpart Zfan0l _ pr => get_hat pr
  | Zpart Zfan1l pl _ => get_fan1l pl
  | Zpart Zfan2l pl _ => get_fan2l pl
  | Zpart Zfan3l pl _ => get_fan3l pl
  | Zpart Zfan0r pl _ => get_hat pl
  | Zpart Zfan1r pl _ => get_fan1r pl
  | Zpart Zfan2r pl _ => get_fan2r pl
  | Zpart Zfan3r pl _ => get_fan3r pl
  end.

Lemma zrange_dart : forall zp, zpvalid zp -> zrange zp (arity (zdart zp)).
Proof.
move=> [zi pl pr]; move/zvalid_fit.
case: zi; rewrite /= /zmove /= ?HgF //.
- move: (HgF x0); rewrite /zporg arity_iter_face Hx0n /nhub /hub_range.
  by case ahub.
- by case Dpl: pl; rewrite /zporg ?HgF //= Dnf fitp_catrev; case/and3P.
- rewrite fitp_catrev Dn2 arity_face.
  by case Dpr: pr; rewrite ?HgF //=; case/and3P.
- rewrite fitp_catrev -Dnf !Dn2 arity_face.
  by case Dpr: pr; rewrite ?HgF //=; case/and4P.
- rewrite -arity_face Enode.
  by case Dpl: pl; rewrite /zporg ?HgF //= Dnf fitp_catrev; case/and3P.
- rewrite fitp_catrev Dn2 !arity_face.
  by case Dpr: pr; rewrite ?HgF //=; case/and3P.
- rewrite fitp_catrev De2 -Dnf !Dn2 !arity_face.
  by case Dpr: pr; rewrite ?HgF //=; case/and4P.
- case: pl => [|s h|h f1|h f1 f2|h f1 f2 f3]; try move=> pl;
  rewrite ?HgF //= fitp_catrev /= Dnf arity_face;
  case/and5P=> _ Ds _ Hf1; try case/andP=> Hf2; try case/andP=> Hf3;
  by clear; rewrite (Dfn Ds) /= !Eface.
- case: pl => [|s h|h f1|h f1 f2|h f1 f2 f3]; try move=> pl;
  rewrite ?HgF //= fitp_catrev /= Dnf arity_face;
  by case/and5P=> _ Ds _ Hf1; case/andP=> Hf2 _; rewrite (Dfn Ds) /= !Eface.
- case: pl => [|s h|h f1|h f1 f2|h f1 f2 f3]; try move=> pl;
  rewrite ?HgF //= fitp_catrev /= Dnf arity_face;
  by case/and5P=> _ Ds _ Hf1 _; rewrite (Dfn Ds) /= !Eface.
- by case Dpl: pl; rewrite /= ?HgF // fitp_catrev /zporg /= Dnf; case/and4P.
- by case Dpl: pl; rewrite /= ?HgF // fitp_catrev /zporg /= Dnf; case/and5P.
- by case Dp: pl; rewrite /= ?HgF // fitp_catrev /zporg /= Dnf 3!andbA; case/and3P.
by case Dpl: pl; rewrite /= ?HgF // fitp_catrev /zporg /= Dnf 4!andbA; case/and3P.
Qed.

Definition zshiftl zi zp :=
  match zp with
  | Zpart _ (Pcons _ _ Pnil) _        => Zpart zi p0l p0r
  | Zpart _ (Pcons6 _ _ Pnil) _       => Zpart zi p0l p0r
  | Zpart _ (Pcons7 _ _ _ Pnil) _     => Zpart zi p0l p0r
  | Zpart _ (Pcons8 _ _ _ _ Pnil) _   => Zpart zi p0l p0r
  | Zpart _ (Pcons s h pl) pr         => Zpart zi pl (Pcons s h pr)
  | Zpart _ (Pcons6 h f1 pl) pr       => Zpart zi pl (Pcons6 h f1 pr)
  | Zpart _ (Pcons7 h f1 f2 pl) pr    => Zpart zi pl (Pcons7 h f1 f2 pr)
  | Zpart _ (Pcons8 h f1 f2 f3 pl) pr => Zpart zi pl (Pcons8 h f1 f2 f3 pr)
  | Zpart _ Pnil _ => Zpart zi (drop_part 1 p0l) (shift_part p0l p0r)
  end.

Definition zshiftr zi zp :=
  match zp with
  | Zpart _ _  (Pcons _ _ Pnil)       => Zpart zi p0l p0r
  | Zpart _ _  (Pcons6 _ _ Pnil)      => Zpart zi p0l p0r
  | Zpart _ _  (Pcons7 _ _ _ Pnil)    => Zpart zi p0l p0r
  | Zpart _ _  (Pcons8 _ _ _ _ Pnil)  => Zpart zi p0l p0r
  | Zpart _ pl (Pcons s h pr)         => Zpart zi (Pcons s h pl) pr
  | Zpart _ pl (Pcons6 h f1 pr)       => Zpart zi (Pcons6 h f1 pl) pr
  | Zpart _ pl (Pcons7 h f1 f2 pr)    => Zpart zi (Pcons7 h f1 f2 pl) pr
  | Zpart _ pl (Pcons8 h f1 f2 f3 pr) => Zpart zi (Pcons8 h f1 f2 f3 pl) pr
  | Zpart _ _  Pnil => Zpart zi (shift_part p0r p0l) (drop_part 1 p0r)
  end.

Lemma zpvalid_shiftl : forall zi zp, zpvalid zp -> zpvalid (zshiftl zi zp).
Proof.
move=> zi [zi' pl pr] {zi'}/=; move: zvalid_init zvalid_initl.
by case: pl => //= [s h|h f1|h f1 f2|h f1 f2 f3]; case.
Qed.

Lemma zproper_shiftl : forall zi zp,
  zproper (zshiftl zi zp) = if zi is Znil then false else true.
Proof.
move=> zi [zi' pl pr] {zi'}/=.
by case: pl => //= [s h|h f1|h f1 f2|h f1 f2 f3]; case.
Qed.

Lemma zpvalid_shiftr : forall zi zp, zpvalid zp -> zpvalid (zshiftr zi zp).
Proof.
move=> zi [zi' pl pr] {zi'}/=; move: zvalid_init zvalid_initr.
by case: pr => //= [s h|h f1|h f1 f2|h f1 f2 f3]; case.
Qed.

Lemma zproper_shiftr : forall zi zp,
  zproper (zshiftr zi zp) = if zi is Znil then false else true.
Proof.
move=> zi [zi' pl pr] {zi'}/=.
by case: pr => //= [s h|h f1|h f1 f2|h f1 f2 f3]; case.
Qed.

Lemma zdart_shiftl : forall zi zp,
  zdart (zshiftl zi zp) = zmove zi (edge (node (zporg zp))).
Proof.
move=> zi [zi' [|s h pl|h f1 pl|h f1 f2 pl|h f1 f2 f3 pl] pr];
 try by case: pl => *; rewrite /= Eface // Dp0l size_rev_part; case/andP: Hp0r;
        move/eqP=> <-; rewrite /= iter_face_arity.
rewrite /zshiftl /zdart /zporg size_drop_part Dp0l size_rev_part subn1 /=.
by rewrite -{2}[x0]iter_face_arity -orderSpred Ep0r -Hx0n /= Eface.
Qed.

Lemma zdart_shiftr : forall zi zp, zpvalid zp ->
  zdart (zshiftr zi zp) = zmove zi (face (zporg zp)).
Proof.
move=> zi [zi' pl pr] Hzp.
move: (congr1 size_part (etrans Hzp (esym zvalid_initr))).
move: {Hzp}(congr1 size_part Hzp).
rewrite !catrev_part_eq !size_cat_part !size_rev_part size_drop_part subn1.
rewrite -{1}(size_rev_part p0r) -Dp0l addnC Ep0r -Hx0n {1 3}/addn.
case: pr => [|s h pr|h f1 pr|h f1 f2 pr|h f1 f2 f3 pr];
 try by case Dpr: pr; rewrite //= f_iter => ->; rewrite iter_addn iter_face_arity.
rewrite /zshiftr /zdart /zporg add0n => _ ->; congr zmove.
by rewrite iter_addn -/(finv face x0) f_iter -iter_f (f_finv (Iface g)).
Qed.

Lemma zshiftl_eq : forall zi zi' pl pr, 1 < size_part pl ->
 zshiftl zi' (Zpart zi pl pr) = Zpart zi' (drop_part 1 pl) (shift_part pl pr).
Proof. by move=> zi zi'; case=> // [s h|h f1|h f1 f2|h f1 f2 f3]; case. Qed.

Lemma zshiftr_eq : forall zi zi' pl pr, 1 < size_part pr ->
 zshiftr zi' (Zpart zi pl pr) = Zpart zi' (shift_part pr pl) (drop_part 1 pr).
Proof. by move=> zi zi' pl; case=> // [s h|h f1|h f1 f2|h f1 f2 f3]; case. Qed.

Definition zfanL pr :=
  match pr with
  | Pcons Pr55 _ _   => Zfan0l
  | Pcons6 _ _ _     => Zfan1l
  | Pcons7 _ _ _   _ => Zfan2l
  | Pcons8 _ _ _ _ _ => Zfan3l
  | _                => Znil
  end.

Definition zfanR pl :=
  match pl with
  | Pcons Pr55 _ _   => Zfan0r
  | Pcons6 _ _ _     => Zfan1r
  | Pcons7 _ _ _ _   => Zfan2r
  | Pcons8 _ _ _ _ _ => Zfan3r
  | _                => Znil
  end.

Definition zstepL zp :=
  match zp with
  | Zpart Zhub _ _     => zshiftl Zhubl zp
  | Zpart Zhubl pl pr  => Zpart Zhat pl pr
  | Zpart Zhubr _ _    => zshiftr Zhubr zp
  | Zpart Zhat _ pr    => zshiftr (zfanL pr) zp
  | Zpart Zhatl pl pr  => Zpart (zfanR pl) pl pr
  | Zpart Zhatr pl pr  => Zpart Zhub pl pr
  | Zpart Zfan0l pl pr => Zpart Zhatr pl pr
  | Zpart Zfan1l pl pr => Zpart Zfan0l pl pr
  | Zpart Zfan2l pl pr => Zpart Zfan1l pl pr
  | Zpart Zfan3l pl pr => Zpart Zfan2l pl pr
  | Zpart _ pl pr      => Zpart Znil pl pr
  end.

Definition zstepR zp  :=
  match zp with
  | Zpart Zhub _ _     => zshiftr Zhubr zp
  | Zpart Zhubl _ _    => zshiftl Zhubl zp
  | Zpart Zhubr pl pr  => Zpart Zhat pl pr
  | Zpart Zhat pl pr   => Zpart (zfanR pl) pl pr
  | Zpart Zhatl pl pr  => Zpart Zhub pl pr
  | Zpart Zhatr _ pr   => zshiftr (zfanL pr) zp
  | Zpart Zfan0r _ _   => zshiftl Zhatl zp
  | Zpart Zfan1r pl pr => Zpart Zfan0r pl pr
  | Zpart Zfan2r pl pr => Zpart Zfan1r pl pr
  | Zpart Zfan3r pl pr => Zpart Zfan2r pl pr
  | Zpart _ pl pr      => Zpart Znil pl pr
  end.

Lemma zproper_stepL : forall zp, zproper (zstepL zp) -> zproper zp.
Proof. by do 2 case. Qed.

Lemma zpvalid_stepL : forall zp, zpvalid zp -> zpvalid (zstepL zp).
Proof.
do 2 case; move=> pl pr //; first [exact: zpvalid_shiftl | exact: zpvalid_shiftr].
Qed.

Lemma zdart_stepL : forall zp, zpvalid zp -> zpfit (qstepL (zdart zp)) (zstepL zp).
Proof.
rewrite /zstepL /qstepL; move=> [zi pl pr]; case Dzi: zi => // [] Hzp Hzpp;
  rewrite ?zdart_shiftr ?zdart_shiftl //= /zmove /= ?Dn3 //;
  try by rewrite ?Dnf ?De2 // ?Dn2 ?De2 ?Enode //.
- move/zvalid_fit: Hzp; rewrite fitp_catrev; rewrite zproper_shiftr in Hzpp.
  by case: pr Hzpp => //= [s h|h f1|h f1 f2|h f1 f2 f3] pr; try case: s => //=;
     clear; move/and3P=> [_ Ds _]; rewrite Dnf {2}[x0]lock (Dfn Ds) /= -lock;
     rewrite ?Eface !Dn2 !De2 -!Dnf Dn2 !Dnf.
move/zvalid_fit: Hzp.
by case: pl Hzpp => //= [s h|h f1|h f1 f2|h f1 f2 f3] pl; try case: s => //=;
   clear; rewrite fitp_catrev /=; move/and3P=> [_ Ds _];
   rewrite Dnf {1}[x0]lock (Dfn Ds) /= ?Eface -lock Dnf.
Qed.

Lemma zproper_stepR : forall zp, zproper (zstepR zp) -> zproper zp.
Proof. by do 2 case. Qed.

Lemma zpvalid_stepR : forall zp, zpvalid zp -> zpvalid (zstepR zp).
Proof.
do 2 case; move=> pl pr //; first [exact: zpvalid_shiftl | exact: zpvalid_shiftr].
Qed.

Lemma zdart_stepR : forall zp, zpvalid zp -> zpfit (qstepR (zdart zp)) (zstepR zp).
Proof.
rewrite /zstepR /qstepR; move=> [zi pl pr]; case Dzi: zi => // [] Hzp Hzpp;
  rewrite ?zdart_shiftr ?zdart_shiftl //= /zmove /= ?Dn3 ?De2 ?Dn3 ?Dnf //;
  first [ by rewrite Dn2 De2 | move/zvalid_fit: Hzp Hzpp ].
- by case: pl => //= [s h|h f1|h f1 f2|h f1 f2 f3] pl; try case: s => //=;
     rewrite fitp_catrev /=; move/and3P=> [_ Ds _] _;
     rewrite Dnf {1}[x0]lock (Dfn Ds) /= ?Eface -lock Dnf.
rewrite fitp_catrev zproper_shiftr -Dnf !Dn2.
by case: pr => //= [s h|h f1|h f1 f2|h f1 f2 f3] pr; try case: s => //=;
   move/and3P=> [_ Ds _] _; rewrite Dnf {2}[x0]lock (Dfn Ds) /= -lock ?Eface.
Qed.

Definition fitqa r qa :=
  match r, qa with
  | Pr55, Qa5 => true
  | Pr56, Qa6 => true
  | Pr66, Qa6 => true
  | Pr57, Qa7 => true
  | Pr67, Qa7 => true
  | Pr77, Qa7 => true
  | Pr58, Qa8 => true
  | Pr68, Qa8 => true
  | Pr78, Qa8 => true
  | Pr88, Qa8 => true
  | _,    _   => false
  end.

Lemma fitqa_proper : forall zp qa, fitqa (zrange zp) qa -> zproper zp.
Proof. by do 2 case. Qed.

Definition popqa r :=
  match r with
  | Pr56 => Pr55
  | Pr57 => Pr56
  | Pr58 => Pr57
  | Pr67 => Pr66
  | Pr68 => Pr67
  | Pr78 => Pr77
  | _    => Pr99
  end.

Definition topqa r :=
  match r with
  | Pr55 => Qa5
  | Pr56 => Qa6
  | Pr66 => Qa6
  | Pr57 => Qa7
  | Pr67 => Qa7
  | Pr77 => Qa7
  | Pr58 => Qa8
  | Pr68 => Qa8
  | Pr78 => Qa8
  | Pr88 => Qa8
  | _    => Qa9
  end.

Lemma fitqa_topqa : forall r qa,
  fitqa r qa = (qa <= 8) && ((qa : nat) =d (topqa r : nat)).
Proof. by do 2 case. Qed.

Lemma fitqa_popqa : forall r qa,
 fitqa r qa -> forall n, r n && (popqa r 9 || negb (popqa r n)) -> n = qa.
Proof. do 2 case=> //; clear; do 9 case=> //. Qed.

Definition zpfit_top zp := arity (zdart zp) = topqa (zrange zp).

(* Variants of the step functions that assume that (zpfit_top zp) holds. *)

Definition zfanLt pr :=
  match pr with
  | Pcons Pr55 _ _   => Zfan0l
  | Pcons Pr56 _ _   => Zfan1l
  | Pcons Pr66 _ _   => Zfan1l
  | Pcons6 _ _ _     => Zfan1l
  | Pcons7 _ _ _ _   => Zfan2l
  | Pcons8 _ _ _ _ _ => Zfan3l
  | _                => Znil
  end.

Definition zfanRt pl :=
  match pl with
  | Pcons Pr55 _ _   => Zfan0r
  | Pcons Pr56 _ _   => Zfan1r
  | Pcons Pr66 _ _   => Zfan1r
  | Pcons6 _ _ _     => Zfan1r
  | Pcons7 _ _ _ _   => Zfan2r
  | Pcons8 _ _ _ _ _ => Zfan3r
  | _                => Znil
  end.

Definition zstepLt zp : zpart :=
  match zp with
  | Zpart Zhub _ _     => zshiftl Zhubl zp
  | Zpart Zhubl pl pr  => Zpart Zhat pl pr
  | Zpart Zhubr _ _    => zshiftr Zhubr zp
  | Zpart Zhat _ pr    => zshiftr (zfanL pr) zp
  | Zpart Zhatl pl pr  => Zpart (zfanRt pl) pl pr
  | Zpart Zhatr pl pr  => Zpart Zhub pl pr
  | Zpart Zfan0l pl pr => Zpart Zhatr pl pr
  | Zpart Zfan1l pl pr => Zpart Zfan0l pl pr
  | Zpart Zfan2l pl pr => Zpart Zfan1l pl pr
  | Zpart Zfan3l pl pr => Zpart Zfan2l pl pr
  | Zpart _ pl pr      => Zpart Znil pl pr
  end.

Definition zstepRt zp :=
  match zp with
  | Zpart Zhub _ _     => zshiftr Zhubr zp
  | Zpart Zhubl _ _    => zshiftl Zhubl zp
  | Zpart Zhubr pl pr  => Zpart Zhat pl pr
  | Zpart Zhat pl pr   => Zpart (zfanR pl) pl pr
  | Zpart Zhatl pl pr  => Zpart Zhub pl pr
  | Zpart Zhatr _ pr   => zshiftr (zfanLt pr) zp
  | Zpart Zfan0r _ _   => zshiftl Zhatl zp
  | Zpart Zfan1r pl pr => Zpart Zfan0r pl pr
  | Zpart Zfan2r pl pr => Zpart Zfan1r pl pr
  | Zpart Zfan3r pl pr => Zpart Zfan2r pl pr
  | Zpart _ pl pr      => Zpart Znil pl pr
  end.

Lemma zproper_stepLt : forall zp, zproper (zstepLt zp) -> zproper zp.
Proof. by do 2 case. Qed.

Lemma zpvalid_stepLt : forall zp, zpvalid zp -> zpvalid (zstepLt zp).
Proof.
do 2 case; move=> pl pr //; first [exact: zpvalid_shiftl |exact: zpvalid_shiftr].
Qed.

Lemma zdart_stepLt : forall zp,
  zpfit_top zp -> zpvalid zp -> zpfit (qstepL (zdart zp)) (zstepLt zp).
Proof.
move=> [zi pl pr] Hzpt Hzp.
case: zi {Hzpt}(esym Hzpt) {Hzp}(zdart_stepL Hzp) (Hzp) => //.
rewrite /zpfit_top /= /zmove /= /qstepL -arity_face Enode.
move=> H; rewrite {H}(Dfn (introT eqP H)).
by case: pl => //; case=> //= h pl _; rewrite /zpfit /= /zmove /= !Eface !Dnf.
Qed.

Lemma zproper_stepRt : forall zp, zproper (zstepRt zp) -> zproper zp.
Proof. by do 2 case. Qed.

Lemma zpvalid_stepRt : forall zp, zpvalid zp -> zpvalid (zstepRt zp).
Proof.
do 2 case; move=> pl pr //; first [exact: zpvalid_shiftl | exact: zpvalid_shiftr].
Qed.

Lemma zdart_stepRt : forall zp, zpfit_top zp -> zpvalid zp ->
  zpfit (qstepR (zdart zp)) (zstepRt zp).
Proof.
move=> [zi pl pr] Hzpt Hzp; case: zi Hzp {Hzpt}(esym Hzpt) (zdart_stepR Hzp) => //.
move=> Hzp; rewrite /zpfit_top /zstepR /zstepRt /zpfit !zdart_shiftr //.
rewrite !zproper_shiftr; case: pr Hzp => //= [s h pr] Hzp.
rewrite /zmove /= Dn2 !arity_face /qstepR.
move=> H; move: {H}(congr1 (iter 4 (comp edge node)) (Dfn (introT eqP H))).
rewrite /comp /=; case: s Hzp => //= _;
by rewrite !Eface => <- _ _; rewrite !De2 Dnf Dn2 De2.
Qed.

(* Updating a part. *)

Definition red_pcons pc r (pr : part) :=
  let rpc r' := red_rec (take_part nhub (cat_part (pc r' pr) p0r)) in
  match r with
  | Pr56 => rpc Pr55
  | Pr57 => rpc Pr56
  | Pr58 => rpc Pr57
  | Pr67 => rpc Pr66
  | Pr68 => rpc Pr67
  | Pr78 => rpc Pr77
  | _    => true
  end.

Lemma red_pcons_fit : forall pc j, part_update pc j ->
    forall r pl pr, zvalid pl (pc r pr) ->
    forall qa, fitqa r qa -> red_pcons pc r pr ->
  arity (j g (iter (size_part pl) face x0)) = qa.
Proof.
move=> pc df Hpc r pl pr Hpl qa Hqa Hpcr; apply: (fitqa_popqa Hqa).
move: (zvalid_fit Hpl); rewrite fitp_catrev.
case/andP; set (y := iter (size_part pl) face x0); move=> _ Hypr.
case: (Hpc r pr) => [Epr H]; case/(H g y): {H}Hypr => [Hyr Hypr'].
rewrite Hyr; apply/norP; rewrite negb_elim; move=> [Hr Hyr'].
set p0r' := cat_part (pc (popqa r) pr) p0r.
case Hp0r': (exact_fitp y (take_part nhub p0r')).
  have Ey: arity y = nhub by rewrite /y arity_iter_face.
  by case/idP: (Hred_rec Ey Hp0r'); rewrite /p0r'; case: (r) Hr Hpcr.
have Ep0r' := cat_take_drop_part nhub p0r'; move/andP: Hp0r => [_ Hx0p0r].
case/andP: Hp0r'; split.
  rewrite /y arity_iter_face eqd_sym Hx0n.
  move: (introT eqP (congr1 size_part Ep0r')); rewrite size_cat_part {2 3}/p0r'.
  by rewrite size_drop_part size_cat_part Ep0r subn_addl addnC eqn_addl.
suffice Hp0r': fitp y p0r' by rewrite -Ep0r' fitp_cat in Hp0r'; case/andP: Hp0r'.
rewrite /p0r' fitp_cat Hypr' // /y -iter_addn addnC.
case: (Hpc (popqa r) pr) => Epr' _; rewrite {}Epr' -{}Epr.
rewrite -(size_rev_part pl) -size_cat_part -catrev_part_eq Hpl size_cat_part.
by rewrite Ep0r -Hx0n iter_addn !iter_face_arity.
Qed.

Definition red_popr_spoke pr :=
  if pr is Pcons s h p then red_pcons (fun s' => Pcons s' h) s p else true.

Lemma red_popr_spoke_fit : forall pl pr, zvalid pl pr ->
   forall qa, fitqa (get_spoke pr) qa -> red_popr_spoke pr -> 
 arity (edge (iter (size_part pl) face x0)) = qa.
Proof.
move=> pl; case=> // [s h pr|h f1 pr|h f1 f2 pr|h f1 f2 f3 pr];
try exact: (red_pcons_fit (updatePs h));
by  move/zvalid_fit; rewrite fitp_catrev /=; case/and3P=> _; move/eqP=> <- _ [].
Qed.

Definition red_popr_hat pr :=
  match pr with
  | Pcons s h p         => red_pcons (fun h' => Pcons s h') h p
  | Pcons6 h f1 p       => red_pcons (fun h' => Pcons6 h' f1) h p
  | Pcons7 h f1 f2 p    => red_pcons (fun h' => Pcons7 h' f1 f2) h p
  | Pcons8 h f1 f2 f3 p => red_pcons (fun h' => Pcons8 h' f1 f2 f3) h p
  | _                   => true
  end.

Lemma red_popr_hat_fit : forall pl pr, zvalid pl pr ->
   forall qa, fitqa (get_hat pr) qa -> red_popr_hat pr ->
 arity (edge (iter 2 face (edge (iter (size_part pl) face x0)))) = qa.
Proof.
move=> pl; case=> // [s h pr|h f1 pr|h f1 f2 pr|h f1 f2 f3 pr].
- exact: (red_pcons_fit (updatePh s)).
- exact: (red_pcons_fit (updateP6h f1)).
- exact: (red_pcons_fit (updateP7h f1 f2)).
exact: (red_pcons_fit (updateP8h f1 f2 f3)).
Qed.

Definition red_popl_spoke pl pr :=
  if pl is Pcons s h _ then red_pcons (fun s' => Pcons s' h) s pr else true.

Lemma red_popl_spoke_fit : forall pl pr, zvalid pl pr ->
    forall qa, fitqa (get_spoke pl) qa -> red_popl_spoke pl pr ->
  arity (node (iter (size_part pl) face x0)) = qa.
Proof.
case=> // [s h pl|h f1 pl|h f1 f2 pl|h f1 f2 f3 pl] pr; rewrite /zvalid /= Dnf;
try exact: (red_pcons_fit (updatePs h));
by  move/zvalid_fit; rewrite fitp_catrev /=; case/and3P=> _; move/eqP=> <- _ [].
Qed.

Definition red_popl_hat pl pr :=
  match pl with
  | Pcons s h _         => red_pcons (fun r => Pcons s r) h pr
  | Pcons6 h f1 _       => red_pcons (fun r => Pcons6 r f1) h pr
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 r f1 f2) h pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 r f1 f2 f3) h pr
  | _                   => true
  end.

Lemma red_popl_hat_fit : forall pl pr, zvalid pl pr ->
    forall qa, fitqa (get_hat pl) qa -> red_popl_hat pl pr ->
  arity (edge (iter 2 face (node (iter (size_part pl) face x0)))) = qa.
Proof.
case=> //= [s h|h f1|h f1 f2|h f1 f2 f3] pl pr; rewrite Dnf /zvalid /=.
- exact: (red_pcons_fit (updatePh _)).
- exact: (red_pcons_fit (updateP6h _)).
- exact: (red_pcons_fit (updateP7h _ _)).
exact: (red_pcons_fit (updateP8h _ _ _)).
Qed.

Definition red_popl_fan1l pl pr :=
  match pl with
  | Pcons6 h f1 _       => red_pcons (fun r => Pcons6 h r) f1 pr
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 h f1 r) f2 pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h f1 f2 r) f3 pr
  | _                   => true
  end.

Definition red_popl_fan2l pl pr :=
  match pl with
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 h r f2) f1 pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h f1 r f3) f2 pr
  | _                   => true
  end.

Definition red_popl_fan3l pl pr :=
  match pl with
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h r f2 f3) f1 pr
  | _                   => true
  end.

Definition red_popl_fan1r pl pr :=
  match pl with
  | Pcons6 h f1 _       => red_pcons (fun r => Pcons6 h r) f1 pr
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 h r f2) f1 pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h r f2 f3) f1 pr
  | _                   => true
  end.

Definition red_popl_fan2r pl pr :=
  match pl with
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 h f1 r) f2 pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h f1 r f3) f2 pr
  | _                   => true
  end.

Definition red_popl_fan3r pl pr :=
  match pl with
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h f1 f2 r) f3 pr
  | _                   => true
  end.

Lemma red_popl_fan1l_fit : forall pl pr, zvalid pl pr ->
    forall qa, fitqa (get_fan1l pl) qa -> red_popl_fan1l pl pr ->
  arity (zdart (Zpart Zfan1l pl pr)) = qa.
Proof.
case=> // [h f1|h f1 f2|h f1 f2 f3] pl pr; rewrite /zvalid /=;
  move=> H; move/zvalid_fit: H (H); rewrite fitp_catrev /=; case/and3P=> _ Dn _;
  rewrite /zmove /= Dnf (Dfn Dn) /= ?Eface arity_face.
- exact: (red_pcons_fit (updateP6f1 _)).
- exact: (red_pcons_fit (updateP7f2 _ _)).
exact: (red_pcons_fit (updateP8f3 _ _ _)).
Qed.

Lemma red_popl_fan2l_fit : forall pl pr, zvalid pl pr ->
    forall qa, fitqa (get_fan2l pl) qa -> red_popl_fan2l pl pr ->
  arity (zdart (Zpart Zfan2l pl pr)) = qa.
Proof.
case=> // [h f1 f2|h f1 f2 f3] pl pr; rewrite /zvalid /=;
  move=> H; move/zvalid_fit: H (H); rewrite fitp_catrev /=; case/and3P=> _ Dn _;
  rewrite /zmove /= Dnf (Dfn Dn) /= ?Eface arity_face.
- exact: (red_pcons_fit (updateP7f1 _ _)).
exact: (red_pcons_fit (updateP8f2 _ _ _)).
Qed.

Lemma red_popl_fan3l_fit : forall pl pr, zvalid pl pr ->
    forall qa, fitqa (get_fan3l pl) qa -> red_popl_fan3l pl pr ->
  arity (zdart (Zpart Zfan3l pl pr)) = qa.
Proof.
case=> // [h f1 f2 f3] pl pr; rewrite /zvalid /=;
  move=> H; move/zvalid_fit: H (H); rewrite fitp_catrev /=; case/and3P=> _ Dn _;
  rewrite /zmove /= Dnf (Dfn Dn) /= ?Eface arity_face.
exact: (red_pcons_fit (updateP8f1 _ _ _)).
Qed.

Lemma red_popl_fan1r_fit : forall pl pr, zvalid pl pr ->
    forall qa, fitqa (get_fan1r pl) qa -> red_popl_fan1r pl pr ->
  arity (zdart (Zpart Zfan1r pl pr)) = qa.
Proof.
case=> // [h f1|h f1 f2|h f1 f2 f3] pl pr; rewrite /zvalid /= /zmove /= Dnf.
- exact: (red_pcons_fit (updateP6f1 _)).
- exact: (red_pcons_fit (updateP7f1 _ _)).
exact: (red_pcons_fit (updateP8f1 _ _ _)).
Qed.

Lemma red_popl_fan2r_fit : forall pl pr, zvalid pl pr ->
    forall qa : qarity, fitqa (get_fan2r pl) qa -> red_popl_fan2r pl pr ->
 arity (zdart (Zpart Zfan2r pl pr)) = qa.
Proof.
case=> // [h f1 f2|h f1 f2 f3] pl pr; rewrite /zvalid /= /zmove /= Dnf.
  exact: (red_pcons_fit (updateP7f2 _ _)).
exact: (red_pcons_fit (updateP8f2 _ _ _)).
Qed.

Lemma red_popl_fan3r_fit : forall pl pr, zvalid pl pr ->
    forall qa, fitqa (get_fan3r pl) qa -> red_popl_fan3r pl pr ->
  arity (zdart (Zpart Zfan3r pl pr)) = qa.
Proof.
case=> // [h f1 f2 f3] pl pr; rewrite /zvalid /= /zmove /= Dnf.
exact: (red_pcons_fit (updateP8f3 _ _ _)).
Qed.

Definition red_pop zp :=
  match zp with
  | Zpart Zhubl  pl pr => red_popl_spoke pl pr
  | Zpart Zhubr  pl pr => red_popr_spoke pr
  | Zpart Zhatl  pl pr => red_popl_spoke pl pr
  | Zpart Zhat   pl pr => red_popr_hat pr
  | Zpart Zhatr  pl pr => red_popr_spoke pr
  | Zpart Zfan0l pl pr => red_popr_hat pr
  | Zpart Zfan1l pl pr => red_popl_fan1l pl pr
  | Zpart Zfan2l pl pr => red_popl_fan2l pl pr
  | Zpart Zfan3l pl pr => red_popl_fan3l pl pr
  | Zpart Zfan0r pl pr => red_popl_hat pl pr
  | Zpart Zfan1r pl pr => red_popl_fan1r pl pr
  | Zpart Zfan2r pl pr => red_popl_fan2r pl pr
  | Zpart Zfan3r pl pr => red_popl_fan3r pl pr
  | _                  => true
  end.

Lemma red_pop_fit : forall zp, zpvalid zp -> forall qa, fitqa (zrange zp) qa ->
  red_pop zp -> arity (zdart zp) = qa.
Proof.
case; case=> //= pl pr; rewrite /zmove /=; try exact: red_popl_spoke_fit.
- by clear; rewrite arity_iter_face Hx0n /hub_range /nhub; case ahub; case.
- rewrite Dn2 arity_face; exact: red_popr_spoke_fit.
- rewrite -Dnf !Dn2 arity_face; exact: red_popr_hat_fit.
- rewrite -arity_face Enode; exact: red_popl_spoke_fit.
- rewrite Dn2 !arity_face; exact: red_popr_spoke_fit.
- rewrite De2 -Dnf !Dn2 !arity_face; exact: red_popr_hat_fit.
- exact: red_popl_fan1l_fit.
- exact: red_popl_fan2l_fit.
- exact: red_popl_fan3l_fit.
- exact: red_popl_hat_fit.
- exact: red_popl_fan1r_fit.
- exact: red_popl_fan2r_fit.
exact: red_popl_fan3r_fit.
Qed.

Fixpoint fitqzp (zp : zpart) (q : question) {struct q} : bool :=
  match q with
  | Qask0 =>
      true
  | Qask1 qa =>
      fitqa (zrange zp) qa
  | QaskL qa ql =>
      if fitqa (zrange zp) qa then fitqzp (zstepLt zp) ql else false
  | QaskR qa qr =>
      if fitqa (zrange zp) qa then fitqzp (zstepRt zp) qr else false
  | QaskLR qa ql qr =>
      if fitqa (zrange zp) qa then
        if fitqzp (zstepL zp) ql then fitqzp (zstepR zp) qr else false
      else false
  | QaskLL qa ql =>
      let zpl := zstepL zp in
      if fitqa (zrange zpl) qa then fitqzp (zstepL zpl) ql else false
  | QaskRR qa qr =>
      let zpr := zstepR zp in
      if fitqa (zrange zpr) qa then fitqzp (zstepR zpr) qr else false
  end.

Fixpoint red_popqzp (zp : zpart) (q : question) {struct q} : bool :=
  match q with
  | Qask0 =>
      true
  | Qask1 _ =>
      red_pop zp
  | QaskL qa ql =>
      red_pop zp && red_popqzp (zstepLt zp) ql
  | QaskR qa qr =>
      red_pop zp && red_popqzp (zstepRt zp) qr
  | QaskLR qa ql qr =>
      and3b (red_pop zp) (red_popqzp (zstepL zp) ql) (red_popqzp (zstepR zp) qr)
  | QaskLL qa ql =>
      let zpl := zstepL zp in red_pop zpl && red_popqzp (zstepL zpl) ql
  | QaskRR qa qr =>
      let zpr := zstepR zp in red_pop zpr && red_popqzp (zstepR zpr) qr
  end.

Lemma fitqzp_proper : forall zp q, fitqzp zp q -> Qask0 = q \/ zproper zp.
Proof. by move=> zp q; case Dq: q; auto=> Hzp; right; case: zp Hzp; case. Qed.

Lemma fitqzp_fit : forall zp q,
  fitqzp zp q -> red_popqzp zp q -> zpvalid zp -> fitq (zdart zp) q.
Proof.
move=> zp q; elim: q zp => //=.
- move=> qa zp Hqa Hzpp Hzp.
  by apply/eqP; rewrite /= (red_pop_fit Hzp Hqa Hzpp).
- move=> qa ql Hrec zp.
  case Hqa: (fitqa (zrange zp) qa) => // Hql; move/andP=> [Hzpp Hzppl] Hzp.
  have Dqa := red_pop_fit Hzp Hqa Hzpp; rewrite /fitq /= eqseq_adds Dqa set11.
  case: (fitqzp_proper Hql) => [<-|Hzp'] //.
  rewrite fitqa_topqa in Hqa; case/andP: Hqa => [_ Eqa].
  rewrite {qa Eqa}(eqP Eqa) in Dqa.
  by rewrite -zdart_stepLt //; apply: Hrec => //; apply zpvalid_stepLt.
- move=> qa qr Hrec zp.
  case Hqa: (fitqa (zrange zp) qa) => [] // Hqr; move/andP=> [Hzpp Hzppr] Hzp.
  have Dqa := (red_pop_fit Hzp Hqa Hzpp); rewrite /fitq /= eqseq_adds Dqa set11.
  case: (fitqzp_proper Hqr) => [<-|Hzp'] //.
  rewrite fitqa_topqa in Hqa; case/andP: Hqa => [_ Eqa].
  rewrite {qa Eqa}(eqP Eqa) in Dqa.
  by rewrite -zdart_stepRt //; apply: Hrec => //; apply zpvalid_stepRt.
- move=> qa ql Hrecl qr Hrecr zp.
  case Hqa: (fitqa (zrange zp) qa) => //.
  case Hql: (fitqzp (zstepL zp) ql) => // Hqr.
  move/and3P=> [Hzpp Hzppl Hzppr] Hzp.
  rewrite /fitq /= eqseq_adds fitq_cat (red_pop_fit Hzp Hqa Hzpp) set11 /=.
  apply/andP; split.
    case: (fitqzp_proper Hql) => [<-|Hzpl] //.
    by rewrite -zdart_stepL //; apply: Hrecl => //; apply zpvalid_stepL.
  case: (fitqzp_proper Hqr) => [<-|Hzpr] //.
  by rewrite -zdart_stepR //; apply: Hrecr => //; apply: zpvalid_stepR.
- move=> qa ql Hrec zp; set zpl := zstepL zp.
  case Hqa: (fitqa (zrange zpl) qa) => // Hql; move/andP=> [Hzplp Hzpllp] Hzp.
  rewrite /fitq /= eqseq_adds -arity_face Enode.
  rewrite -zdart_stepL // -/zpl; last by case: (zpl) Hqa; case.
  move/zpvalid_stepL: Hzp => Hzpl.
  rewrite /zpl (red_pop_fit Hzpl Hqa Hzplp) set11.
  case: (fitqzp_proper Hql) => [<-|Hzpll] //.
  by rewrite -zdart_stepL //; apply: Hrec => //; apply zpvalid_stepL.
move=> qa ql Hrec zp; set zpr := zstepR zp.
case Hqa: (fitqa (zrange zpr) qa) => // Hqr; move/andP=> [Hzprp Hzprrp] Hzp.
rewrite /fitq /= eqseq_adds -zdart_stepR // -/zpr; last by case: (zpr) Hqa; case.
move/zpvalid_stepR: Hzp => Hzpr; rewrite /zpr (red_pop_fit Hzpr Hqa Hzprp) set11.
case: (fitqzp_proper Hqr) => [<-|Hzprr] //.
by rewrite -zdart_stepR //; apply: Hrec => //; apply zpvalid_stepR.
Qed.

Section RedQztLeaf.

Variable zp1 zp2 zp3 : zpart.

Fixpoint red_qzt_leaf (qtl : quiz_tree) : bool :=
  if qtl is QztLeaf q1 q2 q3 qtl' then
    if fitqzp zp3 q3 then
      if fitqzp zp2 q2 then
        if fitqzp zp1 q1 then 
          and3b (red_popqzp zp1 q1) (red_popqzp zp2 q2) (red_popqzp zp3 q3)
        else red_qzt_leaf qtl'
      else red_qzt_leaf qtl'
    else red_qzt_leaf qtl'
  else false.

Lemma red_qzt_leaf_fit : forall qtl, red_qzt_leaf qtl ->
    qzt_proper qtl
 /\ (forall x : g,
       zpfit (qstepR x) zp1               -> zpvalid zp1 ->
       zpfit (qstepR (node x)) zp2        -> zpvalid zp2 ->
       zpfit (qstepR (node (node x))) zp3 -> zpvalid zp3 ->
    ~ negb (qzt_fitl x qtl)).
Proof.
move=> qtl Hqtl; split; first by case: qtl Hqtl.
move=> x Hxzp1 Hzp1 Hxzp2 Hzp2 Hxzp3 Hzp3; case/idP.
elim: qtl Hqtl => //= [q1 q2 q3 qtl Hrec].
case Hqtl: (red_qzt_leaf qtl); first by rewrite Hrec ?orbT.
case Hq3: (fitqzp zp3 q3) => //; case Hq2: (fitqzp zp2 q2) => //.
case Hq1: (fitqzp zp1 q1) => //; move/and3P=> [Hzp1p Hzp2p Hzp3p].
apply/orP; left; apply/and3P; split.
- case: (fitqzp_proper Hq1) => [<-|Hzp1'] //; rewrite -Hxzp1 //; exact: fitqzp_fit.
- case: (fitqzp_proper Hq2) => [<-|Hzp2'] //; rewrite -Hxzp2 //; exact: fitqzp_fit.
case: (fitqzp_proper Hq3) => [<-|Hzp3'] //; rewrite -Hxzp3 //; exact: fitqzp_fit.
Qed.

End RedQztLeaf.

Definition qzt_getr r qt :=
  if qt is QztNode qt5 qt6 qt7 qt8 then
    match r with
    | Pr55 => qt5
    | Pr56 => qt6
    | Pr66 => qt6
    | Pr57 => qt7
    | Pr67 => qt7
    | Pr77 => qt7
    | Pr58 => qt8
    | Pr68 => qt8
    | Pr78 => qt8
    | Pr88 => qt8
    | _    => QztNil
    end
  else QztNil.

Lemma qzt_getr_fit : forall r qt', qzt_proper (qzt_getr r qt') ->
   let qa := topqa r in
 and3 (fitqa r qa) (qzt_get1 qa qt' = qzt_getr r qt') (qzt_proper qt').
Proof. by move=> r; case=> // [qt5 qt6 qt7 qt8]; case: r => //; split. Qed.

Lemma redpart_no_qzt_fitl : forall (y : g) (qa1 qa2 qa3 : qarity),
    arity y = qa1 -> arity (node y) = qa2 -> arity (node (node y)) = qa3 ->
  negb (qzt_fitl y (qzt_get3 qa1 qa2 qa3 qt)).
Proof.
move=> y qa1 qa2 qa3 Dqa1 Dqa2 Dqa3; move: (Hqt y).
by rewrite /qzt_fit /qzt_fita Dqa1 Dqa2 Dqa3 !qarity_of_qarity !set11.
Qed.

Fixpoint red_zpart_rec (zp : zpart) (d : nat) {struct d} : bool :=
  if d is S d' then
    let zp' := zshiftr Zhub zp in
    let: Zpart _ pl pr := zp in
    let s := get_spoke pr in
    let sqt := qzt_getr s (qzt_truncate qt) in
    if (if qzt_proper sqt then
          let: Zpart _ pl' pr':= zp' in
          let sl := get_spoke pl in
          if red_qzt_leaf (Zpart Zhubr pl' pr')
                          (zshiftl Zhubl zp)
                          (Zpart Zhat pl pr)
                          (qzt_getr s (qzt_getr sl (qzt_get1 ahub qt)))
            then red_popr_spoke pr && red_popl_spoke pl pr else
          if red_qzt_leaf (Zpart (zfanLt pr) pl' pr') zp
                          (Zpart (zfanRt pl) pl pr)
                          (qzt_getr (get_hat pr)
                          (qzt_getr sl sqt))
            then
              and3b (red_popr_hat pr) (red_popl_spoke pl pr) (red_popr_spoke pr)
            else
          let zpnil := Zpart Znil pl' pr' in
          match pr with
          | Pcons Pr55 h _ =>
            if red_qzt_leaf (Zpart Zhatr pl' pr')
                            (Zpart Zhatl pl pr) zpnil
                            (qzt_getr (get_hat pr')
                            (qzt_getr h sqt))
              then red_popr_hat pr' && red_popr_hat pr else false
          | Pcons6 h f1 _ =>
            if red_qzt_leaf (Zpart Zfan0l pl' pr')
                            (Zpart Zhatl pl pr)
                            zpnil
                            (qzt_getr f1 (qzt_getr h sqt))
            then red_popl_fan1r pl' pr' && red_popr_hat pr else
            if red_qzt_leaf (Zpart Zhatr pl' pr')
                            (Zpart Zfan0r pl' pr')
                            zpnil
                            (qzt_getr (get_hat pr') (qzt_getr f1 sqt))
            then red_popr_hat pr' && red_popl_fan1r pl' pr' else false
          | Pcons7 h f1 f2 _ =>
            if red_qzt_leaf (Zpart Zfan1l pl' pr')
                            (Zpart Zhatl pl pr)
                            zpnil
                            (qzt_getr f1 (qzt_getr h sqt))
              then red_popl_fan1r pl' pr' && red_popr_hat pr else
            if red_qzt_leaf (Zpart Zfan0l pl' pr')
                            (Zpart Zfan0r pl' pr')
                            zpnil
                           (qzt_getr f2 (qzt_getr f1 sqt))
              then red_popl_fan2r pl' pr' && red_popl_fan1r pl' pr' else
            if red_qzt_leaf (Zpart Zhatr pl' pr')
                            (Zpart Zfan1r pl' pr')
                            zpnil
                            (qzt_getr (get_hat pr') (qzt_getr f2 sqt))
              then red_popr_hat pr' && red_popl_fan2r pl' pr' else false
          | Pcons8 h f1 f2 f3 _ =>
            if red_qzt_leaf (Zpart Zfan2l pl' pr')
                            (Zpart Zhatl pl pr)
                            zpnil
                            (qzt_getr f1 (qzt_getr h sqt))
              then red_popl_fan1r pl' pr' && red_popr_hat pr else
            if red_qzt_leaf (Zpart Zfan1l pl' pr')
                            (Zpart Zfan0r pl' pr')
                            zpnil
                            (qzt_getr f2 (qzt_getr f1 sqt))
              then red_popl_fan2r pl' pr' && red_popl_fan1r pl' pr' else
            if red_qzt_leaf (Zpart Zfan0l pl' pr')
                            (Zpart Zfan1r pl' pr')
                             zpnil
                            (qzt_getr f3 (qzt_getr f2 sqt))
              then red_popl_fan3r pl' pr' && red_popl_fan2r pl' pr' else
            if red_qzt_leaf (Zpart Zhatr pl' pr')
                            (Zpart Zfan2r pl' pr')
                            zpnil
                            (qzt_getr (get_hat pr') (qzt_getr f3 sqt))
              then red_popr_hat pr' && red_popl_fan3r pl' pr' else false
          | _ =>
            false
          end
     else false) then true
   else red_zpart_rec zp' d'
  else false.

Definition red_zpart := red_zpart_rec (Zpart Zhub p0ll p0lr) nhub.

Lemma not_red_zpart : negb red_zpart.
Proof.
apply negbI; rewrite /red_zpart.
have Hp0l: 1 < size_part p0l.
  by do 3 apply ltnW; rewrite Dp0l size_rev_part Ep0r -Hx0n.
have Hpl: 0 < size_part p0ll by rewrite size_drop_part -ltn_lt0sub.
have Hpr: nhub < size_part p0lr.
  by rewrite -add1n /shift_part size_cat_part Ep0r leq_add2r; case: p0l Hp0l.
elim: nhub p0ll p0lr Hpl Hpr zvalid_initl => // [d Hrec] pl pr Hpl Hpr Hzp.
pose pl' := shift_part pr pl; pose pr' := drop_part 1 pr.
pose zp zi := Zpart zi pl pr; pose zp' zi := Zpart zi pl' pr'.
rewrite -/(zp Zhub) [zp]lock /= -{1}lock {1}/zp.
have Dzp': forall zi zi', zshiftr zi' (zp zi) = zp' zi'.
  by move=> *; rewrite /zp zshiftr_eq //; apply: leq_trans Hpr.
have Hzp': zpvalid (zp' Zhub) by
 rewrite -(Dzp' Zhub); apply: zpvalid_shiftr.
 rewrite -lock Dzp' {1}/zp'; move: (frefl zp) (frefl zp'); rewrite {1}/zp {1}/zp'.
move=> H H'; rewrite !{}H !{}H'; set x := iter (size_part pl) face x0.
have Ezp: forall zi, zdart (zp zi) = zmove_def zi x by done.
have Ezp': forall zi, zdart (zp' zi) = zmove_def zi (face x).
  by move=> *; rewrite -(Dzp' Zhub) zdart_shiftr //.
have Ezp'' := Ezp'; rewrite /zp' in Ezp''.
have Dx' := Ezp' Zhub; rewrite /= /zmove /= in Dx'.
have Hpl': 0 < size_part pl'.
  by apply: (leq_trans Hpl); rewrite /pl' /shift_part size_cat_part leq_addl.
have Hpr': d < size_part pr' by move: Hpr; rewrite /pr'; case pr.
apply cases_of_if; last by clear; rewrite /zp'; eauto.
case Hsqt: (qzt_proper (qzt_getr (get_spoke pr) (qzt_truncate qt))) => //.
case: {Hsqt}(qzt_getr_fit Hsqt) (Hsqt) => [Hs <- _].
move/qzt_get1_truncate=> -> <-.
apply cases_of_if; [ case/red_qzt_leaf_fit | clear ].
  case/qzt_getr_fit=> _ <-; case/qzt_getr_fit=> Hsl <- _ Hssl.
  apply/andP; case=> Hsp Hslp.
  case: {Hssl}(Hssl (zdart (zp Zhub))); rewrite // /zpfit.
  - by clear; rewrite Ezp' Ezp /qstepR /= Dnf.
  - by clear; rewrite zdart_shiftl.
  - by apply zpvalid_shiftl.
  apply: redpart_no_qzt_fitl; first by rewrite Ezp /= /x arity_iter_face.
    by rewrite -(red_popl_spoke_fit Hzp).
  by rewrite -(red_popr_spoke_fit Hzp) // Dn2 arity_face.
apply cases_of_if; [ case/red_qzt_leaf_fit | clear ].
  case/qzt_getr_fit=> Hh <-; case/qzt_getr_fit=> Hsl <- _ Hhssl.
  apply/and3P; case=> Hhp Hslp Hsp.
  have Ds := red_popr_spoke_fit Hzp Hs Hsp.
  have Dsl := red_popl_spoke_fit Hzp Hsl Hslp; rewrite -/x in Ds Dsl.
  case: {Hhssl}(Hhssl (zdart (zp Zhatr))); rewrite // /zpfit.
  - rewrite -(Dzp' Zhatr); apply: (@zdart_stepRt (zp Zhatr)) => //.
    by rewrite /zpfit_top Ezp /= Dn2 !arity_face.
  - by rewrite !Ezp /qstepR /= Eface Dn3.
    rewrite (Ezp Zhatr) /= Dnf; apply: (@zdart_stepLt (zp Zhatl)) => //.
  - by rewrite /zpfit_top Ezp /= -arity_face Enode.
  apply: redpart_no_qzt_fitl; first by rewrite Ezp /= Dn2 !arity_face.
    by rewrite Ezp /= Dnf -arity_face Enode.
  by rewrite Ezp /= !Dn2 arity_face -(red_popr_hat_fit Hzp).
move: (erefl (topqa (get_spoke pr))) {Hs}(red_popr_spoke_fit Hzp Hs).
case Dpr: {1 3 4 5}pr => //= [s h p|h f1 p|h f1 f2 p|h f1 f2 f3 p] <-;
  try case: s Dpr => //= Dpr;
  move=> H; move: {H}(introT eqP (H (erefl _))) => Ds; rewrite -/x eqd_sym in Ds;
  have Es := (Dfn Ds); rewrite /= in Es.
- apply cases_of_if; [ case/red_qzt_leaf_fit | done ].
  case/qzt_getr_fit=> Hhr <-; case/qzt_getr_fit=> Hh <- _ Hhhr.
  apply/andP; case=> Hhr' Hh'.
  case: {Hhhr}(Hhhr (iter 3 face (edge x))); rewrite /zpfit //.
  + by clear; rewrite Ezp' /= /qstepR Dnf {1}Es !Dnf -Dn2 Dnf.
  + by clear; rewrite Ezp /qstepR /= Dnf De2 Dnf Dn2.
  apply: redpart_no_qzt_fitl; first by rewrite /= !arity_face (eqP Ds).
    by rewrite /= Dnf -(red_popr_hat_fit Hzp) // Dpr.
  rewrite -(red_popr_hat_fit Hzp') //= Dx' -!Dn2 !Dnf Es Dnf -Dn2.
  by symmetry; rewrite Dnf -2!arity_face Enode -!Dn2 Dnf.
- apply cases_of_if; [ case/red_qzt_leaf_fit | clear ].
  case/qzt_getr_fit=> Hf1 <-; case/qzt_getr_fit=> Hh <- _ Hhf1.
  apply/andP; case=> Hf1' Hh'.
  case: {Hhf1}(Hhf1 (iter 3 face (edge x))); rewrite /zpfit //.
  + by clear; rewrite Ezp' /qstepR /= De2 Dnf {1}Es Eface Dnf -Dn2 Dnf.
  + by clear; rewrite Ezp /qstepR /= Eface Dnf Dn2.
  apply: redpart_no_qzt_fitl; first by rewrite /= !arity_face -(eqP Ds).
    by rewrite /= Dnf -(red_popr_hat_fit Hzp) // Dpr.
  rewrite -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //=.
  by rewrite Dn2 arity_face Dnf.
- apply cases_of_if; [ case/red_qzt_leaf_fit | done ].
  case/qzt_getr_fit=> Hhr <-; case/qzt_getr_fit=> Hf1 <- _ Hf1hr.
  apply/andP; case=> Hhr' Hf1'.
  case: {Hf1hr}(Hf1hr (iter 4 face (edge x))); rewrite /zpfit //.
  + by clear; rewrite Ezp' /qstepR /= Dnf {1}Es Dnf -Dn2 Dnf.
  + by clear; rewrite Ezp' /qstepR /= Dnf Eface Dnf.
  apply: redpart_no_qzt_fitl => //=; first by rewrite /= !arity_face -(eqP Ds).
    by rewrite -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  rewrite -(red_popr_hat_fit Hzp') //= Dx' -!Dn2 !Dnf Es Dnf -Dn2.
  by symmetry; rewrite Dnf -2!arity_face Enode -!Dn2 Dnf.
- apply cases_of_if; [ case/red_qzt_leaf_fit | clear ].
  case/qzt_getr_fit=> Hf1 <-; case/qzt_getr_fit=> Hh <- _ Hhf1.
  apply/andP; case=> Hf1' Hh'.
  case: {Hhf1}(Hhf1 (iter 3 face (edge x))); rewrite /zpfit //.
  + by clear; rewrite Ezp' /qstepR /= De2 Dnf {1}Es !Eface Dnf -Dn2 Dnf.
  + by clear; rewrite Ezp /qstepR /= Eface Dnf Dn2.
  apply: redpart_no_qzt_fitl; first by rewrite /= !arity_face -(eqP Ds).
    by rewrite /= Dnf -(red_popr_hat_fit Hzp) // Dpr.
  rewrite -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //=.
  by rewrite Dn2 arity_face Dnf.
- apply cases_of_if; [ case/red_qzt_leaf_fit | clear ].
  case/qzt_getr_fit=> Hf2 <-; case/qzt_getr_fit=> Hf1 <- _ Hf1f2.
  apply/andP; case=> Hf2' Hf1'.
  case: {Hf1f2}(Hf1f2 (iter 4 face (edge x))); rewrite /zpfit //.
  + by clear; rewrite Ezp' /qstepR /= Dnf {1}Es !Eface -Dn2 Dnf.
  + by clear; rewrite Ezp' /qstepR /= Dnf Eface Dnf.
  apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
    by rewrite -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  rewrite -(red_popl_fan2r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= Dn2 !Dnf.
  by rewrite arity_face.
- apply cases_of_if; [ case/red_qzt_leaf_fit | done ].
  case/qzt_getr_fit=> Hhr <-; case/qzt_getr_fit=> Hf2 <- _ Hf2hr.
  apply/andP; case=> Hhr' Hf2'.
  case: {Hf2hr}(Hf2hr (iter 5 face (edge x))); rewrite /zpfit //.
  + by clear; rewrite Ezp' /qstepR /= Dnf {1}Es Dnf -Dn2 Dnf.
  + by clear; rewrite Ezp' /qstepR /= Dnf Eface Dnf.
  apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
    by rewrite -(red_popl_fan2r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  rewrite -(red_popr_hat_fit Hzp') //= Dx' -!Dn2 !Dnf Es Dnf -Dn2.
  by symmetry; rewrite Dnf -2!arity_face Enode -!Dn2 Dnf.
- apply cases_of_if; [ case/red_qzt_leaf_fit | clear ].
  case/qzt_getr_fit=> Hf1 <-; case/qzt_getr_fit=> Hh <- _ Hhf1.
  apply/andP; case=> Hf1' Hh'.
  case: {Hhf1}(Hhf1 (iter 3 face (edge x))); rewrite /zpfit //.
  + by clear; rewrite Ezp' /qstepR /= De2 Dnf {1}Es !Eface Dnf -Dn2 Dnf.
  + by clear; rewrite Ezp /qstepR /= Eface Dnf Dn2.
  apply: redpart_no_qzt_fitl; first by rewrite /= !arity_face -(eqP Ds).
    by rewrite /= Dnf -(red_popr_hat_fit Hzp) // Dpr.
  rewrite -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //=.
  by rewrite Dn2 arity_face Dnf.
- apply cases_of_if; [ case/red_qzt_leaf_fit | clear ].
  case/qzt_getr_fit=> Hf2 <-; case/qzt_getr_fit=> Hf1 <- _ Hf1f2.
  apply/andP; case=> Hf2' Hf1'.
  case: {Hf1f2}(Hf1f2 (iter 4 face (edge x))); rewrite /zpfit //.
  + by clear; rewrite Ezp' /qstepR /= Dnf {1}Es !Eface -Dn2 Dnf.
  + by clear; rewrite Ezp' /qstepR /= Dnf Eface Dnf.
  apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
    by rewrite -(red_popl_fan1r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  rewrite -(red_popl_fan2r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= Dn2 !Dnf.
  by rewrite arity_face.
- apply cases_of_if; [ case/red_qzt_leaf_fit | clear ].
  case/qzt_getr_fit=> Hf3 <-; case/qzt_getr_fit=> Hf2 <- _ Hf2f3.
  apply/andP; case=> Hf3' Hf2'.
  case: {Hf2f3}(Hf2f3 (iter 5 face (edge x))); rewrite /zpfit //.
  + by clear; rewrite Ezp' /qstepR /= Dnf {1}Es !Eface -Dn2 Dnf.
  + by clear; rewrite Ezp' /qstepR /= Dnf Eface Dnf.
  apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
    by rewrite -(red_popl_fan2r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
  rewrite -(red_popl_fan3r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= Dn2 !Dnf.
  by rewrite arity_face.
apply cases_of_if; [ case/red_qzt_leaf_fit | done ].
case/qzt_getr_fit=> Hhr <-; case/qzt_getr_fit=> Hf3 <- _ Hf2hr.
apply/andP; case=> Hhr' Hf2'.
case: {Hf2hr}(Hf2hr (iter 6 face (edge x))); rewrite /zpfit //.
+ by clear; rewrite Ezp' /qstepR /= Dnf {1}Es Dnf -Dn2 Dnf.
+ by clear; rewrite Ezp' /qstepR /= Dnf Eface Dnf.
apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
  by rewrite -(red_popl_fan3r_fit Hzp') // ?Ezp'' /pl' ?Dpr //= !Dnf.
rewrite -(red_popr_hat_fit Hzp') //= Dx' -!Dn2 !Dnf Es Dnf -Dn2.
by symmetry; rewrite Dnf -2!arity_face Enode -!Dn2 Dnf.
Qed.

End Zpart.

Fixpoint redpart_rec (d : nat) (p : part) {struct d} : bool :=
  if d is S d' then red_zpart (redpart_rec d') (rev_part p) p else false.

End RedpartRec.

(* The bound is mostly to keep Coq from unfolding the recursion too soon. *)
(* There's a logic to it, though : each time we recurse, we pop one       *)
(* prange, there are at most 4 open ranges per sector, and the worst case *)
(* would require a configuration where all but one face is octogonal.     *)
Definition redpart_depth p := size_part p * 12.

Definition redpart p :=
  let nhub := size_part p in
  let ahub := qarity_of_nat nhub in
  (nhub =d (ahub : nat)) && redpart_rec ahub (redpart_depth p) p.

Lemma no_fit_redpart : forall p, redpart p -> forall x : g, negb (exact_fitp x p).
Proof.
move=> p; case/andP; move: (qarity_of_nat (size_part p)) => ahub.
move/eqP=> Ep Hp x; apply/idP => Hxp; case/idPn: Hp; rewrite /redpart.
case/andP: Hxp (Hxp) Ep; move/eqP=> <- _.
elim: (redpart_depth p) x {1 3}p => //= *; eapply not_red_zpart; eauto.
Qed.

End Redpart.

Unset Implicit Arguments.