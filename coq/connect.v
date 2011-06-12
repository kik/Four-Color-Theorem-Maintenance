(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import path.
Require Import fintype.
Require Import compat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Decidable connectivity in finite sets, with an application to the orbits *)
(* and inverses of injective functions.                                     *)

Section Connect.

Variables (d : finType) (e : rel d).

Fixpoint dfs (n : nat) (a : seq d) (x : d) {struct n} : seq d :=
  if n is S n' then
    if x \in a then a else foldl (dfs n') (cons x a) (filter (e x) (enum d))
  else a.

Definition connect : rel d := fun x => mem (dfs #|d| nil x).

Lemma subset_dfs : forall n (a b : seq d), a \subset (foldl (dfs n) a b).
Proof.
have Hs := @subxx d; elim=> [|n Hrec] a b; first by elim: b.
elim: b a => [|x b Hrecb] a //; apply: subset_trans (Hrecb _).
simpl; case (_ \in _); first done; apply: subset_trans (Hrec _ _).
by apply/subsetP => y Ht; apply/orP; right.
Qed.

Inductive dfs_path (x y : d) (a : seq d) : Prop :=
  DfsPath p (_ : path e x p) (_ : last x p = y) (_ : [disjoint (cons x p) & a]).

Lemma dfsP : forall n x y (a : seq d), #|d| <= #|a| + n ->
  negb (y \in a) -> reflect (dfs_path x y a) (y \in dfs n a x).
Proof.
elim=> [|n Hrec] x y a Hn Hy.
case/idPn: (max_card (predU1 y (mem a))).
  by rewrite -ltnNge cardU1 (negbTE Hy) /= addSn addnC.
simpl; case Hx: (x \in a).
  rewrite (negbTE Hy); right; move=> [p Hp Ep Hpa].
  by case/idP: (pred0P Hpa x); rewrite /predI /= mem_head.
move Da': (cons x a) => a'; case Hya': (y \in a').
  rewrite (subsetP (subset_dfs n _ _) _ Hya'); left.
  exists nil; repeat split; last by rewrite disjoint_has /= Hx.
  by rewrite -Da' /= in_cons in Hya'; case/predU1P: Hya'; last by rewrite (negbTE Hy).
have Hna': #|d| <= #|a'| + n.
  by rewrite -Da' /= cardU1 Hx /= add1n addSnnS.
move Db: (filter (e x) (enum d)) => b.
suff Hrec':
    reflect (exists2 x', x' \in b & dfs_path x' y a') (y \in foldl (dfs n) a' b).
- apply: {Hrec Hrec'}(iffP Hrec') => [[x' Hx' [p Hp Ep Hpa]] | [p Hp Ep Hpa]].
    rewrite -Da' /= disjoint_sym disjointU1 in Hpa; move/andP: Hpa => [Hpx Hpa].
    exists (cons x' p); try by rewrite //= disjointU1 Hx disjoint_sym.
    by rewrite -Db filter_enum /in_mem /= in Hx'; rewrite /= Hx'.
  case/shortenP: Hp Ep => [[|y' p']] /= Hp' Up' Hp'p Dy.
    by rewrite -Da' Dy /= mem_head in Hya'.
  move/andP: Hp' => [Hxy' Hp']; move/andP: Up' => [Hp'x' _].
  exists y'; [ by rewrite -Db filter_enum | exists p'; auto ].
  rewrite disjoint_sym -Da' /= disjointU1 Hp'x' /= disjoint_sym.
   by apply: disjoint_trans Hpa; apply/subsetP => [z Hz]; apply: predU1r; apply (Hp'p z); auto.
elim: b a' Hya' Hna' {a x Da' Db Hy Hn Hx} => [|x b Hrecb] a Hy Hn /=.
  by rewrite Hy; right; case.
have Ha := subset_dfs n a [:: x]; simpl in Ha.
case Hdfs_y: (y \in dfs n a x).
  rewrite (subsetP (subset_dfs n _ b) _ Hdfs_y); left.
  exists x; [ apply mem_head | apply: (Hrec _); auto; exact (negbT Hy) ].
have Hca := subset_leq_card Ha; rewrite -(leq_add2r n) in Hca.
apply: {Hrecb Hca}(iffP (Hrecb _ Hdfs_y (leq_trans Hn Hca))).
  move=> [x' Hx' [p Hp Ep Hpa]]; rewrite disjoint_sym in Hpa.
  exists x'; [ rewrite in_cons; by apply predU1r | exists p; try split; try done ].
  rewrite disjoint_sym; exact (disjoint_trans Ha Hpa).
move=> [x' Hx' [p Hp Ep Hpa]].
case Hpa': (disjoint (mem (cons x' p)) (mem (dfs n a x))).
  case/orP: Hx' => [Dx'|Hx']; last by exists x'; auto; exists p.
  move: (pred0P Hpa x') => Hax'; rewrite /predI /= mem_head /= in Hax'.
  case/idP: (pred0P Hpa' x'); rewrite /predI /= mem_head /=.
  apply/(Hrec _ _ _ Hn (negbT Hax')).
  exists nil; auto; simpl; first by apply esym; apply: eqP.
  by rewrite disjoint_has /= -(eqP Dx') Hax'.
case/(Hrec _ _ _ Hn (negbT Hy)): Hdfs_y.
case/pred0Pn: Hpa' => [x'' H]; case/andP: H => [Hpx'' Hdfs_x''].
have Hax'' := pred0P Hpa x''; simpl in Hpx''; rewrite /predI /= Hpx'' /= in Hax''.
case/(Hrec _ _ _ Hn (negbT Hax'')): Hdfs_x'' => [q Hq Eq Hqa].
case/splitPl: {p}Hpx'' Hp Ep Hpa => [p1 p2 Ep1].
rewrite path_cat -cat_cons disjoint_cat last_cat Ep1.
case/andP=> [Hp1 Hp2] Ep2; case/andP=> [Hp1a Hp2a]; exists (cat q p2).
- by rewrite path_cat Hq Eq.
- by rewrite last_cat Eq.
by rewrite -cat_cons disjoint_cat Hqa.
Qed.

Lemma connectPx : forall x y,
  reflect (exists2 p, path e x p & last x p = y) (connect x y).
Proof.
move=> x y; apply: (iffP (@dfsP _ x _ nil _ _)); trivial.
- by rewrite /= card0 leqnn.
- by move=> [p Hp Ep _]; exists p.
by move=> [p Hp Ep]; exists p; try rewrite disjoint_has has_sym.
Qed.

Notation connectP := (connectPx _ _).

Lemma connect_trans : forall x1 x2 x3,
  connect x1 x2 -> connect x2 x3 -> connect x1 x3.
Proof.
move=> x1 x2 x3; move/connectP=> [p1 Hp1 Ep1]; move/connectP=> [p2 Hp2 Ep2].
by apply/connectP; exists (cat p1 p2); rewrite ?path_cat ?Hp1 ?last_cat Ep1.
Qed.

Lemma connect0 : forall x, connect x x.
Proof. by move=> x; apply/connectP; exists nil. Qed.

Lemma eq_connect0 : forall x y : d, x = y -> connect x y.
Proof. move=> x y <-; apply connect0. Qed.

Lemma connect1 : forall x y, e x y -> connect x y.
Proof. by move=> x y Hxy; apply/connectP; exists [:: y]; rewrite /= ?Hxy. Qed.

Lemma path_connect : forall x p, path e x p -> {subset (cons x p) <= (connect x)}.
Proof.
move=> x p Hp x' Hx'; apply/connectP; case/splitPl: p / Hx' Hp => [p p' Ep].
by rewrite path_cat; case/andP; exists p.
Qed.

Definition root x := if pick (connect x) is Some y then y else x.

Definition roots : pred d := fun x => root x == x.

Definition n_comp a := #|predI roots a|.

Lemma connect_root : forall x, connect x (root x).
Proof.
by move=> x; rewrite /root; case: (pickP (connect x)); rewrite // connect0.
Qed.

Definition connect_sym := forall x y, connect x y = connect y x.

Hypothesis He : connect_sym.

Lemma same_connect : forall x y, connect x y -> connect x =1 connect y.
Proof.
by move=> x y Hxy z; apply/idP/idP; apply: connect_trans; rewrite // He.
Qed.

Lemma same_connect_r : forall x y,
  connect x y -> forall z, connect z x = connect z y.
Proof. by move=> x y Hxy z; rewrite !(He z); apply same_connect. Qed.

Lemma rootPx : forall x y, reflect (root x = root y) (connect x y).
Proof.
move=> x y; apply introP=> [Hxy|Hxy Hr].
  rewrite /root -(eq_pick (same_connect Hxy)).
  by case: (pickP (connect x)) => [H|Hx] //; case/idP: (Hx y).
case/negP: Hxy; apply: (connect_trans (connect_root x)).
rewrite Hr He; apply connect_root.
Qed.

Lemma root_root : forall x, root (root x) = root x.
Proof. symmetry; apply: rootPx; apply connect_root. Qed.

Lemma roots_root : forall x, roots (root x).
Proof. move=> *; apply/eqP; apply root_root. Qed.

Lemma eqd_root : forall x y, (root x == root y) = connect x y.
Proof. move=> *; exact (sameP eqP (rootPx _ _)). Qed.

End Connect.

Notation connectP := (connectPx _ _ _).
Notation "'rootP' He" := (rootPx He _ _) (at level 10, He at level 8).

Prenex Implicits connect root roots n_comp.

Notation "'fconnect' f" := (connect (frel f)) (at level 10, f at level 8).

Notation "'froot' f" := (root (frel f)) (at level 10, f at level 8).

Notation "'froots' f" := (roots (frel f)) (at level 10, f at level 8).

Notation "'fcard' f" := (n_comp (frel f)) (at level 10, f at level 8).

Section EqConnect.

Variable d : finType.

Lemma connect_sub : forall e e' : rel d,
  subrel e (connect e') -> subrel (connect e) (connect e').
Proof.
move=> e e' He x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x; [ move=> _; exact: connect0 | simpl ].
move/andP=> [Hx Hp]; exact (connect_trans (He _ _ Hx) (Hrec _ Hp)).
Qed.

Lemma relU_sym : forall e e' : rel d,
  connect_sym e -> connect_sym e' -> connect_sym (relU e e').
Proof.
move=> e e' He He'.
suff Hsub: forall x y, connect (relU e e') x y -> connect (relU e e') y x.
  move=> x y; apply/idP/idP; auto.
move=> x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x /=; first by rewrite connect0.
case/andP=> [Hxp Hp]; apply: {Hrec Hp}(connect_trans (Hrec _ Hp)).
case/orP: Hxp; move/(@connect1 d); rewrite 1?He 1?He';
 apply: connect_sub y x => [x y Hy]; apply connect1; apply/orP; auto.
Qed.

Lemma eq_connect : forall e e' : rel d, e =2 e' -> connect e =2 connect e'.
Proof.
by move=> e e' Ee x y; apply/connectP/connectP=> [] [p Hp Ep]; exists p;
  move: Hp; rewrite // (eq_path Ee).
Qed.

Lemma eq_n_comp : forall e e' : rel d,
  connect e =2 connect e' -> n_comp e =1 n_comp e'.
Proof.
move=> e e' Hee' a; apply: eq_card => x.
by rewrite /predI /roots /root /in_mem /= (eq_pick (Hee' x)).
Qed.

Lemma eq_n_comp_r : forall a a' : pred d, a =1 a' ->
  forall e, n_comp e a = n_comp e a'.
Proof. by move=> a a' Ha e; apply: eq_card => x; rewrite /predI /in_mem /= Ha. Qed.

Lemma n_compC : forall a e, n_comp e d = n_comp e a + n_comp e (predC a).
Proof.
move=> a e; rewrite /n_comp cardIC.
by apply: eq_card => x; rewrite /predI /in_mem /= andbT.
Qed.

End EqConnect.

Section Closure.

Variables (d : finType) (e : rel d).
Hypothesis He : connect_sym e.

Lemma same_connect_rev : connect e =2 connect (fun x y => e y x).
Proof.
suff Hrev: forall e',
    subrel (connect (fun x y : d => e' y x)) (fun x y => connect e' y x).
- move=> x y; rewrite He; apply/idP/idP => [Hyx|Hxy]; apply: Hrev; auto.
move=> e' x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x /=; first by rewrite connect0.
move/andP=> [Hyx Hp]; exact (connect_trans (Hrec _ Hp) (connect1 Hyx)).
Qed.

Definition closed (a : pred d) := forall x y, e x y -> a x = a y.

Lemma intro_closed : forall a : pred d,
  (forall x y, e x y -> a x -> a y) -> closed a.
Proof.
move=> a Ha x y Hxy; apply/idP/idP; first by apply: Ha.
move/connectP: {Hxy}(etrans (He _ _) (connect1 Hxy)) => [p Hp <-].
by elim: p y Hp => [|z p Hrec] y //=; move/andP=> [Hxp Hp]; eauto.
Qed.

Lemma closed_connect : forall a, closed a ->
  forall x y, connect e x y -> a x = a y.
Proof.
move=> a Ha x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x //=; move/andP=> [Hxp Hp].
rewrite (Ha _ _ Hxp); auto.
Qed.

Lemma connect_closed : forall x, closed (connect e x).
Proof. by move=> x y z Hyz; apply (same_connect_r He); apply connect1. Qed.

Lemma setC_closed : forall a, closed a -> closed (predC a).
Proof. by move=> a Ha x y Hxy; rewrite /predC /= (Ha x y Hxy). Qed.

Definition closure a : pred d := fun x => negb (disjoint (mem (connect e x)) a).

Lemma closure_closed : forall a, closed (closure a).
Proof.
move=> a; apply intro_closed; move=> x y Hxy.
by rewrite /closure (eq_disjoint (same_connect He (connect1 Hxy))).
Qed.

Lemma subset_closure : forall a, a \subset (closure a).
Proof.
by move=> a; apply/subsetP => x Hx; apply/pred0Pn; exists x; rewrite /predI /= /in_mem /= connect0.
Qed.

Lemma n_comp_closure2 : forall x y,
  n_comp e (closure (mem (pred2 x y))) = S (negb (connect e x y)).
Proof.
move=> x y; rewrite -(eqd_root He) -card2.
apply: eq_card => [z]; apply/idP/idP.
  case/andP=> Hrz; case/pred0Pn=> z'; case/andP=> Hzz' Hxyz'.
  rewrite -(eqP Hrz) (rootP He Hzz').
   by case: (orP Hxyz'); move/eqP=> Dz'; rewrite /pred2 Dz' /in_mem /= eqxx ?orbT.
rewrite /in_mem /=.
by case/orP; move/eqP=> ->; rewrite /predI (roots_root He);
  apply/pred0Pn; [ exists x | exists y ];
   rewrite /predI /pred2 /= /in_mem /= eqxx ?orbT He connect_root.
Qed.

Lemma n_comp_connect : forall x, n_comp e (connect e x) = 1.
Proof.
move=> x; rewrite -(card1 (root e x)); apply: eq_card => [y].
rewrite /in_mem /=.
apply/andP/eqP => [[Hy Hxy]|->]; first by rewrite (rootP He Hxy) (eqP Hy).
by rewrite (roots_root He) connect_root.
Qed.

End Closure.

Notation "'fclosed' f" := (closed (frel f)) (at level 10, f at level 8).

Notation "'fclosure' f" := (closure (frel f)) (at level 10, f at level 8).

Prenex Implicits closed closure.

Section Orbit.

Variables (d : finType) (f : d -> d).

Definition order x := card (mem (fconnect f x)).

Definition orbit x := traject f x (order x).

Definition findex x y := index y (orbit x).

Definition finv x := iter (order x).-1 f x.

Lemma fconnect_iter : forall n x, fconnect f x (iter n f x).
Proof.
move=> n x; apply/connectP.
exists (traject f (f x) n); [ apply fpath_traject | apply last_traject ].
Qed.

Lemma fconnect1 : forall x, fconnect f x (f x).
Proof. exact (fconnect_iter 1). Qed.

Lemma fconnect_finv : forall x, fconnect f x (finv x).
Proof. move=> x; apply: fconnect_iter. Qed.

Lemma orderSpred : forall x, S (order x).-1 = order x.
Proof. by move=> x; rewrite /order (cardD1 x) /in_mem /= connect0. Qed.

Lemma size_orbit : forall x : d, size (orbit x) = order x.
Proof. move=> x; apply: size_traject. Qed.

Lemma looping_order : forall x, looping f x (order x).
Proof.
move=> x; apply/idPn => [Ux]; rewrite -looping_uniq in Ux.
case/idP: (ltnn (order x)).
move: (card_uniqP Ux); rewrite size_traject; move <-.
apply: subset_leq_card; apply/subsetP=> z.
move/trajectP=> [i _ ->]; rewrite /in_mem /=; apply fconnect_iter.
Qed.

Lemma fconnect_orbit : forall x, fconnect f x =1 mem (orbit x).
Proof.
move=> x y; symmetry; apply/idP/idP.
  move/trajectP=> [i _ ->]; apply fconnect_iter.
move/connectP=> [q' Hq' <-]; move/fpathP: Hq' => [m ->] {q'}.
rewrite last_traject; apply: loopingP; apply looping_order.
Qed.

Lemma uniq_orbit : forall x, uniq (orbit x).
Proof.
move=> x; rewrite /orbit -orderSpred looping_uniq.
apply/trajectP => [[i Hi Ei]]; set (n := (order x).-1); case/idP: (ltnn n).
rewrite {1}/n orderSpred /order -(size_traject f x n).
apply: (leq_trans (subset_leq_card _) (card_size _)); apply/subsetP => [z].
rewrite /in_mem /= fconnect_orbit; move/trajectP=> [j Hj ->] {z}; apply/trajectP.
rewrite -orderSpred -/n ltnS leq_eqVlt in Hj.
by case/predU1P: Hj => [Dj|Hj]; [ rewrite Dj; exists i | exists j ].
Qed.

Lemma findex_max : forall x y, fconnect f x y -> findex x y < order x.
Proof.  by move=> x y; rewrite fconnect_orbit /= -index_mem size_orbit. Qed.

Lemma findex_iter : forall x i, i < order x -> findex x (iter i f x) = i.
Proof.
move=> x i Hi; rewrite -(nth_traject f Hi); rewrite -size_orbit in Hi.
exact (index_uniq x Hi (uniq_orbit x)).
Qed.

Lemma iter_findex : forall x y, fconnect f x y -> iter (findex x y) f x = y.
Proof.
move=> x y; rewrite fconnect_orbit; move=> Hy.
have Hi := Hy; rewrite /= -index_mem size_orbit in Hi.
by rewrite -(nth_traject f Hi) -/(orbit x) nth_index.
Qed.

Lemma findex0 : forall x, findex x x = 0.
Proof. by move=> x; rewrite /findex /orbit -orderSpred /= eqxx. Qed.

Lemma fconnect_invariant : forall (d' : eqType) (k : d -> d'),
  invariant f k =1 d -> forall x y : d, fconnect f x y -> k x = k y.
Proof.
move=> d' k Hk x y; move/iter_findex=> <-; elim: {y}(findex x y) => //= n ->.
exact (esym (eqP (Hk _))).
Qed.

Section Loop.

Variable p : seq d.
Hypotheses (Hp : fcycle f p) (Up : uniq p).
Variable x : d.
Hypothesis Hx : x \in p.

(* The first lemma does not depend on Up : (uniq p) *)
Lemma fconnect_cycle : fconnect f x =1 mem p.
Proof.
case/rot_to: Hx => [i q Dp] y; rewrite /= -(mem_rot i) Dp.
have Hp' := Hp; rewrite -(cycle_rot i) {i}Dp (cycle_path x) /= {1}/frel in Hp'.
case/andP: Hp'; move/eqP=> Eq Hq; apply/idP/idP; last first.
  by have Hc := path_connect; rewrite /sub_mem /in_mem /= in Hc; rewrite /in_mem /=; apply: Hc.
move/connectP=> [q' Hq' <-] {y}; case/fpathP: Hq' => [m ->] {q'}.
case/fpathP: Hq Eq => [n ->]; rewrite !last_traject -iterS -trajectS; move=> Dx.
by apply/loopingP; rewrite /looping Dx /= mem_head.
Qed.

Lemma order_cycle : order x = size p.
Proof. rewrite -(card_uniqP Up); exact (eq_card fconnect_cycle). Qed.

Lemma orbit_rot_cycle : {i : nat | orbit x = rot i p}.
Proof.
case/rot_to: Hx => [i q Dp]; exists i; rewrite (Dp).
have Hp' := Hp; rewrite -(cycle_rot i) (Dp) (cycle_path x) /= in Hp'.
case/andP: Hp'=> _; move/fpathP=> [m Dq].
by rewrite /orbit order_cycle -(size_rot i) Dp /= Dq size_traject.
Qed.

End Loop.

Hypothesis Hf : injective f.

Lemma f_finv : cancel finv f.
Proof.
move=> x; move: (looping_order x) (uniq_orbit x).
rewrite /looping /orbit -orderSpred looping_uniq /= /looping.
set n := (order x).-1; case/predU1P; first done.
move/trajectP=> [i Hi Dnx]; rewrite -iterSr -iterS in Dnx.
by case/trajectP; exists i; last by apply Hf.
Qed.

Lemma finv_f : cancel f finv.
Proof. exact (inj_can_sym f_finv Hf). Qed.

Lemma isoF : bijective f.
Proof. exists finv; [ exact finv_f | exact f_finv ]. Qed.

Lemma finv_iso : bijective finv.
Proof. exists f; [ exact f_finv | exact finv_f ]. Qed.

Lemma finv_inj : injective finv.
Proof. exact (can_inj f_finv). Qed.

Lemma fconnect_sym : forall x y, fconnect f x y = fconnect f y x.
Proof.
suff: forall x y, fconnect f x y -> fconnect f y x.
  move=> *; apply/idP/idP; auto.
move=> x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x /=; first by rewrite connect0.
move/andP=> [Hx Hp]; rewrite -(finv_f x) (eqP Hx).
apply: (connect_trans _ (fconnect_finv _)); auto.
Qed.

Lemma iter_order : forall x, iter (order x) f x = x.
Proof. move=> x; rewrite -orderSpred iterS; exact (f_finv x). Qed.

Lemma iter_finv : forall n x, n <= order x ->
  iter n finv x = iter (order x - n) f x.
Proof.
move=> n x Hn; set m := order x - n.
rewrite -{1}[x]iter_order -(subnKC Hn) -/m iter_add.
move: {m x Hn}(iter m f x) => x.
by elim: n => // [n Hrec]; rewrite iterSr /= finv_f.
Qed.

Lemma cycle_orbit : forall x, fcycle f (orbit x).
Proof.
move=> x; rewrite /orbit -orderSpred (cycle_path x) /= last_traject -/(finv x).
by rewrite fpath_traject /frel f_finv eqxx.
Qed.

Lemma fpath_finv : forall x p,
  fpath finv x p = fpath f (last x p) (rev (belast x p)).
Proof.
move=> x p; elim: p x => [|y p Hrec] x //=.
rewrite rev_cons -cats1 path_cat -{}Hrec andbC /= /frel eq_sym andbT.
bool_congr; rewrite -(inj_eq Hf) f_finv.
by case: p => [|z p] //=; rewrite rev_cons last_rcons.
Qed.

Lemma same_fconnect_finv : fconnect finv =2 fconnect f.
Proof.
move=> x y; rewrite (same_connect_rev fconnect_sym).
apply: {x y}eq_connect => x y.
by rewrite /frel /= -(inj_eq Hf) f_finv eq_sym.
Qed.

Lemma fcard_finv : fcard finv =1 fcard f.
Proof. exact (eq_n_comp same_fconnect_finv). Qed.

Definition order_set n : pred d := fun x => order x == n.

Lemma order_div_card : forall n a,
    a \subset (order_set n) -> fclosed f a -> 0 < n ->
  forall m, (#|a| == n * m) = (fcard f a == m).
Proof.
move=> n a Han Ha Hn; rewrite /n_comp; set b := predI (froots f) a.
have Hb: forall x, b x -> froot f x = x /\ order x = n.
  move=> x; move/andP=> [Hrx Hax]; split; apply: eqP; auto.
  exact (subsetP Han _ Hax).
have <-: #|[pred x | b (froot f x)]| = #|a|.
  apply: eq_card => x; rewrite /b /predI /in_mem /= (roots_root fconnect_sym).
  by rewrite -(closed_connect Ha (connect_root _ x)).
elim: {a b}(#|b|) {1 3 4}b (eqxx #|b|) Hb {Ha Han} => [|m Hrec] b Em Hb.
  rewrite -(@eq_card d pred0); last by move=> x; rewrite /= /in_mem /= (pred0P Em).
  by case=> [|m]; rewrite card0 mulnC -(ltn_predK Hn).
case: (pickP b) => [x Hx|Hb0]; last by rewrite (eq_card Hb0) card0 in Em.
case: (Hb _ Hx) => [Dx Hex].
case=> [|m']; rewrite mulnC /=; first by rewrite (cardD1 x) /in_mem /= Dx Hx.
rewrite (cardD1 x) /in_mem /= Hx in Em; rewrite mulnC.
apply: etrans _ (Hrec _ Em _ _); last by move=> y; case/andP; auto.
rewrite mulnS.
apply: etrans (congr1 (fun p => p == _) _) (eqn_addl _ _ _).
rewrite -(cardIC (fconnect f x)); congr addn.
  apply: etrans Hex; apply: eq_card => y; rewrite /predI ?inE andbC.
  case Hy: (fconnect f x y) => //=.
  by rewrite -(rootP fconnect_sym Hy) Dx Hx.
apply: eq_card => y; rewrite /predI /predD1 /predC ?inE andbC.
by rewrite -{2}Dx eq_sym (eqd_root fconnect_sym).
Qed.

Lemma fclosed1 : forall a, fclosed f a -> forall x, a x = a (f x).
Proof. move=> a Ha x; exact (Ha x _ (eqxx _)). Qed.

Lemma same_fconnect1 : forall x, fconnect f x =1 fconnect f (f x).
Proof. move=> x; exact (same_connect fconnect_sym (fconnect1 x)). Qed.

Lemma same_fconnect1_r : forall x y, fconnect f x y = fconnect f x (f y).
Proof. by move=> x y; rewrite /= !(fconnect_sym x) -same_fconnect1. Qed.

End Orbit.

Prenex Implicits order orbit findex finv order_set.

Section FinMonic.

Variables (d : finType) (f f' : d -> d).
Hypothesis Ef : cancel f f'.

Remark Hf : injective f. Proof. exact (can_inj Ef). Qed.

Lemma finv_eq_monic : finv f =1 f'.
Proof. exact (bij_can_eq (isoF Hf) (finv_f Hf) Ef). Qed.

Lemma monicF_sym : cancel f' f.
Proof. exact (eq_can (f_finv Hf) finv_eq_monic (frefl f)). Qed.

Lemma monicF_smove : forall x y, f' x = y -> x = f y.
Proof. move=>x y; exact (canRL monicF_sym). Qed.

Lemma monic2F_eqd : forall x y, (f x == y) = (x == f' y).
Proof. exact (can2_eq Ef monicF_sym). Qed.

End FinMonic.

Section FconnectEq.

Variables (d : finType) (f f' : d -> d).
Hypothesis Eff' : f =1 f'.

Remark eq_eqdf : frel f =2 frel f'.
Proof. move=> x y; rewrite /frel /= Eff'; done. Qed.

Lemma eq_fconnect : fconnect f =2 fconnect f'.
Proof. exact (eq_connect eq_eqdf). Qed.

Lemma eq_fcard : fcard f =1 fcard f'.
Proof. exact (eq_n_comp eq_fconnect). Qed.

Lemma eq_finv : finv f =1 finv f'.
Proof.
move=> x; rewrite /finv /order (eq_card (eq_fconnect x)).
apply: (eq_iter Eff').
Qed.

Hypothesis Hf : injective f.

Lemma finv_inv : finv (finv f) =1 f.
Proof. exact (finv_eq_monic (f_finv Hf)). Qed.

Lemma order_finv : order (finv f) =1 order f.
Proof. move=> x; exact (eq_card (same_fconnect_finv Hf x)). Qed.

Lemma order_set_finv : order_set (finv f) =2 order_set f.
Proof. by move=> n x; rewrite /order_set order_finv. Qed.

End FconnectEq.

Section RelAdjunction.

Variables (d d' : finType) (h : d' -> d) (e : rel d) (e' : rel d').
Hypotheses (He : connect_sym e) (He' : connect_sym e').

Variable a : pred d.
Hypothesis Ha : closed e a.

Record rel_adjunction : Type := RelAdjunction
  {rel_unit : forall x,
     a x -> {x' : d' | connect e x (h x')};
   rel_functor : forall x' y',
     a (h x') -> connect e' x' y' = connect e (h x') (h y')}.

Lemma intro_adjunction : forall h' : (forall x, a x -> d'),
   (forall x Hx, connect e x (h (h' x Hx))
             /\ (forall y Hy, e x y -> connect e' (h' x Hx) (h' y Hy))) ->
   (forall x' Hx, connect e' x' (h' (h x') Hx)
             /\ (forall y', e' x' y' -> connect e (h x') (h y'))) ->
  rel_adjunction.
Proof.
move=> h' Hee' He'e; split.
  by move=> y Hy; exists (h' y Hy); case (Hee' _ Hy).
move=> x' z' Hx'; apply/idP/idP.
  move/connectP=> [p Hp <-] {z'}.
  elim: p x' Hp Hx' => [|y' p Hrec] x' /=; first by rewrite connect0.
  move/andP=> [Hx' Hp] Hx.
  move: (He'e _ Hx) => [_ H]; move/H: {H}Hx' => Hxp.
  apply: (connect_trans Hxp (Hrec _ Hp _)).
  by rewrite -(closed_connect Ha Hxp).
case: (He'e _ Hx') => [Hx'x'' _] Hxz; apply: (connect_trans Hx'x'').
move/connectP: Hxz Hx' {Hx'x''} => [p Hp Hpz].
elim: p {x'}(h x') Hp Hpz => [|y' p Hrec] x /=.
  by move=> _ Dx; rewrite Dx; move=> Hz'; rewrite He'; case (He'e _ Hz').
move/andP=> [Hx' Hp] Dz' Hy.
move: (Hy) (Hee' _ Hy) => Hx [_ Hhxy]; rewrite (Ha Hx') in Hy.
apply: connect_trans (Hrec _ Hp Dz' Hy); auto.
Qed.

Lemma strict_adjunction :
  injective h -> a \subset (codom h) -> rel_base h e e' (predC a) -> rel_adjunction.
Proof.
rewrite /predC; move=> Hh Hha He'e.
apply intro_adjunction with (fun x Hx => iinv (subsetP Hha x Hx)).
  move=> x Hx; split; first by rewrite f_iinv; apply connect0.
  by move=> y Hy Hxy; apply connect1; rewrite -He'e !f_iinv ?Hx /= ?negbK.
move=> x' Hx'; split; first by rewrite (iinv_f _ Hh); apply connect0.
by move=> y' Hx'y'; apply connect1; rewrite He'e ?Hx' /= ?negbK.
Qed.

Lemma adjunction_closed : rel_adjunction -> closed e' (preim h a).
Proof.
move=> [Hu He'e]; apply (intro_closed He').
move=> x' y'; move/(@connect1 d')=> Hx'y' Hx'.
by rewrite He'e // in Hx'y'; rewrite /preim /= -(closed_connect Ha Hx'y').
Qed.

Lemma adjunction_n_comp : rel_adjunction -> n_comp e a = n_comp e' (preim h a).
Proof.
move=> [Hu He'e]; apply: iso_eq_card; have Hac := closed_connect Ha.
pose f1 := fun w : {x | x \in (predI (roots e) a) } =>
  let x' := let (x, Hw) := w in let (_, Hx) := andP Hw in
    let (x', _) := Hu x Hx in x' in
      root e' x'.
have Hf1: forall w, f1 w \in predI (roots e') (preim h a).
  rewrite /f1.
  move=> [x Hw]; case: (andP Hw) => [_ Hx]; case: (Hu x Hx) => [x' Hxx'].
  move: (connect_root e' x'); rewrite /f1 /predI inE /= (roots_root He') /preim /=.
  rewrite He'e /=; last by rewrite -(Hac _ _ Hxx').
  by move=> Hx'rx'; rewrite -(Hac _ _ (connect_trans Hxx' Hx'rx')).
pose f2 := fun w : {x | x \in (predI (roots e') (preim h a))} =>
  root e (h (sval w)).
have Hf2: forall w : {x | x \in (predI (roots e') (preim h a))},
  f2 w \in predI (roots e) a.
  rewrite /f2.
  move=> [x' Hw]; case: (andP Hw); rewrite /preim /= => _ Hx.
  by rewrite /predI inE /= (roots_root He) -(Hac _ _ (connect_root e (h x'))).
exists (fun w => @exist _ (fun x => x \in _) _ (Hf1 w)).
exists (fun w => @exist _ (fun x => x \in _) _ (Hf2 w)).
  move=> [x Hw]. apply: val_inj => /=.
  rewrite /f1 /f2 /=.
  move: (andP Hw) => [Hrx Hx]; move: (Hu x Hx) => [x' Hx'].
  rewrite -(eqP Hrx); apply: (esym (rootP He (connect_trans Hx' _))).
  rewrite -He'e /preim -?(Hac _ _ Hx') //; exact: connect_root.
move=> w; apply: val_inj => /=.
rewrite /f1 /f2 /=.
case: (andP (Hf2 w)) => _; case/Hu; case: w => [x' Hw] y' /=.
move: (andP Hw) => [Hrx' Hx'] Hrxy; rewrite /roots in Hrx'.
rewrite -(eqP Hrx'); apply: (rootP He').
rewrite He' He'e //; exact: connect_trans (connect_root _ _) Hrxy.
Qed.

End RelAdjunction.

Definition fun_adjunction d d' h f f' := @rel_adjunction d d' h (frel f) (frel f').

Implicit Arguments intro_adjunction [d d' h e e' a].
Implicit Arguments adjunction_n_comp [d d' e e' a].

Unset Implicit Arguments.

