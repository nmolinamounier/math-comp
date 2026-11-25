(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop finset fingroup nmodule order.
From mathcomp Require Import rings_modules_and_algebras divalg orderedzmod.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import Order.Theory GRing.Theory Num.Def orderedzmod.Num.

Module Num.

#[short(type="porderRingType")]
HB.structure Definition POrderRing :=
  { R of GRing.NzRing R & Num.POrderZmodule R }.

#[short(type="orderRingType")]
HB.structure Definition OrderRing :=
  { R of GRing.NzRing R & Num.OrderZmodule R }.

HB.mixin Record Ring_isPOrdered R & POrderRing R := {
  mulr_ge0 : forall x y : R, x >= 0 -> y >= 0 -> x * y >= 0;
  ler01 : 0 <= 1 :> R
}.

#[short(type="porderedRingType")]
HB.structure Definition POrderedRing :=
  { R of POrderRing R & Ring_isPOrdered R & Num.POrderedZmodule R }.

#[short(type="orderedRingType")]
HB.structure Definition OrderedRing :=
  { R of OrderRing R & Ring_isPOrdered R & Num.OrderedZmodule R}.

Module OrderedRingExports.
Bind Scope ring_scope with
  POrderRing.sort OrderRing.sort POrderedRing.sort OrderedRing.sort.
End OrderedRingExports.
HB.export OrderedRingExports.

Module Export Def.

Export Num.Def.

Section POrderRingDef.
Context {R : porderRingType}.

Definition sgr (x : R) : R := if x == 0 then 0 else if x < 0 then -1 else 1.

End POrderRingDef.

End Def.

Notation sg := sgr.

Module Theory.

Section pordered_theory.
Context (R : porderedRingType).
Implicit Types x y : R.

Lemma ler0n n : 0 <= n%:R :> R.
Proof. by apply: mulrn_wge0; exact: ler01. Qed.

Lemma ltr01 : 0 < 1 :> R.
Proof. by rewrite lt_def oner_neq0 ler01. Qed.

Lemma ltr0Sn n : 0 < n.+1%:R :> R.
Proof.
apply: (lt_le_trans ltr01).
by rewrite mulrS lerDl ler0n.
Qed.

Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N.
Proof. by case: n => // n; exact: ltr0Sn. Qed.

Definition lter01 := (@ler01 R, ltr01).

Local Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  solve [apply: ler01 | apply: ler0n] : core.
Local Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  solve [apply: ltr01 | apply: ltr0Sn] : core.

Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
Proof. by case: n => [|n]; rewrite ?eqxx // gt_eqF ?ltr0Sn. Qed.

Lemma pnatr_eq1 n : (n%:R == 1 :> R) = (n == 1)%N.
Proof.
case: n => [|n]; rewrite ?[0 == 1]eq_sym ?oner_eq0 //.
by rewrite mulrS [_ == 1]eq_sym addrC -subr_eq subrr eq_sym pnatr_eq0.
Qed.

Lemma lern0 n : (n%:R <= 0 :> R) = (n == 0).
Proof. by rewrite -pnatr_eq0 eq_le ler0n andbT. Qed.

Lemma ltrn0 n : (n%:R < 0 :> R) = false.
Proof. by rewrite lt_neqAle pnatr_eq0 lern0 andNb. Qed.

Lemma ler_nat m n : (m%:R <= n%:R :> R) = (m <= n)%N.
Proof.
elim: m n => [|m IH] n; rewrite ?ler0n //.
by case: n => [|n]; rewrite ?lern0 // !mulrS lerD2l IH ltnS.
Qed.

Lemma eqr_nat m n : (m%:R == n%:R :> R) = (m == n).
Proof. by rewrite eq_le !ler_nat eqn_leq. Qed.

Lemma ltr_nat m n : (m%:R < n%:R :> R) = (m < n)%N.
Proof. by rewrite lt_neqAle ler_nat eqr_nat ltn_neqAle. Qed.

Lemma ler1n n : (1 <= n%:R :> R) = (1 <= n)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltr1n n : (1 < n%:R :> R) = (1 < n)%N. Proof. by rewrite -ltr_nat. Qed.
Lemma lern1 n : (n%:R <= 1 :> R) = (n <= 1)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltrn1 n : (n%:R < 1 :> R) = (n < 1)%N. Proof. by rewrite -ltr_nat. Qed.

Lemma ltrN10 : -1 < 0 :> R. Proof. by rewrite oppr_lt0. Qed.
Lemma lerN10 : -1 <= 0 :> R. Proof. by rewrite oppr_le0. Qed.
Lemma ltr10 : (1 < 0 :> R) = false. Proof. by rewrite le_gtF. Qed.
Lemma ler10 : (1 <= 0 :> R) = false. Proof. by rewrite lt_geF. Qed.
Lemma ltr0N1 : (0 < -1 :> R) = false. Proof. by rewrite le_gtF // lerN10. Qed.
Lemma ler0N1 : (0 <= -1 :> R) = false. Proof. by rewrite lt_geF // ltrN10. Qed.

Lemma pchar_num : [pchar R] =i pred0.
Proof. by case=> // p /=; rewrite !inE pnatr_eq0 andbF. Qed.

Lemma ler_wpM2l x : 0 <= x -> {homo *%R x : y z / y <= z}.
Proof.
by move=> x_ge0 y z yz; rewrite -subr_ge0 -mulrBr mulr_ge0 // subr_ge0.
Qed.

Lemma ler_wpM2r x : 0 <= x -> {homo *%R^~ x : y z / y <= z}.
Proof.
by move=> x_ge0 y z yz; rewrite -subr_ge0 -mulrBl mulr_ge0 // subr_ge0.
Qed.

Lemma ler_wnM2l x : x <= 0 -> {homo *%R x : y z /~ y <= z}.
Proof. by move=> x_le0 y z leyz; rewrite -![x * _]mulrNN ler_wpM2l ?lterNE. Qed.

Lemma ler_wnM2r x : x <= 0 -> {homo *%R^~ x : y z /~ y <= z}.
Proof. by move=> x_le0 y z leyz; rewrite -![_ * x]mulrNN ler_wpM2r ?lterNE. Qed.

(* Binary forms, for backchaining. *)

Lemma ler_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Proof.
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := le_trans x1ge0 le_xy1.
exact: le_trans (ler_wpM2r x2ge0 le_xy1) (ler_wpM2l y1ge0 le_xy2).
Qed.

(* weak and symmetric lemmas *)
Lemma mulr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. by move=> x_ge0 y_ge0; rewrite -(mulr0 x) ler_wpM2l. Qed.

Lemma mulr_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnM2l. Qed.

Lemma mulr_ge0_le0 x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wpM2l. Qed.

Lemma mulr_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnM2l. Qed.

Fact nneg_mulr_closed : mulr_closed (@nneg R).
Proof.
by split=> [|x y]; [ rewrite nnegrE | exact: mulr_ge0 ].
Qed.
#[export]
HB.instance Definition _ := GRing.isMulClosed.Build R nneg_num_pred
  nneg_mulr_closed.

Fact real_mulr_closed : mulr_closed (@real R).
Proof.
split=> [|x y]; first by rewrite realE ler01.
rewrite !realE => /orP[] x0 /orP[] y0; apply/orP.
- by left; apply: mulr_ge0.
- by right; apply: mulr_ge0_le0.
- by right; apply: mulr_le0_ge0.
- by left; apply: mulr_le0.
Qed.
#[export]
HB.instance Definition _ := GRing.isMulClosed.Build R real_num_pred
  real_mulr_closed.

Lemma real1 : 1 \is @real R. Proof. exact: rpred1. Qed.
#[local] Hint Resolve real1 : core.

Lemma prodr_ge0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 <= E i) -> 0 <= \prod_(i <- r | P i) E i.
Proof. by move=> Ege0; rewrite -nnegrE rpred_prod. Qed.

Lemma prod_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is real} -> \prod_(i <- s | P i) F i \is real.
Proof. by apply/big_real; [apply: rpredM | apply: rpred1]. Qed.

Lemma ler_prod I r (P : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i <= E2 i) ->
  \prod_(i <- r | P i) E1 i <= \prod_(i <- r | P i) E2 i.
Proof.
move=> leE12; elim/(big_load (fun x => 0 <= x)): _.
elim/big_rec2: _ => // i x2 x1 /leE12/andP[le0Ei leEi12] [x1ge0 le_x12].
by rewrite mulr_ge0 // ler_pM.
Qed.

Lemma ler_peMl x y : 0 <= y -> 1 <= x -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wpM2r. Qed.

Lemma ler_neMl x y : y <= 0 -> 1 <= x -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wnM2r. Qed.

Lemma ler_peMr x y : 0 <= y -> 1 <= x -> y <= y * x.
Proof. by move=> hy hx; rewrite -{1}[y]mulr1 ler_wpM2l. Qed.

Lemma ler_neMr x y : y <= 0 -> 1 <= x -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wnM2l. Qed.

Lemma ler_piMl x y : 0 <= y -> x <= 1 -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wpM2r. Qed.

Lemma ler_niMl x y : y <= 0 -> x <= 1 -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wnM2r. Qed.

Lemma ler_piMr x y : 0 <= y -> x <= 1 -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wpM2l. Qed.

Lemma ler_niMr x y : y <= 0 -> x <= 1 -> y <= y * x.
Proof. by move=> hx hy; rewrite -{1}[y]mulr1 ler_wnM2l. Qed.

Lemma mulr_ile1 x y : 0 <= x -> 0 <= y -> x <= 1 -> y <= 1 -> x * y <= 1.
Proof. by move=> *; rewrite (@le_trans _ _ y) ?ler_piMl. Qed.

Lemma prodr_ile1 {I : Type} (s : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> 0 <= F i <= 1) -> \prod_(j <- s | P j) F j <= 1.
Proof.
elim: s => [_ | y s ih xs01]; rewrite ?big_nil// big_cons.
case: ifPn => Py; last by rewrite ih.
have /andP[y0 y1] : 0 <= F y <= 1 by rewrite xs01// mem_head.
rewrite mulr_ile1 ?andbT//; last first.
  by rewrite ih// => e xs; rewrite xs01// in_cons xs orbT.
by rewrite prodr_ge0// => x /xs01 /andP[].
Qed.

Lemma mulr_ilt1 x y : 0 <= x -> 0 <= y -> x < 1 -> y < 1 -> x * y < 1.
Proof. by move=> *; rewrite (@le_lt_trans _ _ y) ?ler_piMl // ltW. Qed.

Definition mulr_ilte1 := (mulr_ile1, mulr_ilt1).

Lemma mulr_ege1 x y : 1 <= x -> 1 <= y -> 1 <= x * y.
Proof.
by move=> le1x le1y; rewrite (@le_trans _ _ y) ?ler_peMl // (le_trans ler01).
Qed.

Lemma exprn_ge0 n x : 0 <= x -> 0 <= x ^+ n.
Proof. by move=> xge0; rewrite -nnegrE rpredX. Qed.

Lemma realX n : {in real, forall x, x ^+ n \is real}.
Proof. exact: rpredX. Qed.

Lemma exprn_ile1 n x : 0 <= x -> x <= 1 -> x ^+ n <= 1.
Proof.
move=> xge0 xle1; elim: n=> [|*]; rewrite ?expr0 // exprS.
by rewrite mulr_ile1 ?exprn_ge0.
Qed.

Lemma exprn_ege1 n x : 1 <= x -> 1 <= x ^+ n.
Proof.
by move=> x_ge1; elim: n=> [|n ihn]; rewrite ?expr0 // exprS mulr_ege1.
Qed.

Lemma ler_iXnr x n : (0 < n)%N -> 0 <= x -> x <= 1 -> x ^+ n <= x.
Proof. by case: n => n // *; rewrite exprS ler_piMr // exprn_ile1. Qed.

Lemma ler_eXnr x n : (0 < n)%N -> 1 <= x -> x <= x ^+ n.
Proof.
case: n => // n _ x_ge1.
by rewrite exprS ler_peMr ?(le_trans _ x_ge1) // exprn_ege1.
Qed.

Lemma ler_wiXn2l x :
  0 <= x -> x <= 1 -> {homo GRing.exp x : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> xge0 xle1 m n /= hmn.
by rewrite -(subnK hmn) exprD ler_piMl ?(exprn_ge0, exprn_ile1).
Qed.

Lemma ler_weXn2l x : 1 <= x -> {homo GRing.exp x : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> xge1 m n /= hmn; rewrite -(subnK hmn) exprD.
by rewrite ler_peMl ?(exprn_ge0, exprn_ege1) // (le_trans _ xge1) ?ler01.
Qed.

(* max and min *)

Lemma natr_min (m n : nat) : (Order.min m n)%:R = Order.min m%:R n%:R :> R.
Proof. by rewrite !minElt ltr_nat /Order.lt/= -fun_if. Qed.

Lemma natr_max (m n : nat) : (Order.max m n)%:R = Order.max m%:R n%:R :> R.
Proof. by rewrite !maxElt ltr_nat /Order.lt/= -fun_if. Qed.

Lemma real_expr2_ge0 x : x \is real -> 0 <= x ^+ 2.
Proof.
by rewrite realE expr2 => /orP[] x0; [apply: mulr_ge0|apply: mulr_le0].
Qed.

Lemma real_exprn_even_ge0 n x : x \is real -> ~~ odd n -> 0 <= x ^+ n.
Proof.
by move=> xR /even_halfK <-; rewrite -muln2 exprM real_expr2_ge0 // rpredX.
Qed.

Lemma real_exprn_even_lt0 n x :
  x \is real -> ~~ odd n -> (x ^+ n < 0) = false.
Proof. by move=> xR n_even; rewrite le_gtF // real_exprn_even_ge0. Qed.

(* Binary sign ((-1) ^+ s). *)

Lemma signr_gt0 (b : bool) : (0 < (-1) ^+ b :> R) = ~~ b.
Proof. by case: b; rewrite (ltr01, ltr0N1). Qed.

Lemma signr_lt0 (b : bool) : ((-1) ^+ b < 0 :> R) = b.
Proof. by case: b; rewrite // ?(ltrN10, ltr10). Qed.

Lemma signr_ge0 (b : bool) : (0 <= (-1) ^+ b :> R) = ~~ b.
Proof. by rewrite le0r signr_eq0 signr_gt0. Qed.

Lemma signr_le0 (b : bool) : ((-1) ^+ b <= 0 :> R) = b.
Proof. by rewrite le_eqVlt signr_eq0 signr_lt0. Qed.

(* This actually holds for char R != 2. *)
Lemma signr_inj : injective (fun b : bool => (-1) ^+ b : R).
Proof. exact: can_inj (fun x => 0 >= x) signr_le0. Qed.

Lemma sgr_def x : sg x = (-1) ^+ (x < 0)%R *+ (x != 0).
Proof. by rewrite /sg; do 2!case: ifP => //. Qed.

Lemma neqr0_sign x : x != 0 -> (-1) ^+ (x < 0)%R = sgr x.
Proof. by rewrite sgr_def  => ->. Qed.

Lemma gtr0_sg x : 0 < x -> sg x = 1.
Proof. by move=> x_gt0; rewrite /sg gt_eqF // lt_gtF. Qed.

Lemma ltr0_sg x : x < 0 -> sg x = -1.
Proof. by move=> x_lt0; rewrite /sg x_lt0 lt_eqF. Qed.

Lemma sgr0 : sg 0 = 0 :> R. Proof. by rewrite /sgr eqxx. Qed.
Lemma sgr1 : sg 1 = 1 :> R. Proof. by rewrite gtr0_sg // ltr01. Qed.
Lemma sgrN1 : sg (-1) = -1 :> R. Proof. by rewrite ltr0_sg // ltrN10. Qed.
Definition sgrE := (sgr0, sgr1, sgrN1).

Lemma sqr_sg x : sg x ^+ 2 = (x != 0)%:R.
Proof. by rewrite sgr_def exprMn_n sqrr_sign -mulnn mulnb andbb. Qed.

Lemma mulr_sg_eq1 x y : (sg x * y == 1) = (x != 0) && (sg x == y).
Proof.
rewrite /sg eq_sym; case: ifP => _; first by rewrite mul0r oner_eq0.
by case: ifP => _; rewrite ?mul1r // mulN1r eqr_oppLR.
Qed.

Lemma mulr_sg_eqN1 x y : (sg x * sg y == -1) = (x != 0) && (sg x == - sg y).
Proof.
move/sg: y => y; rewrite /sg eq_sym eqr_oppLR.
case: ifP => _; first by rewrite mul0r oppr0 oner_eq0.
by case: ifP => _; rewrite ?mul1r // mulN1r eqr_oppLR.
Qed.

Lemma sgr_eq0 x : (sg x == 0) = (x == 0).
Proof.
rewrite /sg; case: ifP => _; first exact: eqxx.
by case: ifP => _; rewrite ?oppr_eq0 oner_eq0.
Qed.

Lemma sgr_odd n x : x != 0 -> (sg x) ^+ n = (sg x) ^+ (odd n).
Proof. by rewrite /sg; do 2!case: ifP => // _; rewrite ?expr1n ?signr_odd. Qed.

Lemma sgr_nat n : sg n%:R = (n != 0)%:R :> R.
Proof. by rewrite /sg pnatr_eq0 ltrn0; case: ifP. Qed.

Lemma sgr_id x : sg (sg x) = sg x.
Proof. by rewrite !(fun_if sg) !sgrE. Qed.

Lemma sgr_lt0 x : (sg x < 0) = (x < 0).
Proof.
rewrite /sg; case: eqP => [-> // | _].
by case: ifP => _; rewrite ?ltrN10 // lt_gtF.
Qed.

Lemma sgr_le0 x : (sgr x <= 0) = (x <= 0).
Proof. by rewrite !le_eqVlt sgr_eq0 sgr_lt0. Qed.

(* leif *)

Lemma leif_nat_r m n C : (m%:R <= n%:R ?= iff C :> R) = (m <= n ?= iff C)%N.
Proof. by rewrite /leif !ler_nat eqr_nat. Qed.

Lemma leifBLR x y z C : (x - y <= z ?= iff C) = (x <= z + y ?= iff C).
Proof. by rewrite /leif !eq_le lerBlDr lerBrDr. Qed.

Lemma leifBRL x y z C : (x <= y - z ?= iff C) = (x + z <= y ?= iff C).
Proof. by rewrite -leifBLR opprK. Qed.

Lemma leifD x1 y1 C1 x2 y2 C2 :
    x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 + x2 <= y1 + y2 ?= iff C1 && C2.
Proof.
rewrite -(mono_leif (C := C1) (lerD2r x2)).
rewrite -(mono_leif (C := C2) (lerD2l y1)).
exact: leif_trans.
Qed.

Lemma leif_sum (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff [forall (i | P i), C i].
Proof.
move=> leE12; rewrite -big_andE.
elim/big_rec3: _ => [|i Ci m2 m1 /leE12]; first by rewrite /leif lexx eqxx.
exact: leifD.
Qed.

Lemma leif_0_sum (I : finType) (P C : pred I) (E : I -> R) :
    (forall i, P i -> 0 <= E i ?= iff C i) ->
  0 <= \sum_(i | P i) E i ?= iff [forall (i | P i), C i].
Proof. by move/leif_sum; rewrite big1_eq. Qed.

(* lteif *)

Lemma subr_lteifr0 C x y : (y - x < 0 ?<= if C) = (y < x ?<= if C).
Proof. by case: C => /=; rewrite subr_lte0. Qed.

Lemma subr_lteif0r C x y : (0 < y - x ?<= if C) = (x < y ?<= if C).
Proof. by case: C => /=; rewrite subr_gte0. Qed.

Definition subr_lteif0 := (subr_lteifr0, subr_lteif0r).

Lemma lteif01 C : 0 < 1 ?<= if C :> R.
Proof. by case: C; rewrite /= lter01. Qed.

Lemma mem0_itvcc_xNx x : (0 \in `[- x, x]) = (0 <= x).
Proof. by rewrite itv_boundlr [in LHS]/<=%O /= oppr_le0 andbb. Qed.

Lemma mem0_itvoo_xNx x : (0 \in `]- x, x[) = (0 < x).
Proof. by rewrite itv_boundlr [in LHS]/<=%O /= oppr_lt0 andbb. Qed.

Lemma oppr_itv ba bb (xa xb x : R) :
  (- x \in Interval (BSide ba xa) (BSide bb xb)) =
  (x \in Interval (BSide (~~ bb) (- xb)) (BSide (~~ ba) (- xa))).
Proof.
by rewrite !itv_boundlr /<=%O /= !implybF negbK andbC lteifNl lteifNr.
Qed.

Lemma oppr_itvoo (a b x : R) : (- x \in `]a, b[) = (x \in `]- b, - a[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvco (a b x : R) : (- x \in `[a, b[) = (x \in `]- b, - a]).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvoc (a b x : R) : (- x \in `]a, b]) = (x \in `[- b, - a[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvcc (a b x : R) : (- x \in `[a, b]) = (x \in `[- b, - a]).
Proof. exact: oppr_itv. Qed.

Section FinGroup.

Variables (gT : finGroupType).
Implicit Types G : {group gT}.

Local Open Scope group_scope.

Lemma natrG_gt0 G : #|G|%:R > 0 :> R.
Proof. by rewrite ltr0n cardG_gt0. Qed.

Lemma natrG_neq0 G : #|G|%:R != 0 :> R.
Proof. by rewrite gt_eqF // natrG_gt0. Qed.

Lemma natr_indexg_gt0 G B : #|G : B|%g%:R > 0 :> R.
Proof. by rewrite ltr0n indexg_gt0. Qed.

Lemma natr_indexg_neq0 G B : #|G : B|%g%:R != 0 :> R.
Proof. by rewrite gt_eqF // natr_indexg_gt0. Qed.

End FinGroup.

End pordered_theory.

Arguments ler01 {R} : rename.
Arguments ltr01 {R}.
Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  solve [apply: ler01 | apply: ler0n | apply: lerN10] : core.
Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  solve [apply: ltr01 | apply: ltr0Sn | apply: ltrN10] : core.

End Theory.

End Num.