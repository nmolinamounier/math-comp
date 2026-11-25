(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop finset fingroup nmodule preorder.
From mathcomp Require Import porder lattice total_order total_order_instances.
From mathcomp Require Import interval rings_modules_and_algebras divalg poly.
From mathcomp Require Import orderedzmod orderedring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import Order.Theory GRing.Theory orderedzmod.Num orderedring.Num.

Module Num.

HB.mixin Record Zmodule_isSemiNormed (R : porderZmodType) M
         & GRing.Zmodule M := {
  norm : M -> R;
  normr_ge0 : forall x, 0 <= norm x;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.

#[short(type="semiNormedZmodType")]
HB.structure Definition SemiNormedZmodule (R : porderZmodType) :=
  { M of Zmodule_isSemiNormed R M & GRing.Zmodule M }.

HB.mixin Record SemiNormedZmodule_isPositiveDefinite
    (R : porderZmodType) M & @SemiNormedZmodule R M := {
  normr0_eq0 : forall x : M, norm x = 0 -> x = 0;
}.

#[short(type="normedZmodType")]
HB.structure Definition NormedZmodule (R : porderZmodType) :=
  { M of SemiNormedZmodule_isPositiveDefinite R M & SemiNormedZmodule R M }.
Arguments norm {R M} x : rename.

HB.factory Record Zmodule_isNormed (R : porderZmodType) M
         & GRing.Zmodule M := {
  norm : M -> R;
  normr_ge0 : forall x, 0 <= norm x;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normr0_eq0 : forall x, norm x = 0 -> x = 0;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.
HB.builders Context (R : POrderZmodule.type) M & Zmodule_isNormed R M.
  HB.instance Definition _ :=
    Zmodule_isSemiNormed.Build R M normr_ge0 ler_normD normrMn normrN.
  HB.instance Definition _ :=
    SemiNormedZmodule_isPositiveDefinite.Build R M normr0_eq0.
HB.end.

HB.mixin Record NzRing_isNormSubMul (R : porderRingType) M
    & SemiNormedZmodule R M & GRing.Ring M := {
  normr1 : @norm _ M 1 = 1 ;
  ler_normM : forall x y : M, norm (x * y) <= norm x * norm y
}.

#[short(type="semiNormedRingType")]
HB.structure Definition SemiNormedRing (R : porderRingType) :=
  { M of GRing.NzRing M & SemiNormedZmodule R M & NzRing_isNormSubMul R M }.

#[short(type="normedRingType")]
HB.structure Definition NormedRing (R : porderRingType) :=
  { M of SemiNormedRing R M & SemiNormedZmodule_isPositiveDefinite R M }.

HB.mixin Record SemiNormedRing_isMulNormed (R : porderRingType) M
    & SemiNormedRing R M := {
  normrM : {morph (norm : M -> R) : x y / x * y}
}.

#[short(type="mulSemiNormedRingType")]
HB.structure Definition MulSemiNormedRing (R : porderRingType) :=
  { M of SemiNormedRing R M & SemiNormedRing_isMulNormed R M }.

#[short(type="mulNormedRingType")]
HB.structure Definition MulNormedRing (R : porderRingType) :=
  { M of NormedRing R M & SemiNormedRing_isMulNormed R M }.

#[short(type="normedFieldType")]
HB.structure Definition NormedField (R : porderRingType) :=
  { F of MulNormedRing R F & GRing.Field F }.

HB.factory Record Ring_isSemiNormed (R : porderRingType) M & GRing.Ring M := {
  norm : M -> R;
  normr_ge0 : forall x, 0 <= norm x;
  normr1 : norm 1 = 1 ;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
  ler_normM : forall x y : M, norm (x * y) <= norm x * norm y
}.
HB.builders Context R M & Ring_isSemiNormed R M.

Let oner_neq0 : 1 != 0 :> M.
Proof.
apply/eqP => /(congr1 norm)/eqP.
by rewrite normr1 -(mulr0n 0) normrMn mulr0n oner_eq0.
Qed.

HB.instance Definition _ := GRing.SemiRing_isNonZero.Build M oner_neq0.
HB.instance Definition _ := Zmodule_isSemiNormed.Build R M
  normr_ge0 ler_normD normrMn normrN.
HB.instance Definition _ := NzRing_isNormSubMul.Build R M normr1 ler_normM. 

HB.end.

HB.factory Record Ring_Ordered_isSemiNormed (R : orderedRingType) M
    & GRing.Ring M := {
  norm : M -> R;
  normr1 : norm 1 = 1 ;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
  ler_normM : forall x y : M, norm (x * y) <= norm x * norm y
}.
HB.builders Context R M & Ring_Ordered_isSemiNormed R M.

Let normr_ge0 (x : M) : 0 <= norm x.
Proof.
rewrite leNgt; apply/negP => Nx0.
suff : norm x *+ 2 < norm x *+ 2 by rewrite ltxx.
apply: (@lt_le_trans _ _ 0); first by rewrite mulrn_llt0.
rewrite mulr2n -[X in _ + X]normrN (le_trans _ (ler_normD _ _)) //.
by rewrite subrr -[in leRHS](mulr0n 0) normrMn mulr0n.
Qed.

HB.instance Definition _ := Ring_isSemiNormed.Build R M
  normr_ge0 normr1 ler_normD normrMn normrN ler_normM.

HB.end.

HB.factory Record Ring_isMulSemiNormed (R : porderRingType) M
    & GRing.Ring M := {
  norm : M -> R;
  normr_ge0 : forall x, 0 <= norm x;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normrM : {morph (norm : M -> R) : x y / x * y};
  normrn : forall n, norm n%:R = n%:R;
  normrN1 : norm (- 1) = 1;
}.
HB.builders Context R M & Ring_isMulSemiNormed R M.

Let normr1 : norm 1 = 1.
Proof. exact: (normrn 1). Qed.

Let normrMn x n : norm (x *+ n) = norm x *+ n.
Proof. by rewrite -mulr_natr normrM normrn mulr_natr. Qed.

Let normrN x : norm (- x) = norm x.
Proof. by rewrite -mulN1r normrM normrN1 mul1r. Qed.

Let ler_normM x y : norm (x * y) <= norm x * norm y.
Proof. by rewrite normrM. Qed.

HB.instance Definition _ := Ring_isSemiNormed.Build R M
  normr_ge0 normr1 ler_normD normrMn normrN ler_normM.
HB.instance Definition _ := SemiNormedRing_isMulNormed.Build R M normrM.

HB.end.

HB.mixin Record Zmodule_isSubSemiNormed (R : porderZmodType)
    (M : semiNormedZmodType R) (S : pred M) U
    & SubType M S U & SemiNormedZmodule R U := {
  norm_valE : forall x : U, norm ((val : U -> M) x) = norm x
}.

#[short(type="subSemiNormedZmodType")]
HB.structure Definition SubSemiNormedZmodule (R : porderZmodType)
    (M : semiNormedZmodType R) (S : pred M) :=
  { U of SubChoice M S U & SemiNormedZmodule R U & GRing.SubZmodule M S U
       & Zmodule_isSubSemiNormed R M S U }.

#[short(type="subNormedZmodType")]
HB.structure Definition SubNormedZmodule (R : porderZmodType)
    (M : semiNormedZmodType R) (S : pred M) :=
  { U of @SubSemiNormedZmodule R M S U & NormedZmodule R U }.

#[short(type="subSemiNormedRingType")]
HB.structure Definition SubSemiNormedRing (R : porderRingType)
    (M : semiNormedRingType R) (S : pred M) :=
  { U of SubChoice M S U & GRing.SubRing M S U & SemiNormedRing R U
      & Zmodule_isSubSemiNormed R M S U }.

#[short(type="subNormedRingType")]
HB.structure Definition SubNormedRing (R : porderRingType)
    (M : semiNormedRingType R) (S : pred M) :=
  { U of SubChoice M S U & GRing.SubRing M S U & NormedRing R U
      & Zmodule_isSubSemiNormed R M S U }.

#[short(type="subMulSemiNormedRingType")]
HB.structure Definition SubMulSemiNormedRing (R : porderRingType)
    (M : semiNormedRingType R) (S : pred M) :=
  { U of SubChoice M S U & GRing.SubRing M S U & MulSemiNormedRing R U
      & Zmodule_isSubSemiNormed R M S U }.

#[short(type="subMulNormedRingType")]
HB.structure Definition SubMulNormedRing (R : porderRingType)
    (M : semiNormedRingType R) (S : pred M) :=
  { U of SubChoice M S U & GRing.SubRing M S U & MulNormedRing R U
      & Zmodule_isSubSemiNormed R M S U }.

#[short(type="subNormedFieldType")]
HB.structure Definition SubNormedField (R : porderRingType)
    (M : normedFieldType R) (S : pred M) :=
  { U of SubChoice M S U & GRing.SubField M S U & NormedField R U
      & Zmodule_isSubSemiNormed R M S U }.

Module NormedScopeExports.
Bind Scope ring_scope with
  SemiNormedZmodule.sort NormedZmodule.sort SemiNormedRing.sort NormedRing.sort
  MulSemiNormedRing.sort MulNormedRing.sort NormedField.sort.
End NormedScopeExports.
HB.export NormedScopeExports.

Module Theory.

End Theory.
End Num.

(*
HB.structure Definition POrderSemiNormedZmodule (R : porderZmodType) :=
  { M of POrderZmodule M & Zmodule_isSemiNormed R M}.

HB.structure Definition POrderNormedZmodule (R : porderZmodType) :=
  { M of POrderZmodule M & Zmodule_isNormed R M}.

HB.structure Definition POrderedSemiNormedZmodule (R : porderZmodType) :=
  { M of POrderedZmodule M & Zmodule_isSemiNormed R M}.

HB.structure Definition POrderedNormedZmodule (R : porderZmodType) :=
  { M of POrderedZmodule M & Zmodule_isNormed R M}. *)