(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop finset fingroup nmodule preorder.
From mathcomp Require Import porder lattice total_order total_order_instances.
From mathcomp Require Import interval rings_modules_and_algebras divalg poly.
From mathcomp Require Import orderedzmod.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import Order.Theory GRing.Theory.
Import orderedzmod.Num.

(* TODO move *)

#[short(type="porderRingType")]
HB.structure Definition POrderRing :=
  { R of GRing.Ring R & Order.POrder ring_display R }.

#[short(type="porderNzRingType")]
HB.structure Definition POrderNzRing :=
  { R of GRing.NzRing R & Order.POrder ring_display R }.

HB.mixin Record Ring_isPOrdered R & POrderRing R := {
  mulr_ge0 : forall x y : R, x >= 0 -> y >= 0 -> x * y >= 0
}.

#[short(type="porderedRingType")]
HB.structure Definition POrderedRing :=
  { R of POrderRing R & Ring_isPOrdered R }.

#[short(type="porderedNzRingType")]
HB.structure Definition POrderedNzRing :=
  { R of POrderNzRing R & Ring_isPOrdered R }.

(* /TODO *)

Module Num.

HB.mixin Record Zmodule_isSemiNormed (R : porderZmodType) M
         & GRing.Zmodule M := {
  norm : M -> R;
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

HB.mixin Record NzRing_isNormSubMul (R : porderRingType) M
    & SemiNormedZmodule R M & GRing.Ring M := {
  normr1 : @norm _ M 1 = 1 ;
  ler_normM : forall x y : M, norm (x * y) <= norm x * norm y
}.

HB.structure Definition SemiNormedRing (R : porderRingType) :=
  { M of GRing.NzRing M & SemiNormedZmodule R M & NzRing_isNormSubMul R M }.

HB.structure Definition NormedRing (R : porderRingType) :=
  { M of SemiNormedRing R M & SemiNormedZmodule_isPositiveDefinite R M }.

HB.mixin Record SemiNormedRing_isMulNormed (R : porderRingType) M
    & SemiNormedRing R M := {
  normrM : {morph (norm : M -> R) : x y / x * y}
}.

HB.structure Definition MulSemiNormedRing (R : porderRingType) :=
  { M of SemiNormedRing R M & SemiNormedRing_isMulNormed R M }.

HB.structure Definition MulNormedRing (R : porderRingType) :=
  { M of NormedRing R M & SemiNormedRing_isMulNormed R M }.

HB.structure Definition NormedField (R : porderRingType) :=
  { F of MulNormedRing R F & GRing.Field F }.

HB.factory Record Ring_isSemiNormed (R : porderNzRingType) M
    & GRing.Ring M := {
  norm : M -> R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
  normr1 : norm 1 = 1;
  ler_normM : forall x y, norm (x * y) <= norm x * norm y
}.
HB.builders Context R M & Ring_isSemiNormed R M.

HB.instance Definition _ :=
  Zmodule_isSemiNormed.Build R M ler_normD normrMn normrN.

Let oner_neq0 : 1 != 0 :> M.
Proof.
apply/eqP => /(congr1 norm) /eqP.
by rewrite normr1 -(mul0rn _ 0) normrMn mulr0n oner_eq0.
Qed.

HB.instance Definition _ := GRing.SemiRing_isNonZero.Build M oner_neq0.
HB.instance Definition _ :=
  NzRing_isNormSubMul.Build R M normr1 ler_normM.

HB.end.

HB.mixin Record Zmodule_isSubNormed (R : porderZmodType) (M : normedZmodType R)
   (S : pred M) U & SubType M S U & NormedZmodule R U := {
  norm_valE : forall x : U, norm ((val : U -> M) x) = norm x
}.

#[short(type="subNormedZmodType")]
HB.structure Definition SubNormedZmodule (R : porderZmodType)
    (M : normedZmodType R) (S : pred M) :=
  { U of SubChoice M S U & Num.NormedZmodule R U & GRing.SubZmodule M S U
       & Zmodule_isSubNormed R M S U }.

HB.factory Record Zmodule_isNormed (R : porderZmodType) M
         & GRing.Zmodule M := {
  norm : M -> R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normr0_eq0 : forall x, norm x = 0 -> x = 0;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.
HB.builders Context (R : POrderZmodule.type) M & Zmodule_isNormed R M.
  HB.instance Definition _ :=
    Zmodule_isSemiNormed.Build R M ler_normD normrMn normrN.
  HB.instance Definition _ :=
    SemiNormedZmodule_isPositiveDefinite.Build R M normr0_eq0.
HB.end.

Module NormedZmoduleExports.
Bind Scope ring_scope with NormedZmodule.sort.
(* Notation "[ 'normedZmodType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (format "[ 'normedZmodType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'normedZmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (format "[ 'normedZmodType'  R  'of'  T ]") : form_scope. *)
End NormedZmoduleExports.
HB.export NormedZmoduleExports.

HB.structure Definition POrderSemiNormedZmodule (R : porderZmodType) :=
  { M of POrderZmodule M & Zmodule_isSemiNormed R M}.

HB.structure Definition POrderNormedZmodule (R : porderZmodType) :=
  { M of POrderZmodule M & Zmodule_isNormed R M}.

HB.structure Definition POrderedSemiNormedZmodule (R : porderZmodType) :=
  { M of POrderedZmodule M & Zmodule_isSemiNormed R M}.

HB.structure Definition POrderedNormedZmodule (R : porderZmodType) :=
  { M of POrderedZmodule M & Zmodule_isNormed R M}.