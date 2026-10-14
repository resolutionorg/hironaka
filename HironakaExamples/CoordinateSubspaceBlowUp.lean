/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Exceptional  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.CoordinateSubspace.ExceptionalProj  -- shake: keep (used only by `example`s)
import HironakaExamples.BlowUp.CoordinateSubspace.Transition  -- shake: keep (used only by `example`s)
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth

/-!
# The blow-up of a coordinate subspace in Hauser's examples

[Hau14, Example 4.34]: the blow-up of `𝔸²_k` at the origin, `I = (x, y)`, with its two charts
`k[x, t₂]` (`t₂ = y/x`) and `k[t₁, y]` (`t₁ = x/y`); and [Hau14, Example 4.47]: the blow-up of
`𝔸³_k` along the `z`-axis `V(x, y)`, with its two chart transition maps. The `example`s
instantiate the model blow-up of `Hironaka/Scheme/BlowUp/CoordinateSubspace/` (the blow-up of `𝔸ⁿ_k`
along the coordinate subspace `x_0 = ⋯ = x_{r−1} = 0`: its charts, their transitions, smoothness,
and the exceptional divisor) at `n = 2 = r` and at `n = 3`, `r = 2`, over a field `k`, the
variables being `x = x_0`, `y = x_1` (and `z = x_2`). The clause `F ≅ ℙ¹_k` of Example 4.34 is
instantiated from `exists_iso_exceptional_proj` at `n = r = 2`.
-/

-- The module consists of `example`s only, so it declares nothing public.
set_option linter.privateModule false

namespace Hironaka.BlowUp.CoordinateSubspace.Examples

open AlgebraicGeometry.CoordinateSubspace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory MvPolynomial Hironaka.BlowUp
open Hironaka.BlowUp.CoordinateSubspace affineBlowUpAlgebra

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k]

section PointOfPlane

/-! ### Hauser's Example 4.34: `𝔸²` blown up at the origin (`n = 2 = r`) -/

/-- The chart of `x` (Hauser's `k[x, t₂]`) is an open immersion into the blow-up. -/
example : IsOpenImmersion (modelChart k 2 2 0 zero_lt_two) := inferInstance

/-- The two charts cover the blow-up. -/
example : ⨆ (j : Fin 2) (hj : j.val < 2), (modelChart k 2 2 j hj).opensRange = ⊤ :=
  iSup_opensRange_modelChart k 2 2

/-- The chart map `π_0` of the chart of `x` is `x ↦ x`, `y ↦ y x` (Hauser's
`(x, t₂) ↦ (x, x t₂)`). -/
example : chartSubst k (center 2 2) 0 (X 1) = X 1 * X 0 := by
  rw [chartSubst_X, ite_eq_left ⟨one_lt_two, one_ne_zero⟩]

example : chartSubst k (center 2 2) 0 (X 0) = X 0 := by
  rw [chartSubst_X, ite_eq_right fun h => h.2 rfl]

/-- Inside the chart of `x`, the chart of `y` is `D(t₂)`. -/
example :
    modelChart k 2 2 0 zero_lt_two ⁻¹ᵁ (modelChart k 2 2 1 one_lt_two).opensRange =
      PrimeSpectrum.basicOpen (X 1 : MvPolynomial (Fin 2) k) :=
  modelChart_preimage_modelChart k 2 2 0 1 zero_lt_two one_lt_two zero_ne_one

/-- The transition `τ_{01}` from the chart of `x` to the chart of `y` is `x ↦ 1/t₂`, `y ↦ x t₂`
(Hauser's `t₁ = 1/t₂`, `y = x t₂`). -/
example :
    modelTransition k 2 2 0 1 (X 0) =
      IsLocalization.Away.invSelf (X 1 : MvPolynomial (Fin 2) k) := by
  rw [modelTransition_X, ite_eq_right zero_ne_one, ite_eq_left rfl]

example :
    modelTransition k 2 2 0 1 (X 1) =
      algebraMap (MvPolynomial (Fin 2) k) (Localization.Away (X 1 : MvPolynomial (Fin 2) k))
        (X 0 * X 1) := by
  rw [modelTransition_X, ite_eq_left rfl]

/-- The two charts are glued along `τ_{01}`. -/
example :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 2) k)
        (Localization.Away (X 1 : MvPolynomial (Fin 2) k)))) ≫ modelChart k 2 2 0 zero_lt_two =
      Spec.map (CommRingCat.ofHom (modelTransition k 2 2 0 1).toRingHom) ≫
        modelChart k 2 2 1 one_lt_two :=
  modelTransition_spec k 2 2 0 1 zero_lt_two one_lt_two zero_ne_one

/-- The blow-up of the plane at a point is a smooth surface over `k`. -/
example :
    SmoothOfRelativeDimension 2 (affineBlowUp.π (centerIdeal k 2 2) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 2) k)))) :=
  smoothOfRelativeDimension_modelBlowUp k 2 2

/-- In the chart of `x` the exceptional curve is `V(x)`. -/
example :
    (affineBlowUp.exceptionalIdeal (centerIdeal k 2 2)).comap (modelChart k 2 2 0 zero_lt_two) =
      Scheme.IdealSheafData.ofIdealTop ((Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}).map
        (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom) :=
  comap_exceptionalIdeal_modelChart k 2 2 0 zero_lt_two

/-- `k[x, t₂]/(x)` is a polynomial ring in one variable (the exceptional curve in the chart is the
affine line `𝔸¹_k`), smooth of relative dimension `1`. -/
example : Nat.card {i : Fin 2 // i ≠ 0} = 1 := card_ne (0 : Fin 2)

example :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 2) k)})))) :=
  smoothOfRelativeDimension_quotient_span_X k (0 : Fin 2)

/-! [Hau14, Example 4.34]: the exceptional curve `F` of the blow-up of `𝔸²_k` at the origin is
`ℙ¹_k`. In general `F ≅ ℙ¹_L = Proj 𝒪(L)[u₀, u₁]` over the center `L = Spec 𝒪(L)`,
`𝒪(L) = k[x, y]/(x, y)`; here `L` is the origin, `𝒪(L) ≅ k` (the quotient by all the variables is
the polynomial ring in no variables), so `ℙ¹_L = ℙ¹_k`. -/

/-- The center of the point blow-up is the point: `k[x, y]/(x, y) ≅ k`. -/
noncomputable example : (MvPolynomial (Fin 2) k ⧸ centerIdeal k 2 2) ≃ₐ[k] k :=
  have : IsEmpty {i : Fin 2 // ¬ i.val < 2} := ⟨fun i => i.2 i.1.2⟩
  (quotientCenterAlgEquiv k 2 2).trans (MvPolynomial.isEmptyAlgEquiv k _)

/-- `F ≅ ℙ¹_{𝒪(L)}`, with `F ∩ U_j = D₊(u_j)` for the two charts and compatibly with the
projections to the origin and to `𝔸²_k`. -/
example :
    ∃ e : (affineBlowUp.exceptionalIdeal (centerIdeal k 2 2)).subscheme ≅
        Proj (homogeneousSubmodule (Fin 2) (MvPolynomial (Fin 2) k ⧸ centerIdeal k 2 2)),
      (∀ (j : Fin 2) (hj : j.val < 2),
        e.hom ''ᵁ ((affineBlowUp.exceptionalIdeal (centerIdeal k 2 2)).subschemeι ⁻¹ᵁ
            (modelChart k 2 2 j hj).opensRange) =
          Proj.basicOpen _ (X (⟨j, hj⟩ : Fin 2))) ∧
      e.inv ≫ (affineBlowUp.exceptionalIdeal (centerIdeal k 2 2)).subschemeι ≫
          affineBlowUp.π (centerIdeal k 2 2) =
        Proj.toSpecZero _ ≫
          Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 2) k ⧸ centerIdeal k 2 2)
            (homogeneousSubmodule (Fin 2) (MvPolynomial (Fin 2) k ⧸ centerIdeal k 2 2) 0))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal k 2 2))) :=
  exists_iso_exceptional_proj k 2 2 le_rfl

end PointOfPlane

section AxisOfSpace

/-! ### Hauser's Example 4.47: `𝔸³` blown up along the `z`-axis (`n = 3`, `r = 2`) -/

/-- The chart map of the chart of `x` is `x ↦ x`, `y ↦ y x`, `z ↦ z`. -/
example : chartSubst k (center 3 2) 0 (X 1) = X 1 * X 0 := by
  rw [chartSubst_X, ite_eq_left ⟨one_lt_two, one_ne_zero⟩]

example : chartSubst k (center 3 2) 0 (X 2) = X 2 := by
  rw [chartSubst_X, ite_eq_right fun h => lt_irrefl 2 h.1]

/-- Hauser's Example 4.47, "compute the two chart transition maps": `τ_{01}` is `x ↦ 1/y`,
`y ↦ x y`, `z ↦ z`. -/
example :
    modelTransition k 3 2 0 1 (X 0) =
      IsLocalization.Away.invSelf (X 1 : MvPolynomial (Fin 3) k) := by
  rw [modelTransition_X, ite_eq_right zero_ne_one, ite_eq_left rfl]

example :
    modelTransition k 3 2 0 1 (X 1) =
      algebraMap (MvPolynomial (Fin 3) k) (Localization.Away (X 1 : MvPolynomial (Fin 3) k))
        (X 0 * X 1) := by
  rw [modelTransition_X, ite_eq_left rfl]

example :
    modelTransition k 3 2 0 1 (X 2) =
      algebraMap (MvPolynomial (Fin 3) k) (Localization.Away (X 1 : MvPolynomial (Fin 3) k))
        (X 2) := by
  rw [modelTransition_X, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide)]

/-- `τ_{10}` is `x ↦ x y`, `y ↦ 1/x`, `z ↦ z`, and the two charts are glued along it. -/
example :
    modelTransition k 3 2 1 0 (X 1) =
      IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin 3) k) := by
  rw [modelTransition_X, ite_eq_right one_ne_zero, ite_eq_left rfl]

example :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 3) k)
        (Localization.Away (X 0 : MvPolynomial (Fin 3) k)))) ≫ modelChart k 3 2 1 one_lt_two =
      Spec.map (CommRingCat.ofHom (modelTransition k 3 2 1 0).toRingHom) ≫
        modelChart k 3 2 0 zero_lt_two :=
  modelTransition_spec k 3 2 1 0 one_lt_two zero_lt_two one_ne_zero

/-- The blow-up of `𝔸³` along a line is smooth of relative dimension `3` over `k`. -/
example :
    SmoothOfRelativeDimension 3 (affineBlowUp.π (centerIdeal k 3 2) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 3) k)))) :=
  smoothOfRelativeDimension_modelBlowUp k 3 2

/-- The `z`-axis is `Spec k[z]`: `k[x, y, z]/(x, y) ≃ k[z]`, `z ↦ z`. -/
example :
    quotientCenterAlgEquiv k 3 2 (Ideal.Quotient.mk _ (X 2)) = X ⟨2, lt_irrefl 2⟩ :=
  quotientCenterAlgEquiv_mk_X k 3 2 (lt_irrefl 2)

/-- In the chart of `x`, the exceptional surface `V(x)` is `𝔸¹_L = L × 𝔸¹` over the `z`-axis `L`,
with fibre coordinate `t = y/x`: `k[x, t, z]/(x) ≃ (k[x, y, z]/(x, y))[t]`. -/
example :
    letI : Algebra (MvPolynomial (Fin 3) k ⧸ centerIdeal k 3 2)
        (MvPolynomial (Fin 3) k ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 3) k)}) :=
      (Ideal.quotientMap (Ideal.span {(X 0 : MvPolynomial (Fin 3) k)})
        (chartSubst k (center 3 2) 0).toRingHom (centerIdeal_le_comap_chartSubst k 3 2 0)).toAlgebra
    ∃ e : (MvPolynomial (Fin 3) k ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 3) k)})
        ≃ₐ[MvPolynomial (Fin 3) k ⧸ centerIdeal k 3 2]
          MvPolynomial {i : Fin 3 // i.val < 2 ∧ i ≠ 0}
            (MvPolynomial (Fin 3) k ⧸ centerIdeal k 3 2),
      ∀ i (h : i.val < 2 ∧ i ≠ 0), e (Ideal.Quotient.mk _ (X i)) = X ⟨i, h⟩ :=
  exists_algEquiv_quotient_span_X_over_center k 3 2 0 zero_lt_two

end AxisOfSpace

end Hironaka.BlowUp.CoordinateSubspace.Examples
