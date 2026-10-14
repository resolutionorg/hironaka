/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Order
public import Hironaka.Manifold.Germ.CoordDeriv
public import Hironaka.Manifold.Germ.TaylorHom
public import Mathlib.RingTheory.MvPowerSeries.Derivative
import Hironaka.Manifold.Germ.CoordDerivChart
import Hironaka.Manifold.IdealSheaf.Order
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Order one at a point

A germ `s ∈ 𝒪_{M,a}` has order one (`ordElem`, the order read on the Taylor series) iff its value
`s(a)` vanishes and some first partial derivative `∂_i s (a)` does not
(`ord_eq_one_iff_exists_coordDerivStalk_ne_zero'`): the degree-`0` coefficient of the Taylor series
is the value (`IsTaylorHom.constantCoeff'`), the degree-`1` coefficients are the partial derivatives
(`IsTaylorHom.pderiv`: `T (∂_i s) = ∂_{X_i} (T s)`), and a power series has order one iff its
constant term vanishes and some linear term does not (`MvPowerSeries.order_eq_one_iff'`, from
`MvPowerSeries.order_eq_nat`). This is the criterion behind Kollár's "local section of `MC(I)` that
has order 1 at `x`" [Kol07, Theorem 80, proof], made chart-free in
`Hironaka/Manifold/Chart/Adapted.lean`.
-/

public section

noncomputable section

open TopologicalSpace Filter Topology Set IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M} (ha : a ∈ φ.source)

/-- The constant coefficient of `∂_{X_i} F` is the coefficient of `X_i` in `F`. -/
theorem constantCoeff_pderiv (i : Fin n) (F : MvPowerSeries (Fin n) 𝕜) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := 𝕜) i F) =
      MvPowerSeries.coeff (Finsupp.single i 1) F := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

/-- The value at `a` of `∂_i s` is the coefficient of `X_i` in the Taylor series of `s`. -/
theorem eval_coordDerivStalk (i : Fin n) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    eval 𝕜 E M a (coordDerivStalk E ψ φ hφ ha i s) =
      MvPowerSeries.coeff (Finsupp.single i 1) (taylorHom E ψ φ ha hφ s) := by
  rw [← IsTaylorHom.constantCoeff' E ψ φ ha (isTaylorHom_taylorHom E ψ φ ha hφ),
    IsTaylorHom.pderiv E ψ φ hφ ha (isTaylorHom_taylorHom E ψ φ ha hφ) i s,
    constantCoeff_pderiv]

/-- A multi-index of degree one is a single index. -/
theorem _root_.Finsupp.degree_eq_one_iff {σ : Type*} (d : σ →₀ ℕ) :
    Finsupp.degree d = 1 ↔ ∃ i, d = Finsupp.single i 1 := by
  classical
  constructor
  · intro hd
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    have hi0 : d i ≠ 0 := by simpa using hi
    have hdi : d i ≤ 1 := hd ▸ Finsupp.le_degree i d
    have hdi1 : d i = 1 := by omega
    refine ⟨i, Finsupp.ext fun j => ?_⟩
    by_cases hji : j = i
    · subst hji
      simp [hdi1]
    · rw [Finsupp.single_eq_of_ne hji]
      by_contra hj
      have : d i + d j ≤ Finsupp.degree d := by
        rw [Finsupp.degree_apply]
        exact Finset.add_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hi0)
          (Finsupp.mem_support_iff.mpr hj) (Ne.symm hji)
      omega
  · rintro ⟨i, rfl⟩
    simp [Finsupp.degree_single]

/-- A power series has order one iff its constant term vanishes and some coefficient of degree
one does not. -/
theorem _root_.MvPowerSeries.order_eq_one_iff' (F : MvPowerSeries (Fin n) 𝕜) :
    F.order = 1 ↔ MvPowerSeries.constantCoeff F = 0 ∧
      ∃ i, MvPowerSeries.coeff (Finsupp.single i 1) F ≠ 0 := by
  rw [← Nat.cast_one, MvPowerSeries.order_eq_nat]
  constructor
  · rintro ⟨⟨d, hd, hdeg⟩, hlt⟩
    refine ⟨by simpa using hlt 0 (by simp), ?_⟩
    obtain ⟨i, rfl⟩ := (Finsupp.degree_eq_one_iff d).mp hdeg
    exact ⟨i, hd⟩
  · rintro ⟨h0, i, hi⟩
    refine ⟨⟨Finsupp.single i 1, hi, by simp⟩, fun d hd => ?_⟩
    have : d = 0 := by
      rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hd
      exact hd
    subst this
    simpa using h0

/-- In a chart `φ` at `a` with coordinates `ψ`, a germ has order one iff it vanishes at `a` and
some partial derivative `∂_i` does not (the order-one sections of [Kol07, Theorem 80, proof]). -/
theorem ord_eq_one_iff_exists_coordDerivStalk_ne_zero'
    (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    ordElem s = 1 ↔
      eval 𝕜 E M a s = 0 ∧ ∃ i, eval 𝕜 E M a (coordDerivStalk E ψ φ hφ ha i s) ≠ 0 := by
  rw [IdealSheaf.ordElem_eq_order_taylorHom ψ φ hφ ha s, MvPowerSeries.order_eq_one_iff',
    IsTaylorHom.constantCoeff' E ψ φ ha (isTaylorHom_taylorHom E ψ φ ha hφ)]
  simp_rw [eval_coordDerivStalk E ψ φ hφ ha]

end Manifold

end
