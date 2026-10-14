/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Jacobian determinant of the blow-up chart map

The chart map `π_i` (`blowUpChartMap σ i`: `x_{σ i} = u_{σ i}`, `x_{σ k} = u_{σ i} u_{σ k}` for
`k ≠ i`, the other coordinates unchanged) has derivative `t ↦ u_{σ i} t_{σ k} + u_{σ k} t_{σ i}`
on the ratio slots and `t ↦ t_j` elsewhere. Its matrix differs from the diagonal matrix with
entries `u_{σ i}` (ratio slots) and `1` (the other slots) only in the column `σ i`, by a vector
vanishing at the row `σ i`; by multilinearity of the determinant in that column the Jacobian
determinant is the diagonal product `u_{σ i}^{c-1}`. For `c ≥ 2` the derivative is therefore
invertible exactly off the exceptional hyperplane `{u_{σ i} = 0}` of the chart.

The chart maps are those of the local model of [BM88, Definition 4.1]; the computation is not in
the source. The determinant enters the Jacobian of the blow-down map of a manifold
(`Hironaka.Manifold.Jacobian.BlowUp`).
-/

@[expose] public section

open scoped ContDiff
open Matrix

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n c : ℕ} (σ : Fin c ↪ Fin n) (i : Fin c) (u : Fin n → 𝕜)

/-- The coordinate projection `Fin n → 𝕜 →L[𝕜] 𝕜` with its ring and fibre fixed. -/
local notation "pr" => ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜)

/-- The derivative of the chart map `π_i` at `u`: `t ↦ u_{σ i} t_j + u_j t_{σ i}` on the ratio
slots `j = σ k`, `k ≠ i`, and `t ↦ t_j` on the other slots. -/
noncomputable def blowUpChartMapDeriv : (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜) := by
  classical
  exact ContinuousLinearMap.pi fun j =>
    if ∃ k, k ≠ i ∧ σ k = j then u (σ i) • pr j + u j • pr (σ i) else pr j

/-- The Fréchet derivative of the chart map `π_i` at `u` is `blowUpChartMapDeriv σ i u`. -/
theorem hasFDerivAt_blowUpChartMap :
    HasFDerivAt (blowUpChartMap σ i) (blowUpChartMapDeriv σ i u) u := by
  classical
  refine hasFDerivAt_pi.mpr fun j => ?_
  by_cases h : ∃ k, k ≠ i ∧ σ k = j
  · simp only [blowUpChartMap, h, ite_true]
    have := (hasFDerivAt_apply (𝕜 := 𝕜) (σ i) u).mul (hasFDerivAt_apply (𝕜 := 𝕜) j u)
    exact this
  · simp only [blowUpChartMap, h, ite_false]
    exact hasFDerivAt_apply (𝕜 := 𝕜) j u

/-- The Fréchet derivative of `π_i`, as an equation. -/
theorem fderiv_blowUpChartMap : fderiv 𝕜 (blowUpChartMap σ i) u = blowUpChartMapDeriv σ i u :=
  (hasFDerivAt_blowUpChartMap σ i u).fderiv

/-- The diagonal of the Jacobian: `u_{σ i}` on the ratio slots, `1` elsewhere. -/
noncomputable def jacobianDiag : Fin n → 𝕜 := by
  classical
  exact fun j => if ∃ k, k ≠ i ∧ σ k = j then u (σ i) else 1

/-- The off-diagonal column `σ i` of the Jacobian: `u_j` on the ratio slots, `0` elsewhere. -/
noncomputable def jacobianCol : Fin n → 𝕜 := by
  classical
  exact fun j => if ∃ k, k ≠ i ∧ σ k = j then u j else 0

/-- The block indices are injective: no `k ≠ i` has `σ k = σ i`. -/
theorem not_exists_ne_and_apply_eq_self : ¬ ∃ k, k ≠ i ∧ σ k = σ i :=
  fun ⟨_, hk, hke⟩ => hk (σ.injective hke)

/-- The matrix of the derivative: the diagonal matrix with the column `σ i` perturbed. -/
theorem toMatrix'_blowUpChartMapDeriv :
    LinearMap.toMatrix' (blowUpChartMapDeriv σ i u : (Fin n → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)) =
      (diagonal (jacobianDiag σ i u)).updateCol (σ i)
        ((fun j => diagonal (jacobianDiag σ i u) j (σ i)) + jacobianCol σ i u) := by
  classical
  ext j k
  rw [LinearMap.toMatrix'_apply, updateCol_apply]
  simp only [Pi.add_apply]
  change blowUpChartMapDeriv σ i u (Pi.single k 1) j = _
  simp only [blowUpChartMapDeriv, ContinuousLinearMap.pi_apply]
  by_cases hk : k = σ i
  · subst hk
    rw [ite_eq_left rfl]
    by_cases h : ∃ l, l ≠ i ∧ σ l = j
    · have hj : j ≠ σ i := fun hji => not_exists_ne_and_apply_eq_self σ i (hji ▸ h)
      rw [ite_eq_left h, _root_.add_apply, _root_.smul_apply, _root_.smul_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.proj_apply, Pi.single_apply,
        Pi.single_apply, ite_eq_right hj, ite_eq_left rfl,
        smul_eq_mul, smul_eq_mul, mul_zero, mul_one, zero_add, diagonal_apply_ne _ hj, zero_add,
        jacobianCol, ite_eq_left h]
    · rw [ite_eq_right h, ContinuousLinearMap.proj_apply, Pi.single_apply, jacobianCol,
        ite_eq_right h, add_zero]
      by_cases hj : j = σ i
      · subst hj
        rw [ite_eq_left rfl, diagonal_apply_eq, jacobianDiag,
          ite_eq_right (not_exists_ne_and_apply_eq_self σ i)]
      · rw [ite_eq_right hj, diagonal_apply_ne _ hj]
  · rw [ite_eq_right hk]
    have hk' : σ i ≠ k := Ne.symm hk
    by_cases h : ∃ l, l ≠ i ∧ σ l = j
    · rw [ite_eq_left h, _root_.add_apply, _root_.smul_apply, _root_.smul_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.proj_apply, Pi.single_apply,
        Pi.single_apply, ite_eq_right hk', smul_eq_mul,
        smul_eq_mul, mul_zero, add_zero, diagonal_apply, jacobianDiag, ite_eq_left h]
      split_ifs <;> simp
    · rw [ite_eq_right h, ContinuousLinearMap.proj_apply, Pi.single_apply, diagonal_apply,
        jacobianDiag, ite_eq_right h]

/-- The diagonal product: `u_{σ i}^{c - 1}`. -/
theorem prod_jacobianDiag : ∏ j, jacobianDiag σ i u j = u (σ i) ^ (c - 1) := by
  classical
  simp only [jacobianDiag]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1
  have himg : (Finset.univ.filter fun j : Fin n => ∃ k, k ≠ i ∧ σ k = j) =
      (Finset.univ.erase i).image σ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase,
      and_true]
  rw [himg, Finset.card_image_of_injective _ σ.injective,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

variable {i} in
/-- The Jacobian determinant of the chart map `π_i` is `u_{σ i}^{c-1}`. -/
theorem det_fderiv_blowUpChartMap :
    (fderiv 𝕜 (blowUpChartMap σ i) u).det = u (σ i) ^ (c - 1) := by
  classical
  rw [fderiv_blowUpChartMap]
  change LinearMap.det (blowUpChartMapDeriv σ i u : (Fin n → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)) = _
  rw [← LinearMap.det_toMatrix', toMatrix'_blowUpChartMapDeriv, det_updateCol_add,
    updateCol_eq_self, det_diagonal, prod_jacobianDiag, det_eq_zero_of_row_eq_zero (σ i), add_zero]
  intro k
  rw [updateCol_apply]
  split_ifs with hk
  · simp [jacobianCol]
  · exact diagonal_apply_ne _ (Ne.symm hk)

end Manifold
