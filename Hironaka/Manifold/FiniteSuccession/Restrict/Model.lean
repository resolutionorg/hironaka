/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold
public import Hironaka.Manifold.BlowUp.Defs
import Hironaka.Manifold.BlowUp.Transition
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The blow-up chart map in the coordinates of a flag

The identification `S_{i+1} ≅ Bl_{Z_i ∩ S_i} S_i` of the stages of a restricted blow-up sequence
[Kol07, Definition 30.2] is checked in charts. Kollár's computation for a hypersurface
`S = (x_1 = 0)` containing the centre [Kol07, Theorem 88, proof] observes that the blow-up charts
whose distinguished coordinate is not `x_1` cover the strict transform `S_1`; this module carries
out the corresponding computation in a flag chart, for arbitrary codimensions. In a flag chart
`Y = {z_σ = 0} ⊆ S = {z_{σ (τ j)} = 0}` (`τ : Fin s ↪ Fin c`) the blow-up chart map
`blowUpChartMap σ i` of [BM88, Definition 4.1] for an index `i ∉ range τ` preserves the coordinate
subspace `{z_{σ (τ j)} = 0}` and acts on the complementary coordinates `𝕜^{n-s}` (`projCompl`,
`embedCompl` along `τ.trans σ`) as the blow-up chart map of the induced data: the embedding
`restrictEmb σ τ : Fin (c - s) ↪ Fin (n - s)` of the remaining centre indices `σ k`, `k ∉ range τ`,
among the complementary coordinates, and the index `restrictIdx τ hi` of `i` among them. This is
the computation behind the description of the blow-up charts of `S'` as the ambient charts of
index `∉ range τ` read in the complementary coordinates. Not in the sources beyond Kollár's
remark; the proofs are coordinate computations.
-/

@[expose] public section

noncomputable section

open Set

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n c s : ℕ}

/-- The index of `σ k`, `k ∉ range τ`, among the complementary coordinates of `τ.trans σ`. -/
theorem apply_notMem_range_trans {σ : Fin c ↪ Fin n} {τ : Fin s ↪ Fin c} {k : Fin c}
    (hk : k ∉ Set.range τ) : σ k ∉ Set.range (τ.trans σ) := by
  rintro ⟨j, hj⟩
  exact hk ⟨j, σ.injective hj⟩

/-- The remaining centre indices `σ k`, `k ∉ range τ`, read among the coordinates of `𝕜^{n-s}`
complementary to `range (τ.trans σ)`: the block embedding of the centre `Y ⊆ S` inside the
bundled `S`. -/
def restrictEmb (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c) : Fin (c - s) ↪ Fin (n - s) where
  toFun m := complEquiv (τ.trans σ)
    ⟨σ ((complEquiv τ).symm m).1, apply_notMem_range_trans ((complEquiv τ).symm m).2⟩
  inj' m m' h := by
    have h1 := (complEquiv (τ.trans σ)).injective h
    exact (complEquiv τ).symm.injective (Subtype.ext (σ.injective (congrArg Subtype.val h1)))

theorem restrictEmb_apply (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c) (m : Fin (c - s)) :
    restrictEmb σ τ m = complEquiv (τ.trans σ)
      ⟨σ ((complEquiv τ).symm m).1, apply_notMem_range_trans ((complEquiv τ).symm m).2⟩ :=
  rfl

/-- The coordinate of `𝕜^n` read by the `m`-th coordinate of `restrictEmb σ τ`. -/
theorem symm_restrictEmb (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c) (m : Fin (c - s)) :
    ((complEquiv (τ.trans σ)).symm (restrictEmb σ τ m)).1 = σ ((complEquiv τ).symm m).1 := by
  rw [restrictEmb_apply, Equiv.symm_apply_apply]

/-- The index of a centre index `i ∉ range τ` among the remaining ones. -/
def restrictIdx (τ : Fin s ↪ Fin c) {i : Fin c} (hi : i ∉ Set.range τ) : Fin (c - s) :=
  complEquiv τ ⟨i, hi⟩

theorem symm_restrictIdx (τ : Fin s ↪ Fin c) {i : Fin c} (hi : i ∉ Set.range τ) :
    ((complEquiv τ).symm (restrictIdx τ hi)).1 = i := by
  rw [restrictIdx, Equiv.symm_apply_apply]

theorem symm_restrictEmb_restrictIdx (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c) {i : Fin c}
    (hi : i ∉ Set.range τ) :
    ((complEquiv (τ.trans σ)).symm (restrictEmb σ τ (restrictIdx τ hi))).1 = σ i := by
  rw [symm_restrictEmb, symm_restrictIdx]

theorem restrictIdx_ne (τ : Fin s ↪ Fin c) {i k : Fin c} (hi : i ∉ Set.range τ)
    (hk : k ∉ Set.range τ) (hki : k ≠ i) : restrictIdx τ hk ≠ restrictIdx τ hi := fun h =>
  hki (congrArg Subtype.val ((complEquiv τ).injective h))

/-- A complementary coordinate reading `σ k`, `k ∉ range τ`, is the `restrictIdx`-th coordinate of
`restrictEmb`. -/
theorem eq_restrictEmb_restrictIdx (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c) {m : Fin (n - s)}
    {k : Fin c} (hk : k ∉ Set.range τ) (h : ((complEquiv (τ.trans σ)).symm m).1 = σ k) :
    m = restrictEmb σ τ (restrictIdx τ hk) := by
  apply (complEquiv (τ.trans σ)).symm.injective
  apply Subtype.ext
  rw [symm_restrictEmb_restrictIdx]
  exact h

/-- A complementary coordinate off the block of `σ` is off the block of `restrictEmb σ τ`. -/
theorem restrictEmb_ne_of_forall_ne (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c) {m : Fin (n - s)}
    (hm : ∀ k, σ k ≠ ((complEquiv (τ.trans σ)).symm m).1) : ∀ k', restrictEmb σ τ k' ≠ m := by
  intro k' h
  apply hm ((complEquiv τ).symm k').1
  rw [← h, symm_restrictEmb]

/-- In the complementary coordinates of `τ.trans σ`, the blow-up chart map of an index
`i ∉ range τ` is the blow-up chart map of the induced data `(restrictEmb σ τ, restrictIdx τ hi)`;
compare the charts covering the strict transform `S_1` in [Kol07, Theorem 88, proof]. -/
theorem projCompl_blowUpChartMap (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c) {i : Fin c}
    (hi : i ∉ Set.range τ) (x : Fin n → 𝕜) :
    projCompl (τ.trans σ) (blowUpChartMap σ i x) =
      blowUpChartMap (restrictEmb σ τ) (restrictIdx τ hi) (projCompl (τ.trans σ) x) := by
  funext m
  have hj : ((complEquiv (τ.trans σ)).symm m).1 ∉ Set.range (τ.trans σ) :=
    ((complEquiv (τ.trans σ)).symm m).2
  change blowUpChartMap σ i x ((complEquiv (τ.trans σ)).symm m).1 = _
  rcases exists_eq_or_forall_ne σ ((complEquiv (τ.trans σ)).symm m).1 with ⟨k, hk⟩ | hoff
  · have hk' : k ∉ Set.range τ := fun ⟨j', hj'⟩ =>
      hj ⟨j', by rw [Function.Embedding.trans_apply, hj', hk]⟩
    have hm : m = restrictEmb σ τ (restrictIdx τ hk') := eq_restrictEmb_restrictIdx σ τ hk' hk.symm
    rw [hm, symm_restrictEmb_restrictIdx]
    by_cases hki : k = i
    · subst hki
      rw [blowUpChartMap_apply_scaling, blowUpChartMap_apply_scaling]
      exact (congrArg x (symm_restrictEmb_restrictIdx σ τ _)).symm
    · rw [blowUpChartMap_apply_ratio σ x hki, blowUpChartMap_apply_ratio (restrictEmb σ τ)
        (projCompl (τ.trans σ) x) (restrictIdx_ne τ hi hk' hki)]
      exact congrArg₂ (· * ·) (congrArg x (symm_restrictEmb_restrictIdx σ τ hi)).symm
        (congrArg x (symm_restrictEmb_restrictIdx σ τ hk')).symm
  · rw [blowUpChartMap_apply_off σ x hoff, blowUpChartMap_apply_off (restrictEmb σ τ)
      (projCompl (τ.trans σ) x) (restrictEmb_ne_of_forall_ne σ τ hoff)]
    rfl

/-- The blow-up chart map of an index `i ∉ range τ` preserves the coordinate subspace
`{z_{σ (τ j)} = 0}`, on which it is the blow-up chart map of the induced data read through
`embedCompl`. -/
theorem blowUpChartMap_embedCompl (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c) {i : Fin c}
    (hi : i ∉ Set.range τ) (v : Fin (n - s) → 𝕜) :
    blowUpChartMap σ i (embedCompl (τ.trans σ) v) =
      embedCompl (τ.trans σ) (blowUpChartMap (restrictEmb σ τ) (restrictIdx τ hi) v) := by
  funext j
  by_cases hj : j ∈ Set.range (τ.trans σ)
  · obtain ⟨j', rfl⟩ := hj
    rw [embedCompl_apply_range, Function.Embedding.trans_apply,
      blowUpChartMap_apply_ratio σ (embedCompl (τ.trans σ) v) (fun h => hi ⟨j', h⟩),
      ← Function.Embedding.trans_apply,
      embedCompl_apply_range, mul_zero]
  · have h1 := congrFun (projCompl_blowUpChartMap σ τ hi (embedCompl (τ.trans σ) v))
      (complEquiv (τ.trans σ) ⟨j, hj⟩)
    rw [projCompl_embedCompl] at h1
    simp only [projCompl, Equiv.symm_apply_apply] at h1
    rw [h1]
    simp only [embedCompl, dite_eq_right hj]

end Manifold

end
