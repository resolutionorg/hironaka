/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold
public import Hironaka.Manifold.StructureSheaf
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Adapted coordinates as generators

On the source of an adapted chart `(φ, σ)` for `Y`, the adapted coordinates `z_i := ψ_{σ i} ∘ φ` —
the sections `chartSection E ψ φ hφ (σ i)` of `𝒪_M` over the chart domain — have `Y` as their
common zero set and linearly independent differentials at every point of the domain: the
differential of `z_i` is the coordinate functional `π_{σ i} ∘ ψ` composed with the derivative of
the chart, which is onto (a chart of the maximal atlas has an analytic inverse, so its manifold
derivative is invertible: Mathlib's `OpenPartialHomeomorph.MDifferentiable.mfderiv_surjective`,
reached through `mdifferentiable_of_mem_maximalAtlas`), and the coordinate functionals
`π_{σ i} ∘ ψ` are independent (`linearIndependent_coordFunctional`). So a closed submanifold is
locally the common zero set of `c` sections with independent differentials
(`IsClosedSubmanifold.exists_generators'`), a smooth subspace being "locally a coordinate subspace
of a coordinate chart" [BM97, (3.8)(2)]; the converse (generators with independent differentials
complete to an adapted chart) is the chart-extension theorem of
`Hironaka/Manifold/AdaptedChart.lean`.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Y : Set M} {φ : OpenPartialHomeomorph M E} {c : ℕ} {σ : Fin c ↪ Fin n}

/-- A chart of the maximal atlas is a differentiable open partial homeomorphism in Mathlib's sense
(`OpenPartialHomeomorph.MDifferentiable`, whose `mfderiv` is a continuous linear equivalence,
`mfderiv_surjective`, …). Mathlib's `mdifferentiable_of_mem_atlas` asks for an `IsManifold`
instance; this is the maximal-atlas form, from Mathlib's `contMDiffOn_of_mem_maximalAtlas` and
`contMDiffOn_symm_of_mem_maximalAtlas`. -/
theorem mdifferentiable_of_mem_maximalAtlas (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    φ.MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E) :=
  ⟨(contMDiffOn_of_mem_maximalAtlas hφ).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas hφ).mdifferentiableOn (by simp)⟩

/-- The coordinate functional `π_j ∘ ψ`. -/
def coordFunctional (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (j : Fin n) : E →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) j).comp (ψ : E →L[𝕜] (Fin n → 𝕜))

/-- The coordinate functional `π_j ∘ ψ` evaluated at `v` (unfolding lemma). -/
theorem coordFunctional_apply (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (j : Fin n) (v : E) :
    coordFunctional ψ j v = ψ v j := rfl

/-- The coordinate functionals `π_{σ i} ∘ ψ`, `i : Fin c`, are linearly independent. -/
theorem linearIndependent_coordFunctional (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (σ : Fin c ↪ Fin n) :
    LinearIndependent 𝕜 fun i => coordFunctional ψ (σ i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := congrArg (fun L : E →L[𝕜] 𝕜 => L (ψ.symm (Pi.single (σ j) 1))) hg
  simp only [sum_apply, smul_apply, coordFunctional_apply, ContinuousLinearEquiv.apply_symm_apply,
    zero_apply, smul_eq_mul] at this
  rwa [Finset.sum_eq_single j (fun i _ hi => by
      rw [Pi.single_apply, ite_eq_right (σ.injective.ne hi), mul_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one] at this

/-- The adapted coordinates `ψ_{σ i} ∘ φ` have independent differentials at every point of the
chart domain. -/
theorem IsAdaptedChart.hasIndependentDifferentialsAt (h : IsAdaptedChart ψ Y φ σ) {x : M}
    (hx : x ∈ φ.source) :
    HasIndependentDifferentialsAt E (fun i y => ψ (φ y) (σ i)) x := by
  have hD := (mdifferentiable_of_mem_maximalAtlas h.1).mfderiv_surjective hx
  have hφ' : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E) φ x :=
    (mdifferentiable_of_mem_maximalAtlas h.1).mdifferentiableAt hx
  have hL : ∀ i, mfderiv 𝓘(𝕜, E) 𝓘(𝕜) (fun y => ψ (φ y) (σ i)) x =
      (coordFunctional ψ (σ i)).comp (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) φ x) := by
    intro i
    have := mfderiv_comp x (coordFunctional ψ (σ i)).hasMFDerivAt.mdifferentiableAt hφ'
    rwa [(coordFunctional ψ (σ i)).hasMFDerivAt.mfderiv] at this
  have hLI := linearIndependent_coordFunctional ψ σ
  unfold HasIndependentDifferentialsAt mderivFun
  simp only [hL]
  rw [Fintype.linearIndependent_iff] at hLI ⊢
  intro g hg j
  refine hLI g ?_ j
  ext w
  obtain ⟨v, hv⟩ := hD w
  have h1 := congrArg (fun L : TangentSpace 𝓘(𝕜, E) x →L[𝕜] 𝕜 => L v) hg
  simp only [sum_apply, smul_apply, zero_apply] at h1 ⊢
  rw [← hv]
  exact h1

/-- A closed submanifold is locally the common zero set of `c` sections of `𝒪_M` with independent
differentials — the adapted coordinates of an adapted chart [BM97, (3.8)(2)]. -/
theorem IsClosedSubmanifold.exists_generators' (hY : IsClosedSubmanifold ψ Y c) {a : M}
    (ha : a ∈ Y) :
    ∃ (U : Opens M) (_ : a ∈ U) (z : Fin c → (structureSheaf 𝕜 E M).presheaf.obj (op U)),
      (∀ x ∈ Y ∩ U, HasIndependentDifferentialsAt E (fun i => extendSection 𝕜 E (z i)) x) ∧
      Y ∩ U = {x ∈ U | ∀ i, extendSection 𝕜 E (z i) x = 0} := by
  obtain ⟨φ, σ, has, h⟩ := hY.exists_adaptedChart a ha
  refine ⟨⟨φ.source, φ.open_source⟩, has, fun i => chartSection E ψ φ h.1 (σ i), ?_, ?_⟩
  · rintro x ⟨-, hx⟩
    have hx' : x ∈ φ.source := hx
    have key := h.hasIndependentDifferentialsAt hx'
    unfold HasIndependentDifferentialsAt mderivFun at key ⊢
    have heq : (fun i =>
          mfderiv 𝓘(𝕜, E) 𝓘(𝕜) (extendSection 𝕜 E (chartSection E ψ φ h.1 (σ i))) x) =
        fun i => mfderiv 𝓘(𝕜, E) 𝓘(𝕜) (fun y => ψ (φ y) (σ i)) x := by
      funext i
      refine Filter.EventuallyEq.mfderiv_eq ?_
      filter_upwards [φ.open_source.mem_nhds hx'] with y hy
      exact extendSection_of_mem 𝕜 E _ hy
    exact heq ▸ key
  · ext x
    constructor
    · rintro ⟨hxY, hxs⟩
      refine ⟨hxs, fun i => ?_⟩
      rw [extendSection_of_mem 𝕜 E _ hxs]
      exact (h.2 x hxs).mp hxY i
    · rintro ⟨hxs, hz⟩
      refine ⟨(h.2 x hxs).mpr fun i => ?_, hxs⟩
      have := hz i
      rwa [extendSection_of_mem 𝕜 E _ hxs] at this

end Manifold
