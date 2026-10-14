/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A closed submanifold is a manifold

With the charts induced by the adapted charts — the complementary coordinates,
`IsAdaptedChart.chartOn` — a closed submanifold `Y` of codimension `c` is an analytic manifold
modelled on `𝕜^{n-c}` (Bierstone–Milman: a smooth subspace of a manifold "is a manifold and is
locally a coordinate subspace of a coordinate chart" [BM97, (3.8)(2)]). The chart change between
two induced charts is the chart change `φ₂ ∘ φ₁⁻¹` of `M` (analytic, both charts being in the
maximal atlas) conjugated by the linear maps `ψ⁻¹ ∘ embedCompl` and `projCompl ∘ ψ`
(`chartChange_contDiffOn`), so it lies in the analytic groupoid (`chartChange_mem`); hence the
induced charted space is a manifold (`isManifold'`) and every chart induced by an adapted chart is
in its maximal atlas (`chartOn_mem_maximalAtlas'`). Also here: `mem_contDiffGroupoid_self`, the
criterion for an open partial homeomorphism of a normed space to lie in the analytic groupoid. The
manifold structure on `Y` is what makes a centre, a hypersurface of maximal contact or a stratum of
the boundary an analytic manifold in its own right.
-/

public noncomputable section

open TopologicalSpace Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Coordinates

variable {𝕜 : Type} [RCLike 𝕜] {n c : ℕ}

/-- The inclusion `𝕜^{n-c} → 𝕜^n` along the coordinates outside `σ` is analytic (it is linear). -/
theorem contDiff_embedCompl (σ : Fin c ↪ Fin n) : ContDiff 𝕜 ω (embedCompl (𝕜 := 𝕜) σ) := by
  refine (contDiff_pi (𝕜 := 𝕜)).mpr fun j => ?_
  by_cases h : j ∈ Set.range σ
  · simp only [embedCompl, dite_eq_left h]
    exact contDiff_const
  · simp only [embedCompl, dite_eq_right h]
    exact contDiff_apply 𝕜 𝕜 _

/-- The projection `𝕜^n → 𝕜^{n-c}` onto the coordinates outside `σ` is analytic (it is linear). -/
theorem contDiff_projCompl (σ : Fin c ↪ Fin n) : ContDiff 𝕜 ω (projCompl (𝕜 := 𝕜) σ) :=
  (contDiff_pi (𝕜 := 𝕜)).mpr fun _ => contDiff_apply 𝕜 𝕜 _

/-- An open partial homeomorphism of a normed space that is analytic with analytic inverse lies in
the analytic groupoid of the model space. -/
theorem mem_contDiffGroupoid_self {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : OpenPartialHomeomorph F F) (h : ContDiffOn 𝕜 ω e e.source)
    (h' : ContDiffOn 𝕜 ω e.symm e.target) : e ∈ contDiffGroupoid ω 𝓘(𝕜, F) := by
  refine mem_groupoid_of_pregroupoid.mpr ⟨?_, ?_⟩
  · simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
    exact h
  · simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
    exact h'

end Coordinates

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Y : Set M} {c : ℕ}

/-- The chart change of two charts of the maximal atlas is analytic. -/
theorem contDiffOn_chartChange {φ₁ φ₂ : OpenPartialHomeomorph M E}
    (h₁ : φ₁ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (h₂ : φ₂ ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    ContDiffOn 𝕜 ω (φ₂ ∘ φ₁.symm) (φ₁.target ∩ φ₁.symm ⁻¹' φ₂.source) :=
  contMDiffOn_iff_contDiffOn.mp
    ((contMDiffOn_of_mem_maximalAtlas (n := ω) h₂).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas (n := ω) h₁).mono inter_subset_left) fun _ hy => hy.2)

/-- The chart change between two induced charts of `Y` is analytic on its domain. -/
theorem IsAdaptedChart.chartChange_contDiffOn {φ₁ φ₂ : OpenPartialHomeomorph M E}
    {σ₁ σ₂ : Fin c ↪ Fin n} (h₁ : IsAdaptedChart ψ Y φ₁ σ₁) {a₁ : M} (ha₁ : a₁ ∈ Y)
    (h₂ : IsAdaptedChart ψ Y φ₂ σ₂) {a₂ : M} (ha₂ : a₂ ∈ Y) :
    ContDiffOn 𝕜 ω ((h₁.chartOn ha₁).symm ≫ₕ h₂.chartOn ha₂)
      ((h₁.chartOn ha₁).symm ≫ₕ h₂.chartOn ha₂).source := by
  have hcomp : ContDiffOn 𝕜 ω
      ((projCompl σ₂ ∘ ψ) ∘ (φ₂ ∘ φ₁.symm) ∘ (ψ.symm ∘ embedCompl σ₁))
      ((h₁.chartOn ha₁).symm ≫ₕ h₂.chartOn ha₂).source := by
    refine ((contDiff_projCompl σ₂).comp ψ.contDiff).comp_contDiffOn ?_
    refine (contDiffOn_chartChange h₁.1 h₂.1).comp
      ((ψ.symm.contDiff.comp (contDiff_embedCompl σ₁)).contDiffOn) ?_
    rintro w ⟨hw₁, hw₂⟩
    have hw₁' : ψ.symm (embedCompl σ₁ w) ∈ φ₁.target := hw₁
    refine ⟨hw₁', ?_⟩
    have : ((h₁.chartOn ha₁).symm w : M) ∈ φ₂.source := hw₂
    rwa [h₁.chartOn_symm_apply, h₁.coe_symmAux ha₁ hw₁'] at this
  refine hcomp.congr fun w hw => ?_
  obtain ⟨hw₁, -⟩ := hw
  have hw₁' : ψ.symm (embedCompl σ₁ w) ∈ φ₁.target := hw₁
  change projCompl σ₂ (ψ (φ₂ ((h₁.chartOn ha₁).symm w : M))) = _
  rw [h₁.chartOn_symm_apply, h₁.coe_symmAux ha₁ hw₁']
  rfl

/-- The chart change between two induced charts lies in the analytic groupoid. -/
theorem IsAdaptedChart.chartChange_mem {φ₁ φ₂ : OpenPartialHomeomorph M E}
    {σ₁ σ₂ : Fin c ↪ Fin n} (h₁ : IsAdaptedChart ψ Y φ₁ σ₁) {a₁ : M} (ha₁ : a₁ ∈ Y)
    (h₂ : IsAdaptedChart ψ Y φ₂ σ₂) {a₂ : M} (ha₂ : a₂ ∈ Y) :
    (h₁.chartOn ha₁).symm ≫ₕ h₂.chartOn ha₂ ∈ contDiffGroupoid ω 𝓘(𝕜, Fin (n - c) → 𝕜) := by
  refine mem_contDiffGroupoid_self _ (h₁.chartChange_contDiffOn ha₁ h₂ ha₂) ?_
  have hset : ((h₁.chartOn ha₁).symm ≫ₕ h₂.chartOn ha₂).target =
      ((h₂.chartOn ha₂).symm ≫ₕ h₁.chartOn ha₁).source := by
    rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source]
    rfl
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm, hset]
  exact h₂.chartChange_contDiffOn ha₂ h₁ ha₁

/-- With the induced charts, a closed submanifold is an analytic manifold modelled on `𝕜^{n-c}`
[BM97, (3.8)(2)]. -/
theorem IsClosedSubmanifold.isManifold' (hY : IsClosedSubmanifold ψ Y c) :
    letI := hY.chartedSpace
    IsManifold 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y := by
  let _i := hY.chartedSpace
  have : HasGroupoid Y (contDiffGroupoid ω 𝓘(𝕜, Fin (n - c) → 𝕜)) := by
    refine hasGroupoid_of_pregroupoid _ fun {e e'} he he' => ?_
    obtain ⟨x, rfl⟩ := he
    obtain ⟨x', rfl⟩ := he'
    have hmem := (hY.isAdaptedChart_adaptedChartAt x).chartChange_mem x.2
      (hY.isAdaptedChart_adaptedChartAt x') x'.2
    exact (mem_groupoid_of_pregroupoid.mp hmem).1
  exact ⟨⟩

/-- Every chart of `Y` induced by an adapted chart is a chart of the maximal atlas of `Y`. -/
theorem IsAdaptedChart.chartOn_mem_maximalAtlas' (hY : IsClosedSubmanifold ψ Y c)
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} (h : IsAdaptedChart ψ Y φ σ) {a : M}
    (ha : a ∈ Y) :
    letI := hY.chartedSpace
    h.chartOn ha ∈ maximalAtlas 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y := by
  let _i := hY.chartedSpace
  intro e' he'
  obtain ⟨x, rfl⟩ := he'
  exact ⟨h.chartChange_mem ha (hY.isAdaptedChart_adaptedChartAt x) x.2,
    (hY.isAdaptedChart_adaptedChartAt x).chartChange_mem x.2 h ha⟩

end Manifold
