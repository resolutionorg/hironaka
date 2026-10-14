/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Closed analytic submanifolds: coordinates and the induced manifold structure

For a closed analytic submanifold `Y` of codimension `c` (`IsClosedSubmanifold ψ Y c`, with its
adapted charts `IsAdaptedChart ψ Y φ σ`, on whose source `Y = {z_σ = 0}` for the coordinates
`z = ψ ∘ φ`), this module provides the coordinate bookkeeping and the manifold structure on `Y`.
The adapted charts are the shape in which the chart-extension theorem
(`Hironaka/Manifold/AdaptedChart.lean`) produces charts (`z_i = π_{σ i} ∘ ψ ∘ φ`).

* `IsClosedSubmanifoldOn ψ U Y c`, `Y` a closed submanifold of the open subset `U`, phrased in `M`;
* `HasIndependentDifferentialsAt E z a`: the differentials `d(z_i)(a)` are linearly independent
  (as functionals on the tangent space, through `mderivFun`);
* the induced structure of a manifold on `Y`: the chart `IsAdaptedChart.chartOn` of `Y` induced by
  an adapted chart (the complementary coordinates, `Fin (n - c)` many, through the coordinate
  splitting `embedCompl`, `projCompl`), the charted space `IsClosedSubmanifold.chartedSpace` (a
  chosen adapted chart at each point), the stalk `IsClosedSubmanifold.stalk hY a` of `𝒪_Y`, and
  the specification `IsRestrictStalk` of the restriction of germs `𝒪_{M,a} →+* 𝒪_{Y,a}` (through
  `stalkToGerm`, as germs of functions on `Y`).

The field lives in `Type`, the manifold in `Type u`. The manifold structure on `Y`, the
restriction of germs and the ideal sheaf of `Y` are developed in `Hironaka/Manifold/Submanifold/`.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Coordinates

variable {𝕜 : Type} [RCLike 𝕜] {n c : ℕ}

/-- The coordinates not in the range of `σ`, indexed by `Fin (n - c)`. -/
def complEquiv (σ : Fin c ↪ Fin n) : {j : Fin n // j ∉ Set.range σ} ≃ Fin (n - c) := by
  classical
  refine Fintype.equivFinOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  rw [Fintype.card_congr (Equiv.refl _), Set.card_range_of_injective σ.injective, Fintype.card_fin]

/-- `𝕜^{n-c}` embedded as the coordinate subspace `{y | ∀ i, y (σ i) = 0}`. -/
def embedCompl (σ : Fin c ↪ Fin n) (w : Fin (n - c) → 𝕜) : Fin n → 𝕜 :=
  fun j => if h : j ∈ Set.range σ then 0 else w (complEquiv σ ⟨j, h⟩)

/-- The coordinates outside the range of `σ`. -/
def projCompl (σ : Fin c ↪ Fin n) (y : Fin n → 𝕜) : Fin (n - c) → 𝕜 :=
  fun k => y ((complEquiv σ).symm k).1

/-- The embedded vector vanishes on the range of `σ`. -/
theorem embedCompl_apply_range (σ : Fin c ↪ Fin n) (w : Fin (n - c) → 𝕜) (i : Fin c) :
    embedCompl σ w (σ i) = 0 := by
  simp only [embedCompl, dite_eq_left (Set.mem_range_self i)]

/-- Projecting the embedding of `w` gives back `w`. -/
theorem projCompl_embedCompl (σ : Fin c ↪ Fin n) (w : Fin (n - c) → 𝕜) :
    projCompl σ (embedCompl σ w) = w := by
  funext k
  simp only [projCompl, embedCompl, dite_eq_right ((complEquiv σ).symm k).2]
  change w (complEquiv σ ((complEquiv σ).symm k)) = w k
  rw [Equiv.apply_symm_apply]

/-- Embedding the projection of `y` gives back `y` when `y` vanishes on the range of `σ`. -/
theorem embedCompl_projCompl (σ : Fin c ↪ Fin n) {y : Fin n → 𝕜} (hy : ∀ i, y (σ i) = 0) :
    embedCompl σ (projCompl σ y) = y := by
  funext j
  by_cases h : j ∈ Set.range σ
  · obtain ⟨i, rfl⟩ := h
    simp only [embedCompl, dite_eq_left (Set.mem_range_self i), hy i]
  · simp only [embedCompl, dite_eq_right h, projCompl]
    rw [Equiv.symm_apply_apply]

/-- The embedding `embedCompl σ` is continuous. -/
theorem continuous_embedCompl (σ : Fin c ↪ Fin n) : Continuous (embedCompl (𝕜 := 𝕜) σ) := by
  refine continuous_pi fun j => ?_
  by_cases h : j ∈ Set.range σ
  · simp only [embedCompl, dite_eq_left h]; exact continuous_const
  · simp only [embedCompl, dite_eq_right h]; exact continuous_apply _

/-- The projection `projCompl σ` is continuous. -/
theorem continuous_projCompl (σ : Fin c ↪ Fin n) : Continuous (projCompl (𝕜 := 𝕜) σ) :=
  continuous_pi fun _ => continuous_apply _

end Coordinates

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- `Y` is a closed submanifold of the open subset `U`: `Y ∩ U` is closed in `U` and every point of
`Y ∩ U` lies in the source of an adapted chart whose source is inside `U`. -/
def IsClosedSubmanifoldOn (U Y : Set M) (c : ℕ) : Prop :=
  IsClosed ((Subtype.val : U → M) ⁻¹' Y) ∧
    ∀ a ∈ Y ∩ U, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n),
      a ∈ φ.source ∧ φ.source ⊆ U ∧ IsAdaptedChart ψ Y φ σ

variable (E) in
/-- The manifold derivative of a function `M → 𝕜` at `a`, as a functional on the tangent space (the
codomain `TangentSpace 𝓘(𝕜) (z a)` is `𝕜` by definition; this form makes a family of derivatives
non-dependent). -/
def mderivFun (z : M → 𝕜) (a : M) : TangentSpace 𝓘(𝕜, E) a →L[𝕜] 𝕜 :=
  mfderiv 𝓘(𝕜, E) 𝓘(𝕜) z a

variable (E) in
/-- The differentials of `z_1, …, z_c` at `a` are linearly independent. -/
def HasIndependentDifferentialsAt {c : ℕ} (z : Fin c → M → 𝕜) (a : M) : Prop :=
  LinearIndependent 𝕜 fun i => mderivFun E (z i) a

variable {ψ} {Y : Set M} {φ : OpenPartialHomeomorph M E} {c : ℕ} {σ : Fin c ↪ Fin n}

open Classical in
/-- The inverse of the induced chart (junk value `a` off the target). -/
def IsAdaptedChart.symmAux (h : IsAdaptedChart ψ Y φ σ) {a : M} (ha : a ∈ Y)
    (w : Fin (n - c) → 𝕜) : Y :=
  if hw : ψ.symm (embedCompl σ w) ∈ φ.target then
    ⟨φ.symm (ψ.symm (embedCompl σ w)), (h.2 _ (φ.map_target hw)).mpr fun i => by
      rw [φ.right_inv hw, ψ.apply_symm_apply, embedCompl_apply_range]⟩
  else ⟨a, ha⟩

/-- The inverse of the induced chart on the target. -/
theorem IsAdaptedChart.coe_symmAux (h : IsAdaptedChart ψ Y φ σ) {a : M} (ha : a ∈ Y)
    {w : Fin (n - c) → 𝕜} (hw : ψ.symm (embedCompl σ w) ∈ φ.target) :
    (h.symmAux ha w : M) = φ.symm (ψ.symm (embedCompl σ w)) := by
  simp only [IsAdaptedChart.symmAux, dite_eq_left hw]

/-- The induced chart maps its source into its target. -/
theorem IsAdaptedChart.mem_target_of_mem_source (h : IsAdaptedChart ψ Y φ σ) {x : Y}
    (hx : (x : M) ∈ φ.source) : ψ.symm (embedCompl σ (projCompl σ (ψ (φ x)))) ∈ φ.target := by
  rw [embedCompl_projCompl σ ((h.2 x hx).mp x.2), ψ.symm_apply_apply]
  exact φ.map_source hx

/-- The chart of `Y` induced by an adapted chart: the complementary coordinates. -/
def IsAdaptedChart.chartOn (h : IsAdaptedChart ψ Y φ σ) {a : M} (ha : a ∈ Y) :
    OpenPartialHomeomorph Y (Fin (n - c) → 𝕜) where
  toFun x := projCompl σ (ψ (φ x))
  invFun := h.symmAux ha
  source := {x | (x : M) ∈ φ.source}
  target := {w | ψ.symm (embedCompl σ w) ∈ φ.target}
  map_source' _ hx := h.mem_target_of_mem_source hx
  map_target' w hw := by
    change (h.symmAux ha w : M) ∈ φ.source
    rw [h.coe_symmAux ha hw]
    exact φ.map_target hw
  left_inv' x hx := by
    refine Subtype.ext ?_
    rw [h.coe_symmAux ha (h.mem_target_of_mem_source hx),
      embedCompl_projCompl σ ((h.2 x hx).mp x.2), ψ.symm_apply_apply, φ.left_inv hx]
  right_inv' w hw := by
    rw [h.coe_symmAux ha hw, φ.right_inv hw, ψ.apply_symm_apply, projCompl_embedCompl]
  open_source := φ.open_source.preimage continuous_subtype_val
  open_target := φ.open_target.preimage (ψ.symm.continuous.comp (continuous_embedCompl σ))
  continuousOn_toFun := ((continuous_projCompl σ).comp ψ.continuous).comp_continuousOn
    (φ.continuousOn.comp continuous_subtype_val.continuousOn fun _ hx => hx)
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_induced_rng.mpr ?_
    have h1 : Continuous fun w : {w : Fin (n - c) → 𝕜 | ψ.symm (embedCompl σ w) ∈ φ.target} =>
        φ.symm (ψ.symm (embedCompl σ w)) :=
      φ.continuousOn_symm.comp_continuous
        (ψ.symm.continuous.comp ((continuous_embedCompl σ).comp continuous_subtype_val))
        fun w => w.2
    exact h1.congr fun w => (h.coe_symmAux ha w.2).symm

/-- The induced chart of `Y` is the adapted chart followed by the projection onto the coordinates
outside `σ` (`rfl`). -/
theorem IsAdaptedChart.chartOn_apply (h : IsAdaptedChart ψ Y φ σ) {a : M} (ha : a ∈ Y) (x : Y) :
    h.chartOn ha x = projCompl σ (ψ (φ x)) := rfl

/-- The inverse of the induced chart is `symmAux`, the inverse adapted chart on the coordinate
subspace `{z_σ = 0}`, with the junk value `a` off the target (`rfl`). -/
theorem IsAdaptedChart.chartOn_symm_apply (h : IsAdaptedChart ψ Y φ σ) {a : M} (ha : a ∈ Y)
    (w : Fin (n - c) → 𝕜) : (h.chartOn ha).symm w = h.symmAux ha w := rfl

/-- The source of the induced chart is the trace of the adapted chart's source on `Y` (`rfl`). -/
theorem IsAdaptedChart.chartOn_source (h : IsAdaptedChart ψ Y φ σ) {a : M} (ha : a ∈ Y) :
    (h.chartOn ha).source = {x : Y | (x : M) ∈ φ.source} := rfl

/-- The target of the induced chart is the set of `w ∈ 𝕜^{n-c}` whose embedding into `{z_σ = 0}`
lies in the adapted chart's target (`rfl`). -/
theorem IsAdaptedChart.chartOn_target (h : IsAdaptedChart ψ Y φ σ) {a : M} (ha : a ∈ Y) :
    (h.chartOn ha).target = {w | ψ.symm (embedCompl σ w) ∈ φ.target} := rfl

/-- A chosen adapted chart at each point of a closed submanifold. -/
def IsClosedSubmanifold.adaptedChartAt (hY : IsClosedSubmanifold ψ Y c) (x : Y) :
    OpenPartialHomeomorph M E :=
  (hY.exists_adaptedChart x x.2).choose

/-- The index set of the chosen adapted chart. -/
def IsClosedSubmanifold.adaptedIdx (hY : IsClosedSubmanifold ψ Y c) (x : Y) : Fin c ↪ Fin n :=
  (hY.exists_adaptedChart x x.2).choose_spec.choose

/-- The chosen adapted chart contains its point. -/
theorem IsClosedSubmanifold.mem_source_adaptedChartAt (hY : IsClosedSubmanifold ψ Y c) (x : Y) :
    (x : M) ∈ (hY.adaptedChartAt x).source :=
  (hY.exists_adaptedChart x x.2).choose_spec.choose_spec.1

/-- The chosen chart is adapted. -/
theorem IsClosedSubmanifold.isAdaptedChart_adaptedChartAt (hY : IsClosedSubmanifold ψ Y c) (x : Y) :
    IsAdaptedChart ψ Y (hY.adaptedChartAt x) (hY.adaptedIdx x) :=
  (hY.exists_adaptedChart x x.2).choose_spec.choose_spec.2

/-- The charted space structure of a closed submanifold, modelled on `𝕜^{n-c}`. -/
@[instance_reducible]
def IsClosedSubmanifold.chartedSpace (hY : IsClosedSubmanifold ψ Y c) :
    ChartedSpace (Fin (n - c) → 𝕜) Y where
  atlas := Set.range fun x : Y => (hY.isAdaptedChart_adaptedChartAt x).chartOn x.2
  chartAt x := (hY.isAdaptedChart_adaptedChartAt x).chartOn x.2
  mem_chart_source x := hY.mem_source_adaptedChartAt x
  chart_mem_atlas x := ⟨x, rfl⟩

/-- The stalk of `𝒪_Y` at `a`, for the induced charted structure. -/
abbrev IsClosedSubmanifold.stalk (hY : IsClosedSubmanifold ψ Y c) (a : Y) : Type u :=
  letI := hY.chartedSpace
  (structureSheaf 𝕜 (Fin (n - c) → 𝕜) Y).presheaf.stalk a

example (hY : IsClosedSubmanifold ψ Y c) (a : Y) : CommRing (hY.stalk a) := inferInstance

/-- The specification of **the restriction of germs to `Y`**: a ring homomorphism
`r : 𝒪_{M,a} →+* 𝒪_{Y,a}` is the restriction when it sends the germ of every section `f` of `𝒪_M`
to the germ of `f|_Y` (read as germs of functions on `Y` through `stalkToGerm`). -/
def IsClosedSubmanifold.IsRestrictStalk (hY : IsClosedSubmanifold ψ Y c) (a : Y)
    (r : (structureSheaf 𝕜 E M).presheaf.stalk (a : M) →+* hY.stalk a) : Prop :=
  letI := hY.chartedSpace
  ∀ (U : Opens M) (hU : (a : M) ∈ U) (f : (structureSheaf 𝕜 E M).presheaf.obj (op U)),
    stalkToGerm 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y a
        (r ((structureSheaf 𝕜 E M).presheaf.germ U (a : M) hU f)) =
      ↑(extendBy0 𝓘(𝕜, E) ω M f ∘ (Subtype.val : Y → M))

end Manifold
