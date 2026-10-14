/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Cons
public import Hironaka.Manifold.FiniteSuccession.Restrict.Fields
public import Hironaka.Manifold.FiniteSuccession.Restrict.Nested
public import Hironaka.Manifold.BlowUp.Transform.StrictFlag
public import Hironaka.Manifold.BlowUp.Transform.StrictCharts
import Hironaka.Manifold.BlowUp.Unique
public import Hironaka.Manifold.FiniteSuccession.Restrict.BlowUpChart
import Hironaka.Manifold.FiniteSuccession.Restrict.Transport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Lean.Server.Rpc.Basic
import Std.Time.Format.Modifier
import Mathlib.CategoryTheory.GlueData

/-!
# The strict transform is the blowing-up of the submanifold

Kollár identifies the stage `S_{i+1} := Bl_{Z_i ∩ S_i} S_i` of a restricted blow-up sequence with
the birational transform `(π_i)⁻¹_* S_i ⊂ X_{i+1}`, with a reference to Hartshorne
[Kol07, Definition 30.2]. This module proves the manifold statement: for a blowing-up
`π : M' → M` along `Y ⊆ S`, both closed submanifolds, the strict transform
`S' = closure (π⁻¹(S ∖ Y))` with the restricted blow-down `π|_{S'} : S' → S` is a blowing-up of
the bundled `S` along `Y` in the sense of [BM88, Definition 4.1] (`isBlowUp_restrictMap`), and it
is identified over `S` with the blowing-up `Bl_Y S` (`BlowUpSpace`, `blowUp`) by a diffeomorphism
(`exists_diffeomorph_restrictMap`; unique by `IsBlowUp.exists_unique_diffeomorph`).

The proof is the lift construction of `BlowUp/Unique.lean` with the chart data supplied by the
flag charts: `IsBlowUp` asks for blow-up charts over *every* adapted chart of `Y` in `S`, which
the strict transform does not offer directly, so we first build the two lifts `S' → Bl_Y S` and
`Bl_Y S → S'` over `S`. At a point over the centre both are read in one pair of blow-up charts of
one index over one adapted chart of `Y` in `S`: the induced chart of a flag chart of `M` at the
point (`isAdaptedChart_chartOn_flag`), over which `S'` has the induced charts of the ambient
blow-up charts of index `∉ range τ` (`isBlowUpChart_chartOn_flag`; the charts covering `S_1` in
[Kol07, Theorem 88, proof]) and `Bl_Y S` has charts by definition (`exists_chart`, `cover`). Off
the centre both lifts are the unique preimage. The lifts are analytic (chart formulas over the
centre, local inverses off it — `Fields.lean`'s restriction of the ambient local inverse for the
lift into `S'`), and inverse to each other by the uniqueness of lifts
(`eqOn_of_comp_eq_of_dense`: two continuous lifts agree off the centre by injectivity there and
extend by density, `S' ∖ π⁻¹(Y)` being dense in `S'` by the definition of `S'`). The resulting
diffeomorphism transports `IsBlowUp` from `Bl_Y S` to `S'` (`Transport.lean`).

The hypotheses of one step are packaged in the `Prop`-structure `RestrictBlowUpData`; the two
main statements at the end unpack it. Not in the sources beyond Kollár's remark; the proof is a
chart construction.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

/-! ### Uniqueness of lifts, the general form -/

/-- Two continuous maps over `π₁` into a space where `π₂` is injective off `T` agree on an open set
`N`, provided the points off `T` are dense in the source (the form of `IsBlowUp.eqOn_of_comp_eq`
with the two inputs made explicit). -/
theorem eqOn_of_comp_eq_of_dense {X X' Z : Type*} [TopologicalSpace X] [TopologicalSpace X']
    [T2Space X'] {π₁ : X → Z} {π₂ : X' → Z} {T : Set Z} (hinj : Set.InjOn π₂ (π₂ ⁻¹' Tᶜ))
    (hdense : Dense (π₁ ⁻¹' Tᶜ)) {N : Set X} (hN : IsOpen N) {G G' : X → X'}
    (hG : ContinuousOn G N) (hG' : ContinuousOn G' N) (hπ : ∀ p ∈ N, π₂ (G p) = π₁ p)
    (hπ' : ∀ p ∈ N, π₂ (G' p) = π₁ p) : Set.EqOn G G' N := by
  have hS : Set.EqOn G G' (N ∩ π₁ ⁻¹' Tᶜ) := by
    rintro p ⟨hp, hpT⟩
    have e1 : G p ∈ π₂ ⁻¹' Tᶜ := by
      change π₂ (G p) ∉ T
      rw [hπ p hp]
      exact hpT
    have e2 : G' p ∈ π₂ ⁻¹' Tᶜ := by
      change π₂ (G' p) ∉ T
      rw [hπ' p hp]
      exact hpT
    exact hinj e1 e2 ((hπ p hp).trans (hπ' p hp).symm)
  refine hS.of_subset_closure hG hG' Set.inter_subset_left fun p hp => ?_
  rw [mem_closure_iff]
  intro O hO hpO
  obtain ⟨q, ⟨hqO, hqN⟩, hq⟩ :=
    mem_closure_iff.mp (hdense p) (O ∩ N) (hO.inter hN) ⟨hpO, hp⟩
  exact ⟨q, hqO, hqN, hq⟩

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- The data of one step of a restricted blow-up sequence [Kol07, Definition 30.2]: a blowing-up
`π : M' → M` along a closed submanifold `Y` contained in a closed submanifold `S` (the ambient
manifolds carry all the instances the construction needs). -/
structure RestrictBlowUpData {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {M' : Type u}
    [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
    [SecondCountableTopology M'] (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (π : M' → M) (Y S : Set M) (c s : ℕ) :
    Prop where
  hS : IsClosedSubmanifold ψ S s
  hY : IsClosedSubmanifold ψ Y c
  isBlowUp : IsBlowUp ψ Y c π
  subset : Y ⊆ S

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M] [T2Space M]
  [SecondCountableTopology M] {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M']
  [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M']

namespace RestrictBlowUpData

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {π : M' → M} {Y S : Set M} {c s : ℕ}
  (D : RestrictBlowUpData ψ π Y S c s)

include D in
/-- The strict transform `S'` is a closed submanifold of `M'` of the codimension of `S`. -/
theorem hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s :=
  D.hS.strictTransform D.hY D.isBlowUp D.subset

include D in
/-- `π` carries `S'` into `S`. -/
theorem mapsTo : ∀ x ∈ strictTransformSet π Y S, π x ∈ S :=
  strictTransform_subset_preimage D.isBlowUp.contMDiff.continuous D.hS.isClosed

/-- The centre `Y` is a closed submanifold of the bundled `S` of codimension `c − s`. -/
theorem hY' : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
    (D.hS.preimageVal Y) (c - s) :=
  D.hS.preimage_val_of_subset D.hY D.subset

/-- The restricted blow-down `π|_{S'} : S' → S`. -/
abbrev blowDown : AnalyticMap D.hS'.toAnalyticManifold D.hS.toAnalyticManifold :=
  D.hS'.restrictMap D.hS π D.isBlowUp.contMDiff D.mapsTo

/-- The blowing-up `Bl_Y S` of the bundled `S` along `Y`. -/
abbrev space : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜) :=
  blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) D.hY'

/-- Its blow-down. -/
abbrev proj : AnalyticMap D.space D.hS.toAnalyticManifold :=
  blowUpπ (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) D.hY'

theorem isBlowUp_proj : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
    (D.hS.preimageVal Y) (c - s) D.proj :=
  isBlowUp_blowUpπ _ D.hY'

/-! ### The chart data at a point of the centre -/

section FlagData

variable {a : M} (ha : a ∈ Y)

/-- A flag chart of `Y ⊆ S` at `a ∈ Y`. -/
def flagChart : OpenPartialHomeomorph M E := (exists_adaptedChart_flag D.hY D.hS D.subset ha).choose

/-- Its block embedding for `Y`. -/
def flagEmb : Fin c ↪ Fin n := (exists_adaptedChart_flag D.hY D.hS D.subset ha).choose_spec.choose

/-- The `S`-indices among the centre indices. -/
def flagTau : Fin s ↪ Fin c :=
  (exists_adaptedChart_flag D.hY D.hS D.subset ha).choose_spec.choose_spec.choose

theorem flagChart_spec : a ∈ (D.flagChart ha).source ∧
    IsAdaptedChart ψ Y (D.flagChart ha) (D.flagEmb ha) ∧
    ∀ x ∈ (D.flagChart ha).source,
      x ∈ S ↔ ∀ j, ψ (D.flagChart ha x) (D.flagEmb ha (D.flagTau ha j)) = 0 :=
  (exists_adaptedChart_flag D.hY D.hS D.subset ha).choose_spec.choose_spec.choose_spec

/-- The flag chart is adapted to `S` with the indices `τ.trans σ`. -/
theorem isAdaptedChart_flagChart_S :
    IsAdaptedChart ψ S (D.flagChart ha) ((D.flagTau ha).trans (D.flagEmb ha)) :=
  (D.flagChart_spec ha).2.1.flag (D.flagChart_spec ha).2.2

/-- The induced chart of the flag chart on the bundled `S`. -/
def flagChartS : OpenPartialHomeomorph D.hS.toAnalyticManifold (Fin (n - s) → 𝕜) :=
  D.hS.inducedChart (D.isAdaptedChart_flagChart_S ha) (D.subset ha)

/-- The induced chart is adapted to `Y` inside `S`, with the block `restrictEmb σ τ`. -/
theorem isAdaptedChart_flagChartS :
    IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (D.hS.preimageVal Y)
      (D.flagChartS ha) (restrictEmb (D.flagEmb ha) (D.flagTau ha)) :=
  isAdaptedChart_chartOn_flag D.hS (D.flagChart_spec ha).2.1 (D.flagChart_spec ha).2.2
    (D.subset ha)

theorem mem_flagChartS_source {y : D.hS.toAnalyticManifold}
    (hy : (y : S).1 ∈ (D.flagChart ha).source) : y ∈ (D.flagChartS ha).source :=
  hy

/-- The ambient blow-up chart of an index over the flag chart (the clause `exists_chart` of
`IsBlowUp`). -/
def ambChart (i : Fin c) : OpenPartialHomeomorph M' E :=
  (D.isBlowUp.exists_chart _ _ (D.flagChart_spec ha).2.1 i).choose

theorem ambChart_spec (i : Fin c) :
    IsBlowUpChart ψ π (D.flagChart ha) (D.flagEmb ha) i (D.ambChart ha i) :=
  (D.isBlowUp.exists_chart _ _ (D.flagChart_spec ha).2.1 i).choose_spec

variable {i : Fin c} {Φ : OpenPartialHomeomorph M' E}

/-- An ambient blow-up chart of an index `∉ range τ` over the flag chart is adapted to `S'`. -/
theorem isAdaptedChart_S' (hΦ : IsBlowUpChart ψ π (D.flagChart ha) (D.flagEmb ha) i Φ)
    (hi : i ∉ Set.range (D.flagTau ha)) :
    IsAdaptedChart ψ (strictTransformSet π Y S) Φ ((D.flagTau ha).trans (D.flagEmb ha)) :=
  isAdaptedChart_strictTransform_of_not_mem_range (D.flagChart_spec ha).2.1 hΦ
    (D.flagChart_spec ha).2.2 hi

/-- The induced chart of `S'` from an ambient blow-up chart of an index `∉ range τ`. -/
def chartS' (hΦ : IsBlowUpChart ψ π (D.flagChart ha) (D.flagEmb ha) i Φ)
    (hi : i ∉ Set.range (D.flagTau ha)) {p₀ : M'} (hp₀ : p₀ ∈ strictTransformSet π Y S) :
    OpenPartialHomeomorph D.hS'.toAnalyticManifold (Fin (n - s) → 𝕜) :=
  D.hS'.inducedChart (D.isAdaptedChart_S' ha hΦ hi) hp₀

/-- The induced chart of `S'` is a blow-up chart of the restricted blow-down over the induced
chart of `S`. -/
theorem isBlowUpChart_chartS' (hΦ : IsBlowUpChart ψ π (D.flagChart ha) (D.flagEmb ha) i Φ)
    (hi : i ∉ Set.range (D.flagTau ha)) {p₀ : M'} (hp₀ : p₀ ∈ strictTransformSet π Y S) :
    IsBlowUpChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) D.blowDown (D.flagChartS ha)
      (restrictEmb (D.flagEmb ha) (D.flagTau ha)) (restrictIdx (D.flagTau ha) hi)
      (D.chartS' ha hΦ hi hp₀) :=
  isBlowUpChart_chartOn_flag D.hS D.isBlowUp D.hS' (D.flagChart_spec ha).2.1
    (D.flagChart_spec ha).2.2 (D.subset ha) hΦ hi hp₀

theorem mem_chartS'_source (hΦ : IsBlowUpChart ψ π (D.flagChart ha) (D.flagEmb ha) i Φ)
    (hi : i ∉ Set.range (D.flagTau ha)) {p₀ : M'} (hp₀ : p₀ ∈ strictTransformSet π Y S)
    {p : D.hS'.toAnalyticManifold} (hp : (p : strictTransformSet π Y S).1 ∈ Φ.source) :
    p ∈ (D.chartS' ha hΦ hi hp₀).source :=
  hp

/-- The blow-up chart of `Bl_Y S` of an index over the induced flag chart. -/
def chartB (i'' : Fin (c - s)) : OpenPartialHomeomorph D.space (Fin (n - s) → 𝕜) :=
  (D.isBlowUp_proj.exists_chart _ _ (D.isAdaptedChart_flagChartS ha) i'').choose

theorem isBlowUpChart_chartB (i'' : Fin (c - s)) :
    IsBlowUpChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) D.proj (D.flagChartS ha)
      (restrictEmb (D.flagEmb ha) (D.flagTau ha)) i'' (D.chartB ha i'') :=
  (D.isBlowUp_proj.exists_chart _ _ (D.isAdaptedChart_flagChartS ha) i'').choose_spec

end FlagData

/-! ### The chart pair at a point of `S'` over the centre -/

section Forward

variable (p : D.hS'.toAnalyticManifold) (hp : π (p : strictTransformSet π Y S).1 ∈ Y)

/-- The index of an ambient blow-up chart at `p` over the flag chart at `π p` (the clause `cover`
of `IsBlowUp`). -/
def fIdx : Fin c :=
  (D.isBlowUp.cover _ _ (D.flagChart_spec hp).2.1 _ (D.flagChart_spec hp).1).choose

/-- An ambient blow-up chart at `p`. -/
def fChart : OpenPartialHomeomorph M' E :=
  (D.isBlowUp.cover _ _ (D.flagChart_spec hp).2.1 _ (D.flagChart_spec hp).1).choose_spec.choose

theorem fChart_spec : IsBlowUpChart ψ π (D.flagChart hp) (D.flagEmb hp) (D.fIdx p hp)
    (D.fChart p hp) ∧ (p : strictTransformSet π Y S).1 ∈ (D.fChart p hp).source :=
  (D.isBlowUp.cover _ _ (D.flagChart_spec hp).2.1 _
    (D.flagChart_spec hp).1).choose_spec.choose_spec

/-- Its index is not an `S`-index: `S'` misses those charts. -/
theorem fIdx_notMem : D.fIdx p hp ∉ Set.range (D.flagTau hp) := fun hi =>
  Set.eq_empty_iff_forall_notMem.mp
    (strictTransform_inter_source_of_mem_range (D.flagChart_spec hp).2.1 (D.fChart_spec p hp).1
      (D.flagChart_spec hp).2.2 hi)
    _ ⟨(p : strictTransformSet π Y S).2, (D.fChart_spec p hp).2⟩

/-- The induced blow-up chart of `S'` at `p`. -/
def fChartS' : OpenPartialHomeomorph D.hS'.toAnalyticManifold (Fin (n - s) → 𝕜) :=
  D.chartS' hp (D.fChart_spec p hp).1 (D.fIdx_notMem p hp) (p : strictTransformSet π Y S).2

theorem fChartS'_spec :
    IsBlowUpChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) D.blowDown (D.flagChartS hp)
      (restrictEmb (D.flagEmb hp) (D.flagTau hp)) (restrictIdx (D.flagTau hp) (D.fIdx_notMem p hp))
      (D.fChartS' p hp) ∧ p ∈ (D.fChartS' p hp).source :=
  ⟨D.isBlowUpChart_chartS' hp _ _ _, (D.fChart_spec p hp).2⟩

/-- The blow-up chart of `Bl_Y S` of the same index over the same induced chart. -/
def fChartB : OpenPartialHomeomorph D.space (Fin (n - s) → 𝕜) :=
  D.chartB hp (restrictIdx (D.flagTau hp) (D.fIdx_notMem p hp))

theorem fChartB_spec :
    IsBlowUpChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) D.proj (D.flagChartS hp)
      (restrictEmb (D.flagEmb hp) (D.flagTau hp)) (restrictIdx (D.flagTau hp) (D.fIdx_notMem p hp))
      (D.fChartB p hp) :=
  D.isBlowUpChart_chartB hp _

end Forward

/-! ### The chart pair at a point of `Bl_Y S` over the centre -/

section Reverse

variable (q : D.space) (hq : ((D.proj q : D.hS.toAnalyticManifold) : S).1 ∈ Y)

/-- The index of a blow-up chart of `Bl_Y S` at `q` over the induced flag chart. -/
def rIdx : Fin (c - s) :=
  (D.isBlowUp_proj.cover _ _ (D.isAdaptedChart_flagChartS hq) q
    (D.mem_flagChartS_source hq (D.flagChart_spec hq).1)).choose

/-- A blow-up chart of `Bl_Y S` at `q`. -/
def rChartB : OpenPartialHomeomorph D.space (Fin (n - s) → 𝕜) :=
  (D.isBlowUp_proj.cover _ _ (D.isAdaptedChart_flagChartS hq) q
    (D.mem_flagChartS_source hq (D.flagChart_spec hq).1)).choose_spec.choose

theorem rChartB_spec :
    IsBlowUpChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) D.proj (D.flagChartS hq)
      (restrictEmb (D.flagEmb hq) (D.flagTau hq)) (D.rIdx q hq) (D.rChartB q hq) ∧
      q ∈ (D.rChartB q hq).source :=
  (D.isBlowUp_proj.cover _ _ (D.isAdaptedChart_flagChartS hq) q
    (D.mem_flagChartS_source hq (D.flagChart_spec hq).1)).choose_spec.choose_spec

/-- The ambient index of the chart of `q`. -/
def rIdxAmb : Fin c := ((complEquiv (D.flagTau hq)).symm (D.rIdx q hq)).1

theorem rIdxAmb_notMem : D.rIdxAmb q hq ∉ Set.range (D.flagTau hq) :=
  ((complEquiv (D.flagTau hq)).symm (D.rIdx q hq)).2

theorem restrictIdx_rIdxAmb : restrictIdx (D.flagTau hq) (D.rIdxAmb_notMem q hq) = D.rIdx q hq :=
  (complEquiv (D.flagTau hq)).apply_symm_apply _

/-- The ambient blow-up chart of that index over the flag chart. -/
def rChart : OpenPartialHomeomorph M' E := D.ambChart hq (D.rIdxAmb q hq)

theorem rChart_spec :
    IsBlowUpChart ψ π (D.flagChart hq) (D.flagEmb hq) (D.rIdxAmb q hq) (D.rChart q hq) :=
  D.ambChart_spec hq _

/-- The chart image of `q`, embedded on the coordinate subspace `{u_{σ (τ j)} = 0}`, lies in the
target of the ambient chart. -/
theorem symm_embedCompl_mem_target :
    ψ.symm (embedCompl ((D.flagTau hq).trans (D.flagEmb hq)) (D.rChartB q hq q)) ∈
      (D.rChart q hq).target := by
  apply symm_embedCompl_mem_target_of_mem D.hS (D.flagChart_spec hq).2.1
    (D.flagChart_spec hq).2.2 (D.subset hq) (D.rChart_spec q hq) (D.rIdxAmb_notMem q hq)
  rw [restrictIdx_rIdxAmb]
  have h1 := ((D.rChartB_spec q hq).1.mem_target_iff _).mp
    ((D.rChartB q hq).map_source (D.rChartB_spec q hq).2)
  rw [mem_image_refl_iff] at h1
  exact h1

/-- The point of `S'` corresponding to `q`: the ambient chart's inverse on the coordinate
subspace. -/
def rPoint : D.hS'.toAnalyticManifold :=
  ⟨(D.rChart q hq).symm (ψ.symm (embedCompl ((D.flagTau hq).trans (D.flagEmb hq))
      (D.rChartB q hq q))),
    symm_embedCompl_mem_strictTransform (D.flagChart_spec hq).2.1 (D.flagChart_spec hq).2.2
      (D.rChart_spec q hq) (D.rIdxAmb_notMem q hq) (D.symm_embedCompl_mem_target q hq)⟩

/-- The induced blow-up chart of `S'` of the index of `q`. -/
def rChartS' : OpenPartialHomeomorph D.hS'.toAnalyticManifold (Fin (n - s) → 𝕜) :=
  D.chartS' hq (D.rChart_spec q hq) (D.rIdxAmb_notMem q hq) (D.rPoint q hq).2

theorem rChartS'_spec :
    IsBlowUpChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) D.blowDown (D.flagChartS hq)
      (restrictEmb (D.flagEmb hq) (D.flagTau hq)) (D.rIdx q hq) (D.rChartS' q hq) := by
  have h1 := D.isBlowUpChart_chartS' hq (D.rChart_spec q hq) (D.rIdxAmb_notMem q hq)
    (D.rPoint q hq).2
  rwa [restrictIdx_rIdxAmb] at h1

end Reverse

/-! ### The lift `S' → Bl_Y S` -/

open scoped Classical in
/-- The lift of the restricted blow-down to `Bl_Y S`: over the centre `Φ_B⁻¹ ∘ Φ_{S'}` in the
induced blow-up charts of one index over one induced flag chart, off the centre the unique point of
`Bl_Y S` over `π p`. -/
def liftToBlowUp (p : D.hS'.toAnalyticManifold) : D.space :=
  if hp : π (p : strictTransformSet π Y S).1 ∈ Y then (D.fChartB p hp).symm (D.fChartS' p hp p)
  else (D.isBlowUp_proj.bijOn_compl.surjOn
    (show D.blowDown p ∈ (D.hS.preimageVal Y)ᶜ from hp)).choose

theorem liftToBlowUp_of_mem {p : D.hS'.toAnalyticManifold}
    (hp : π (p : strictTransformSet π Y S).1 ∈ Y) :
    D.liftToBlowUp p = (D.fChartB p hp).symm (D.fChartS' p hp p) := by
  rw [liftToBlowUp, dite_eq_left hp]

theorem liftToBlowUp_of_notMem {p : D.hS'.toAnalyticManifold}
    (hp : π (p : strictTransformSet π Y S).1 ∉ Y) :
    D.liftToBlowUp p = (D.isBlowUp_proj.bijOn_compl.surjOn
      (show D.blowDown p ∈ (D.hS.preimageVal Y)ᶜ from hp)).choose := by
  rw [liftToBlowUp, dite_eq_right hp]

/-- The lift is over `S`. -/
theorem proj_liftToBlowUp (p : D.hS'.toAnalyticManifold) :
    D.proj (D.liftToBlowUp p) = D.blowDown p := by
  by_cases hp : π (p : strictTransformSet π Y S).1 ∈ Y
  · rw [D.liftToBlowUp_of_mem hp]
    exact (D.fChartS'_spec p hp).1.blowDown_symm_apply (D.fChartB_spec p hp)
      (D.fChartS'_spec p hp).2
  · rw [D.liftToBlowUp_of_notMem hp]
    exact (D.isBlowUp_proj.bijOn_compl.surjOn
      (show D.blowDown p ∈ (D.hS.preimageVal Y)ᶜ from hp)).choose_spec.2

/-- Off the centre, the lift is the unique point off the divisor over `π p`. -/
theorem liftToBlowUp_eq_of_notMem {p : D.hS'.toAnalyticManifold}
    (hp : π (p : strictTransformSet π Y S).1 ∉ Y) {q : D.space} (hq : D.proj q = D.blowDown p) :
    D.liftToBlowUp p = q := by
  have hmem : D.liftToBlowUp p ∈ D.proj ⁻¹' (D.hS.preimageVal Y)ᶜ := by
    rw [D.liftToBlowUp_of_notMem hp]
    exact (D.isBlowUp_proj.bijOn_compl.surjOn
      (show D.blowDown p ∈ (D.hS.preimageVal Y)ᶜ from hp)).choose_spec.1
  have hq' : q ∈ D.proj ⁻¹' (D.hS.preimageVal Y)ᶜ := by
    change D.proj q ∉ D.hS.preimageVal Y
    rw [hq]
    exact hp
  exact D.isBlowUp_proj.bijOn_compl.injOn hmem hq' ((D.proj_liftToBlowUp p).trans hq.symm)

/-- Near a point over the centre, the lift is the chart formula `Φ_B⁻¹ ∘ Φ_{S'}`. -/
theorem liftToBlowUp_eqOn_of_mem {p : D.hS'.toAnalyticManifold}
    (hp : π (p : strictTransformSet π Y S).1 ∈ Y) :
    Set.EqOn D.liftToBlowUp ((D.fChartB p hp).symm ∘ D.fChartS' p hp) (D.fChartS' p hp).source := by
  intro q hq
  have hΦ₁ := (D.fChartS'_spec p hp).1
  have hΦ₂ := D.fChartB_spec p hp
  by_cases hqY : π (q : strictTransformSet π Y S).1 ∈ Y
  · have hΦ₁' := (D.fChartS'_spec q hqY).1
    have hΦ₂' := D.fChartB_spec q hqY
    have hN : IsOpen ((D.fChartS' p hp).source ∩ (D.fChartS' q hqY).source) :=
      (D.fChartS' p hp).open_source.inter (D.fChartS' q hqY).open_source
    have heq := eqOn_of_comp_eq_of_dense D.isBlowUp_proj.bijOn_compl.injOn
      (dense_preimage_compl_restrictMap D.hS D.isBlowUp D.hS') hN
      ((hΦ₁'.contMDiffOn_symm_comp hΦ₂').continuousOn.mono Set.inter_subset_right)
      ((hΦ₁.contMDiffOn_symm_comp hΦ₂).continuousOn.mono Set.inter_subset_left)
      (fun r hr => hΦ₁'.blowDown_symm_apply hΦ₂' hr.2)
      (fun r hr => hΦ₁.blowDown_symm_apply hΦ₂ hr.1) ⟨hq, (D.fChartS'_spec q hqY).2⟩
    rw [D.liftToBlowUp_of_mem hqY]
    exact heq
  · exact D.liftToBlowUp_eq_of_notMem hqY (hΦ₁.blowDown_symm_apply hΦ₂ hq)

/-- Near a point off the centre, the lift is `Ψ⁻¹ ∘ π|_{S'}` for a local inverse `Ψ` of the
blow-down of `Bl_Y S`. -/
theorem exists_eqOn_liftToBlowUp_of_notMem {p : D.hS'.toAnalyticManifold}
    (hp : π (p : strictTransformSet π Y S).1 ∉ Y) :
    ∃ N : Set D.hS'.toAnalyticManifold, IsOpen N ∧ p ∈ N ∧
      ∃ Ψ : PartialDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) D.space
        D.hS.toAnalyticManifold ω, N ⊆ D.blowDown ⁻¹' Ψ.target ∧
        Set.EqOn D.liftToBlowUp (Ψ.invFun ∘ D.blowDown) N := by
  have hmem : D.liftToBlowUp p ∈ D.proj ⁻¹' (D.hS.preimageVal Y)ᶜ := by
    change D.proj (D.liftToBlowUp p) ∉ D.hS.preimageVal Y
    rw [D.proj_liftToBlowUp p]
    exact hp
  obtain ⟨Ψ, hqΨ, hΨ⟩ :=
    (D.isBlowUp_proj.isLocalDiffeomorphOn_compl ⟨_, hmem⟩).exists_partialDiffeomorph
  have hqΨ' : D.liftToBlowUp p ∈ Ψ.source := hqΨ
  refine ⟨D.blowDown ⁻¹' (Ψ.target ∩ (D.hS.preimageVal Y)ᶜ),
    (Ψ.open_target.inter D.hY'.isClosed.isOpen_compl).preimage D.blowDown.contMDiff.continuous,
    ⟨?_, hp⟩, Ψ, fun _ hr => hr.1, fun r hr => ?_⟩
  · rw [← D.proj_liftToBlowUp p, hΨ hqΨ']
    exact Ψ.map_source hqΨ'
  · have hr1 : D.blowDown r ∈ Ψ.target := hr.1
    have hr2 : π (r : strictTransformSet π Y S).1 ∉ Y := hr.2
    have hmem' : Ψ.invFun (D.blowDown r) ∈ Ψ.source := Ψ.map_target hr1
    refine D.liftToBlowUp_eq_of_notMem hr2 ?_
    change D.proj (Ψ.invFun (D.blowDown r)) = D.blowDown r
    rw [hΨ hmem']
    exact Ψ.right_inv hr1

/-- The lift `S' → Bl_Y S` is analytic. -/
theorem contMDiff_liftToBlowUp :
    ContMDiff 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω D.liftToBlowUp := by
  intro p
  by_cases hp : π (p : strictTransformSet π Y S).1 ∈ Y
  · have hΦ₁ := (D.fChartS'_spec p hp).1
    have hΦ₂ := D.fChartB_spec p hp
    exact ((hΦ₁.contMDiffOn_symm_comp hΦ₂).congr (D.liftToBlowUp_eqOn_of_mem hp)).contMDiffAt
      ((D.fChartS' p hp).open_source.mem_nhds (D.fChartS'_spec p hp).2)
  · obtain ⟨N, hN, hpN, Ψ, hNΨ, heq⟩ := D.exists_eqOn_liftToBlowUp_of_notMem hp
    have hsm : ContMDiffOn 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω
        (Ψ.invFun ∘ D.blowDown) N :=
      Ψ.contMDiffOn_invFun.comp D.blowDown.contMDiff.contMDiffOn hNΨ
    exact (hsm.congr heq).contMDiffAt (hN.mem_nhds hpN)

/-! ### The lift `Bl_Y S → S'` -/

open scoped Classical in
/-- The lift of the blow-down of `Bl_Y S` to `S'`: over the centre `Φ_{S'}⁻¹ ∘ Φ_B` in the induced
blow-up charts of one index over one induced flag chart, off the centre the unique point of `S'`
over the image. -/
def liftFromBlowUp (q : D.space) : D.hS'.toAnalyticManifold :=
  if hq : ((D.proj q : D.hS.toAnalyticManifold) : S).1 ∈ Y then
    (D.rChartS' q hq).symm (D.rChartB q hq q)
  else ((bijOn_restrictMap_compl D.hS D.isBlowUp D.hS').surjOn
    (show D.proj q ∈ (D.hS.preimageVal Y)ᶜ from hq)).choose

theorem liftFromBlowUp_of_mem {q : D.space}
    (hq : ((D.proj q : D.hS.toAnalyticManifold) : S).1 ∈ Y) :
    D.liftFromBlowUp q = (D.rChartS' q hq).symm (D.rChartB q hq q) := by
  rw [liftFromBlowUp, dite_eq_left hq]

theorem liftFromBlowUp_of_notMem {q : D.space}
    (hq : ((D.proj q : D.hS.toAnalyticManifold) : S).1 ∉ Y) :
    D.liftFromBlowUp q = ((bijOn_restrictMap_compl D.hS D.isBlowUp D.hS').surjOn
      (show D.proj q ∈ (D.hS.preimageVal Y)ᶜ from hq)).choose := by
  rw [liftFromBlowUp, dite_eq_right hq]

/-- The lift is over `S`. -/
theorem blowDown_liftFromBlowUp (q : D.space) : D.blowDown (D.liftFromBlowUp q) = D.proj q := by
  by_cases hq : ((D.proj q : D.hS.toAnalyticManifold) : S).1 ∈ Y
  · rw [D.liftFromBlowUp_of_mem hq]
    exact (D.rChartB_spec q hq).1.blowDown_symm_apply (D.rChartS'_spec q hq)
      (D.rChartB_spec q hq).2
  · rw [D.liftFromBlowUp_of_notMem hq]
    exact ((bijOn_restrictMap_compl D.hS D.isBlowUp D.hS').surjOn
      (show D.proj q ∈ (D.hS.preimageVal Y)ᶜ from hq)).choose_spec.2

/-- Off the centre, the lift is the unique point of `S'` off the divisor over the image. -/
theorem liftFromBlowUp_eq_of_notMem {q : D.space}
    (hq : ((D.proj q : D.hS.toAnalyticManifold) : S).1 ∉ Y) {p : D.hS'.toAnalyticManifold}
    (hp : D.blowDown p = D.proj q) : D.liftFromBlowUp q = p := by
  have hmem : D.liftFromBlowUp q ∈ D.blowDown ⁻¹' (D.hS.preimageVal Y)ᶜ := by
    rw [D.liftFromBlowUp_of_notMem hq]
    exact ((bijOn_restrictMap_compl D.hS D.isBlowUp D.hS').surjOn
      (show D.proj q ∈ (D.hS.preimageVal Y)ᶜ from hq)).choose_spec.1
  have hp' : p ∈ D.blowDown ⁻¹' (D.hS.preimageVal Y)ᶜ := by
    change D.blowDown p ∉ D.hS.preimageVal Y
    rw [hp]
    exact hq
  exact (bijOn_restrictMap_compl D.hS D.isBlowUp D.hS').injOn hmem hp'
    ((D.blowDown_liftFromBlowUp q).trans hp.symm)

/-- Near a point over the centre, the lift is the chart formula `Φ_{S'}⁻¹ ∘ Φ_B`. -/
theorem liftFromBlowUp_eqOn_of_mem {q : D.space}
    (hq : ((D.proj q : D.hS.toAnalyticManifold) : S).1 ∈ Y) :
    Set.EqOn D.liftFromBlowUp ((D.rChartS' q hq).symm ∘ D.rChartB q hq)
      (D.rChartB q hq).source := by
  intro r hr
  have hΦ₁ := (D.rChartB_spec q hq).1
  have hΦ₂ := D.rChartS'_spec q hq
  by_cases hrY : ((D.proj r : D.hS.toAnalyticManifold) : S).1 ∈ Y
  · have hΦ₁' := (D.rChartB_spec r hrY).1
    have hΦ₂' := D.rChartS'_spec r hrY
    have hN : IsOpen ((D.rChartB q hq).source ∩ (D.rChartB r hrY).source) :=
      (D.rChartB q hq).open_source.inter (D.rChartB r hrY).open_source
    have heq := eqOn_of_comp_eq_of_dense
      (bijOn_restrictMap_compl D.hS D.isBlowUp D.hS').injOn
      (D.isBlowUp_proj.dense_preimage_compl D.hY') hN
      ((hΦ₁'.contMDiffOn_symm_comp hΦ₂').continuousOn.mono Set.inter_subset_right)
      ((hΦ₁.contMDiffOn_symm_comp hΦ₂).continuousOn.mono Set.inter_subset_left)
      (fun t ht => hΦ₁'.blowDown_symm_apply hΦ₂' ht.2)
      (fun t ht => hΦ₁.blowDown_symm_apply hΦ₂ ht.1) ⟨hr, (D.rChartB_spec r hrY).2⟩
    rw [D.liftFromBlowUp_of_mem hrY]
    exact heq
  · exact D.liftFromBlowUp_eq_of_notMem hrY (hΦ₁.blowDown_symm_apply hΦ₂ hr)

/-- Near a point off the centre, the lift is `Ψ⁻¹ ∘ π_B` for a local inverse `Ψ` of the restricted
blow-down (`Fields.lean`). -/
theorem exists_eqOn_liftFromBlowUp_of_notMem {q : D.space}
    (hq : ((D.proj q : D.hS.toAnalyticManifold) : S).1 ∉ Y) :
    ∃ N : Set D.space, IsOpen N ∧ q ∈ N ∧
      ∃ Ψ : PartialDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜)
        D.hS'.toAnalyticManifold D.hS.toAnalyticManifold ω, N ⊆ D.proj ⁻¹' Ψ.target ∧
        Set.EqOn D.liftFromBlowUp (Ψ.invFun ∘ D.proj) N := by
  have hmem : D.liftFromBlowUp q ∈ D.blowDown ⁻¹' (D.hS.preimageVal Y)ᶜ := by
    change D.blowDown (D.liftFromBlowUp q) ∉ D.hS.preimageVal Y
    rw [D.blowDown_liftFromBlowUp q]
    exact hq
  obtain ⟨Ψ, hpΨ, hΨ⟩ :=
    (isLocalDiffeomorphOn_restrictMap_compl D.hS D.hY D.isBlowUp D.hS'
      ⟨_, hmem⟩).exists_partialDiffeomorph
  have hpΨ' : D.liftFromBlowUp q ∈ Ψ.source := hpΨ
  refine ⟨D.proj ⁻¹' (Ψ.target ∩ (D.hS.preimageVal Y)ᶜ),
    (Ψ.open_target.inter D.hY'.isClosed.isOpen_compl).preimage D.proj.contMDiff.continuous,
    ⟨?_, hq⟩, Ψ, fun _ hr => hr.1, fun r hr => ?_⟩
  · rw [← D.blowDown_liftFromBlowUp q, hΨ hpΨ']
    exact Ψ.map_source hpΨ'
  · have hr1 : D.proj r ∈ Ψ.target := hr.1
    have hr2 : ((D.proj r : D.hS.toAnalyticManifold) : S).1 ∉ Y := hr.2
    have hmem' : Ψ.invFun (D.proj r) ∈ Ψ.source := Ψ.map_target hr1
    refine D.liftFromBlowUp_eq_of_notMem hr2 ?_
    change D.blowDown (Ψ.invFun (D.proj r)) = D.proj r
    rw [hΨ hmem']
    exact Ψ.right_inv hr1

/-- The lift `Bl_Y S → S'` is analytic. -/
theorem contMDiff_liftFromBlowUp :
    ContMDiff 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω D.liftFromBlowUp := by
  intro q
  by_cases hq : ((D.proj q : D.hS.toAnalyticManifold) : S).1 ∈ Y
  · have hΦ₁ := (D.rChartB_spec q hq).1
    have hΦ₂ := D.rChartS'_spec q hq
    exact ((hΦ₁.contMDiffOn_symm_comp hΦ₂).congr (D.liftFromBlowUp_eqOn_of_mem hq)).contMDiffAt
      ((D.rChartB q hq).open_source.mem_nhds (D.rChartB_spec q hq).2)
  · obtain ⟨N, hN, hqN, Ψ, hNΨ, heq⟩ := D.exists_eqOn_liftFromBlowUp_of_notMem hq
    have hsm : ContMDiffOn 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω
        (Ψ.invFun ∘ D.proj) N :=
      Ψ.contMDiffOn_invFun.comp D.proj.contMDiff.contMDiffOn hNΨ
    exact (hsm.congr heq).contMDiffAt (hN.mem_nhds hqN)

/-! ### The identification -/

/-- The two lifts are inverse: `S' → Bl_Y S → S'`. -/
theorem liftFromBlowUp_liftToBlowUp (p : D.hS'.toAnalyticManifold) :
    D.liftFromBlowUp (D.liftToBlowUp p) = p := by
  have h := eqOn_of_comp_eq_of_dense
    (bijOn_restrictMap_compl D.hS D.isBlowUp D.hS').injOn
    (dense_preimage_compl_restrictMap D.hS D.isBlowUp D.hS') isOpen_univ
    (D.contMDiff_liftFromBlowUp.continuous.comp D.contMDiff_liftToBlowUp.continuous).continuousOn
    continuous_id.continuousOn
    (fun q _ => by
      change D.blowDown (D.liftFromBlowUp (D.liftToBlowUp q)) = D.blowDown q
      rw [D.blowDown_liftFromBlowUp, D.proj_liftToBlowUp])
    (fun _ _ => rfl)
  exact h (Set.mem_univ p)

/-- The two lifts are inverse: `Bl_Y S → S' → Bl_Y S`. -/
theorem liftToBlowUp_liftFromBlowUp (q : D.space) :
    D.liftToBlowUp (D.liftFromBlowUp q) = q := by
  have h := eqOn_of_comp_eq_of_dense D.isBlowUp_proj.bijOn_compl.injOn
    (D.isBlowUp_proj.dense_preimage_compl D.hY') isOpen_univ
    (D.contMDiff_liftToBlowUp.continuous.comp D.contMDiff_liftFromBlowUp.continuous).continuousOn
    continuous_id.continuousOn
    (fun r _ => by
      change D.proj (D.liftToBlowUp (D.liftFromBlowUp r)) = D.proj r
      rw [D.proj_liftToBlowUp, D.blowDown_liftFromBlowUp])
    (fun _ _ => rfl)
  exact h (Set.mem_univ q)

/-- The diffeomorphism `Bl_Y S ≅ S'` over `S`: Kollár's identification of `Bl_{Z_i ∩ S_i} S_i`
with the birational transform of `S_i` [Kol07, Definition 30.2]. -/
def diffeomorph : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) D.space
    D.hS'.toAnalyticManifold ω where
  toFun := D.liftFromBlowUp
  invFun := D.liftToBlowUp
  left_inv := D.liftToBlowUp_liftFromBlowUp
  right_inv := D.liftFromBlowUp_liftToBlowUp
  contMDiff_toFun := D.contMDiff_liftFromBlowUp
  contMDiff_invFun := D.contMDiff_liftToBlowUp

/-- The restricted blow-down is a blowing-up of the bundled `S` along `Y`. -/
theorem isBlowUp_blowDown : IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
    (D.hS.preimageVal Y) (c - s) D.blowDown := by
  have e : (D.blowDown : D.hS'.toAnalyticManifold → D.hS.toAnalyticManifold) =
      D.proj ∘ D.diffeomorph.symm :=
    funext fun p => (D.proj_liftToBlowUp p).symm
  rw [e]
  exact D.isBlowUp_proj.comp_diffeomorph D.diffeomorph.symm

end RestrictBlowUpData

/-! ### The two main statements -/

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {π : M' → M} {Y S : Set M} {c s : ℕ}

/-- The restricted blow-down `π|_{S'} : S' → S` is a blowing-up in the sense of
[BM88, Definition 4.1] (`IsBlowUp`) of the bundled `S` along `Y`, of codimension `c − s`, in the
induced charts: Kollár's `S_{i+1} := Bl_{Z_i ∩ S_i} S_i`, naturally identified with the birational
transform of `S_i` [Kol07, Definition 30.2]. -/
theorem isBlowUp_restrictMap (hS : IsClosedSubmanifold ψ S s) (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hYS : Y ⊆ S) :
    IsBlowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (hS.preimageVal Y) (c - s)
      ((hS.strictTransform hY h hYS).restrictMap hS π h.contMDiff
        (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed)) :=
  (RestrictBlowUpData.mk hS hY h hYS).isBlowUp_blowDown

/-- The strict transform `S'` is identified over `S` with the blowing-up `Bl_Y S`
[Kol07, Definition 30.2] (the identification is unique by `IsBlowUp.exists_unique_diffeomorph`). -/
theorem exists_diffeomorph_restrictMap (hS : IsClosedSubmanifold ψ S s)
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (hYS : Y ⊆ S) :
    ∃ g : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜)
        (blowUp (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
          (hS.preimage_val_of_subset hY hYS))
        (hS.strictTransform hY h hYS).toAnalyticManifold ω,
      ∀ p, (hS.strictTransform hY h hYS).restrictMap hS π h.contMDiff
          (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed) (g p) =
        blowUpπ (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
          (hS.preimage_val_of_subset hY hYS) p :=
  ⟨(RestrictBlowUpData.mk hS hY h hYS).diffeomorph,
    fun p => (RestrictBlowUpData.mk hS hY h hYS).blowDown_liftFromBlowUp p⟩

end Manifold

end
