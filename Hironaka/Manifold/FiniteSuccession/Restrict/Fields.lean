/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Bundle
public import Hironaka.Manifold.BlowUp.Transform.Basic
public import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.LocalDiffeomorph
import Hironaka.Manifold.Submanifold.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The restricted blow-down off the centre

For a blowing-up `π : M' → M` along a closed submanifold `Y ⊆ S` of a closed submanifold `S`, and
the strict transform `S' = closure (π⁻¹(S ∖ Y))`, the restricted blow-down `π|_{S'} : S' → S`
(`IsClosedSubmanifold.restrictMap`, between the bundled submanifolds) has the properties of a
blowing-up of `S` along `Y` in the sense of [BM88, Definition 4.1] away from the exceptional
divisor, read off the ambient `IsBlowUp`. This is the manifold form of Kollár's identification of
the stage `S_{i+1} := Bl_{Z_i ∩ S_i} S_i` of a restricted blow-up sequence with the birational
transform of `S_i` [Kol07, Definition 30.2]:

* it is proper (`S'` is closed in `M'`; `isProperMap_restrictMap`);
* it is a bijection `S' ∖ π⁻¹(Y) → S ∖ Y` (`bijOn_restrictMap_compl`: the ambient bijection, and
  `π⁻¹(S ∖ Y) ⊆ S'`);
* `S' ∖ π⁻¹(Y)` is dense in `S'` — by the definition of `S'` as a closure
  (`dense_preimage_compl_restrictMap`);
* it is a local analytic isomorphism there (`isLocalDiffeomorphOn_restrictMap_compl`): the local
  inverse `Ψ` of `π` at a point of `S'` off `Y` restricts to the submanifolds, `Ψ⁻¹` carrying
  `S ∩ Ψ.target ∖ Y` into `π⁻¹(S ∖ Y) ⊆ S'` (`restrictPartialDiffeomorph`), analytic for the induced
  charts because a map into a closed submanifold is analytic as soon as its composite with the
  inclusion is (`IsClosedSubmanifold.contMDiffAt_of_val`, the local form of
  `IsClosedSubmanifold.contMDiff_codRestrict`).

The chart clauses of `IsBlowUp` over the centre are proved in `Lift.lean`. Not in the sources; the
arguments are routine.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {S : Set M} {s : ℕ}

/-! ### Analyticity into a closed submanifold, locally -/

section Local

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {N : Type u} [TopologicalSpace N]
  [ChartedSpace F N]

omit [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] in
/-- A map into a closed submanifold is analytic at a point for the induced charts as soon as its
composite with the inclusion is: in the induced chart at the image point it reads
`projCompl σ ∘ ψ ∘ φ ∘ (val ∘ g)` (the local form of
`IsClosedSubmanifold.contMDiff_codRestrict`). -/
theorem IsClosedSubmanifold.contMDiffAt_of_val (hS : IsClosedSubmanifold ψ S s) {g : N → S} {x : N}
    (hg : ContMDiffAt 𝓘(𝕜, F) 𝓘(𝕜, E) ω (Subtype.val ∘ g) x) :
    letI := hS.chartedSpace
    ContMDiffAt 𝓘(𝕜, F) 𝓘(𝕜, Fin (n - s) → 𝕜) ω g x := by
  let _i := hS.chartedSpace
  rw [contMDiffAt_iff_target]
  refine ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hg.continuousAt, ?_⟩
  set φ := hS.adaptedChartAt (g x) with hφdef
  set σ := hS.adaptedIdx (g x) with hσdef
  have hφ : IsAdaptedChart ψ S φ σ := hS.isAdaptedChart_adaptedChartAt (g x)
  have hyφ : (g x).1 ∈ φ.source := hS.mem_source_adaptedChartAt (g x)
  have heq : (extChartAt 𝓘(𝕜, Fin (n - s) → 𝕜) (g x) ∘ g) =
      fun z => projCompl σ (ψ (φ (g z).1)) := by
    funext z
    rfl
  rw [heq]
  have h1 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, Fin (n - s) → 𝕜) ω (fun v : E => projCompl σ (ψ v))
      (φ (g x).1) :=
    (contMDiff_iff_contDiff.mpr ((contDiff_projCompl σ).comp ψ.contDiff)).contMDiffAt
  have h2 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ (g x).1 :=
    (contMDiffOn_of_mem_maximalAtlas (n := ω) hφ.1).contMDiffAt (φ.open_source.mem_nhds hyφ)
  exact h1.comp x (h2.comp x hg)

end Local

/-! ### The restricted blow-down off the centre -/

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M} {Y : Set M} {c : ℕ}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The restricted blow-down is proper: `S'` is closed in `M'` and `S` is Hausdorff. -/
theorem isProperMap_restrictMap (hS : IsClosedSubmanifold ψ S s) (h : IsBlowUp ψ Y c π)
    (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s) :
    IsProperMap (hS'.restrictMap hS π h.contMDiff
      (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed)) :=
  isProperMap_of_comp_of_t2 (hS'.restrictMap hS π h.contMDiff
    (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed)).contMDiff.continuous
    continuous_subtype_val (h.isProperMap.restrict hS'.isClosed)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The restricted blow-down is a bijection `S' ∖ π⁻¹(Y) → S ∖ Y` (the ambient bijection of
`IsBlowUp`, and `π⁻¹(S ∖ Y) ⊆ S'`). -/
theorem bijOn_restrictMap_compl (hS : IsClosedSubmanifold ψ S s) (h : IsBlowUp ψ Y c π)
    (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s) :
    Set.BijOn (hS'.restrictMap hS π h.contMDiff
        (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed))
      (hS'.restrictMap hS π h.contMDiff
        (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed) ⁻¹'
          (hS.preimageVal Y)ᶜ)
      (hS.preimageVal Y)ᶜ := by
  refine ⟨fun p hp => hp, fun p hp q hq hpq => ?_, fun y hy => ?_⟩
  · have hp' : (p : strictTransformSet π Y S).1 ∈ π ⁻¹' Yᶜ := hp
    have hq' : (q : strictTransformSet π Y S).1 ∈ π ⁻¹' Yᶜ := hq
    exact Subtype.ext (h.bijOn_compl.injOn hp' hq' (congrArg Subtype.val hpq))
  · have hy' : (y : S).1 ∈ Yᶜ := hy
    obtain ⟨p, hp, hpy⟩ := h.bijOn_compl.surjOn hy'
    have hpS : π p ∈ S := by rw [hpy]; exact (y : S).2
    have hpS' : p ∈ strictTransformSet π Y S := subset_closure ⟨hpS, hp⟩
    exact ⟨⟨p, hpS'⟩, hp, Subtype.ext hpy⟩

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- `S' ∖ π⁻¹(Y)` is dense in `S'`: `S'` is the closure of `π⁻¹(S ∖ Y)`. -/
theorem dense_preimage_compl_restrictMap (hS : IsClosedSubmanifold ψ S s) (h : IsBlowUp ψ Y c π)
    (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s) :
    Dense (hS'.restrictMap hS π h.contMDiff
      (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed) ⁻¹'
        (hS.preimageVal Y)ᶜ) := by
  refine IsInducing.subtypeVal.dense_iff.mpr fun p => ?_
  refine closure_mono ?_ p.2
  intro q hq
  exact ⟨⟨q, subset_closure hq⟩, hq.2, rfl⟩

omit [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] in
/-- The local inverse `Ψ` of `π` at a point off the centre carries `S ∩ Ψ.target ∖ Y` into `S'`. -/
theorem invFun_mem_strictTransform (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' M ω)
    (hΨ : Set.EqOn π Ψ Ψ.source) {y : M} (hy : y ∈ Ψ.target) (hyS : y ∈ S) (hyY : y ∉ Y) :
    Ψ.invFun y ∈ strictTransformSet π Y S := by
  have hm : Ψ.invFun y ∈ Ψ.source := Ψ.map_target hy
  have hπ : π (Ψ.invFun y) = y := by
    rw [hΨ hm]
    exact Ψ.right_inv hy
  refine subset_closure ⟨?_, ?_⟩
  · rw [hπ]; exact hyS
  · rw [hπ]; exact hyY

variable (hS : IsClosedSubmanifold ψ S s) (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
  (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s)

open scoped Classical in
/-- The inverse of the restricted blow-down near a point off the centre: the local inverse `Ψ` of
`π` read on `S ∩ Ψ.target ∖ Y` (junk `p₀` elsewhere). -/
def restrictInvFun (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' M ω) (hΨ : Set.EqOn π Ψ Ψ.source)
    (p₀ : hS'.toAnalyticManifold) (y : hS.toAnalyticManifold) : hS'.toAnalyticManifold :=
  if hy : (y : S).1 ∈ Ψ.target ∧ (y : S).1 ∉ Y then
    ⟨Ψ.invFun (y : S).1, invFun_mem_strictTransform Ψ hΨ hy.1 (y : S).2 hy.2⟩
  else p₀

omit [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω M'] in
open scoped Classical in
theorem restrictInvFun_of_mem (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' M ω)
    (hΨ : Set.EqOn π Ψ Ψ.source) (p₀ : hS'.toAnalyticManifold) {y : hS.toAnalyticManifold}
    (hy : (y : S).1 ∈ Ψ.target ∧ (y : S).1 ∉ Y) :
    restrictInvFun hS hS' Ψ hΨ p₀ y =
      ⟨Ψ.invFun (y : S).1, invFun_mem_strictTransform Ψ hΨ hy.1 (y : S).2 hy.2⟩ := by
  unfold restrictInvFun
  exact dite_eq_left hy

/-- The local inverse of `π` at a point of `S'` off the centre, restricted to the submanifolds:
a partial diffeomorphism of the bundled `S'` and `S` agreeing with the restricted blow-down on
`S' ∩ Ψ.source ∖ π⁻¹(Y)`. -/
def restrictPartialDiffeomorph (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' M ω)
    (hΨ : Set.EqOn π Ψ Ψ.source) (p₀ : hS'.toAnalyticManifold) :
    PartialDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) hS'.toAnalyticManifold
      hS.toAnalyticManifold ω where
  toFun := hS'.restrictMap hS π h.contMDiff
    (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed)
  invFun := restrictInvFun hS hS' Ψ hΨ p₀
  source := {p | (p : strictTransformSet π Y S).1 ∈ Ψ.source ∧
    π (p : strictTransformSet π Y S).1 ∉ Y}
  target := {y | (y : S).1 ∈ Ψ.target ∧ (y : S).1 ∉ Y}
  map_source' p hp := by
    refine ⟨?_, hp.2⟩
    change π (p : strictTransformSet π Y S).1 ∈ Ψ.target
    rw [hΨ hp.1]
    exact Ψ.map_source hp.1
  map_target' y hy := by
    have hy' : (y : S).1 ∈ Ψ.target ∧ (y : S).1 ∉ Y := hy
    rw [restrictInvFun_of_mem hS hS' Ψ hΨ p₀ hy']
    have hm : Ψ.invFun (y : S).1 ∈ Ψ.source := Ψ.map_target hy'.1
    have hπ : π (Ψ.invFun (y : S).1) = (y : S).1 := (hΨ hm).trans (Ψ.right_inv hy'.1)
    exact ⟨hm, fun hY => hy'.2 (hπ ▸ hY)⟩
  left_inv' p hp := by
    have hc : π (p : strictTransformSet π Y S).1 ∈ Ψ.target ∧
        π (p : strictTransformSet π Y S).1 ∉ Y := by
      refine ⟨?_, hp.2⟩
      rw [hΨ hp.1]
      exact Ψ.map_source hp.1
    rw [restrictInvFun_of_mem hS hS' Ψ hΨ p₀ hc]
    apply Subtype.ext
    change Ψ.invFun (π (p : strictTransformSet π Y S).1) = (p : strictTransformSet π Y S).1
    rw [hΨ hp.1]
    exact Ψ.left_inv hp.1
  right_inv' y hy := by
    have hy' : (y : S).1 ∈ Ψ.target ∧ (y : S).1 ∉ Y := hy
    rw [restrictInvFun_of_mem hS hS' Ψ hΨ p₀ hy']
    have hm : Ψ.invFun (y : S).1 ∈ Ψ.source := Ψ.map_target hy'.1
    exact Subtype.ext ((hΨ hm).trans (Ψ.right_inv hy'.1))
  open_source :=
    (Ψ.open_source.inter (hY.isClosed.isOpen_compl.preimage h.contMDiff.continuous)).preimage
      continuous_subtype_val
  open_target := (Ψ.open_target.inter hY.isClosed.isOpen_compl).preimage continuous_subtype_val
  contMDiffOn_toFun := (hS'.restrictMap hS π h.contMDiff
    (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed)).contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    intro y hy
    have hy' : (y : S).1 ∈ Ψ.target ∧ (y : S).1 ∉ Y := hy
    have hT : IsOpen {y : hS.toAnalyticManifold | (y : S).1 ∈ Ψ.target ∧ (y : S).1 ∉ Y} :=
      (Ψ.open_target.inter hY.isClosed.isOpen_compl).preimage continuous_subtype_val
    refine ContMDiffAt.contMDiffWithinAt ?_
    refine hS'.contMDiffAt_of_val ?_
    have hev : (Subtype.val ∘ restrictInvFun hS hS' Ψ hΨ p₀) =ᶠ[nhds y]
        fun z : hS.toAnalyticManifold => Ψ.invFun (z : S).1 := by
      filter_upwards [hT.mem_nhds hy'] with z hz
      have hz' : (z : S).1 ∈ Ψ.target ∧ (z : S).1 ∉ Y := hz
      change Subtype.val (restrictInvFun hS hS' Ψ hΨ p₀ z) = Ψ.invFun (z : S).1
      rw [restrictInvFun_of_mem hS hS' Ψ hΨ p₀ hz']
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
    exact (Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds hy'.1)).comp y
      (hS.contMDiff_val y)

omit [IsManifold 𝓘(𝕜, E) ω M] in
include hY in
/-- The restricted blow-down is a local analytic isomorphism off the centre: the restriction of
the ambient local inverse to the submanifolds. -/
theorem isLocalDiffeomorphOn_restrictMap_compl :
    IsLocalDiffeomorphOn 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω
      (hS'.restrictMap hS π h.contMDiff
        (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed))
      (hS'.restrictMap hS π h.contMDiff
        (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed) ⁻¹'
          (hS.preimageVal Y)ᶜ) := by
  intro x
  have hx : ((x.1 : hS'.toAnalyticManifold) : strictTransformSet π Y S).1 ∈ π ⁻¹' Yᶜ := x.2
  obtain ⟨Ψ, hxΨ, hΨ⟩ := (h.isLocalDiffeomorphOn_compl ⟨_, hx⟩).exists_partialDiffeomorph
  exact (restrictPartialDiffeomorph hS hY h hS' Ψ hΨ x.1).isLocalDiffeomorphAt _ _ _ ⟨hxΨ, hx⟩

end Manifold

end
