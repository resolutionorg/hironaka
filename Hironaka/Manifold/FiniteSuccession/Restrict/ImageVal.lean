/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Nested
import Hironaka.Manifold.AdaptedChart
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A closed submanifold of the bundled `S` is a closed submanifold of `M`

The push-forward of a blow-up sequence of a closed subscheme `S ⊆ X` regards its centres
`Z_i^S ⊆ S_i ⊆ X_i` as closed subschemes `Z_i^X := (j_i)_* Z_i^S` of `X_i`
[Kol07, Definition 30.3]. This module proves the manifold statement, the converse of
`IsClosedSubmanifold.preimage_val_of_subset` (`Nested.lean`): a closed submanifold `Y'` of the
bundled `S` (with its induced charts on `𝕜^{n-s}`) of codimension `c'` is, read in `M`, a closed
submanifold of codimension `c' + s` (`IsClosedSubmanifold.imageVal_isClosedSubmanifold`); a smooth
subspace of a manifold is locally a coordinate subspace [BM97, (3.8)(2)].

The adapted chart at a point of `Y'` is built from an adapted chart `φ` of `S` in `M`
(`S = {z_{σ₁} = 0}`) and an adapted chart `χ` of `Y'` in `S`: the chart change
`θ = χ ∘ χ₀⁻¹` of `𝕜^{n-s}` between the induced chart `χ₀` of `φ` and `χ` is analytic (both lie in
the maximal atlas of `S`), and it is extended to `𝕜^n` by the identity on the `σ₁`-coordinates
(`extendComplFun`, `extendCompl`, `extendComplE`) — a chart change of `E` in the analytic
groupoid. The chart `φ ∘ Θ` of `M` then reads `S` on the `σ₁`-coordinates and `χ` on the
complementary ones, so `Y'` is the zero set of the `s + c'` coordinates `σ₁ ⊔ σ'`
(`imageValEmb`). Not in the sources; a chart computation.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

/-! ### The model: a chart change of `𝕜^{n-s}` extended by the identity on `s` coordinates -/

section Model

variable {𝕜 : Type} {n s : ℕ}

/-- The map of `𝕜^n` that is the identity on the coordinates `σ` and `f` on the complementary
coordinates (read through `projCompl` and `complEquiv`). -/
def extendComplFun (σ : Fin s ↪ Fin n) (f : (Fin (n - s) → 𝕜) → (Fin (n - s) → 𝕜))
    (z : Fin n → 𝕜) : Fin n → 𝕜 :=
  fun j => if h : j ∈ Set.range σ then z j else f (projCompl σ z) (complEquiv σ ⟨j, h⟩)

theorem extendComplFun_apply_range (σ : Fin s ↪ Fin n) (f : (Fin (n - s) → 𝕜) → (Fin (n - s) → 𝕜))
    (z : Fin n → 𝕜) (i : Fin s) : extendComplFun σ f z (σ i) = z (σ i) := by
  simp only [extendComplFun, dite_eq_left (Set.mem_range_self i)]

theorem extendComplFun_apply_compl (σ : Fin s ↪ Fin n) (f : (Fin (n - s) → 𝕜) → (Fin (n - s) → 𝕜))
    (z : Fin n → 𝕜) (k : Fin (n - s)) :
    extendComplFun σ f z ((complEquiv σ).symm k).1 = f (projCompl σ z) k := by
  simp only [extendComplFun, dite_eq_right ((complEquiv σ).symm k).2]
  change f (projCompl σ z) (complEquiv σ ((complEquiv σ).symm k)) = _
  rw [Equiv.apply_symm_apply]

theorem projCompl_extendComplFun (σ : Fin s ↪ Fin n) (f : (Fin (n - s) → 𝕜) → (Fin (n - s) → 𝕜))
    (z : Fin n → 𝕜) : projCompl σ (extendComplFun σ f z) = f (projCompl σ z) := by
  funext k
  exact extendComplFun_apply_compl σ f z k

theorem extendComplFun_extendComplFun (σ : Fin s ↪ Fin n)
    {f g : (Fin (n - s) → 𝕜) → (Fin (n - s) → 𝕜)} {z : Fin n → 𝕜}
    (hgf : g (f (projCompl σ z)) = projCompl σ z) :
    extendComplFun σ g (extendComplFun σ f z) = z := by
  funext j
  by_cases h : j ∈ Set.range σ
  · obtain ⟨i, rfl⟩ := h
    rw [extendComplFun_apply_range, extendComplFun_apply_range]
  · have h1 := extendComplFun_apply_compl σ g (extendComplFun σ f z) (complEquiv σ ⟨j, h⟩)
    rw [projCompl_extendComplFun, hgf, Equiv.symm_apply_apply] at h1
    simp only [projCompl, Equiv.symm_apply_apply] at h1
    exact h1

variable [RCLike 𝕜]

theorem continuousOn_extendComplFun (σ : Fin s ↪ Fin n)
    {f : (Fin (n - s) → 𝕜) → (Fin (n - s) → 𝕜)} {U : Set (Fin (n - s) → 𝕜)}
    (hf : ContinuousOn f U) : ContinuousOn (extendComplFun σ f) {z | projCompl σ z ∈ U} := by
  refine continuousOn_pi.mpr fun j => ?_
  by_cases h : j ∈ Set.range σ
  · simp only [extendComplFun, dite_eq_left h]
    exact (continuous_apply j).continuousOn
  · simp only [extendComplFun, dite_eq_right h]
    exact (continuous_apply _).comp_continuousOn
      (hf.comp (continuous_projCompl σ).continuousOn fun z hz => hz)

theorem contDiffOn_extendComplFun (σ : Fin s ↪ Fin n)
    {f : (Fin (n - s) → 𝕜) → (Fin (n - s) → 𝕜)} {U : Set (Fin (n - s) → 𝕜)}
    (hf : ContDiffOn 𝕜 ω f U) : ContDiffOn 𝕜 ω (extendComplFun σ f) {z | projCompl σ z ∈ U} := by
  refine contDiffOn_pi.mpr fun j => ?_
  by_cases h : j ∈ Set.range σ
  · simp only [extendComplFun, dite_eq_left h]
    exact (contDiff_apply 𝕜 𝕜 j).contDiffOn
  · simp only [extendComplFun, dite_eq_right h]
    exact (contDiff_apply 𝕜 𝕜 _).comp_contDiffOn
      (hf.comp (contDiff_projCompl σ).contDiffOn fun z hz => hz)

/-- A partial homeomorphism `θ` of `𝕜^{n-s}` extended to `𝕜^n` by the identity on the coordinates
`σ`. -/
def extendCompl (σ : Fin s ↪ Fin n)
    (θ : OpenPartialHomeomorph (Fin (n - s) → 𝕜) (Fin (n - s) → 𝕜)) :
    OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜) where
  toFun := extendComplFun σ θ
  invFun := extendComplFun σ θ.symm
  source := {z | projCompl σ z ∈ θ.source}
  target := {w | projCompl σ w ∈ θ.target}
  map_source' z hz := by
    change projCompl σ (extendComplFun σ θ z) ∈ θ.target
    rw [projCompl_extendComplFun]
    exact θ.map_source hz
  map_target' w hw := by
    change projCompl σ (extendComplFun σ θ.symm w) ∈ θ.source
    rw [projCompl_extendComplFun]
    exact θ.map_target hw
  left_inv' _ hz := extendComplFun_extendComplFun σ (θ.left_inv hz)
  right_inv' _ hw := extendComplFun_extendComplFun σ (θ.right_inv hw)
  open_source := θ.open_source.preimage (continuous_projCompl σ)
  open_target := θ.open_target.preimage (continuous_projCompl σ)
  continuousOn_toFun := continuousOn_extendComplFun σ θ.continuousOn
  continuousOn_invFun := continuousOn_extendComplFun σ θ.continuousOn_symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The chart change of `E` corresponding to `extendCompl σ θ` through `ψ`. -/
def extendComplE (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (σ : Fin s ↪ Fin n)
    (θ : OpenPartialHomeomorph (Fin (n - s) → 𝕜) (Fin (n - s) → 𝕜)) : OpenPartialHomeomorph E E :=
  ψ.toHomeomorph.toOpenPartialHomeomorph ≫ₕ
    (extendCompl σ θ ≫ₕ ψ.symm.toHomeomorph.toOpenPartialHomeomorph)

variable (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (σ : Fin s ↪ Fin n)
  (θ : OpenPartialHomeomorph (Fin (n - s) → 𝕜) (Fin (n - s) → 𝕜))

theorem extendComplE_apply (v : E) : extendComplE ψ σ θ v = ψ.symm (extendComplFun σ θ (ψ v)) :=
  rfl

theorem mem_extendComplE_source {v : E} :
    v ∈ (extendComplE ψ σ θ).source ↔ projCompl σ (ψ v) ∈ θ.source :=
  ⟨fun h => h.2.1, fun h => ⟨Set.mem_univ _, h, Set.mem_univ _⟩⟩

theorem mem_extendComplE_target {v : E} :
    v ∈ (extendComplE ψ σ θ).target ↔ projCompl σ (ψ v) ∈ θ.target :=
  ⟨fun h => h.1.2, fun h => ⟨⟨Set.mem_univ _, h⟩, Set.mem_univ _⟩⟩

/-- The extended chart change lies in the analytic groupoid of `E` when `θ` is analytic both
ways. -/
theorem extendComplE_mem_contDiffGroupoid (hθ : ContDiffOn 𝕜 ω θ θ.source)
    (hθ' : ContDiffOn 𝕜 ω θ.symm θ.target) :
    extendComplE ψ σ θ ∈ contDiffGroupoid ω 𝓘(𝕜, E) := by
  refine mem_contDiffGroupoid_self _ ?_ ?_
  · have h1 : ContDiffOn 𝕜 ω (fun v : E => ψ.symm (extendComplFun σ θ (ψ v)))
        {v | projCompl σ (ψ v) ∈ θ.source} :=
      ψ.symm.contDiff.comp_contDiffOn
        ((contDiffOn_extendComplFun σ hθ).comp ψ.contDiff.contDiffOn fun v hv => hv)
    exact h1.mono fun v hv => (mem_extendComplE_source ψ σ θ).mp hv
  · have h1 : ContDiffOn 𝕜 ω (fun v : E => ψ.symm (extendComplFun σ θ.symm (ψ v)))
        {v | projCompl σ (ψ v) ∈ θ.target} :=
      ψ.symm.contDiff.comp_contDiffOn
        ((contDiffOn_extendComplFun σ hθ').comp ψ.contDiff.contDiffOn fun v hv => hv)
    exact h1.mono fun v hv => (mem_extendComplE_target ψ σ θ).mp hv

/-- The block embedding of `Y' ⊆ S ⊆ M`: the `s` coordinates of `S` and the `c'` coordinates of
`Y'` inside `S`, the latter read among the complementary coordinates. -/
def imageValEmb {c' : ℕ} (σ₁ : Fin s ↪ Fin n) (σ' : Fin c' ↪ Fin (n - s)) :
    Fin (c' + s) ↪ Fin n where
  toFun k := Sum.elim (fun k' => ((complEquiv σ₁).symm (σ' k')).1) (fun j => σ₁ j)
    (finSumFinEquiv.symm k)
  inj' := by
    have hf : Function.Injective fun k' : Fin c' => ((complEquiv σ₁).symm (σ' k')).1 :=
      fun a b h => σ'.injective ((complEquiv σ₁).symm.injective (Subtype.ext h))
    exact (hf.sumElim σ₁.injective fun a b h => ((complEquiv σ₁).symm (σ' a)).2 ⟨b, h.symm⟩).comp
      finSumFinEquiv.symm.injective

theorem imageValEmb_inl {c' : ℕ} (σ₁ : Fin s ↪ Fin n) (σ' : Fin c' ↪ Fin (n - s)) (k' : Fin c') :
    imageValEmb σ₁ σ' (finSumFinEquiv (Sum.inl k')) = ((complEquiv σ₁).symm (σ' k')).1 := by
  change Sum.elim _ _ (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl k'))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem imageValEmb_inr {c' : ℕ} (σ₁ : Fin s ↪ Fin n) (σ' : Fin c' ↪ Fin (n - s)) (j : Fin s) :
    imageValEmb σ₁ σ' (finSumFinEquiv (Sum.inr j)) = σ₁ j := by
  change Sum.elim _ _ (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end Model

/-! ### The image of a closed submanifold of the bundled `S` -/

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {S : Set M} {s : ℕ}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- A subset of the bundled `S` read in `M` through the inclusion (the centres
`Z_i^X := (j_i)_* Z_i^S` of the push-forward of a blow-up sequence, [Kol07, Definition 30.3]). -/
def IsClosedSubmanifold.imageVal (hS : IsClosedSubmanifold ψ S s) (Y' : Set hS.toAnalyticManifold) :
    Set M :=
  Subtype.val '' Y'

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.mem_imageVal (hS : IsClosedSubmanifold ψ S s)
    (Y' : Set hS.toAnalyticManifold) (x : M) :
    x ∈ hS.imageVal Y' ↔ ∃ p ∈ Y', (p : S).1 = x :=
  Iff.rfl

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Reading a subset of the bundled `S` in `M` and back gives it back. -/
theorem IsClosedSubmanifold.preimageVal_imageVal (hS : IsClosedSubmanifold ψ S s)
    (Y' : Set hS.toAnalyticManifold) : hS.preimageVal (hS.imageVal Y') = Y' :=
  Set.preimage_image_eq Y' Subtype.val_injective

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.imageVal_subset (hS : IsClosedSubmanifold ψ S s)
    (Y' : Set hS.toAnalyticManifold) : hS.imageVal Y' ⊆ S := by
  rintro _ ⟨p, -, rfl⟩
  exact (p : S).2

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.isClosed_imageVal (hS : IsClosedSubmanifold ψ S s)
    {Y' : Set hS.toAnalyticManifold} (hY' : IsClosed Y') : IsClosed (hS.imageVal Y') :=
  hS.isClosed.isClosedMap_subtype_val _ hY'

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The chart of `M` extending a chart of the bundled `S` by the equations of `S` (the chart of
`imageVal_isClosedSubmanifold`, stated separately because the chart itself is used when simple
normal crossings are lifted along a restricted succession): for `φ` adapted to `S` and containing
`(a' : M)` in its source, `χ₀` the induced chart of `φ` on `S`, and `χ` a chart of `S` adapted to
`Y'` containing `a'` in its source, the chart `φ ≫ₕ extendComplE ψ σ₁ (χ₀⁻¹ ≫ₕ χ)` of `M` contains
`(a' : M)` in its source and is adapted to `imageVal Y'` with the indices `imageValEmb σ₁ σ'` — the
`s` coordinates of `S` from `φ`, the `c'` coordinates of `Y'` from `χ` through the chart change
`χ ∘ χ₀⁻¹` of `𝕜^{n−s}`. -/
theorem IsClosedSubmanifold.isAdaptedChart_extendComplE (hS : IsClosedSubmanifold ψ S s)
    {Y' : Set hS.toAnalyticManifold} {c' : ℕ} {a' : hS.toAnalyticManifold}
    {χ : OpenPartialHomeomorph hS.toAnalyticManifold (Fin (n - s) → 𝕜)}
    {σ' : Fin c' ↪ Fin (n - s)} (ha'χ : a' ∈ χ.source)
    (hχ : IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Y' χ σ')
    {φ : OpenPartialHomeomorph M E} {σ₁ : Fin s ↪ Fin n} (haφ : (a' : S).1 ∈ φ.source)
    (hφ : IsAdaptedChart ψ S φ σ₁) :
    (a' : S).1 ∈ (φ ≫ₕ extendComplE ψ σ₁ ((hS.inducedChart hφ (a' : S).2).symm ≫ₕ χ)).source ∧
      IsAdaptedChart ψ (hS.imageVal Y')
        (φ ≫ₕ extendComplE ψ σ₁ ((hS.inducedChart hφ (a' : S).2).symm ≫ₕ χ))
        (imageValEmb σ₁ σ') := by
  -- the induced chart of `φ` on the bundled `S`, taken opaque
  have hχ₀mem : hS.inducedChart hφ (a' : S).2 ∈
      maximalAtlas 𝓘(𝕜, Fin (n - s) → 𝕜) ω hS.toAnalyticManifold :=
    hS.inducedChart_mem_maximalAtlas hφ (a' : S).2
  have hχ₀app : ∀ p : hS.toAnalyticManifold,
      hS.inducedChart hφ (a' : S).2 p = projCompl σ₁ (ψ (φ (p : S).1)) := fun _ => rfl
  have hχ₀src : ∀ p : hS.toAnalyticManifold,
      p ∈ (hS.inducedChart hφ (a' : S).2).source ↔ (p : S).1 ∈ φ.source := fun _ => Iff.rfl
  set χ₀ := hS.inducedChart hφ (a' : S).2 with hχ₀def
  clear_value χ₀
  -- the chart change `θ = χ ∘ χ₀⁻¹` of `𝕜^{n-s}` and its analyticity both ways
  have hθ : ContDiffOn 𝕜 ω (χ₀.symm ≫ₕ χ) (χ₀.symm ≫ₕ χ).source :=
    contDiffOn_chartChange hχ₀mem hχ.1
  have hθ' : ContDiffOn 𝕜 ω (χ₀.symm ≫ₕ χ).symm (χ₀.symm ≫ₕ χ).target := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact contDiffOn_chartChange hχ.1 hχ₀mem
  have he := extendComplE_mem_contDiffGroupoid ψ σ₁ _ hθ hθ'
  -- the coordinates of a point of `S ∩ φ.source` in the induced chart, and through `θ`
  have hcoord : ∀ p : hS.toAnalyticManifold, (p : S).1 ∈ φ.source →
      (χ₀.symm ≫ₕ χ) (projCompl σ₁ (ψ (φ (p : S).1))) = χ p := by
    intro p hp
    rw [← hχ₀app p]
    change χ (χ₀.symm (χ₀ p)) = χ p
    rw [χ₀.left_inv ((hχ₀src p).mpr hp)]
  have hmemχ : ∀ p : hS.toAnalyticManifold, (p : S).1 ∈ φ.source →
      projCompl σ₁ (ψ (φ (p : S).1)) ∈ (χ₀.symm ≫ₕ χ).source → p ∈ χ.source := by
    intro p hp hp'
    have h2 : χ₀.symm (projCompl σ₁ (ψ (φ (p : S).1))) ∈ χ.source := hp'.2
    rw [← hχ₀app p, χ₀.left_inv ((hχ₀src p).mpr hp)] at h2
    exact h2
  refine ⟨⟨haφ, ?_⟩, ⟨trans_mem_maximalAtlas hφ.1 he, fun x hx => ?_⟩⟩
  · -- `a` lies in the source of the extended chart change
    refine (mem_extendComplE_source ψ σ₁ _).mpr ⟨?_, ?_⟩
    · change projCompl σ₁ (ψ (φ (a' : S).1)) ∈ χ₀.target
      rw [← hχ₀app a']
      exact χ₀.map_source ((hχ₀src a').mpr haφ)
    · change χ₀.symm (projCompl σ₁ (ψ (φ (a' : S).1))) ∈ χ.source
      rw [← hχ₀app a', χ₀.left_inv ((hχ₀src a').mpr haφ)]
      exact ha'χ
  · have hx1 : x ∈ φ.source := hx.1
    have hx2 : projCompl σ₁ (ψ (φ x)) ∈ (χ₀.symm ≫ₕ χ).source := by
      have h2 : φ x ∈ (extendComplE ψ σ₁ (χ₀.symm ≫ₕ χ)).source := hx.2
      exact (mem_extendComplE_source ψ σ₁ _).mp h2
    have hw : ψ ((φ ≫ₕ extendComplE ψ σ₁ (χ₀.symm ≫ₕ χ)) x) =
        extendComplFun σ₁ (χ₀.symm ≫ₕ χ) (ψ (φ x)) :=
      ψ.apply_symm_apply _
    -- the `c' + s` coordinates split into the `s` coordinates of `S` and the `c'` of `Y'`
    have hsplit : (∀ i, extendComplFun σ₁ (χ₀.symm ≫ₕ χ) (ψ (φ x)) (imageValEmb σ₁ σ' i) = 0) ↔
        (∀ k', (χ₀.symm ≫ₕ χ) (projCompl σ₁ (ψ (φ x))) (σ' k') = 0) ∧
          ∀ j, ψ (φ x) (σ₁ j) = 0 := by
      constructor
      · intro hall
        refine ⟨fun k' => ?_, fun j => ?_⟩
        · have h1 := hall (finSumFinEquiv (Sum.inl k'))
          rwa [imageValEmb_inl, extendComplFun_apply_compl σ₁ (χ₀.symm ≫ₕ χ) (ψ (φ x)) (σ' k')]
            at h1
        · have h1 := hall (finSumFinEquiv (Sum.inr j))
          rwa [imageValEmb_inr, extendComplFun_apply_range σ₁ (χ₀.symm ≫ₕ χ) (ψ (φ x)) j] at h1
      · rintro ⟨hk, hj⟩ i
        obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective i
        rcases u with k' | j
        · rw [imageValEmb_inl, extendComplFun_apply_compl σ₁ (χ₀.symm ≫ₕ χ) (ψ (φ x)) (σ' k')]
          exact hk k'
        · rw [imageValEmb_inr, extendComplFun_apply_range σ₁ (χ₀.symm ≫ₕ χ) (ψ (φ x)) j]
          exact hj j
    rw [hw]
    refine Iff.trans ?_ hsplit.symm
    constructor
    · rintro ⟨p, hpY', rfl⟩
      have hpχ : p ∈ χ.source := hmemχ p hx1 hx2
      refine ⟨fun k' => ?_, (hφ.2 _ hx1).mp (p : S).2⟩
      rw [hcoord p hx1]
      exact (hχ.2 p hpχ).mp hpY' k'
    · rintro ⟨hk, hj⟩
      have hxS : x ∈ S := (hφ.2 x hx1).mpr hj
      have hpχ : (⟨x, hxS⟩ : hS.toAnalyticManifold) ∈ χ.source := hmemχ ⟨x, hxS⟩ hx1 hx2
      refine ⟨⟨x, hxS⟩, (hχ.2 _ hpχ).mpr fun k' => ?_, rfl⟩
      have h1 := hk k'
      rw [hcoord ⟨x, hxS⟩ hx1] at h1
      exact h1

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- A closed submanifold of a closed submanifold is a closed submanifold, the converse of
`preimage_val_of_subset`: a closed submanifold `Y'` of the bundled `S` of codimension `c'` is,
read in `M`, a closed submanifold of codimension `c' + s`. -/
theorem IsClosedSubmanifold.imageVal_isClosedSubmanifold (hS : IsClosedSubmanifold ψ S s)
    {Y' : Set hS.toAnalyticManifold} {c' : ℕ}
    (hY' : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Y' c') :
    IsClosedSubmanifold ψ (hS.imageVal Y') (c' + s) := by
  refine ⟨hS.isClosed_imageVal hY'.isClosed, fun a ha => ?_⟩
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨χ, σ', ha'χ, hχ⟩ := hY'.exists_adaptedChart a' ha'
  obtain ⟨φ, σ₁, haφ, hφ⟩ := hS.exists_adaptedChart (a' : S).1 (a' : S).2
  exact ⟨_, _, hS.isAdaptedChart_extendComplE ha'χ hχ haφ hφ⟩

end Manifold

end
