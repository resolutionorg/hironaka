/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.StructureSheaf
public import Hironaka.Manifold.Submanifold
import Hironaka.Manifold.Chart.Atlas
import Hironaka.Manifold.Germ.ChartTransport
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Generators
import Hironaka.Manifold.Submanifold.Manifold
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Adapted charts from generators

A closed subset `Y` of an analytic manifold `M` which is, near each of its points, the common
zero set of `c` analytic functions with linearly independent differentials is a closed
submanifold of codimension `c` (`isClosedSubmanifold_of_generators`; the converse of the
description of a closed submanifold by an adapted chart, `IsClosedSubmanifold`).
This is the implicit function theorem as the sources use it: "by the implicit function theorem,
`z = 0` defines a regular submanifold" [BM97, §1], a smooth space is "locally a coordinate
subspace of a coordinate chart" [BM97, (3.8)(2)], and a local section of order `1` has a smooth
zero divisor [Kol07, Theorem 80, proof].

The proof completes the generators `z_1, …, z_c` to a chart at `a` (`exists_chart_extending`); no
analysis is reproved, the analytic inverse function theorem being Mathlib's
`ContDiffAt.toOpenPartialHomeomorph` at `n = ω`:

* `exists_dual_basis_extension_rclike` (linear algebra): linearly independent continuous
  functionals `ℓ_i` on a finite-dimensional `E` sit at positions `σ i` of a family `lam` of
  `n = dim E` functionals with `v ↦ (lam_j v)_j` bijective;
* `coordExtension`, `exists_coordExtension`: the map `Ψ x = ψ⁻¹ (g_i x at σ i, lam_j (x − y)
  elsewhere)`, analytic at `y` with invertible derivative when the `dg_i(y)` are independent;
* `exists_openPartialHomeomorph_mem_contDiffGroupoid`: an analytic map with invertible derivative
  at `y` restricts to an `OpenPartialHomeomorph E E` in the analytic groupoid
  `contDiffGroupoid ω 𝓘(𝕜, E)` with `y` in its source;
* `trans_mem_maximalAtlas`: a chart of the maximal atlas composed with an element of the
  groupoid is a chart of the maximal atlas; so is its composite with an analytic open partial
  homeomorphism of `E` with analytic inverse, and every restriction of that composite to an open
  set (`trans_mem_maximalAtlas_of_analytic'`, `trans_restrOpen_mem_maximalAtlas_of_analytic'`);
* `mfderiv_eq_fderiv_comp_chart`, `hasIndependentDifferentialsAt_iff_chart`: independence of the
  manifold derivatives is independence of the differentials read in any chart;
* `exists_chart_extending`: analytic `z_i` vanishing at `a` with independent differentials are
  the coordinates `σ i` of a chart `e` of the maximal atlas at `a` with `e a = 0`;
* `isClosedSubmanifold_of_generators`: the statement above, from `exists_chart_extending` at each
  `a ∈ Y`, the chart restricted to the neighbourhood carrying the generators.

The chart-extension theorem is how the zero sets of analytic functions with independent
differentials — hypersurfaces of maximal contact, centres — are recognised as closed
submanifolds in the `Hironaka` library (`Hironaka/Manifold/Chart/`).
-/

@[expose] public section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set Module
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### Linear algebra: extending independent functionals to a dual basis -/

section DualBasis

variable {n : ℕ}

/-- Linearly independent continuous functionals `ℓ_i` on a finite-dimensional `E` of dimension `n`
sit at positions `σ i` in a family `lam` of `n` functionals with `v ↦ (lam_j v)_j` bijective: a
basis of the dual extending them (`Basis.extend`). Not in the sources; linear algebra for
`exists_coordExtension`. -/
theorem exists_dual_basis_extension_rclike [FiniteDimensional 𝕜 E] (hE : finrank 𝕜 E = n)
    {ι : Type*} (ℓ : ι → (E →L[𝕜] 𝕜)) (hℓ : LinearIndependent 𝕜 ℓ) :
    ∃ (lam : Fin n → (E →L[𝕜] 𝕜)) (σ : ι → Fin n), Function.Injective σ ∧
      (∀ i, lam (σ i) = ℓ i) ∧ Function.Bijective (ContinuousLinearMap.pi lam) := by
  classical
  have hs : LinearIndepOn 𝕜 id (Set.range ℓ) := hℓ.linearIndepOn_id
  let B := Basis.extend hs
  have : Fintype (hs.extend (Set.subset_univ _)) := FiniteDimensional.fintypeBasisIndex B
  have hdual : finrank 𝕜 (E →L[𝕜] 𝕜) = n := by
    rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] (E →L[𝕜] 𝕜)).finrank_eq, ← hE]
    exact Subspace.dual_finrank_eq
  have hcard : Fintype.card (hs.extend (Set.subset_univ _)) = n := by
    rw [← Module.finrank_eq_card_basis B, hdual]
  let τ := Fintype.equivFinOfCardEq hcard
  have hmem : ∀ i, ℓ i ∈ hs.extend (Set.subset_univ _) := fun i =>
    Basis.subset_extend hs ⟨i, rfl⟩
  have hinj : Function.Injective
      (ContinuousLinearMap.pi fun j => ((τ.symm j).1 : E →L[𝕜] 𝕜)) := by
    intro v w hvw
    rw [← sub_eq_zero]
    have hx : ∀ x : hs.extend (Set.subset_univ _), (x : E →L[𝕜] 𝕜) (v - w) = 0 := by
      intro x
      have := congrFun hvw (τ x)
      simp only [ContinuousLinearMap.pi_apply, Equiv.symm_apply_apply] at this
      rw [map_sub, this, sub_self]
    have hall : ∀ φ : E →L[𝕜] 𝕜, φ (v - w) = 0 := by
      intro φ
      rw [← B.sum_repr φ, sum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [smul_apply, Basis.extend_apply_self, hx x, smul_zero]
    rw [← Module.forall_dual_apply_eq_zero_iff 𝕜]
    intro φ
    have := hall (LinearMap.toContinuousLinearMap φ)
    rwa [LinearMap.coe_toContinuousLinearMap'] at this
  have hsurj : Function.Surjective
      (ContinuousLinearMap.pi fun j => ((τ.symm j).1 : E →L[𝕜] 𝕜)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := ((ContinuousLinearMap.pi fun j => ((τ.symm j).1 : E →L[𝕜] 𝕜)) :
        E →ₗ[𝕜] (Fin n → 𝕜))) (by rw [hE, Module.finrank_fin_fun])).mp hinj
  refine ⟨fun j => (τ.symm j).1, fun i => τ ⟨ℓ i, hmem i⟩, ?_, ?_, hinj, hsurj⟩
  · intro i j h
    exact hℓ.injective (Subtype.ext_iff.mp (τ.injective h))
  · intro i
    simp

end DualBasis

/-! ### The coordinate extension -/

section CoordExtension

variable {n c : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- The coordinate extension of `g_1, …, g_c` at `y` along `σ`: the map `x ↦ ψ⁻¹ (w x)` with
`w x (σ i) = g i x` and `w x j = lam j (x − y)` for `j` outside the range of `σ`
(`Function.extend`). -/
noncomputable def coordExtension (σ : Fin c → Fin n) (g : Fin c → E → 𝕜)
    (lam : Fin n → (E →L[𝕜] 𝕜)) (y x : E) : E :=
  ψ.symm (Function.extend σ (fun i => g i x) fun j => lam j (x - y))

variable {σ : Fin c → Fin n} (hσ : Function.Injective σ) {g : Fin c → E → 𝕜}
  (lam : Fin n → (E →L[𝕜] 𝕜)) {y : E}

include hσ in
/-- The `σ i`-th coordinate of the extension is `g i`. -/
theorem coordExtension_apply (g : Fin c → E → 𝕜) (x : E) (i : Fin c) :
    ψ (coordExtension ψ σ g lam y x) (σ i) = g i x := by
  simp only [coordExtension, ContinuousLinearEquiv.apply_symm_apply, hσ.extend_apply]

/-- The coordinates outside the range of `σ` are the affine forms `lam j (x − y)`. -/
theorem coordExtension_apply_of_not_mem_range (g : Fin c → E → 𝕜) (x : E) {j : Fin n}
    (hj : ¬∃ i, σ i = j) : ψ (coordExtension ψ σ g lam y x) j = lam j (x - y) := by
  simp only [coordExtension, ContinuousLinearEquiv.apply_symm_apply,
    Function.extend_apply' _ _ _ hj]

include hσ in
/-- The extension is centred: `Ψ y = 0` when the `g i` vanish at `y`. -/
theorem coordExtension_self (hg0 : ∀ i, g i y = 0) : coordExtension ψ σ g lam y y = 0 := by
  have : (Function.extend σ (fun i => g i y) fun j => lam j (y - y)) = 0 := by
    funext j
    by_cases hj : ∃ i, σ i = j
    · obtain ⟨i, rfl⟩ := hj
      simp only [hσ.extend_apply, hg0 i, Pi.zero_apply]
    · simp only [Function.extend_apply' _ _ _ hj, sub_self, map_zero, Pi.zero_apply]
  simp only [coordExtension, this, map_zero]

include hσ in
/-- The extension is analytic at `y` when the `g i` are. -/
theorem contDiffAt_coordExtension (hg : ∀ i, ContDiffAt 𝕜 ω (g i) y) :
    ContDiffAt 𝕜 ω (coordExtension ψ σ g lam y) y := by
  have hpi : ContDiffAt 𝕜 ω
      (fun x => Function.extend σ (fun i => g i x) fun j => lam j (x - y)) y := by
    refine contDiffAt_pi.mpr fun j => ?_
    by_cases hj : ∃ i, σ i = j
    · obtain ⟨i, rfl⟩ := hj
      simp only [hσ.extend_apply]
      exact hg i
    · simp only [Function.extend_apply' _ _ _ hj]
      exact ((lam j).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  exact ψ.symm.contDiff.contDiffAt.comp y hpi

include hσ in
/-- The derivative of the extension at `y` is `ψ⁻¹` composed with the family of functionals
`dg_i(y)` at `σ i` and `lam j` elsewhere. -/
theorem hasFDerivAt_coordExtension (hg : ∀ i, DifferentiableAt 𝕜 (g i) y) :
    HasFDerivAt (coordExtension ψ σ g lam y)
      ((ψ.symm : (Fin n → 𝕜) →L[𝕜] E).comp
        (ContinuousLinearMap.pi (Function.extend σ (fun i => fderiv 𝕜 (g i) y) lam))) y := by
  have hpi : HasFDerivAt
      (fun x j => Function.extend σ (fun i => g i x) (fun j => lam j (x - y)) j)
      (ContinuousLinearMap.pi (Function.extend σ (fun i => fderiv 𝕜 (g i) y) lam)) y := by
    refine hasFDerivAt_pi.mpr fun j => ?_
    by_cases hj : ∃ i, σ i = j
    · obtain ⟨i, rfl⟩ := hj
      simp only [hσ.extend_apply]
      exact (hg i).hasFDerivAt
    · simp only [Function.extend_apply' _ _ _ hj]
      have := (lam j).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const y)
      rwa [ContinuousLinearMap.comp_id] at this
  exact ψ.symm.hasFDerivAt.comp y hpi

omit hσ in
/-- Analytic functions `g_1, …, g_c` at `y` with linearly independent differentials extend to a
coordinate system at `y`: an injection `σ : Fin c ↪ Fin n` and `Ψ : E → E`, analytic at `y` with
invertible derivative, whose `σ i`-th coordinate is `g i`; `Ψ y = 0` when the `g i` vanish at `y`.
The linear-algebra step of completing `z = 0` to a coordinate system. -/
theorem exists_coordExtension (hg : ∀ i, ContDiffAt 𝕜 ω (g i) y)
    (hind : LinearIndependent 𝕜 fun i => fderiv 𝕜 (g i) y) :
    ∃ (σ : Fin c ↪ Fin n) (Ψ : E → E) (L : E ≃L[𝕜] E), ContDiffAt 𝕜 ω Ψ y ∧
      HasFDerivAt Ψ (L : E →L[𝕜] E) y ∧ (∀ x i, ψ (Ψ x) (σ i) = g i x) ∧
      ((∀ i, g i y = 0) → Ψ y = 0) := by
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  have hE : finrank 𝕜 E = n := by
    rw [ψ.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  obtain ⟨lam, σ, hσ, hlamσ, hbij⟩ := exists_dual_basis_extension_rclike hE _ hind
  -- the family of functionals is `lam` itself
  have hext : Function.extend σ (fun i => fderiv 𝕜 (g i) y) lam = lam := by
    funext j
    by_cases hj : ∃ i, σ i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hσ.extend_apply, hlamσ]
    · rw [Function.extend_apply' _ _ _ hj]
  let Λ : E ≃L[𝕜] (Fin n → 𝕜) :=
    (LinearEquiv.ofBijective (ContinuousLinearMap.pi lam : E →ₗ[𝕜] (Fin n → 𝕜))
      hbij).toContinuousLinearEquiv
  refine ⟨⟨σ, hσ⟩, coordExtension ψ σ g lam y, Λ.trans ψ.symm,
    contDiffAt_coordExtension ψ hσ lam hg, ?_, fun x i => coordExtension_apply ψ hσ lam g x i,
    fun hg0 => coordExtension_self ψ hσ lam hg0⟩
  have hd := hasFDerivAt_coordExtension ψ hσ lam fun i =>
    (hg i).differentiableAt WithTop.top_ne_zero
  rw [hext] at hd
  convert hd using 1
  ext v
  rfl

end CoordExtension

/-! ### The analytic inverse function theorem, chart-valued -/

section InverseFunction

/-- The analytic inverse function theorem in chart-valued form (Mathlib's
`ContDiffAt.toOpenPartialHomeomorph` at `n = ω` and `ContDiffAt.to_localInverse`): a map `Ψ : E → E`
analytic at `y` with invertible derivative restricts, inside any open `s ∋ y`, to an open partial
homeomorphism `e` with `y ∈ e.source`, `e = Ψ` on its source, lying in the analytic groupoid
`contDiffGroupoid ω 𝓘(𝕜, E)` (analytic with analytic inverse). -/
theorem exists_openPartialHomeomorph_mem_contDiffGroupoid [CompleteSpace E] {Ψ : E → E} {y : E}
    (hΨ : ContDiffAt 𝕜 ω Ψ y) (L : E ≃L[𝕜] E) (hL : HasFDerivAt Ψ (L : E →L[𝕜] E) y)
    {s : Set E} (hs : IsOpen s) (hy : y ∈ s) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧ e.source ⊆ s ∧ Set.EqOn e Ψ e.source ∧
      e ∈ contDiffGroupoid ω 𝓘(𝕜, E) := by
  have hn : (ω : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_zero
  set e₁ := hΨ.toOpenPartialHomeomorph Ψ hL hn with he₁
  have hcoe : ⇑e₁ = Ψ := hΨ.toOpenPartialHomeomorph_coe hL hn
  have hy₁ : y ∈ e₁.source := hΨ.mem_toOpenPartialHomeomorph_source hL hn
  -- `Ψ` is analytic near `y`
  obtain ⟨s', hs'sub, hs'open, hys'⟩ :=
    eventually_nhds_iff.mp hΨ.analyticAt.eventually_analyticAt
  -- the inverse is analytic near `Ψ y`
  have hinv : ContDiffAt 𝕜 ω e₁.symm (Ψ y) := hΨ.to_localInverse hL hn
  obtain ⟨t, htsub, htopen, hyt⟩ := eventually_nhds_iff.mp hinv.analyticAt.eventually_analyticAt
  -- the shrunk chart
  have hopen : IsOpen (s ∩ s' ∩ (e₁.source ∩ e₁ ⁻¹' t)) :=
    (hs.inter hs'open).inter (e₁.isOpen_inter_preimage htopen)
  refine ⟨e₁.restrOpen _ hopen, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    refine ⟨hy₁, ⟨hy, hys'⟩, hy₁, ?_⟩
    rw [Set.mem_preimage, hcoe]
    exact hyt
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact fun x hx => hx.2.1.1
  · intro x _
    rw [OpenPartialHomeomorph.coe_restrOpen, hcoe]
  · refine mem_contDiffGroupoid_self _ ?_ ?_
    · rw [OpenPartialHomeomorph.coe_restrOpen, OpenPartialHomeomorph.restrOpen_source, hcoe]
      exact fun x hx => (hs'sub x hx.2.1.2).contDiffAt.contDiffWithinAt
    · rw [OpenPartialHomeomorph.coe_restrOpen_symm]
      intro b hb
      have hb' := (e₁.restrOpen _ hopen).map_target hb
      rw [OpenPartialHomeomorph.restrOpen_source] at hb'
      have hbt : b ∈ t := by
        have h1 : e₁ (e₁.symm b) ∈ t := hb'.2.2.2
        have h2 : e₁ (e₁.symm b) = b := (e₁.restrOpen _ hopen).right_inv hb
        rwa [h2] at h1
      exact (htsub b hbt).contDiffAt.contDiffWithinAt

end InverseFunction

/-! ### Composing a chart with an element of the analytic groupoid -/

section Atlas

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- A chart `χ` of the maximal analytic atlas composed with an element `e` of the analytic
groupoid of the model space is again a chart of the maximal atlas (`mem_maximalAtlas_iff`: the
transition maps with the atlas are `e.symm ≫ₕ (χ.symm ≫ₕ e')` and `(e'.symm ≫ₕ χ) ≫ₕ e`). -/
theorem trans_mem_maximalAtlas {χ : OpenPartialHomeomorph M E}
    (hχ : χ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {e : OpenPartialHomeomorph E E}
    (he : e ∈ contDiffGroupoid ω 𝓘(𝕜, E)) : χ.trans e ∈ maximalAtlas 𝓘(𝕜, E) ω M := by
  intro e' he'
  obtain ⟨h1, h2⟩ := hχ e' he'
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ω 𝓘(𝕜, E)).trans ((contDiffGroupoid ω 𝓘(𝕜, E)).symm he) h1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ω 𝓘(𝕜, E)).trans h2 he

/-- The composite of a chart of the maximal atlas with an analytic open partial homeomorphism of
`E` with analytic inverse is a chart of the maximal atlas (`trans_mem_maximalAtlas` with
`mem_contDiffGroupoid_omega_of_analytic'`). -/
theorem trans_mem_maximalAtlas_of_analytic' {e : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) {e₀ : OpenPartialHomeomorph E E}
    (h : AnalyticOnNhd 𝕜 e₀ e₀.source) (h' : AnalyticOnNhd 𝕜 e₀.symm e₀.target) :
    e.trans e₀ ∈ maximalAtlas 𝓘(𝕜, E) ω M :=
  trans_mem_maximalAtlas he (mem_contDiffGroupoid_omega_of_analytic' e₀ h h')

/-- So is each restriction of that composite to an open set (Mathlib's
`restr_mem_maximalAtlas`). -/
theorem trans_restrOpen_mem_maximalAtlas_of_analytic' {e : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) {e₀ : OpenPartialHomeomorph E E}
    (h : AnalyticOnNhd 𝕜 e₀ e₀.source) (h' : AnalyticOnNhd 𝕜 e₀.symm e₀.target) (s : Set M)
    (hs : IsOpen s) : (e.trans e₀).restrOpen s hs ∈ maximalAtlas 𝓘(𝕜, E) ω M := by
  rw [OpenPartialHomeomorph.restrOpen_eq_restr]
  exact restr_mem_maximalAtlas _ (trans_mem_maximalAtlas_of_analytic' he h h') hs

end Atlas

/-! ### Differentials read in a chart -/

section Differentials

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {χ : OpenPartialHomeomorph M E} (hχ : χ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M} (ha : a ∈ χ.source)

include hχ ha in
/-- The chain rule: the manifold derivative of `f : M → 𝕜` at `a` is the derivative of `f ∘ χ⁻¹`
at `χ a`, read through the chart's derivative. -/
theorem mfderiv_eq_fderiv_comp_chart {f : M → 𝕜} (hf : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) f a) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜) f a =
      (fderiv 𝕜 (f ∘ χ.symm) (χ a)).comp (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) χ a) := by
  have hχa : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E) χ a :=
    (mdifferentiable_of_mem_maximalAtlas hχ).mdifferentiableAt ha
  have hsymm : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E) χ.symm (χ a) :=
    (mdifferentiable_of_mem_maximalAtlas hχ).symm.mdifferentiableAt (χ.map_source ha)
  have hf' : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) f (χ.symm (χ a)) := by rwa [χ.left_inv ha]
  have hg : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (f ∘ χ.symm) (χ a) := hf'.comp (χ a) hsymm
  have heq : f =ᶠ[𝓝 a] (f ∘ χ.symm) ∘ χ := by
    filter_upwards [χ.open_source.mem_nhds ha] with x hx
    simp only [Function.comp_apply, χ.left_inv hx]
  rw [heq.mfderiv_eq, mfderiv_comp a hg hχa, mfderiv_eq_fderiv]
  rfl

include hχ ha in
/-- Independence of the differentials (`HasIndependentDifferentialsAt`, in terms of `mfderiv`) is
independence of the differentials of the functions read in any chart `χ` at `a`: `mfderiv` is
`fderiv` in the chart composed with the chart's derivative, an isomorphism of the tangent
spaces. -/
theorem hasIndependentDifferentialsAt_iff_chart {c : ℕ} {z : Fin c → M → 𝕜}
    (hz : ∀ i, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (z i) a) :
    HasIndependentDifferentialsAt E z a ↔
      LinearIndependent 𝕜 fun i => fderiv 𝕜 (z i ∘ χ.symm) (χ a) := by
  set L : TangentSpace 𝓘(𝕜, E) a →L[𝕜] E := mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) χ a with hLdef
  have hL : ∀ i, mderivFun E (z i) a = (fderiv 𝕜 (z i ∘ χ.symm) (χ a)).comp L := fun i =>
    mfderiv_eq_fderiv_comp_chart hχ ha (hz i)
  unfold HasIndependentDifferentialsAt
  constructor
  · intro h
    rw [Fintype.linearIndependent_iff] at h ⊢
    intro g hg j
    refine h g ?_ j
    ext v
    have h1 := congrArg (fun D : E →L[𝕜] 𝕜 => D (L v)) hg
    simp only [sum_apply, smul_apply, zero_apply] at h1 ⊢
    simpa only [hL, ContinuousLinearMap.comp_apply] using h1
  · intro h
    have hsurj : Function.Surjective L :=
      (mdifferentiable_of_mem_maximalAtlas hχ).mfderiv_surjective ha
    rw [Fintype.linearIndependent_iff] at h ⊢
    intro g hg j
    refine h g ?_ j
    ext w
    obtain ⟨v, hv⟩ := hsurj w
    have h1 := congrArg (fun D : TangentSpace 𝓘(𝕜, E) a →L[𝕜] 𝕜 => D v) hg
    simp only [hL, sum_apply, smul_apply, zero_apply, ContinuousLinearMap.comp_apply] at h1 ⊢
    rw [← hv]
    exact h1

end Differentials

/-! ### The adapted chart -/

section AdaptedChart

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- **Completion of generators to a chart** — the implicit function theorem as used in
[BM97, §1] ("by the implicit function theorem, `z = 0` defines a regular submanifold"),
[Kol07, Theorem 80, proof] and [Hir64, p. 121]: analytic functions `z_1, …, z_c` at `a` vanishing
at `a` with linearly independent differentials are the coordinates `σ 1, …, σ c` of a chart `e` of
the maximal analytic atlas at `a` with `e a = 0`, i.e. `z i = π_{σ i} ∘ ψ ∘ e` on the source of `e`.
Proof: read the `z i` in the chart `χ = chartAt E a` (`hasIndependentDifferentialsAt_iff_chart`),
extend their differentials to a dual basis and the functions to a coordinate map `Ψ` at `χ a`
(`exists_coordExtension`), invert it analytically
(`exists_openPartialHomeomorph_mem_contDiffGroupoid`) and compose (`trans_mem_maximalAtlas`). -/
theorem exists_chart_extending [IsManifold 𝓘(𝕜, E) ω M] {c : ℕ} (z : Fin c → M → 𝕜) (a : M)
    (hz : ∀ i, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (z i) a) (hz0 : ∀ i, z i a = 0)
    (hind : HasIndependentDifferentialsAt E z a) :
    ∃ (e : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n), e ∈ maximalAtlas 𝓘(𝕜, E) ω M ∧
      a ∈ e.source ∧ e a = 0 ∧ ∀ x ∈ e.source, ∀ i, z i x = ψ (e x) (σ i) := by
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set χ : OpenPartialHomeomorph M E := chartAt E a with hχdef
  have hχ : χ ∈ maximalAtlas 𝓘(𝕜, E) ω M :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := ω) a
  have ha : a ∈ χ.source := mem_chart_source E a
  -- the generators read in the chart
  set g : Fin c → E → 𝕜 := fun i => z i ∘ χ.symm with hgdef
  have hg : ∀ i, ContDiffAt 𝕜 ω (g i) (χ a) := fun i =>
    contMDiffAt_iff_contDiffAt.mp
      (ContMDiffAt.comp_of_eq (hz i) (contMDiffAt_chart_symm E χ ha hχ) (χ.left_inv ha))
  have hg0 : ∀ i, g i (χ a) = 0 := fun i => by
    simp only [hgdef, Function.comp_apply, χ.left_inv ha, hz0 i]
  have hgind : LinearIndependent 𝕜 fun i => fderiv 𝕜 (g i) (χ a) :=
    (hasIndependentDifferentialsAt_iff_chart hχ ha fun i =>
      (hz i).mdifferentiableAt WithTop.top_ne_zero).mp hind
  -- the coordinate extension and its analytic inverse
  obtain ⟨σ, Ψ, L, hΨ, hL, hΨσ, hΨ0⟩ := exists_coordExtension ψ hg hgind
  obtain ⟨e₀, hy₀, -, heq₀, hG₀⟩ :=
    exists_openPartialHomeomorph_mem_contDiffGroupoid hΨ L hL χ.open_target (χ.map_source ha)
  refine ⟨χ.trans e₀, σ, trans_mem_maximalAtlas hχ hG₀, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨ha, hy₀⟩
  · rw [OpenPartialHomeomorph.trans_apply, heq₀ hy₀]
    exact hΨ0 hg0
  · intro x hx i
    rw [OpenPartialHomeomorph.trans_source] at hx
    rw [OpenPartialHomeomorph.trans_apply, heq₀ hx.2, hΨσ]
    simp only [hgdef, Function.comp_apply, χ.left_inv hx.1]

end AdaptedChart

/-! ### Closed submanifolds from generators -/

section

variable (E) (M : Type u) [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {Y : Set M} {c : ℕ}

/-- A closed set `Y` such that every `a ∈ Y` has an open neighbourhood `U` and sections
`z_1, …, z_c ∈ 𝒪_M(U)` with linearly independent differentials at every point of `Y ∩ U` and
`Y ∩ U = {z_1 = … = z_c = 0}` is a closed submanifold of codimension `c` ([BM97, (3.8)(2)]; the
converse of the description by adapted charts). Proof: at `a ∈ Y`, `exists_chart_extending`
completes the `z i` — analytic at `a`, vanishing at `a`, independent — to a chart `e` at `a` whose
coordinates `σ i` are the `z i`; the restriction of `e` to `U` is adapted to `Y`, because on `U`
the zero set of the `z i` is `Y`. -/
theorem isClosedSubmanifold_of_generators [IsManifold 𝓘(𝕜, E) ω M] (hY : IsClosed Y)
    (h : ∀ a ∈ Y, ∃ (U : Opens M) (_ : a ∈ U)
      (z : Fin c → (structureSheaf 𝕜 E M).presheaf.obj (op U)),
      (∀ x ∈ Y ∩ U, HasIndependentDifferentialsAt E (fun i => extendSection 𝕜 E (z i)) x) ∧
      Y ∩ U = {x ∈ U | ∀ i, extendSection 𝕜 E (z i) x = 0}) :
    IsClosedSubmanifold ψ Y c := by
  refine ⟨hY, fun a ha => ?_⟩
  obtain ⟨U, haU, z, hind, hYU⟩ := h a ha
  have hmem : ∀ x, x ∈ Y ∩ U ↔ x ∈ U ∧ ∀ i, extendSection 𝕜 E (z i) x = 0 := fun x => by
    rw [hYU]
    exact Iff.rfl
  have hz : ∀ i, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (extendSection 𝕜 E (z i)) a := fun i =>
    (contMDiffOn_extendBy0 𝓘(𝕜, E) ω M (z i)).contMDiffAt (U.isOpen.mem_nhds haU)
  have hz0 : ∀ i, extendSection 𝕜 E (z i) a = 0 := ((hmem a).mp ⟨ha, haU⟩).2
  obtain ⟨e, σ, he, hae, -, hcoord⟩ :=
    exists_chart_extending ψ (fun i => extendSection 𝕜 E (z i)) a hz hz0 (hind a ⟨ha, haU⟩)
  refine ⟨e.restrOpen U U.isOpen, σ, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hae, haU⟩
  · refine ⟨?_, fun x hx => ?_⟩
    · rw [OpenPartialHomeomorph.restrOpen_eq_restr]
      exact restr_mem_maximalAtlas _ he U.isOpen
    · rw [OpenPartialHomeomorph.restrOpen_source] at hx
      rw [OpenPartialHomeomorph.coe_restrOpen]
      have hcx : ∀ i, ψ (e x) (σ i) = extendSection 𝕜 E (z i) x := fun i =>
        (hcoord x hx.1 i).symm
      simp only [hcx]
      exact ⟨fun hxY => ((hmem x).mp ⟨hxY, hx.2⟩).2, fun h0 => ((hmem x).mpr ⟨hx.2, h0⟩).1⟩

end

end Manifold
