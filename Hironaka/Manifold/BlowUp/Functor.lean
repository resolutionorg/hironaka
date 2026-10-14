/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Unique
public import Hironaka.Manifold.Chart.Transport
import Hironaka.Manifold.BlowUp.Restrict
import Hironaka.Manifold.LocalDiffeomorph
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Functoriality of the blowing-up under local isomorphisms

An analytic isomorphism `g` between open subsets `U₁ ⊆ M₁`, `U₂ ⊆ M₂` carrying `Y₁ ∩ U₁` onto
`Y₂ ∩ U₂` lifts to a unique analytic isomorphism `π₁⁻¹(U₁) → π₂⁻¹(U₂)` over `g` between
blowings-up with centres `Y₁`, `Y₂` (`IsBlowUp.exists_lift_partialDiffeomorph`). This is the
functoriality of the blowing-up under local isomorphisms, the case of an isomorphism onto an open
subset of the pull-back of a blow-up along a smooth morphism [Kol07, Definition 30, 30.1]; it
follows from the uniqueness clause of [BM88, Definition 4.1]. The lift is built as in
`Hironaka.Manifold.BlowUp.Unique`: over the centre by blow-up charts of one index over an
adapted chart `φ₁` of `Y₁` at `π₁ p` and its transport `φ₁ ∘ g⁻¹` (an adapted chart of `Y₂`), off
the centre as the unique point off the divisor over `g(π₁ p)`; uniqueness of lifts (density of
the complement of the divisor, injectivity of `π₂` off `Y₂`) gives the local chart formulas, the
inverse and the uniqueness clause. The first ingredient is that a chart of the maximal atlas
composed with the inverse of a partial diffeomorphism is a chart of the maximal atlas of the
target (`transportChart`, `Hironaka/Manifold/Chart/Transport.lean`). The centres are required to
have positive codimension: for `c = 0` no total map `M₁' → M₂'` need exist.

This functoriality is what makes the blowing-up, and the sequences of blowings-up built from it,
compatible with local isomorphisms of the ambient manifold
(`Hironaka.Manifold.FiniteSuccession.Lift`,
`Hironaka.Manifold.FiniteSuccession.Restrict.Transport`).
-/

@[expose] public section

open TopologicalSpace Topology Filter
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The lift of a partial diffeomorphism carrying the centres to each other -/

section Lift

variable {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace E M₁] {M₂ : Type u}
  [TopologicalSpace M₂] [ChartedSpace E M₂] {Y₁ : Set M₁} {Y₂ : Set M₂} {c : ℕ}
  (g : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁ M₂ ω) (hg : g '' (Y₁ ∩ g.source) = Y₂ ∩ g.target)

variable {φ : OpenPartialHomeomorph M₁ E} {σ : Fin c ↪ Fin n}

variable {M₁' M₂' : Type u} [TopologicalSpace M₁'] [ChartedSpace E M₁'] [TopologicalSpace M₂']
  [ChartedSpace E M₂'] {π₁ : M₁' → M₁} {π₂ : M₂' → M₂} {i : Fin c}
  {Φ₁ : OpenPartialHomeomorph M₁' E} {Φ₂ : OpenPartialHomeomorph M₂' E}

/-- `Φ₂⁻¹ ∘ Φ₁` lifts `π₁` to `π₂` over `g`, for blow-up charts of one index over an adapted chart
and its transport. -/
theorem IsBlowUpChart.blowDown_symm_apply_transport (hsub : φ.source ⊆ g.source)
    (hΦ₁ : IsBlowUpChart ψ π₁ φ σ i Φ₁) (hΦ₂ : IsBlowUpChart ψ π₂ (transportChart g φ) σ i Φ₂)
    {p : M₁'} (hp : p ∈ Φ₁.source) : π₂ (Φ₂.symm (Φ₁ p)) = g (π₁ p) := by
  have hT : Φ₁.target = Φ₂.target := by
    ext v
    rw [hΦ₁.mem_target_iff, hΦ₂.mem_target_iff, transportChart_target_eq g hsub]
  have hw : Φ₁ p ∈ Φ₂.target := by rw [← hT]; exact Φ₁.map_source hp
  have hq : Φ₂.symm (Φ₁ p) ∈ Φ₂.source := Φ₂.map_target hw
  have h1 := hΦ₂.comm _ hq
  rw [Φ₂.right_inv hw, ← hΦ₁.comm p hp, transportChart_apply] at h1
  have hs := hΦ₂.source_subset hq
  rw [transportChart_source] at hs
  have h2 : g.invFun (π₂ (Φ₂.symm (Φ₁ p))) = π₁ p :=
    φ.injOn hs.2 (hΦ₁.source_subset hp) (ψ.injective h1)
  have e : g (g.invFun (π₂ (Φ₂.symm (Φ₁ p)))) = π₂ (Φ₂.symm (Φ₁ p)) := g.right_inv hs.1
  rw [← e, h2]

/-- The chart change between a blow-up chart of `π₁` over `φ` and a blow-up chart of `π₂` over the
transported chart is analytic on the source (the two charts read the same coordinates through `g`).
-/
theorem IsBlowUpChart.contMDiffOn_symm_comp_transport (hsub : φ.source ⊆ g.source)
    (hΦ₁ : IsBlowUpChart ψ π₁ φ σ i Φ₁) (hΦ₂ : IsBlowUpChart ψ π₂ (transportChart g φ) σ i Φ₂) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Φ₂.symm ∘ Φ₁) Φ₁.source := by
  have hT : Φ₁.target = Φ₂.target := by
    ext v
    rw [hΦ₁.mem_target_iff, hΦ₂.mem_target_iff, transportChart_target_eq g hsub]
  exact (contMDiffOn_symm_of_mem_maximalAtlas hΦ₂.mem_maximalAtlas).comp
    (contMDiffOn_of_mem_maximalAtlas hΦ₁.mem_maximalAtlas) fun _ hp => by
      rw [← hT]
      exact Φ₁.map_source hp

variable [IsManifold 𝓘(𝕜, E) ω M₁'] [T2Space M₁'] [SecondCountableTopology M₁']
  [IsManifold 𝓘(𝕜, E) ω M₂'] [T2Space M₂'] [SecondCountableTopology M₂']
  (hY₁ : IsClosedSubmanifold ψ Y₁ c) (h₁ : IsBlowUp ψ Y₁ c π₁) (h₂ : IsBlowUp ψ Y₂ c π₂)

include hg hY₁ h₁ h₂ in
/-- Uniqueness of lifts over `g`: two continuous maps over `g ∘ π₁` into the second blowing-up
agree on an open subset of `π₁⁻¹(g.source)`. -/
theorem IsBlowUp.eqOn_of_comp_eq_of_image_eq {N : Set M₁'} (hN : IsOpen N)
    (hNs : N ⊆ π₁ ⁻¹' g.source) {G G' : M₁' → M₂'} (hG : ContinuousOn G N)
    (hG' : ContinuousOn G' N) (hπ : ∀ p ∈ N, π₂ (G p) = g (π₁ p))
    (hπ' : ∀ p ∈ N, π₂ (G' p) = g (π₁ p)) : Set.EqOn G G' N := by
  have hS : Set.EqOn G G' (N ∩ π₁ ⁻¹' Y₁ᶜ) := by
    rintro p ⟨hp, hpY⟩
    have hpY' : π₁ p ∉ Y₁ := hpY
    have hgp : g (π₁ p) ∉ Y₂ := fun h => hpY' ((mem_iff_apply_mem_of_image_eq g hg (hNs hp)).mpr h)
    have e1 : G p ∈ π₂ ⁻¹' Y₂ᶜ := by
      change π₂ (G p) ∉ Y₂
      rw [hπ p hp]
      exact hgp
    have e2 : G' p ∈ π₂ ⁻¹' Y₂ᶜ := by
      change π₂ (G' p) ∉ Y₂
      rw [hπ' p hp]
      exact hgp
    exact h₂.bijOn_compl.injOn e1 e2 ((hπ p hp).trans (hπ' p hp).symm)
  refine hS.of_subset_closure hG hG' Set.inter_subset_left fun p hp => ?_
  rw [mem_closure_iff]
  intro O hO hpO
  obtain ⟨q, ⟨hqO, hqN⟩, hq⟩ :=
    mem_closure_iff.mp (h₁.dense_preimage_compl hY₁ p) (O ∩ N) (hO.inter hN) ⟨hpO, hp⟩
  exact ⟨q, hqO, hqN, hq⟩

/-! #### The chart data at a point over the centre -/

section ChartData

variable {a : M₁}

/-- The adapted chart at a point of the centre, restricted to the source of `g`. -/
noncomputable def adChartG (ha : a ∈ Y₁) : OpenPartialHomeomorph M₁ E :=
  (adChart hY₁ ha).restrOpen g.source g.open_source

/-- The chosen adapted chart at `a`, cut down to `g.source`, is adapted to `Y₁`. -/
theorem adChartG_isAdaptedChart (ha : a ∈ Y₁) :
    IsAdaptedChart ψ Y₁ (adChartG g hY₁ ha) (adEmb hY₁ ha) :=
  (adChart_spec hY₁ ha).2.restrOpen' g.source g.open_source

/-- The cut-down adapted chart has source inside `g.source`. -/
theorem adChartG_source_subset (ha : a ∈ Y₁) : (adChartG g hY₁ ha).source ⊆ g.source := by
  rw [adChartG, OpenPartialHomeomorph.restrOpen_source]
  exact Set.inter_subset_right

/-- A point of `Y₁ ∩ g.source` lies in the source of its cut-down adapted chart. -/
theorem mem_adChartG_source (hp : a ∈ g.source) (ha : a ∈ Y₁) :
    a ∈ (adChartG g hY₁ ha).source := by
  rw [adChartG, OpenPartialHomeomorph.restrOpen_source]
  exact ⟨(adChart_spec hY₁ ha).1, hp⟩

variable {p : M₁'}

/-- The index of a blow-up chart of `π₁` at `p`. -/
noncomputable def bIdxG (hp : π₁ p ∈ g.source) (hY : π₁ p ∈ Y₁) : Fin c :=
  (h₁.cover _ _ (adChartG_isAdaptedChart g hY₁ hY) p (mem_adChartG_source g hY₁ hp hY)).choose

/-- A blow-up chart of `π₁` at `p`. -/
noncomputable def bChart₁G (hp : π₁ p ∈ g.source) (hY : π₁ p ∈ Y₁) :
    OpenPartialHomeomorph M₁' E :=
  (h₁.cover _ _ (adChartG_isAdaptedChart g hY₁ hY) p
    (mem_adChartG_source g hY₁ hp hY)).choose_spec.choose

/-- The chosen blow-up chart of `π₁` at `p` over the cut-down adapted chart is a blow-up chart
containing `p`. -/
theorem bChart₁G_spec (hp : π₁ p ∈ g.source) (hY : π₁ p ∈ Y₁) :
    IsBlowUpChart ψ π₁ (adChartG g hY₁ hY) (adEmb hY₁ hY) (bIdxG g hY₁ h₁ hp hY)
        (bChart₁G g hY₁ h₁ hp hY) ∧ p ∈ (bChart₁G g hY₁ h₁ hp hY).source :=
  (h₁.cover _ _ (adChartG_isAdaptedChart g hY₁ hY) p
    (mem_adChartG_source g hY₁ hp hY)).choose_spec.choose_spec

variable [IsManifold 𝓘(𝕜, E) ω M₁] [IsManifold 𝓘(𝕜, E) ω M₂]

/-- A blow-up chart of `π₂` of the same index over the transported adapted chart. -/
noncomputable def bChart₂G (hp : π₁ p ∈ g.source) (hY : π₁ p ∈ Y₁) :
    OpenPartialHomeomorph M₂' E :=
  (h₂.exists_chart _ _ (isAdaptedChart_transportChart g hg (adChartG_isAdaptedChart g hY₁ hY))
    (bIdxG g hY₁ h₁ hp hY)).choose

omit [IsManifold 𝓘(𝕜, E) ω M₁] in
/-- The chosen blow-up chart of `π₂` over the transported chart (same block indices and index) is a
blow-up chart. -/
theorem bChart₂G_spec (hp : π₁ p ∈ g.source) (hY : π₁ p ∈ Y₁) :
    IsBlowUpChart ψ π₂ (transportChart g (adChartG g hY₁ hY)) (adEmb hY₁ hY)
      (bIdxG g hY₁ h₁ hp hY) (bChart₂G g hg hY₁ h₁ h₂ hp hY) :=
  (h₂.exists_chart _ _ (isAdaptedChart_transportChart g hg (adChartG_isAdaptedChart g hY₁ hY))
    (bIdxG g hY₁ h₁ hp hY)).choose_spec

end ChartData

variable [IsManifold 𝓘(𝕜, E) ω M₁] [IsManifold 𝓘(𝕜, E) ω M₂] [Nonempty M₂']

open scoped Classical in
/-- The lift of `π₁` to `π₂` over `g`: over the centre `Φ₂⁻¹ ∘ Φ₁` in blow-up charts of one index
over an adapted chart and its transport, off the centre the unique point of `M₂'` off the divisor
over `g (π₁ p)`; an arbitrary point outside `π₁⁻¹(g.source)`. -/
noncomputable def liftPointG (p : M₁') : M₂' :=
  if hp : π₁ p ∈ g.source then
    if hY : π₁ p ∈ Y₁ then (bChart₂G g hg hY₁ h₁ h₂ hp hY).symm (bChart₁G g hY₁ h₁ hp hY p)
    else (h₂.bijOn_compl.surjOn (show g (π₁ p) ∈ Y₂ᶜ from
      fun h => hY ((mem_iff_apply_mem_of_image_eq g hg hp).mpr h))).choose
  else Classical.arbitrary M₂'

omit [IsManifold 𝓘(𝕜, E) ω M₁] in
/-- Over the centre the lift of `g` is read through the chosen blow-up charts. -/
theorem liftPointG_of_mem {p : M₁'} (hp : π₁ p ∈ g.source) (hY : π₁ p ∈ Y₁) :
    liftPointG g hg hY₁ h₁ h₂ p =
      (bChart₂G g hg hY₁ h₁ h₂ hp hY).symm (bChart₁G g hY₁ h₁ hp hY p) := by
  rw [liftPointG, dite_eq_left hp, dite_eq_left hY]

omit [IsManifold 𝓘(𝕜, E) ω M₁] in
/-- The lift commutes with the blow-downs over `g`: `π₂ ∘ liftPointG = g ∘ π₁` on `π₁⁻¹(g.source)`.
-/
theorem blowDown_liftPointG {p : M₁'} (hp : π₁ p ∈ g.source) :
    π₂ (liftPointG g hg hY₁ h₁ h₂ p) = g (π₁ p) := by
  by_cases hY : π₁ p ∈ Y₁
  · rw [liftPointG_of_mem g hg hY₁ h₁ h₂ hp hY]
    exact (bChart₁G_spec g hY₁ h₁ hp hY).1.blowDown_symm_apply_transport g
      (adChartG_source_subset g hY₁ hY) (bChart₂G_spec g hg hY₁ h₁ h₂ hp hY)
      (bChart₁G_spec g hY₁ h₁ hp hY).2
  · rw [liftPointG, dite_eq_left hp, dite_eq_right hY]
    exact (h₂.bijOn_compl.surjOn (show g (π₁ p) ∈ Y₂ᶜ from
      fun h => hY ((mem_iff_apply_mem_of_image_eq g hg hp).mpr h))).choose_spec.2

omit [IsManifold 𝓘(𝕜, E) ω M₁] in
/-- Off the centre, the lift is the unique point off the divisor over `g (π₁ p)`. -/
theorem liftPointG_eq_of_notMem {p : M₁'} (hp : π₁ p ∈ g.source) (hY : π₁ p ∉ Y₁) {q : M₂'}
    (hq : π₂ q = g (π₁ p)) : liftPointG g hg hY₁ h₁ h₂ p = q := by
  have hgp : g (π₁ p) ∉ Y₂ := fun h => hY ((mem_iff_apply_mem_of_image_eq g hg hp).mpr h)
  have hmem : liftPointG g hg hY₁ h₁ h₂ p ∈ π₂ ⁻¹' Y₂ᶜ := by
    rw [liftPointG, dite_eq_left hp, dite_eq_right hY]
    exact (h₂.bijOn_compl.surjOn (show g (π₁ p) ∈ Y₂ᶜ from
      fun h => hY ((mem_iff_apply_mem_of_image_eq g hg hp).mpr h))).choose_spec.1
  have hq' : q ∈ π₂ ⁻¹' Y₂ᶜ := by
    change π₂ q ∉ Y₂
    rw [hq]
    exact hgp
  exact h₂.bijOn_compl.injOn hmem hq' ((blowDown_liftPointG g hg hY₁ h₁ h₂ hp).trans hq.symm)

omit [IsManifold 𝓘(𝕜, E) ω M₁] in
/-- Near a point over the centre, the lift is the chart formula `Φ₂⁻¹ ∘ Φ₁`. -/
theorem liftPointG_eqOn_of_mem {p : M₁'} (hp : π₁ p ∈ g.source) (hY : π₁ p ∈ Y₁) :
    Set.EqOn (liftPointG g hg hY₁ h₁ h₂)
      ((bChart₂G g hg hY₁ h₁ h₂ hp hY).symm ∘ bChart₁G g hY₁ h₁ hp hY)
      (bChart₁G g hY₁ h₁ hp hY).source := by
  intro q hq
  have hΦ₁ := (bChart₁G_spec g hY₁ h₁ hp hY).1
  have hΦ₂ := bChart₂G_spec g hg hY₁ h₁ h₂ hp hY
  have hsub := adChartG_source_subset g hY₁ hY
  have hq' : π₁ q ∈ g.source := hsub (hΦ₁.source_subset hq)
  by_cases hqY : π₁ q ∈ Y₁
  · have hΦ₁' := (bChart₁G_spec g hY₁ h₁ hq' hqY).1
    have hΦ₂' := bChart₂G_spec g hg hY₁ h₁ h₂ hq' hqY
    have hsub' := adChartG_source_subset g hY₁ hqY
    have hN : IsOpen ((bChart₁G g hY₁ h₁ hp hY).source ∩ (bChart₁G g hY₁ h₁ hq' hqY).source) :=
      (bChart₁G g hY₁ h₁ hp hY).open_source.inter (bChart₁G g hY₁ h₁ hq' hqY).open_source
    have heq := h₁.eqOn_of_comp_eq_of_image_eq g hg hY₁ h₂ hN
      (fun r hr => hsub (hΦ₁.source_subset hr.1))
      ((hΦ₁'.contMDiffOn_symm_comp_transport g hsub' hΦ₂').continuousOn.mono
        Set.inter_subset_right)
      ((hΦ₁.contMDiffOn_symm_comp_transport g hsub hΦ₂).continuousOn.mono Set.inter_subset_left)
      (fun r hr => hΦ₁'.blowDown_symm_apply_transport g hsub' hΦ₂' hr.2)
      (fun r hr => hΦ₁.blowDown_symm_apply_transport g hsub hΦ₂ hr.1)
      ⟨hq, (bChart₁G_spec g hY₁ h₁ hq' hqY).2⟩
    rw [liftPointG_of_mem g hg hY₁ h₁ h₂ hq' hqY]
    exact heq
  · exact liftPointG_eq_of_notMem g hg hY₁ h₁ h₂ hq' hqY
      (hΦ₁.blowDown_symm_apply_transport g hsub hΦ₂ hq)

omit [IsManifold 𝓘(𝕜, E) ω M₁] in
/-- Near a point off the centre, the lift is `Ψ⁻¹ ∘ g ∘ π₁` for a local inverse `Ψ` of `π₂`. -/
theorem exists_eqOn_of_notMem_G {p : M₁'} (hp : π₁ p ∈ g.source) (hY : π₁ p ∉ Y₁) :
    ∃ N : Set M₁', IsOpen N ∧ p ∈ N ∧ N ⊆ π₁ ⁻¹' g.source ∧
      ∃ Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₂' M₂ ω, (∀ r ∈ N, g (π₁ r) ∈ Ψ.target) ∧
        Set.EqOn (liftPointG g hg hY₁ h₁ h₂) (Ψ.invFun ∘ g ∘ π₁) N := by
  have hgp : g (π₁ p) ∉ Y₂ := fun h => hY ((mem_iff_apply_mem_of_image_eq g hg hp).mpr h)
  have hmem : liftPointG g hg hY₁ h₁ h₂ p ∈ π₂ ⁻¹' Y₂ᶜ := by
    change π₂ (liftPointG g hg hY₁ h₁ h₂ p) ∉ Y₂
    rw [blowDown_liftPointG g hg hY₁ h₁ h₂ hp]
    exact hgp
  obtain ⟨Ψ, hqΨ, hΨ⟩ := (h₂.isLocalDiffeomorphOn_compl ⟨_, hmem⟩).exists_partialDiffeomorph
  have hqΨ' : liftPointG g hg hY₁ h₁ h₂ p ∈ Ψ.source := hqΨ
  have hopen : IsOpen (g.source ∩ g ⁻¹' Ψ.target) :=
    g.toOpenPartialHomeomorph.isOpen_inter_preimage Ψ.open_target
  refine ⟨π₁ ⁻¹' ((g.source ∩ g ⁻¹' Ψ.target) ∩ Y₁ᶜ),
    (hopen.inter hY₁.isClosed.isOpen_compl).preimage h₁.contMDiff.continuous,
    ⟨⟨hp, ?_⟩, hY⟩, fun _ hr => hr.1.1, Ψ, fun _ hr => hr.1.2, fun r hr => ?_⟩
  · change g (π₁ p) ∈ Ψ.target
    rw [← blowDown_liftPointG g hg hY₁ h₁ h₂ hp, hΨ hqΨ']
    exact Ψ.map_source hqΨ'
  · have hr1 : g (π₁ r) ∈ Ψ.target := hr.1.2
    have hr2 : π₁ r ∉ Y₁ := hr.2
    have hmem' : Ψ.invFun (g (π₁ r)) ∈ Ψ.source := Ψ.map_target hr1
    refine liftPointG_eq_of_notMem g hg hY₁ h₁ h₂ hr.1.1 hr2 ?_
    change π₂ (Ψ.invFun (g (π₁ r))) = g (π₁ r)
    rw [hΨ hmem']
    exact Ψ.right_inv hr1

omit [IsManifold 𝓘(𝕜, E) ω M₁] in
/-- The lift is analytic on `π₁⁻¹(g.source)`. -/
theorem contMDiffOn_liftPointG :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (liftPointG g hg hY₁ h₁ h₂) (π₁ ⁻¹' g.source) := by
  intro p hp
  have hp' : π₁ p ∈ g.source := hp
  refine ContMDiffAt.contMDiffWithinAt ?_
  by_cases hY : π₁ p ∈ Y₁
  · have hΦ₁ := (bChart₁G_spec g hY₁ h₁ hp' hY).1
    have hΦ₂ := bChart₂G_spec g hg hY₁ h₁ h₂ hp' hY
    exact ((hΦ₁.contMDiffOn_symm_comp_transport g (adChartG_source_subset g hY₁ hY) hΦ₂).congr
      (liftPointG_eqOn_of_mem g hg hY₁ h₁ h₂ hp' hY)).contMDiffAt
      ((bChart₁G g hY₁ h₁ hp' hY).open_source.mem_nhds (bChart₁G_spec g hY₁ h₁ hp' hY).2)
  · obtain ⟨N, hN, hpN, hNs, Ψ, hNΨ, heq⟩ := exists_eqOn_of_notMem_G g hg hY₁ h₁ h₂ hp' hY
    have hsm : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Ψ.invFun ∘ g ∘ π₁) N :=
      Ψ.contMDiffOn_invFun.comp
        (g.contMDiffOn_toFun.comp h₁.contMDiff.contMDiffOn fun r hr => hNs hr) hNΨ
    exact (hsm.congr heq).contMDiffAt (hN.mem_nhds hpN)

omit [IsManifold 𝓘(𝕜, E) ω M₁] in
/-- The lift of `g` maps `π₁⁻¹(g.source)` into `π₂⁻¹(g.target)`. -/
theorem liftPointG_mem_preimage {p : M₁'} (hp : π₁ p ∈ g.source) :
    liftPointG g hg hY₁ h₁ h₂ p ∈ π₂ ⁻¹' g.target := by
  change π₂ (liftPointG g hg hY₁ h₁ h₂ p) ∈ g.target
  rw [blowDown_liftPointG g hg hY₁ h₁ h₂ hp]
  exact g.map_source hp

/-! ### The lift as a partial diffeomorphism -/

variable [Nonempty M₁'] (hY₂ : IsClosedSubmanifold ψ Y₂ c)

/-- The lift in the other direction inverts the lift on `π₁⁻¹(g.source)` (uniqueness of lifts of
`π₁` to itself). -/
theorem liftPointG_liftPointG_symm {p : M₁'} (hp : π₁ p ∈ g.source) :
    liftPointG g.symm (image_symm_eq_of_image_eq g hg) hY₂ h₂ h₁ (liftPointG g hg hY₁ h₁ h₂ p) =
      p := by
  have hN : IsOpen (π₁ ⁻¹' g.source) := g.open_source.preimage h₁.contMDiff.continuous
  have hcont : ContinuousOn (liftPointG g.symm (image_symm_eq_of_image_eq g hg) hY₂ h₂ h₁ ∘
      liftPointG g hg hY₁ h₁ h₂) (π₁ ⁻¹' g.source) :=
    (contMDiffOn_liftPointG g.symm (image_symm_eq_of_image_eq g hg) hY₂ h₂ h₁).continuousOn.comp
      (contMDiffOn_liftPointG g hg hY₁ h₁ h₂).continuousOn
      fun _ hq => liftPointG_mem_preimage g hg hY₁ h₁ h₂ hq
  refine h₁.eqOn_of_comp_eq hY₁ h₁ hN hcont continuousOn_id (fun q hq => ?_) (fun _ _ => rfl) hp
  have hq' : π₁ q ∈ g.source := hq
  change π₁ (liftPointG g.symm (image_symm_eq_of_image_eq g hg) hY₂ h₂ h₁
    (liftPointG g hg hY₁ h₁ h₂ q)) = π₁ q
  rw [blowDown_liftPointG g.symm (image_symm_eq_of_image_eq g hg) hY₂ h₂ h₁
    (liftPointG_mem_preimage g hg hY₁ h₁ h₂ hq'), blowDown_liftPointG g hg hY₁ h₁ h₂ hq']
  exact g.left_inv hq'

/-- The lift of `g` as a partial diffeomorphism `M₁' → M₂'` with source `π₁⁻¹(g.source)` and
target `π₂⁻¹(g.target)`. -/
noncomputable def liftPartialDiffeomorph : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁' M₂' ω where
  toFun := liftPointG g hg hY₁ h₁ h₂
  invFun := liftPointG g.symm (image_symm_eq_of_image_eq g hg) hY₂ h₂ h₁
  source := π₁ ⁻¹' g.source
  target := π₂ ⁻¹' g.target
  map_source' _ hp := liftPointG_mem_preimage g hg hY₁ h₁ h₂ hp
  map_target' _ hq := liftPointG_mem_preimage g.symm (image_symm_eq_of_image_eq g hg) hY₂ h₂ h₁ hq
  left_inv' _ hp := liftPointG_liftPointG_symm g hg hY₁ h₁ h₂ hY₂ hp
  right_inv' _ hq :=
    liftPointG_liftPointG_symm g.symm (image_symm_eq_of_image_eq g hg) hY₂ h₂ h₁ hY₁ hq
  open_source := g.open_source.preimage h₁.contMDiff.continuous
  open_target := g.open_target.preimage h₂.contMDiff.continuous
  contMDiffOn_toFun := contMDiffOn_liftPointG g hg hY₁ h₁ h₂
  contMDiffOn_invFun := contMDiffOn_liftPointG g.symm (image_symm_eq_of_image_eq g hg) hY₂ h₂ h₁

end Lift

/-! ### Functoriality under local isomorphisms -/

section Statement

variable {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace E M₁] [IsManifold 𝓘(𝕜, E) ω M₁]
  {M₂ : Type u} [TopologicalSpace M₂] [ChartedSpace E M₂] [IsManifold 𝓘(𝕜, E) ω M₂]
  {Y₁ : Set M₁} {Y₂ : Set M₂} {c : ℕ} {M₁' M₂' : Type u} [TopologicalSpace M₁']
  [ChartedSpace E M₁'] [IsManifold 𝓘(𝕜, E) ω M₁'] [T2Space M₁'] [SecondCountableTopology M₁']
  [TopologicalSpace M₂'] [ChartedSpace E M₂'] [IsManifold 𝓘(𝕜, E) ω M₂'] [T2Space M₂']
  [SecondCountableTopology M₂'] {π₁ : M₁' → M₁} {π₂ : M₂' → M₂}

/-- **Functoriality under local isomorphisms**: an analytic isomorphism `g` between open subsets
with `g(Y₁ ∩ U₁) = Y₂ ∩ U₂` lifts to an analytic isomorphism `π₁⁻¹(U₁) → π₂⁻¹(U₂)` over `g`,
unique as a map on `π₁⁻¹(U₁)`; the centres have positive codimension. This is the pull-back of a
blow-up along an isomorphism onto an open subset [Kol07, Definition 30, 30.1], and the uniqueness
is that of [BM88, Definition 4.1]. -/
theorem IsBlowUp.exists_lift_partialDiffeomorph (hc : 0 < c) (hY₁ : IsClosedSubmanifold ψ Y₁ c)
    (hY₂ : IsClosedSubmanifold ψ Y₂ c) (h₁ : IsBlowUp ψ Y₁ c π₁) (h₂ : IsBlowUp ψ Y₂ c π₂)
    (g : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁ M₂ ω) (hg : g '' (Y₁ ∩ g.source) = Y₂ ∩ g.target) :
    ∃ g' : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁' M₂' ω, g'.source = π₁ ⁻¹' g.source ∧
      g'.target = π₂ ⁻¹' g.target ∧ (∀ p ∈ g'.source, π₂ (g' p) = g (π₁ p)) ∧
      ∀ g'' : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁' M₂' ω, g''.source = π₁ ⁻¹' g.source →
        (∀ p ∈ g''.source, π₂ (g'' p) = g (π₁ p)) → Set.EqOn g'' g' g'.source := by
  by_cases hne : Nonempty M₁'
  · have hne₂ : Nonempty M₂' := by
      obtain ⟨p⟩ := hne
      obtain ⟨q, -⟩ := h₂.surjective hY₂ ⟨0, hc⟩ (g (π₁ p))
      exact ⟨q⟩
    refine ⟨liftPartialDiffeomorph g hg hY₁ h₁ h₂ hY₂, rfl, rfl,
      fun _ hp => blowDown_liftPointG g hg hY₁ h₁ h₂ hp, fun g'' hs hcomm => ?_⟩
    have hN : IsOpen (π₁ ⁻¹' g.source) := g.open_source.preimage h₁.contMDiff.continuous
    exact h₁.eqOn_of_comp_eq_of_image_eq g hg hY₁ h₂ hN (fun _ hp => hp)
      (by rw [← hs]; exact g''.contMDiffOn_toFun.continuousOn)
      (contMDiffOn_liftPointG g hg hY₁ h₁ h₂).continuousOn
      (fun p hp => hcomm p (by rw [hs]; exact hp)) fun _ hp => blowDown_liftPointG g hg hY₁ h₁ h₂ hp
  · rw [not_nonempty_iff] at hne
    have hne₂ : IsEmpty M₂' := by
      refine ⟨fun q => ?_⟩
      obtain ⟨p, -⟩ := h₁.surjective hY₁ ⟨0, hc⟩ (g.invFun (π₂ q))
      exact hne.false p
    refine ⟨{ toFun := fun p => hne.elim p
              invFun := fun q => hne₂.elim q
              source := ∅
              target := ∅
              map_source' := fun p _ => hne.elim p
              map_target' := fun q _ => hne₂.elim q
              left_inv' := fun p _ => hne.elim p
              right_inv' := fun q _ => hne₂.elim q
              open_source := isOpen_empty
              open_target := isOpen_empty
              contMDiffOn_toFun := fun p _ => hne.elim p
              contMDiffOn_invFun := fun q _ => hne₂.elim q }, ?_, ?_, fun p _ => hne.elim p,
      fun _ _ _ p _ => hne.elim p⟩
    · exact (Set.eq_empty_of_isEmpty _).symm
    · exact (Set.eq_empty_of_isEmpty _).symm

end Statement

end Manifold
