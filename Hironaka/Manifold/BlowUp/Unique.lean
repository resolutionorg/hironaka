/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Defs
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.BlowUp.Lift
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Uniqueness of the blowing-up up to a unique diffeomorphism

Conditions (1) and (2) of [BM88, Definition 4.1] define the blowing-up `π : M' → M` uniquely, up
to an isomorphism of `M'` commuting with `π`. For two blowings-up `π₁ : M₁' → M`, `π₂ : M₂' → M`
of `M` with centre `Y`:

* **uniqueness of lifts**: two continuous maps `G, G' : N → M₂'` (`N ⊆ M₁'` open) with
  `π₂ ∘ G = π₂ ∘ G' = π₁` agree: off the exceptional divisor `π₂` is injective, and the
  complement of the divisor is dense (in a blow-up chart it is `{u_i ≠ 0}`);
* **the lift**: `g p` is the unique point over `π₁ p` off the divisor when `π₁ p ∉ Y`, and
  `Φ₂⁻¹(Φ₁ p)` for blow-up charts `Φ₁`, `Φ₂` of the same index over one adapted chart at `π₁ p`
  when `π₁ p ∈ Y` (their targets coincide: the full model chart domain); near every point `g` is
  given by such a chart formula (by uniqueness of lifts), so it is analytic; the lift in the other
  direction is a two-sided inverse (uniqueness of lifts again), and any diffeomorphism commuting
  with the blow-downs equals `g`.

The uniqueness statement is `IsBlowUp.exists_unique_diffeomorph`; the source states it without
proof. It is what allows the blowing-up to be transported along isomorphisms
(`Hironaka.Manifold.BlowUp.Functor`).
-/

@[expose] public section

open TopologicalSpace Topology Filter
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] {Y : Set M} {c : ℕ}

/-! ### Blow-up charts of one index over one adapted chart -/

section Charts

variable {M₁' M₂' : Type u} [TopologicalSpace M₁'] [ChartedSpace E M₁'] [TopologicalSpace M₂']
  [ChartedSpace E M₂'] {π₁ : M₁' → M} {π₂ : M₂' → M} {φ : OpenPartialHomeomorph M E}
  {σ : Fin c ↪ Fin n} {i : Fin c} {Φ₁ : OpenPartialHomeomorph M₁' E}
  {Φ₂ : OpenPartialHomeomorph M₂' E}

/-- Two blow-up charts of the same index over one adapted chart have the same target. -/
theorem IsBlowUpChart.target_eq (hΦ₁ : IsBlowUpChart ψ π₁ φ σ i Φ₁)
    (hΦ₂ : IsBlowUpChart ψ π₂ φ σ i Φ₂) : Φ₁.target = Φ₂.target := by
  ext v
  rw [hΦ₁.mem_target_iff, hΦ₂.mem_target_iff]

/-- `Φ₂⁻¹ ∘ Φ₁` lifts `π₁` to `π₂`. -/
theorem IsBlowUpChart.blowDown_symm_apply
    (hΦ₁ : IsBlowUpChart ψ π₁ φ σ i Φ₁) (hΦ₂ : IsBlowUpChart ψ π₂ φ σ i Φ₂) {p : M₁'}
    (hp : p ∈ Φ₁.source) : π₂ (Φ₂.symm (Φ₁ p)) = π₁ p := by
  have hw : Φ₁ p ∈ Φ₂.target := by rw [← hΦ₁.target_eq hΦ₂]; exact Φ₁.map_source hp
  have hq : Φ₂.symm (Φ₁ p) ∈ Φ₂.source := Φ₂.map_target hw
  have h1 := hΦ₂.comm _ hq
  rw [Φ₂.right_inv hw, ← hΦ₁.comm p hp] at h1
  exact φ.injOn (hΦ₂.source_subset hq) (hΦ₁.source_subset hp) (ψ.injective h1)

/-- The chart change `Φ₂⁻¹ ∘ Φ₁` between blow-up charts of the same index over the same adapted
chart, for two blowings-up, is analytic on `Φ₁.source` (both charts read the same coordinates). -/
theorem IsBlowUpChart.contMDiffOn_symm_comp (hΦ₁ : IsBlowUpChart ψ π₁ φ σ i Φ₁)
    (hΦ₂ : IsBlowUpChart ψ π₂ φ σ i Φ₂) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Φ₂.symm ∘ Φ₁) Φ₁.source :=
  (contMDiffOn_symm_of_mem_maximalAtlas hΦ₂.mem_maximalAtlas).comp
    (contMDiffOn_of_mem_maximalAtlas hΦ₁.mem_maximalAtlas) fun _ hp => by
      rw [← hΦ₁.target_eq hΦ₂]; exact Φ₁.map_source hp

end Charts

variable [ChartedSpace E M]

/-! ### Density of the complement of the divisor and uniqueness of lifts -/

section Lifts

variable {M₁' M₂' : Type u} [TopologicalSpace M₁'] [ChartedSpace E M₁'] [IsManifold 𝓘(𝕜, E) ω M₁']
  [T2Space M₁'] [SecondCountableTopology M₁'] [TopologicalSpace M₂'] [ChartedSpace E M₂']
  [IsManifold 𝓘(𝕜, E) ω M₂'] [T2Space M₂'] [SecondCountableTopology M₂'] {π₁ : M₁' → M}
  {π₂ : M₂' → M}

/-- The complement of the exceptional divisor is dense: in a blow-up chart it is `{u_i ≠ 0}`. -/
theorem IsBlowUp.dense_preimage_compl (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π₁) :
    Dense (π₁ ⁻¹' Yᶜ) := by
  intro p
  by_cases hp : π₁ p ∈ Y
  · obtain ⟨φ, σ, ha, hφ⟩ := hY.exists_adaptedChart (π₁ p) hp
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p ha
    rw [mem_closure_iff]
    intro O hO hpO
    have hopen : IsOpen (ψ '' (Φ '' (O ∩ Φ.source))) :=
      ψ.toHomeomorph.isOpenMap _
        (Φ.isOpen_image_of_subset_source (hO.inter Φ.open_source) Set.inter_subset_right)
    have hmem : ψ (Φ p) ∈ ψ '' (Φ '' (O ∩ Φ.source)) := ⟨_, ⟨p, ⟨hpO, hpΦ⟩, rfl⟩, rfl⟩
    have hcl := subset_closure_ne σ (i := i) hopen hmem
    obtain ⟨_, hw, ⟨_, ⟨q, ⟨hqO, hqΦ⟩, rfl⟩, rfl⟩, hne⟩ :=
      mem_closure_iff.mp hcl _ hopen hmem
    refine ⟨q, hqO, ?_⟩
    change π₁ q ∉ Y
    exact fun hqY => hne ((hΦ.mem_preimage_iff hφ hqΦ).mp hqY)
  · exact subset_closure hp

/-- Uniqueness of lifts: two continuous maps over `π₁` into the second blowing-up agree on an open
set. -/
theorem IsBlowUp.eqOn_of_comp_eq (hY : IsClosedSubmanifold ψ Y c) (h₁ : IsBlowUp ψ Y c π₁)
    (h₂ : IsBlowUp ψ Y c π₂) {N : Set M₁'} (hN : IsOpen N) {G G' : M₁' → M₂'}
    (hG : ContinuousOn G N) (hG' : ContinuousOn G' N) (hπ : ∀ p ∈ N, π₂ (G p) = π₁ p)
    (hπ' : ∀ p ∈ N, π₂ (G' p) = π₁ p) : Set.EqOn G G' N := by
  have hS : Set.EqOn G G' (N ∩ π₁ ⁻¹' Yᶜ) := by
    rintro p ⟨hp, hpY⟩
    have hpY' : π₁ p ∉ Y := hpY
    have e1 : G p ∈ π₂ ⁻¹' Yᶜ := by
      change π₂ (G p) ∉ Y
      rw [hπ p hp]
      exact hpY'
    have e2 : G' p ∈ π₂ ⁻¹' Yᶜ := by
      change π₂ (G' p) ∉ Y
      rw [hπ' p hp]
      exact hpY'
    exact h₂.bijOn_compl.injOn e1 e2 ((hπ p hp).trans (hπ' p hp).symm)
  refine hS.of_subset_closure hG hG' Set.inter_subset_left fun p hp => ?_
  rw [mem_closure_iff]
  intro O hO hpO
  obtain ⟨q, ⟨hqO, hqN⟩, hq⟩ :=
    mem_closure_iff.mp (h₁.dense_preimage_compl hY p) (O ∩ N) (hO.inter hN) ⟨hpO, hp⟩
  exact ⟨q, hqO, hqN, hq⟩

/-! ### The lift -/

variable (hY : IsClosedSubmanifold ψ Y c) (h₁ : IsBlowUp ψ Y c π₁) (h₂ : IsBlowUp ψ Y c π₂)

section ChartData

variable {a : M} (ha : a ∈ Y)

/-- An adapted chart at a point of the centre. -/
noncomputable def adChart : OpenPartialHomeomorph M E := (hY.exists_adaptedChart a ha).choose

/-- Its block embedding. -/
noncomputable def adEmb : Fin c ↪ Fin n := (hY.exists_adaptedChart a ha).choose_spec.choose

/-- The chosen adapted chart at a point of `Y` contains it and is adapted. -/
theorem adChart_spec :
    a ∈ (adChart hY ha).source ∧ IsAdaptedChart ψ Y (adChart hY ha) (adEmb hY ha) :=
  (hY.exists_adaptedChart a ha).choose_spec.choose_spec

variable (p : M₁') (hp : π₁ p ∈ Y)

/-- The index of a blow-up chart of `π₁` at `p` over the adapted chart. -/
noncomputable def bIdx : Fin c :=
  (h₁.cover _ _ (adChart_spec hY hp).2 p (adChart_spec hY hp).1).choose

/-- A blow-up chart of `π₁` at `p`. -/
noncomputable def bChart₁ : OpenPartialHomeomorph M₁' E :=
  (h₁.cover _ _ (adChart_spec hY hp).2 p (adChart_spec hY hp).1).choose_spec.choose

/-- The chosen blow-up chart of `π₁` at `p` is a blow-up chart containing `p`. -/
theorem bChart₁_spec :
    IsBlowUpChart ψ π₁ (adChart hY hp) (adEmb hY hp) (bIdx hY h₁ p hp) (bChart₁ hY h₁ p hp) ∧
      p ∈ (bChart₁ hY h₁ p hp).source :=
  (h₁.cover _ _ (adChart_spec hY hp).2 p (adChart_spec hY hp).1).choose_spec.choose_spec

/-- A blow-up chart of `π₂` of the same index over the same adapted chart. -/
noncomputable def bChart₂ : OpenPartialHomeomorph M₂' E :=
  (h₂.exists_chart _ _ (adChart_spec hY hp).2 (bIdx hY h₁ p hp)).choose

/-- The chosen blow-up chart of `π₂` over the same adapted chart and index is a blow-up chart. -/
theorem bChart₂_spec :
    IsBlowUpChart ψ π₂ (adChart hY hp) (adEmb hY hp) (bIdx hY h₁ p hp)
      (bChart₂ hY h₁ h₂ p hp) :=
  (h₂.exists_chart _ _ (adChart_spec hY hp).2 (bIdx hY h₁ p hp)).choose_spec

end ChartData

open scoped Classical in
/-- The lift of `π₁` to `π₂`: over the centre `Φ₂⁻¹ ∘ Φ₁` in blow-up charts of one index over one
adapted chart, off the centre the unique point of `M₂'` off the divisor over `π₁ p`. -/
noncomputable def liftPoint (p : M₁') : M₂' :=
  if hp : π₁ p ∈ Y then (bChart₂ hY h₁ h₂ p hp).symm (bChart₁ hY h₁ p hp p)
  else (h₂.bijOn_compl.surjOn (show π₁ p ∈ Yᶜ from hp)).choose

/-- Over the centre the lift is read through the chosen blow-up charts. -/
theorem liftPoint_of_mem {p : M₁'} (hp : π₁ p ∈ Y) :
    liftPoint hY h₁ h₂ p = (bChart₂ hY h₁ h₂ p hp).symm (bChart₁ hY h₁ p hp p) := by
  rw [liftPoint, dite_eq_left hp]

/-- Off the centre the lift is the unique preimage under `π₂` of `π₁ p`. -/
theorem liftPoint_of_notMem {p : M₁'} (hp : π₁ p ∉ Y) :
    liftPoint hY h₁ h₂ p = (h₂.bijOn_compl.surjOn (show π₁ p ∈ Yᶜ from hp)).choose := by
  rw [liftPoint, dite_eq_right hp]

/-- The lift commutes with the blow-downs: `π₂ ∘ liftPoint = π₁`. -/
theorem blowDown_liftPoint (p : M₁') : π₂ (liftPoint hY h₁ h₂ p) = π₁ p := by
  by_cases hp : π₁ p ∈ Y
  · rw [liftPoint_of_mem hY h₁ h₂ hp]
    exact (bChart₁_spec hY h₁ p hp).1.blowDown_symm_apply (bChart₂_spec hY h₁ h₂ p hp)
      (bChart₁_spec hY h₁ p hp).2
  · rw [liftPoint_of_notMem hY h₁ h₂ hp]
    exact (h₂.bijOn_compl.surjOn (show π₁ p ∈ Yᶜ from hp)).choose_spec.2

/-- Off the centre, `liftPoint` is the unique point off the divisor over `π₁ p`. -/
theorem liftPoint_eq_of_notMem {p : M₁'} (hp : π₁ p ∉ Y) {q : M₂'} (hq : π₂ q = π₁ p) :
    liftPoint hY h₁ h₂ p = q := by
  have hmem : liftPoint hY h₁ h₂ p ∈ π₂ ⁻¹' Yᶜ := by
    rw [liftPoint_of_notMem hY h₁ h₂ hp]
    exact (h₂.bijOn_compl.surjOn (show π₁ p ∈ Yᶜ from hp)).choose_spec.1
  have hq' : q ∈ π₂ ⁻¹' Yᶜ := by
    change π₂ q ∉ Y
    rw [hq]
    exact hp
  exact h₂.bijOn_compl.injOn hmem hq' ((blowDown_liftPoint hY h₁ h₂ p).trans hq.symm)

/-- Near a point over the centre, the lift is the chart formula `Φ₂⁻¹ ∘ Φ₁`. -/
theorem liftPoint_eqOn_of_mem {p : M₁'} (hp : π₁ p ∈ Y) :
    Set.EqOn (liftPoint hY h₁ h₂) ((bChart₂ hY h₁ h₂ p hp).symm ∘ bChart₁ hY h₁ p hp)
      (bChart₁ hY h₁ p hp).source := by
  intro q hq
  have hΦ₁ := (bChart₁_spec hY h₁ p hp).1
  have hΦ₂ := bChart₂_spec hY h₁ h₂ p hp
  have hφ := (adChart_spec hY hp).2
  by_cases hqY : π₁ q ∈ Y
  · -- both are continuous lifts near `q`
    have hΦ₁' := (bChart₁_spec hY h₁ q hqY).1
    have hΦ₂' := bChart₂_spec hY h₁ h₂ q hqY
    have hφ' := (adChart_spec hY hqY).2
    have hN : IsOpen ((bChart₁ hY h₁ p hp).source ∩ (bChart₁ hY h₁ q hqY).source) :=
      (bChart₁ hY h₁ p hp).open_source.inter (bChart₁ hY h₁ q hqY).open_source
    have heq := h₁.eqOn_of_comp_eq hY h₂ hN
      ((hΦ₁'.contMDiffOn_symm_comp hΦ₂').continuousOn.mono Set.inter_subset_right)
      ((hΦ₁.contMDiffOn_symm_comp hΦ₂).continuousOn.mono Set.inter_subset_left)
      (fun r hr => hΦ₁'.blowDown_symm_apply hΦ₂' hr.2)
      (fun r hr => hΦ₁.blowDown_symm_apply hΦ₂ hr.1) ⟨hq, (bChart₁_spec hY h₁ q hqY).2⟩
    rw [liftPoint_of_mem hY h₁ h₂ hqY]
    exact heq
  · exact liftPoint_eq_of_notMem hY h₁ h₂ hqY (hΦ₁.blowDown_symm_apply hΦ₂ hq)

/-- Near a point off the centre, the lift is `Ψ⁻¹ ∘ π₁` for a local inverse `Ψ` of `π₂`. -/
theorem exists_eqOn_of_notMem {p : M₁'} (hp : π₁ p ∉ Y) :
    ∃ N : Set M₁', IsOpen N ∧ p ∈ N ∧
      ∃ Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₂' M ω, N ⊆ π₁ ⁻¹' Ψ.target ∧
        Set.EqOn (liftPoint hY h₁ h₂) (Ψ.invFun ∘ π₁) N := by
  have hmem : liftPoint hY h₁ h₂ p ∈ π₂ ⁻¹' Yᶜ := by
    change π₂ (liftPoint hY h₁ h₂ p) ∉ Y
    rw [blowDown_liftPoint hY h₁ h₂ p]
    exact hp
  obtain ⟨Ψ, hqΨ, hΨ⟩ := (h₂.isLocalDiffeomorphOn_compl ⟨_, hmem⟩).exists_partialDiffeomorph
  have hqΨ' : liftPoint hY h₁ h₂ p ∈ Ψ.source := hqΨ
  refine ⟨π₁ ⁻¹' (Ψ.target ∩ Yᶜ), (Ψ.open_target.inter hY.isClosed.isOpen_compl).preimage
    h₁.contMDiff.continuous, ⟨?_, hp⟩, Ψ, fun _ hr => hr.1, fun r hr => ?_⟩
  · rw [← blowDown_liftPoint hY h₁ h₂ p, hΨ hqΨ']
    exact Ψ.map_source hqΨ'
  · have hr1 : π₁ r ∈ Ψ.target := hr.1
    have hr2 : π₁ r ∉ Y := hr.2
    have hmem' : Ψ.invFun (π₁ r) ∈ Ψ.source := Ψ.map_target hr1
    refine liftPoint_eq_of_notMem hY h₁ h₂ hr2 ?_
    change π₂ (Ψ.invFun (π₁ r)) = π₁ r
    rw [hΨ hmem']
    exact Ψ.right_inv hr1

/-- The lift is analytic. -/
theorem contMDiff_liftPoint : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω (liftPoint hY h₁ h₂) := by
  intro p
  by_cases hp : π₁ p ∈ Y
  · have hΦ₁ := (bChart₁_spec hY h₁ p hp).1
    have hΦ₂ := bChart₂_spec hY h₁ h₂ p hp
    exact ((hΦ₁.contMDiffOn_symm_comp hΦ₂).congr (liftPoint_eqOn_of_mem hY h₁ h₂ hp)).contMDiffAt
      ((bChart₁ hY h₁ p hp).open_source.mem_nhds (bChart₁_spec hY h₁ p hp).2)
  · obtain ⟨N, hN, hpN, Ψ, hNΨ, heq⟩ := exists_eqOn_of_notMem hY h₁ h₂ hp
    have hsm : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Ψ.invFun ∘ π₁) N :=
      Ψ.contMDiffOn_invFun.comp h₁.contMDiff.contMDiffOn hNΨ
    exact (hsm.congr heq).contMDiffAt (hN.mem_nhds hpN)

/-- The lift is a two-sided inverse of the lift in the other direction. -/
theorem liftPoint_liftPoint (p : M₁') : liftPoint hY h₂ h₁ (liftPoint hY h₁ h₂ p) = p := by
  have h := h₁.eqOn_of_comp_eq hY h₁ isOpen_univ
    ((contMDiff_liftPoint hY h₂ h₁).continuous.comp
      (contMDiff_liftPoint hY h₁ h₂).continuous).continuousOn continuous_id.continuousOn
    (fun q _ => by
      change π₁ (liftPoint hY h₂ h₁ (liftPoint hY h₁ h₂ q)) = π₁ q
      rw [blowDown_liftPoint hY h₂ h₁, blowDown_liftPoint hY h₁ h₂])
    (fun _ _ => rfl)
  exact h (Set.mem_univ p)

end Lifts

/-! ### Uniqueness up to a unique diffeomorphism -/

section Uniqueness

variable {M₁' M₂' : Type u} [TopologicalSpace M₁'] [ChartedSpace E M₁'] [IsManifold 𝓘(𝕜, E) ω M₁']
  [T2Space M₁'] [SecondCountableTopology M₁'] [TopologicalSpace M₂'] [ChartedSpace E M₂']
  [IsManifold 𝓘(𝕜, E) ω M₂'] [T2Space M₂'] [SecondCountableTopology M₂'] {π₁ : M₁' → M}
  {π₂ : M₂' → M}

/-- The diffeomorphism between two blowings-up of `M` with centre `Y`. -/
noncomputable def IsBlowUp.diffeomorph (hY : IsClosedSubmanifold ψ Y c) (h₁ : IsBlowUp ψ Y c π₁)
    (h₂ : IsBlowUp ψ Y c π₂) : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁' M₂' ω where
  toFun := liftPoint hY h₁ h₂
  invFun := liftPoint hY h₂ h₁
  left_inv := liftPoint_liftPoint hY h₁ h₂
  right_inv := liftPoint_liftPoint hY h₂ h₁
  contMDiff_toFun := contMDiff_liftPoint hY h₁ h₂
  contMDiff_invFun := contMDiff_liftPoint hY h₂ h₁

/-- Two blowings-up of `M` with centre `Y` are isomorphic over `M` by a unique diffeomorphism
[BM88, Definition 4.1]. -/
theorem IsBlowUp.exists_unique_diffeomorph (hY : IsClosedSubmanifold ψ Y c)
    (h₁ : IsBlowUp ψ Y c π₁) (h₂ : IsBlowUp ψ Y c π₂) :
    ∃! g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁' M₂' ω, ∀ p, π₂ (g p) = π₁ p := by
  refine ⟨h₁.diffeomorph hY h₂, fun p => blowDown_liftPoint hY h₁ h₂ p, fun g hg => ?_⟩
  refine Diffeomorph.ext fun p => ?_
  exact h₁.eqOn_of_comp_eq hY h₂ isOpen_univ g.continuous.continuousOn
    (contMDiff_liftPoint hY h₁ h₂).continuous.continuousOn (fun q _ => hg q)
    (fun q _ => blowDown_liftPoint hY h₁ h₂ q) (Set.mem_univ p)

end Uniqueness

end Manifold
