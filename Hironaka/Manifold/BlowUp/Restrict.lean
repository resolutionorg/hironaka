/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Defs
import Hironaka.Manifold.BlowUp.Transition
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# The blowing-up restricted to an open subset

The blowing-up commutes with restriction to open sets: for `U ⊆ M` open, `π : π⁻¹(U) → U` is the
blowing-up of `U` with centre `Y ∩ U`. This is implicit in the uniqueness clause of
[BM88, Definition 4.1], and it is the case of an open immersion of the pull-back of a blow-up
along a smooth morphism [Kol07, Definition 30, 30.1]. Charts of an open subset `U` (Mathlib's
`Opens` charted space: the restrictions `subtypeRestr` of the charts of `M`) and charts of `M` are
exchanged along the inclusion: a chart of the maximal atlas of `M` restricts to one of `U`
(`subtypeRestr_mem_maximalAtlas_of_mem_maximalAtlas`), and a chart of the maximal atlas of `U`
extends along the inclusion to one of `M` (`Opens.extendChart`); adapted charts and blow-up
charts are exchanged accordingly, and every clause of `IsBlowUp` descends
(`IsBlowUp.restrictOpens'`). More generally an analytic map restricted to open submanifolds stays
analytic (`contMDiff_codRestrict_opens`).

The restriction of a finite succession of blowings-up to an open subset
(`FiniteSuccession.restrict`) is built from `IsBlowUp.restrictOpens'`.
-/

@[expose] public section

open TopologicalSpace Topology Filter
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

open TopologicalSpace

/-! ### Charts of an open subset and of the ambient space -/

section OpensCharts

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]

/-- The inverse of the inclusion chart of an open subset, at a point of the subset. -/
theorem _root_.TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_symm_apply {s : Opens M}
    (hs : Nonempty s) {x : M}
    (hx : x ∈ s) : (s.openPartialHomeomorphSubtypeCoe hs).symm x = ⟨x, hx⟩ :=
  IsOpenEmbedding.toOpenPartialHomeomorph_left_inv (Subtype.val : s → M)
    s.2.isOpenEmbedding_subtypeVal (x := ⟨x, hx⟩)

/-- A chart of an open subset `s`, extended along the inclusion to a chart of `M`:
`coe⁻¹ ≫ₕ φ`. -/
noncomputable def _root_.TopologicalSpace.Opens.extendChart {s : Opens M} (hs : Nonempty s)
    (φ : OpenPartialHomeomorph s H) : OpenPartialHomeomorph M H :=
  (s.openPartialHomeomorphSubtypeCoe hs).symm ≫ₕ φ

variable {s : Opens M} (hs : Nonempty s) (φ : OpenPartialHomeomorph s H)

/-- Membership in the source of the extended chart, unfolded. -/
theorem _root_.TopologicalSpace.Opens.mem_extendChart_source_iff {x : M} :
    x ∈ (Opens.extendChart hs φ).source ↔ ∃ hx : x ∈ s, (⟨x, hx⟩ : s) ∈ φ.source := by
  rw [Opens.extendChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Opens.openPartialHomeomorphSubtypeCoe_target]
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    rw [Set.mem_preimage, Opens.openPartialHomeomorphSubtypeCoe_symm_apply hs hx] at hx'
    exact hx'
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    rw [Set.mem_preimage, Opens.openPartialHomeomorphSubtypeCoe_symm_apply hs hx]
    exact hx'

/-- The source of the extended chart lies in the open set. -/
theorem _root_.TopologicalSpace.Opens.extendChart_source_subset :
    (Opens.extendChart hs φ).source ⊆ s := fun _ hx =>
  ((Opens.mem_extendChart_source_iff hs φ).mp hx).1

/-- The extended chart agrees with the chart of the open subset. -/
theorem _root_.TopologicalSpace.Opens.extendChart_apply {x : M} (hx : x ∈ s) :
    Opens.extendChart hs φ x = φ ⟨x, hx⟩ := by
  rw [Opens.extendChart, OpenPartialHomeomorph.trans_apply,
    Opens.openPartialHomeomorphSubtypeCoe_symm_apply hs hx]

/-- The extended chart has the target of the chart it extends. -/
theorem _root_.TopologicalSpace.Opens.extendChart_target : (Opens.extendChart hs φ).target =
    φ.target := by
  rw [Opens.extendChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    Opens.openPartialHomeomorphSubtypeCoe_source, Set.preimage_univ, Set.inter_univ]

variable [ChartedSpace H M] {G : StructureGroupoid H} [HasGroupoid M G] [ClosedUnderRestriction G]

/-- Restricting a chart of the maximal atlas of `M` to an open subset yields a chart of the maximal
atlas of the subset (Mathlib's `StructureGroupoid.subtypeRestr_mem_maximalAtlas` for the charts of
the atlas). -/
theorem subtypeRestr_mem_maximalAtlas_of_mem_maximalAtlas {e : OpenPartialHomeomorph M H}
    (he : e ∈ G.maximalAtlas M) : e.subtypeRestr hs ∈ G.maximalAtlas s := by
  intro e' he'
  obtain ⟨x, rfl⟩ := Opens.chart_eq hs he'
  exact ⟨G.mem_of_eqOnSource (closedUnderRestriction'
      (G.compatible_of_mem_maximalAtlas he (G.chart_mem_maximalAtlas (x : M)))
      (e.isOpen_inter_preimage_symm s.2)) (e.subtypeRestr_symm_trans_subtypeRestr hs _),
    G.mem_of_eqOnSource (closedUnderRestriction'
      (G.compatible_of_mem_maximalAtlas (G.chart_mem_maximalAtlas (x : M)) he)
      ((chartAt H (x : M)).isOpen_inter_preimage_symm s.2))
      ((chartAt H (x : M)).subtypeRestr_symm_trans_subtypeRestr hs _)⟩

/-- A chart of the maximal atlas of an open subset extends to a chart of the maximal atlas of `M`.
-/
theorem _root_.TopologicalSpace.Opens.extendChart_mem_maximalAtlas (hφ : φ ∈ G.maximalAtlas s) :
    Opens.extendChart hs φ ∈ G.maximalAtlas M := by
  intro e he
  have h1 := G.compatible_of_mem_maximalAtlas hφ (G.subtypeRestr_mem_maximalAtlas he hs)
  have h2 := G.compatible_of_mem_maximalAtlas (G.subtypeRestr_mem_maximalAtlas he hs) hφ
  refine ⟨?_, ?_⟩
  · rw [Opens.extendChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.subtypeRestr_def]
    exact h1
  · rw [Opens.extendChart, ← OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      ← OpenPartialHomeomorph.subtypeRestr_def]
    exact h2

end OpensCharts

/-! ### Analytic maps restricted to open submanifolds -/

section CodRestrict

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace E' N]

/-- An analytic map restricted to open submanifolds is analytic (`contMDiff_restrict`,
for any analytic map). -/
theorem contMDiff_codRestrict_opens {f : N → M} (hf : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω f)
    {V : Opens M} {W : Opens N} {f' : W → V} (hf' : ∀ p, (f' p : M) = f p) :
    ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω f' := by
  intro p
  have h1 : Subtype.val ∘ f' = f ∘ Subtype.val := funext hf'
  have : ContMDiffAt 𝓘(𝕜, E') 𝓘(𝕜, E) ω (Subtype.val ∘ f') p := by
    rw [h1]
    exact (hf.comp contMDiff_subtype_val) p
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f' Set.univ p).mp this

end CodRestrict

/-! ### Restriction of a blowing-up over an open subset -/

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] {M' : Type u} [TopologicalSpace M']
  {π : M' → M}

/-- A point whose blow-down lies in `U` lies in `U' = π⁻¹(U)`. -/
theorem mem_opens_of_blowDown_mem {U : Opens M} {U' : Opens M'} (hU' : (U' : Set M') = π ⁻¹' U)
    {q : M'} (hq : π q ∈ U) : q ∈ U' := by
  rw [← SetLike.mem_coe, hU']
  exact hq

section ChartRestr

variable [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] {c : ℕ} {U : Opens M} {U' : Opens M'}
  (hU' : (U' : Set M') = π ⁻¹' U) {π' : U' → U} (hπ' : ∀ p, (π' p : M) = π p)

include hU' hπ'

/-- The restriction of a blow-up chart to `U'` is a blow-up chart of the restricted blowing-up over
the restricted adapted chart. -/
theorem IsBlowUpChart.subtypeRestr (hU : Nonempty U) (hU'ne : Nonempty U')
    {φ : OpenPartialHomeomorph U E} {σ : Fin c ↪ Fin n} {i : Fin c}
    {Φ : OpenPartialHomeomorph M' E} (hΦ : IsBlowUpChart ψ π (Opens.extendChart hU φ) σ i Φ) :
    IsBlowUpChart ψ π' φ σ i (Φ.subtypeRestr hU'ne) where
  mem_maximalAtlas :=
    subtypeRestr_mem_maximalAtlas_of_mem_maximalAtlas hU'ne hΦ.mem_maximalAtlas
  source_subset := by
    intro q hq
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hq
    have hs := hΦ.source_subset hq
    obtain ⟨hxU, hx'⟩ := (Opens.mem_extendChart_source_iff hU φ).mp hs
    have : π' q = ⟨π q, hxU⟩ := Subtype.ext (hπ' q)
    change π' q ∈ φ.source
    rw [this]
    exact hx'
  mem_target_iff v := by
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
      Opens.openPartialHomeomorphSubtypeCoe_target, ← Opens.extendChart_target hU φ,
      ← hΦ.mem_target_iff]
    constructor
    · exact fun hv => hv.1
    · intro hv
      refine ⟨hv, ?_⟩
      have hq := Φ.map_target hv
      exact mem_opens_of_blowDown_mem hU'
        (Opens.extendChart_source_subset hU φ (hΦ.source_subset hq))
  comm q hq := by
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hq
    have hs := hΦ.source_subset hq
    have hxU : π q ∈ U := Opens.extendChart_source_subset hU φ hs
    have h1 := hΦ.comm q hq
    rw [Opens.extendChart_apply hU φ hxU] at h1
    have : π' q = ⟨π q, hxU⟩ := Subtype.ext (hπ' q)
    rw [this, OpenPartialHomeomorph.subtypeRestr_coe]
    exact h1

end ChartRestr

variable [ChartedSpace E M] {Y : Set M} {c : ℕ}

/-- An adapted chart of `Y ∩ U` on the open subset `U` extends to an adapted chart of `Y`. -/
theorem isAdaptedChart_extendChart [IsManifold 𝓘(𝕜, E) ω M] {U : Opens M} (hU : Nonempty U)
    {φ : OpenPartialHomeomorph U E} {σ : Fin c ↪ Fin n}
    (hφ : IsAdaptedChart ψ (Subtype.val ⁻¹' Y) φ σ) :
    IsAdaptedChart ψ Y (Opens.extendChart hU φ) σ := by
  refine ⟨Opens.extendChart_mem_maximalAtlas hU φ hφ.1, fun x hx => ?_⟩
  obtain ⟨hxU, hx'⟩ := (Opens.mem_extendChart_source_iff hU φ).mp hx
  rw [Opens.extendChart_apply hU φ hxU]
  exact hφ.2 ⟨x, hxU⟩ hx'

variable [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M']

/-- A blowing-up with a nonempty centre is surjective: a point of `Y` is the blow-down of the
centre point of a blow-up chart. -/
theorem IsBlowUp.surjective (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (i₀ : Fin c) :
    Function.Surjective π := by
  intro a
  by_cases ha : a ∈ Y
  · obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
    obtain ⟨Φ, hΦ⟩ := h.exists_chart φ σ hφ i₀
    have hxc : ψ (φ a) ∈ blowUpCenter σ := (hφ.2 a haφ).mp ha
    have hmem : ψ.symm (ψ (φ a)) ∈ Φ.target := by
      rw [hΦ.mem_target_iff, ψ.apply_symm_apply, BlowUpGlue.blowUpChartMap_of_mem_center hxc]
      exact ⟨_, φ.map_source haφ, rfl⟩
    refine ⟨Φ.symm (ψ.symm (ψ (φ a))), ?_⟩
    have hp := Φ.map_target hmem
    have hc := hΦ.comm _ hp
    rw [Φ.right_inv hmem, ψ.apply_symm_apply, BlowUpGlue.blowUpChartMap_of_mem_center hxc] at hc
    exact φ.injOn (hΦ.source_subset hp) haφ (ψ.injective hc)
  · obtain ⟨p, -, hp⟩ := h.bijOn_compl.surjOn ha
    exact ⟨p, hp⟩

section Restrict

variable {U : Opens M} {U' : Opens M'} (hU' : (U' : Set M') = π ⁻¹' U) {π' : U' → U}
  (hπ' : ∀ p, (π' p : M) = π p)

include hπ'

/-- The restricted blow-down is analytic. -/
theorem contMDiff_restrict (h : IsBlowUp ψ Y c π) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω π' := by
  intro p
  have h1 : Subtype.val ∘ π' = π ∘ Subtype.val := funext hπ'
  have : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Subtype.val ∘ π') p := by
    rw [h1]
    exact (h.contMDiff.comp contMDiff_subtype_val) p
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff π' Set.univ p).mp this

/-- The restricted blow-down is continuous. -/
theorem continuous_restrict (h : IsBlowUp ψ Y c π) : Continuous π' := by
  rw [continuous_induced_rng]
  have h1 : Subtype.val ∘ π' = π ∘ Subtype.val := funext hπ'
  rw [h1]
  exact h.contMDiff.continuous.comp continuous_subtype_val

include hU'

/-- The restricted blow-down is a bijection off the restricted centre (condition (1) of
[BM88, Definition 4.1] for `π⁻¹(U) → U`). -/
theorem bijOn_restrict (h : IsBlowUp ψ Y c π) :
    Set.BijOn π' (π' ⁻¹' (Subtype.val ⁻¹' Y)ᶜ) (Subtype.val ⁻¹' Y)ᶜ := by
  refine ⟨fun _ hq => hq, fun q₁ h₁ q₂ h₂ heq => ?_, fun a ha => ?_⟩
  · have e₁ : π q₁.1 ∈ Yᶜ := by
      change (π' q₁ : M) ∉ Y at h₁
      rwa [hπ' q₁] at h₁
    have e₂ : π q₂.1 ∈ Yᶜ := by
      change (π' q₂ : M) ∉ Y at h₂
      rwa [hπ' q₂] at h₂
    have : π q₁.1 = π q₂.1 := by rw [← hπ' q₁, ← hπ' q₂, heq]
    exact Subtype.ext (h.bijOn_compl.injOn e₁ e₂ this)
  · have ha' : (a : M) ∉ Y := ha
    obtain ⟨q, hq, hqa⟩ := h.bijOn_compl.surjOn ha'
    have hqU : q ∈ U' := mem_opens_of_blowDown_mem hU' (by rw [hqa]; exact a.2)
    refine ⟨⟨q, hqU⟩, ?_, Subtype.ext (by rw [hπ']; exact hqa)⟩
    change (π' ⟨q, hqU⟩ : M) ∉ Y
    rw [hπ']
    exact hq

/-- The restricted blow-down is proper: a compact subset of `U` is compact in `M`, its preimage
under `π` is compact and lies in `π⁻¹(U)`. -/
theorem isProperMap_restrict [T2Space M] (h : IsBlowUp ψ Y c π) : IsProperMap π' := by
  have : FiniteDimensional 𝕜 E := ψ.symm.toLinearEquiv.finiteDimensional
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_restrict hπ' h, fun K hK => ?_⟩
  have hK' : IsCompact (π ⁻¹' (Subtype.val '' K)) :=
    h.isProperMap.isCompact_preimage (hK.image continuous_subtype_val)
  have hsub : π ⁻¹' (Subtype.val '' K) ⊆ Set.range (Subtype.val : U' → M') := by
    rintro q ⟨a, -, ha⟩
    rw [Subtype.range_val]
    exact mem_opens_of_blowDown_mem hU' (by rw [← ha]; exact a.2)
  have heq : Subtype.val ⁻¹' (π ⁻¹' (Subtype.val '' K)) = π' ⁻¹' K := by
    ext p
    constructor
    · rintro ⟨a, ha, hEq⟩
      have : a = π' p := Subtype.ext (hEq.trans (hπ' p).symm)
      change π' p ∈ K
      rw [← this]
      exact ha
    · intro hp
      exact ⟨π' p, hp, hπ' p⟩
  rw [← heq]
  exact (U'.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage_iff hsub).mpr hK'

/-- The local diffeomorphism of `π` at a point off the divisor, restricted over `U`. -/
theorem isLocalDiffeomorphOn_restrict (h : IsBlowUp ψ Y c π) :
    IsLocalDiffeomorphOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω π' (π' ⁻¹' (Subtype.val ⁻¹' Y)ᶜ) := by
  rintro ⟨p, hp⟩
  have hp' : π p.1 ∉ Y := by
    change (π' p : M) ∉ Y at hp
    rwa [hπ' p] at hp
  obtain ⟨Φ, hpΦ, hΦ⟩ := (h.isLocalDiffeomorphOn_compl ⟨p.1, hp'⟩).exists_partialDiffeomorph
  have hpΦ' : (p : M') ∈ Φ.source := hpΦ
  have hinv : ∀ a : U, (a : M) ∈ Φ.target → Φ.invFun a ∈ U' := fun a ha => by
    have hmem : Φ.invFun a ∈ Φ.source := Φ.map_target ha
    refine mem_opens_of_blowDown_mem hU' ?_
    rw [hΦ hmem]
    change Φ.toPartialEquiv (Φ.toPartialEquiv.symm a) ∈ U
    rw [Φ.right_inv ha]
    exact a.2
  classical
  refine PartialDiffeomorph.isLocalDiffeomorphAt _ _ _
          { toFun := π'
            invFun := fun a => if ha : (a : M) ∈ Φ.target then ⟨Φ.invFun a, hinv a ha⟩ else p
            source := Subtype.val ⁻¹' Φ.source
            target := Subtype.val ⁻¹' Φ.target
            map_source' := fun q hq => ?_
            map_target' := fun a ha => ?_
            left_inv' := fun q hq => ?_
            right_inv' := fun a ha => ?_
            open_source := Φ.open_source.preimage continuous_subtype_val
            open_target := Φ.open_target.preimage continuous_subtype_val
            contMDiffOn_toFun := (contMDiff_restrict hπ' h).contMDiffOn
            contMDiffOn_invFun := ?_ } hpΦ'
  · change (π' q : M) ∈ Φ.target
    rw [hπ' q, hΦ hq]
    exact Φ.map_source hq
  · have ha' : (a : M) ∈ Φ.target := ha
    change (if ha : (a : M) ∈ Φ.target then _ else _) ∈ Subtype.val ⁻¹' Φ.source
    rw [dite_eq_left ha']
    exact Φ.map_target ha'
  · have hq' : (π' q : M) ∈ Φ.target := by rw [hπ' q, hΦ hq]; exact Φ.map_source hq
    change (if ha : (π' q : M) ∈ Φ.target then _ else _) = q
    rw [dite_eq_left hq']
    apply Subtype.ext
    change Φ.invFun (π' q) = q
    rw [hπ' q, hΦ hq]
    exact Φ.left_inv hq
  · have ha' : (a : M) ∈ Φ.target := ha
    change π' (if ha : (a : M) ∈ Φ.target then _ else _) = a
    rw [dite_eq_left ha']
    apply Subtype.ext
    rw [hπ']
    change π (Φ.invFun a) = a
    have hmem : Φ.invFun a ∈ Φ.source := Φ.map_target ha'
    rw [hΦ hmem]
    exact Φ.right_inv ha'
  · intro a ha
    have ha' : (a : M) ∈ Φ.target := ha
    have hsm : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Φ.invFun ∘ Subtype.val)
        (Subtype.val ⁻¹' Φ.target) a :=
      (Φ.contMDiffOn_invFun.comp contMDiff_subtype_val.contMDiffOn fun _ hb => hb) a ha
    refine (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).mp (hsm.congr ?_ ?_)
    · intro b hb
      have hb' : (b : M) ∈ Φ.target := hb
      change Subtype.val (if hb' : (b : M) ∈ Φ.target then _ else _) = Φ.invFun b
      rw [dite_eq_left hb']
    · change Subtype.val (if ha' : (a : M) ∈ Φ.target then _ else _) = Φ.invFun a
      rw [dite_eq_left ha']

/-- The blowing-up restricted over an open subset `U` is a blowing-up of `U` with centre `Y ∩ U`
(the pull-back along the open immersion `U → M`, [Kol07, Definition 30, 30.1]). -/
theorem IsBlowUp.restrictOpens' [IsManifold 𝓘(𝕜, E) ω M] [T2Space M]
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) :
    IsBlowUp ψ (Subtype.val ⁻¹' Y) c π' where
  contMDiff := contMDiff_restrict hπ' h
  isProperMap := isProperMap_restrict hU' hπ' h
  isLocalDiffeomorphOn_compl := isLocalDiffeomorphOn_restrict hU' hπ' h
  bijOn_compl := bijOn_restrict hU' hπ' h
  exists_chart := by
    intro φ σ hφ i
    have hU : Nonempty U := ⟨φ.symm 0⟩
    have hU'ne : Nonempty U' := by
      obtain ⟨u⟩ := hU
      obtain ⟨q, hq⟩ := h.surjective hY i u.1
      exact ⟨⟨q, mem_opens_of_blowDown_mem hU' (by rw [hq]; exact u.2)⟩⟩
    obtain ⟨Φ, hΦ⟩ := h.exists_chart _ σ (isAdaptedChart_extendChart hU hφ) i
    exact ⟨Φ.subtypeRestr hU'ne, hΦ.subtypeRestr hU' hπ' hU hU'ne⟩
  cover := by
    intro φ σ hφ q hq
    have hU : Nonempty U := ⟨π' q⟩
    have hU'ne : Nonempty U' := ⟨q⟩
    have hxU : π q ∈ U := by
      rw [← hπ' q]
      exact (π' q).2
    have hs : π q ∈ (Opens.extendChart hU φ).source := by
      rw [Opens.mem_extendChart_source_iff]
      refine ⟨hxU, ?_⟩
      have : (⟨π q, hxU⟩ : U) = π' q := Subtype.ext (hπ' q).symm
      rw [this]
      exact hq
    obtain ⟨i, Φ, hΦ, hqΦ⟩ := h.cover _ σ (isAdaptedChart_extendChart hU hφ) q.1 hs
    refine ⟨i, Φ.subtypeRestr hU'ne, hΦ.subtypeRestr hU' hπ' hU hU'ne, ?_⟩
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hqΦ

end Restrict

end Manifold
