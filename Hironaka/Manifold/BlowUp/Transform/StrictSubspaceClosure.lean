/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.AnalyticSpace.VanishingIdeal
public import Hironaka.Manifold.BlowUp.Transform.Defs
public import Mathlib.Analysis.Complex.Basic
import Hironaka.AnalyticSpace.Nullstellensatz
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.StrictSubspace
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceBasic
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The strict transform off the centre is an isomorphic copy; its points over `ℂ`

* Off the exceptional divisor the blowing-down `π` is a local analytic isomorphism (condition (1)
  of [BM88, Definition 4.1]), so its stalk maps are bijective
  (`IsBlowUp.germMap_bijective_of_notMem`: `germMap π` agrees with the stalk map of the partial
  diffeomorphism supplied by `isLocalDiffeomorphOn_compl`, bijective by
  `germMapOn_partialDiffeomorph_bijective`); hence the total transform of a subspace with radical
  stalks has radical stalks off the divisor (`isRadical_stalkIdeal_totalTransform_of_notMem`, via
  `Ideal.map_radical_of_surjective`).
* Over `ℂ`, **`|X'| = closure(π⁻¹(|X| ∖ Y))`** ([BM97, Remark 3.15], with Rückert's
  Nullstellensatz). The inclusion `⊇` is general
  (`closure_subset_cosupport_strictTransformSubspace_of_hasLocalGenerators`). For `⊆`: a point
  `a'` of `|X'|` outside the closure has a neighbourhood `o` meeting `π⁻¹(|X| ∖ Y)` in nothing, so
  on `o` the set `|X'|` lies in `|F|` (off `F`, `|X'| = π⁻¹(|X|)`); every germ `f ∈ I_{F,a'}`
  therefore vanishes on `|X'|` near `a'`, i.e. `f ∈ √(I_{X',a'})` by Rückert
  (`vanishingStalkIdeal_cosupport_eq_radical` at the analytic space of `M'`); the stalk being
  Noetherian, `I_{F,a'}^k ⊆ I_{X',a'} = ⋃_j (π^*I : I_F^j)` for some `k`, hence
  `I_{F,a'}^{k+N} ⊆ π^*I_{a'}` for some `N`, so `1 ∈ (π^*I : I_F^{k+N}) ⊆ I_{X',a'}`,
  contradicting `a' ∈ |X'|`. The finite type of the saturation is the explicit hypothesis `hex`.

Rückert's Nullstellensatz for stalks and the Noetherianness of the stalks are proved in
`Hironaka.AnalyticSpace.Nullstellensatz` and `Hironaka.Manifold.Germ.StalkNoetherian`.
-/

public section

open TopologicalSpace Opposite CategoryTheory Set Filter Topology CompleteLattice
open scoped Manifold ContDiff

universe u

namespace Manifold

section OffCentre

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- At a point off the exceptional divisor the stalk map of the
blowing-down is bijective — `π` is a local analytic isomorphism there. -/
theorem IsBlowUp.germMap_bijective_of_notMem (h : IsBlowUp ψ Y c π) {a' : M'} (ha' : π a' ∉ Y) :
    Function.Bijective (germMap π h.contMDiff a') := by
  obtain ⟨Φ, hΦa, hΦeq⟩ := (h.isLocalDiffeomorphOn_compl ⟨a', ha'⟩).exists_partialDiffeomorph
  have hbij : ∀ (b : M) (hb : Φ a' = b), Function.Bijective
      (germMapOn (Φ : M' → M) (V := ⟨Φ.source, Φ.open_source⟩) Φ.contMDiffOn_toFun hΦa hb) := by
    rintro b rfl
    exact germMapOn_partialDiffeomorph_bijective Φ hΦa
  have heq : germMap π h.contMDiff a' = germMapOn (Φ : M' → M) (V := ⟨Φ.source, Φ.open_source⟩)
      Φ.contMDiffOn_toFun hΦa (hΦeq hΦa).symm := by
    refine RingHom.ext fun s => ?_
    apply stalkToGerm_injective 𝓘(𝕜, E) ω M' a'
    rw [stalkToGerm_germMap, stalkToGerm_germMapOn]
    induction stalkToGerm 𝓘(𝕜, E) ω M (π a') s using Germ.inductionOn with
    | h f =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_eq]
      filter_upwards [Φ.open_source.mem_nhds hΦa] with x hx
      simp only [Function.comp_apply, hΦeq hx]
  rw [heq]
  exact hbij _ _

/-- Off the exceptional divisor the total transform of a subspace with
radical stalks has radical stalks (the stalk map is a ring isomorphism there). -/
theorem isRadical_stalkIdeal_totalTransform_of_notMem (h : IsBlowUp ψ Y c π)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) (hI : ∀ x, (I.stalkIdeal x).IsRadical) {a' : M'}
    (ha' : π a' ∉ Y) : ((I.pullback π h.contMDiff).stalkIdeal a').IsRadical := by
  rw [IdealSheaf.stalkIdeal_pullback π h.contMDiff]
  have hb := h.germMap_bijective_of_notMem ha'
  refine Ideal.radical_eq_iff.mp ?_
  rw [← Ideal.map_radical_of_surjective hb.2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hb.1]; exact bot_le),
    Ideal.radical_eq_iff.mpr (hI (π a'))]

end OffCentre

section Rueckert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (ψ : E ≃L[ℂ] (Fin n → ℂ))
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℂ, E) ω M'] [T2Space M']
  [SecondCountableTopology M']

include ψ

/-- Rückert's Nullstellensatz at the analytic space `Sp(M')` of a complex
manifold: the radical of a stalk ideal is the vanishing ideal of the cosupport. -/
theorem radical_stalkIdeal_eq_vanishingStalkIdeal (J : IdealSheaf (structureSheaf ℂ E M'))
    (a' : M') :
    (J.stalkIdeal a').radical = AnalyticSpace.vanishingStalkIdeal
      (AnalyticSpace.toSpace ψ
        ({ carrier := M' } : AnalyticManifold.{u} ℂ E)).toLocallyRingedSpace
      J.support a' :=
  (AnalyticSpace.vanishingStalkIdeal_cosupport_eq_radical
    (AnalyticSpace.toSpace ψ
        ({ carrier := M' } : AnalyticManifold.{u} ℂ E))
    J a').symm

/-- A germ of an ideal sheaf `F` at `a'` whose cosupport contains `|J|` near `a'` lies in the
radical of `J_{a'}` (Rückert): it vanishes at every point of `|J|` near `a'`. -/
theorem mem_radical_stalkIdeal_of_cosupport_subset (J F : IdealSheaf (structureSheaf ℂ E M'))
    {a' : M'} {o : Opens M'} (ha'o : a' ∈ o) (ho : ∀ y' ∈ o, y' ∈ J.support → y' ∈ F.support)
    {f : (structureSheaf ℂ E M').presheaf.stalk a'} (hf : f ∈ F.stalkIdeal a') :
    f ∈ (J.stalkIdeal a').radical := by
  rw [radical_stalkIdeal_eq_vanishingStalkIdeal ψ J a']
  obtain ⟨V₀, ha'V₀, g, hg, rfl⟩ := (IdealSheaf.mem_stalkIdeal_iff F).mp hf
  refine ⟨V₀ ⊓ o, ⟨ha'V₀, ha'o⟩,
    (structureSheaf ℂ E M').presheaf.map (homOfLE (inf_le_left : V₀ ⊓ o ≤ V₀)).op g, ?_, ?_⟩
  · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  · intro y' hy' hyJ
    have hyF : y' ∈ F.support := ho y' hy'.2 hyJ
    have hmem : (structureSheaf ℂ E M').presheaf.germ (V₀ ⊓ o) y' hy'
        ((structureSheaf ℂ E M').presheaf.map (homOfLE (inf_le_left : V₀ ⊓ o ≤ V₀)).op g) ∈
        F.stalkIdeal y' :=
      F.germ_mem_stalkIdeal hy' (F.res_mem _ g hg)
    let _ : IsLocalRing ((structureSheaf ℂ E M').presheaf.stalk y') :=
      (AnalyticSpace.toSpace ψ ({ carrier := M' } :
        AnalyticManifold.{u} ℂ E)).toLocallyRingedSpace.isLocalRing y'
    exact IsLocalRing.le_maximalIdeal ((IdealSheaf.mem_support F).mp hyF) hmem

end Rueckert

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {ψ : E ≃L[ℂ] (Fin n → ℂ)}
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M} {c : ℕ} {M' : Type u}
  [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℂ, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M}
  (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (I : IdealSheaf (structureSheaf ℂ E M))

/-- Over `ℂ` ([BM97, Remark 3.15], with Rückert's Nullstellensatz), given the
finite type of the saturation: **the strict transform is the closure of the transform off the
centre**, `|X'| = closure(π⁻¹(|X| ∖ Y))`. -/
theorem cosupport_strictTransformSubspace_eq_closure_of_hasLocalGenerators
    (hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf ℂ E M') (saturationStalk hY h I)) :
    (strictTransformSubspace hY h I).support = closure (π ⁻¹' (I.support \ Y)) := by
  have : FiniteDimensional ℂ E := ψ.symm.toLinearEquiv.finiteDimensional
  refine le_antisymm ?_
    (closure_subset_cosupport_strictTransformSubspace_of_hasLocalGenerators hY h I hex)
  intro a' ha'
  by_contra hcl
  obtain ⟨o, ho, ha'o, hoe⟩ :
      ∃ o : Set M', IsOpen o ∧ a' ∈ o ∧ o ∩ π ⁻¹' (I.support \ Y) = ∅ := by
    rw [mem_closure_iff] at hcl
    push Not at hcl
    exact hcl
  -- near `a'`, the points of `X'` lie on the exceptional divisor
  have hsub : ∀ y' ∈ (⟨o, ho⟩ : Opens M'), y' ∈ (strictTransformSubspace hY h I).support →
      y' ∈ (hY.idealSheaf.pullback π h.contMDiff).support := by
    intro y' hy'o hy'
    by_contra hyF
    have hmem : y' ∈ (strictTransformSubspace hY h I).support \
        (hY.idealSheaf.pullback π h.contMDiff).support := ⟨hy', hyF⟩
    rw [cosupport_strictTransformSubspace_diff_of_hasLocalGenerators hY h I hex] at hmem
    have hyY : π y' ∉ Y := by
      rw [IsBlowUp.cosupport_exceptionalIdealSheaf hY h] at hyF
      exact hyF
    exact Set.eq_empty_iff_forall_notMem.mp hoe y' ⟨hy'o, hmem.1, hyY⟩
  -- Rückert: the exceptional ideal lies in the radical of the strict transform's stalk
  have hle : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ≤
      ((strictTransformSubspace hY h I).stalkIdeal a').radical := fun f hf =>
    mem_radical_stalkIdeal_of_cosupport_subset ψ _ _ ha'o hsub hf
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hle (IsNoetherian.noetherian _)
  rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex] at hk
  -- a finitely generated ideal below a directed union lies below one member
  have hcomp : IsCompactElement ((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ^ k) :=
    (Submodule.fg_iff_compact _).mp (IsNoetherian.noetherian _)
  obtain ⟨s, hs⟩ := IsCompactElement.exists_finset_of_le_iSup (hk := hcomp)
    (f := fun j : ℕ => Submodule.colon ((I.pullback π h.contMDiff).stalkIdeal a')
      (SetLike.coe ((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ^ j))) (h := hk)
  have hmono : Monotone fun j : ℕ => Submodule.colon ((I.pullback π h.contMDiff).stalkIdeal a')
      (SetLike.coe ((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ^ j)) := fun j j' hjj' =>
    Submodule.colon_mono le_rfl (Ideal.pow_le_pow_right hjj')
  have hN : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ^ k ≤
      Submodule.colon ((I.pullback π h.contMDiff).stalkIdeal a')
        (SetLike.coe ((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ^ s.sup id)) :=
    hs.trans (iSup₂_le fun j hj => hmono (Finset.le_sup (f := id) hj))
  -- hence `I_F^{k+N} ⊆ π^*I`, so `1` lies in the saturation
  have hpow : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ^ (k + s.sup id) ≤
      (I.pullback π h.contMDiff).stalkIdeal a' := by
    rw [pow_add]
    refine Ideal.mul_le.mpr fun r hr p hp => ?_
    have := Submodule.mem_colon.mp (hN hr) p hp
    rwa [smul_eq_mul] at this
  have hone : (1 : (structureSheaf ℂ E M').presheaf.stalk a') ∈ saturationStalk hY h I a' := by
    refine Submodule.mem_iSup_of_mem (k + s.sup id) (Submodule.mem_colon.mpr fun p hp => ?_)
    rw [one_smul]
    exact hpow hp
  have htop : (strictTransformSubspace hY h I).stalkIdeal a' = ⊤ := by
    rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex]
    exact (Ideal.eq_top_iff_one _).mpr hone
  exact (IdealSheaf.mem_support _).mp ha' htop

end Complex

end Manifold
