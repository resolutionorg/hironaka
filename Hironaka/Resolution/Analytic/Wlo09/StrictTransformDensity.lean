/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeq
import Hironaka.AnalyticSpace.Noether.Saturation
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.SaturationFiniteType
import Hironaka.Manifold.BlowUp.Transform.StrictSubspace
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceBasic
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceClosure
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.NonSingular
import Hironaka.Resolution.Analytic.OrderReduction.BDCor85
import Hironaka.Resolution.Analytic.Wlo09.BoundaryBridge
import Hironaka.Resolution.Analytic.Wlo09.Components
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Density of the strict transform off the exceptional divisor at a regular point

Along a finite succession of blow-ups with smooth centres, at a point of the strict transform `Y_i`
of a closed subspace whose quotient stalk is regular, the points of `Y_i` off the exceptional family
`E_i` accumulate (`mem_closure_cosupport_strictTransformSubspaceSeq_diff_support_of_isRegular`).
This is not stated in the sources; it is what turns clause (3) of [Wlo09, Theorem 2.0.2] into its
proper form, where no exceptional divisor through a point carries a coordinate of the final strict
transform (`Hironaka/Resolution/Analytic/Wlo09/ProperSncOfEmbeddedDesing.lean`), and it gives the
density of the preimage of the regular locus under the resolution of an analytic space.

The strict transform is taken stalkwise as the saturation `⋃_k (σ^*𝓘 : 𝓘_D^k)` of the total
transform by the exceptional ideal [BM97, Proposition 3.13]; since these saturations have local
generators (`saturationStalk_hasLocalGenerators`), the definition `strictTransformSubspace` takes
this branch at every point (`stalkIdeal_strictTransformSubspace`). The lemmas:

* a regular quotient stalk is a coordinate ideal on an adapted chart and the full vanishing ideal
  of the smooth germ (`exists_adaptedChart_of_isRegularLocalRing_quotient` with
  `vanishingStalk_cosupport_eq_stalkIdeal_of_eq_span_coord`), and regularity of the quotient stalk
  is open along the cosupport (`eventually_isRegularLocalRing_quotient_of_isRegular`);
* a saturation by the exceptional ideal never contains the exceptional ideal unless it is the unit
  ideal (`stalkIdeal_strictTransformSubspace_eq_top_of_exceptional_le`);
* off the centre, regularity of the quotient stalk transports along the blowing-down
  (`isRegularLocalRing_quotient_strictTransformSubspace_iff_of_notMem`), which is an open map there
  (`IsBlowUp.image_mem_nhds_of_notMem`);
* the theorem, by induction on the stage; the case of a point on the new exceptional divisor is
  `mem_closure_cosupport_diff_exceptional_of_isRegular` at one blow-up.

The argument is uniform in the field `𝕜` and uses no Nullstellensatz.
-/

public section

open Set Topology TopologicalSpace AnalyticManifold Hironaka.Manifold Filter
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section OneStep

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}
  (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (I : Manifold.IdealSheaf
      (structureSheaf 𝕜 E M))

/-- The stalks of the strict transform are the saturations, unconditionally: the saturation stalks
have local generators (`saturationStalk_hasLocalGenerators`), so the definition
`strictTransformSubspace` takes its saturation branch at every point
(`stalkIdeal_strictTransformSubspace_of_hasLocalGenerators`). -/
theorem stalkIdeal_strictTransformSubspace (a' : M') :
    (strictTransformSubspace hY h I).stalkIdeal a' = saturationStalk hY h I a' :=
  stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I
    (saturationStalk_hasLocalGenerators hY h I) a'

/-- A saturation by the exceptional ideal never contains the exceptional ideal unless it is the unit
ideal: if `𝓘_D ≤ Ỹ_{a'}` then `Ỹ_{a'} = ⊤`. The chain `k ↦ (T : 𝓘_D^k)` is stationary from some
`N` in the Noetherian stalk (`exists_colon_pow_stationary_at`), so the saturation is
`(T : 𝓘_D^N)`; `𝓘_D ≤ (T : 𝓘_D^N)` gives `𝓘_D^{N+1} ≤ T`, hence
`1 ∈ (T : 𝓘_D^{N+1}) = (T : 𝓘_D^N)`. -/
theorem stalkIdeal_strictTransformSubspace_eq_top_of_exceptional_le (a' : M')
    (hle : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ≤
      (strictTransformSubspace hY h I).stalkIdeal a') :
    (strictTransformSubspace hY h I).stalkIdeal a' = ⊤ := by
  rw [stalkIdeal_strictTransformSubspace hY h I a'] at hle ⊢
  obtain ⟨N, hN⟩ := AnalyticSpace.exists_colon_pow_stationary_at
    (AnalyticSpace.toSpace ψ (⟨M'⟩ : AnalyticManifold.{u} 𝕜 E))
    (I.pullback π h.contMDiff) (hY.idealSheaf.pullback π h.contMDiff) a'
  set T := (I.pullback π h.contMDiff).stalkIdeal a' with hT
  set D := (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' with hD
  -- the saturation is the `N`-th colon
  have hsat : saturationStalk hY h I a' = Submodule.colon T (SetLike.coe (D ^ N)) := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup (fun k => Submodule.colon T
      (SetLike.coe (D ^ k))) N)
    rcases le_or_gt k N with hk | hk
    · intro g hg
      rw [Submodule.mem_colon] at hg ⊢
      intro s hs
      exact hg s (Ideal.pow_le_pow_right hk hs)
    · exact (hN k hk.le).le
  rw [hsat] at hle ⊢
  -- `𝓘_D ≤ (T : 𝓘_D^N)` gives `𝓘_D^{N+1} ≤ T`, so `1 ∈ (T : 𝓘_D^{N+1}) = (T : 𝓘_D^N)`
  have hpow : D ^ (N + 1) ≤ T := by
    rw [pow_succ']
    refine Ideal.mul_le.mpr fun g hg s hs => ?_
    have := Submodule.mem_colon.mp (hle hg) s hs
    simpa [smul_eq_mul] using this
  have hone : (1 : (structureSheaf 𝕜 E M').presheaf.stalk a') ∈
      Submodule.colon T (SetLike.coe (D ^ (N + 1))) := by
    rw [Submodule.mem_colon]
    intro s hs
    simpa using hpow hs
  have hEq : Submodule.colon T (SetLike.coe (D ^ (N + 1))) =
      Submodule.colon T (SetLike.coe (D ^ N)) := hN (N + 1) (Nat.le_succ N)
  rw [hEq] at hone
  exact (Ideal.eq_top_iff_one _).mpr hone

/-- At a point of the strict transform under one blow-up whose quotient stalk is regular, the points
of the strict transform off the exceptional divisor accumulate: the stalk is a coordinate ideal on
an adapted chart and the full vanishing ideal of the cosupport there, the exceptional equation is
not in it (`stalkIdeal_strictTransformSubspace_eq_top_of_exceptional_le`), so it does not vanish
identically on the cosupport near the point. -/
theorem mem_closure_cosupport_diff_exceptional_of_isRegular (a' : M')
    (ha' : a' ∈ (strictTransformSubspace hY h I).support)
    (hreg : IsRegularLocalRing ((structureSheaf 𝕜 E M').presheaf.stalk a' ⧸
      (strictTransformSubspace hY h I).stalkIdeal a')) :
    a' ∈ closure ((strictTransformSubspace hY h I).support \
      (hY.idealSheaf.pullback π h.contMDiff).support) := by
  set J := strictTransformSubspace hY h I with hJdef
  -- an adapted chart on whose source the stalks of `J` are the coordinate span
  obtain ⟨c', φ, σ, hφ, haφ, hJ⟩ :=
    exists_adaptedChart_of_isRegularLocalRing_quotient (ψ := ψ) J hreg
  have hvan : vanishingStalk (𝕜 := 𝕜) (E := E) J.support a' = J.stalkIdeal a' :=
    vanishingStalk_cosupport_eq_stalkIdeal_of_eq_span_coord (ψ := ψ)
      (M := (⟨M'⟩ : AnalyticManifold.{u} 𝕜 E)) J hφ.1 σ hJ haφ
  -- the exceptional stalk is not contained in `J_{a'}` (which is proper)
  have hnle : ¬ (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ≤ J.stalkIdeal a' := fun hle =>
    ha' (stalkIdeal_strictTransformSubspace_eq_top_of_exceptional_le hY h I a' hle)
  obtain ⟨u, huE, huJ⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  obtain ⟨V, haV, g, hgV, rfl⟩ := huE
  rw [mem_closure_iff_nhds]
  intro N hN
  -- the section `g` does not vanish identically on the cosupport near `a'`
  rw [← hvan, mem_vanishingStalk_iff, stalkToGerm_structureSheaf_germ, Germ.vanishesOn_coe,
    Filter.not_eventually] at huJ
  have hNV : (N ∩ V) ∩ J.support ∈ 𝓝[J.support] a' :=
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Filter.inter_mem hN (V.2.mem_nhds haV)))
      self_mem_nhdsWithin
  obtain ⟨y, hy0, ⟨hyN, hyV⟩, hyJ⟩ := (huJ.and_eventually hNV).exists
  refine ⟨y, hyN, hyJ, fun hyE => ?_⟩
  -- at `y` the germ of `g` is a unit of the exceptional stalk, so that stalk is the unit ideal
  have hmem : (structureSheaf 𝕜 E M').presheaf.germ V y hyV g ∈
      (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal y :=
    (hY.idealSheaf.pullback π h.contMDiff).germ_mem_stalkIdeal hyV hgV
  have hunit : IsUnit ((structureSheaf 𝕜 E M').presheaf.germ V y hyV g) := by
    rw [← IsLocalRing.notMem_maximalIdeal, mem_maximalIdeal_iff_eval, eval_germ' V hyV g]
    exact fun h0 => hy0 h0
  exact hyE (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

/-- Off the centre, regularity of the quotient stalk transports along the blowing-down: the germ
map is bijective there (`IsBlowUp.germMap_bijective_of_notMem`) and the stalk of the strict
transform is the image of the stalk of `I`. -/
theorem isRegularLocalRing_quotient_strictTransformSubspace_iff_of_notMem (a' : M')
    (ha' : π a' ∉ Y) :
    IsRegularLocalRing ((structureSheaf 𝕜 E M').presheaf.stalk a' ⧸
        (strictTransformSubspace hY h I).stalkIdeal a') ↔
      IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk (π a') ⧸ I.stalkIdeal (π a')) := by
  have hnot : a' ∉ (hY.idealSheaf.pullback π h.contMDiff).support := by
    rw [IsBlowUp.cosupport_exceptionalIdealSheaf hY h]
    exact ha'
  have hst := stalkIdeal_strictTransformSubspace_of_notMem_cosupport_of_hasLocalGenerators hY h I
    (saturationStalk_hasLocalGenerators hY h I) hnot
  have hbij := h.germMap_bijective_of_notMem ha'
  let e : (structureSheaf 𝕜 E M).presheaf.stalk (π a') ≃+*
      (structureSheaf 𝕜 E M').presheaf.stalk a' := RingEquiv.ofBijective _ hbij
  have hmap : (strictTransformSubspace hY h I).stalkIdeal a' =
      Ideal.map (e : (structureSheaf 𝕜 E M).presheaf.stalk (π a') →+*
        (structureSheaf 𝕜 E M').presheaf.stalk a') (I.stalkIdeal (π a')) := hst
  let q := Ideal.quotientEquiv (I.stalkIdeal (π a'))
    ((strictTransformSubspace hY h I).stalkIdeal a') e hmap
  exact ⟨fun hr => IsRegularLocalRing.of_ringEquiv q.symm,
    fun hr => IsRegularLocalRing.of_ringEquiv q⟩

include h in
/-- Off the centre the blowing-down is an open map: the image of a neighbourhood of a point off the
exceptional divisor is a neighbourhood of its image (the field `isLocalDiffeomorphOn_compl`, a local
homeomorphism there). -/
theorem _root_.Manifold.IsBlowUp.image_mem_nhds_of_notMem {a' : M'} (ha' : π a' ∉ Y) {N : Set M'}
    (hN : N ∈ 𝓝 a') : π '' N ∈ 𝓝 (π a') := by
  have hloc := h.isLocalDiffeomorphOn_compl.isLocalHomeomorphOn
  rw [← hloc.map_nhds_eq (show a' ∈ π ⁻¹' Yᶜ from ha')]
  exact Filter.image_mem_map hN

omit [T2Space M'] [SecondCountableTopology M'] in
include ψ in
/-- Regularity of the quotient stalk is open along the cosupport: on the source of the adapted
chart the stalks of `J` are the coordinate span
(`exists_adaptedChart_of_isRegularLocalRing_quotient`), a coordinate span is proper iff its
coordinates vanish (`span_coord_ne_top_iff`), and a proper coordinate span has a regular quotient
(`isRegularLocalRing_quotient_span_coord`). -/
theorem eventually_isRegularLocalRing_quotient_of_isRegular (J : Manifold.IdealSheaf
    (structureSheaf 𝕜 E M'))
    {a : M'}
    (hreg : IsRegularLocalRing ((structureSheaf 𝕜 E M').presheaf.stalk a ⧸ J.stalkIdeal a)) :
    ∀ᶠ y in 𝓝 a, y ∈ J.support →
      IsRegularLocalRing ((structureSheaf 𝕜 E M').presheaf.stalk y ⧸ J.stalkIdeal y) := by
  obtain ⟨c', φ, σ, hφ, haφ, hJ⟩ :=
    exists_adaptedChart_of_isRegularLocalRing_quotient (ψ := ψ) J hreg
  filter_upwards [φ.open_source.mem_nhds haφ] with y hy hyJ
  have hne : J.stalkIdeal y ≠ ⊤ := hyJ
  rw [hJ y hy] at hne ⊢
  exact isRegularLocalRing_quotient_span_coord φ hφ.1 hy σ
    ((span_coord_ne_top_iff ψ φ hφ.1 hy σ).mp hne)

end OneStep

section Succession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M) (J : AnalyticManifold.IdealSheaf M)

/-- **Density of the strict transform off the exceptional divisor at a regular point**, at every
stage `i` of a finite succession: at a point `z` of the strict transform `Y_i` whose quotient stalk
is regular, the points of `Y_i` off the exceptional family `E_i` accumulate at `z`. Base `i = 0`:
`E_0 = ∅` (`totalTransformSeq_zero`). Step: if `z` is off the new divisor (the first case), push
down along the local isomorphism and apply the induction hypothesis at `π z`; if `z` is on the new
divisor (the second case), `mem_closure_cosupport_diff_exceptional_of_isRegular` gives a regular
point of `Y_{i+1}` off the new divisor arbitrarily near `z`, and the first case applies to it.
Uniform in `𝕜`; no Nullstellensatz. -/
theorem mem_closure_cosupport_strictTransformSubspaceSeq_diff_support_of_isRegular
    (i : Fin (S.length + 1)) (z : S.stage i)
    (hz : z ∈ (S.strictTransformSubspaceSeq J i).support)
    (hreg : IsRegularLocalRing ((structureSheaf 𝕜 E (S.stage i)).presheaf.stalk z ⧸
      (S.strictTransformSubspaceSeq J i).stalkIdeal z)) :
    z ∈ closure ((S.strictTransformSubspaceSeq J i).support \
      (S.totalTransformSeq i).support) := by
  induction i using Fin.induction with
  | zero =>
    have hE : (S.totalTransformSeq 0).support = ∅ := by
      rw [FiniteSuccession.totalTransformSeq_zero]
      exact Set.eq_empty_of_forall_notMem fun x hx =>
        (Set.mem_iUnion.mp hx).elim fun j _ => PEmpty.elim j
    rw [hE, Set.sdiff_empty]
    exact subset_closure hz
  | succ i ih =>
    -- the `i`-th blow-up: its centre `Z_i`, its map `π`, the one-step strict transform
    have hY := S.isClosedSubmanifold_center i
    have hb := S.isBlowUp_map i
    have hex := saturationStalk_hasLocalGenerators hY hb (S.strictTransformSubspaceSeq J i.castSucc)
    -- the members of the exceptional family are closed at every stage
    -- (`isClosed_hyp_totalTransformSeqFrom` from the empty start, `totalTransformSeqFrom_empty`)
    have hcl : ∀ j, IsClosed ((S.totalTransformSeq i.castSucc).hyp j) :=
      S.isClosed_hyp_totalTransformSeqFrom (F := HypersurfaceFamily.empty M) (fun j => j.elim)
        i.castSucc
    have hsupp := support_totalTransformSeq_succ S i hcl
    have hDeq : (hY.idealSheaf.pullback _ hb.contMDiff).support = S.exceptionalAt i :=
      IsBlowUp.cosupport_exceptionalIdealSheaf hY hb
    have hDclosed : IsClosed (S.exceptionalAt i) :=
      (IdealSheaf.isClosed_support (J := S.center i)).preimage (S.map i).2.continuous
    have hdiff := cosupport_strictTransformSubspace_diff_of_hasLocalGenerators hY hb
      (S.strictTransformSubspaceSeq J i.castSucc) hex
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨U, hUN, hUo, hzU⟩ := mem_nhds_iff.mp hN
    -- the first case, as a local statement: a regular point of `Y_{i+1}` off the new divisor,
    -- inside the open `U`, is accumulated by points of `Y_{i+1}` off `E_{i+1}` inside `U`.
    have case1 : ∀ y ∈ U, y ∉ S.exceptionalAt i →
        y ∈ (S.strictTransformSubspaceSeq J i.succ).support →
        IsRegularLocalRing ((structureSheaf 𝕜 E (S.stage i.succ)).presheaf.stalk y ⧸
          (S.strictTransformSubspaceSeq J i.succ).stalkIdeal y) →
        ∃ y'' ∈ U, y'' ∈ (S.strictTransformSubspaceSeq J i.succ).support ∧
          y'' ∉ (S.totalTransformSeq i.succ).support := by
      intro y hyU hyD hyY hyreg
      have hπy : S.map i y ∉ (S.center i).support := hyD
      -- regularity and membership push down to `π y`
      have hπreg := (isRegularLocalRing_quotient_strictTransformSubspace_iff_of_notMem hY hb
        (S.strictTransformSubspaceSeq J i.castSucc) y hπy).mp hyreg
      have hyD' : y ∉ (hY.idealSheaf.pullback _ hb.contMDiff).support := by rw [hDeq]; exact hyD
      have hπyY : S.map i y ∈ (S.strictTransformSubspaceSeq J i.castSucc).support := by
        have := (Set.ext_iff.mp hdiff y).mp ⟨hyY, hyD'⟩
        exact this.1
      -- the induction hypothesis at `π y`, read in the neighbourhood `π '' W`
      set W := U ∩ (S.exceptionalAt i)ᶜ with hW
      have hWo : IsOpen W := hUo.inter hDclosed.isOpen_compl
      have hyW : y ∈ W := ⟨hyU, hyD⟩
      have himg := IsBlowUp.image_mem_nhds_of_notMem hb hπy (hWo.mem_nhds hyW)
      obtain ⟨_, ⟨y'', hy''W, rfl⟩, hy''Y, hy''E⟩ :=
        mem_closure_iff_nhds.mp (ih (S.map i y) hπyY hπreg) _ himg
      refine ⟨y'', hy''W.1, ?_, ?_⟩
      · have hy''D' : y'' ∉ (hY.idealSheaf.pullback _ hb.contMDiff).support := by
          rw [hDeq]; exact hy''W.2
        exact ((Set.ext_iff.mp hdiff y'').mpr ⟨hy''Y, hy''D'⟩).1
      · rw [hsupp]
        rintro (h1 | h2)
        · exact hy''E h1
        · exact hy''W.2 h2
    by_cases hD : z ∈ S.exceptionalAt i
    · -- the second case: `z` on the new divisor; a regular point of `Y_{i+1}` off it lies in `U`,
      -- and the first case applies at that point
      have hev := eventually_isRegularLocalRing_quotient_of_isRegular (ψ := S.chartAt i)
        (S.strictTransformSubspaceSeq J i.succ) hreg
      have hS3 := mem_closure_cosupport_diff_exceptional_of_isRegular hY hb
        (S.strictTransformSubspaceSeq J i.castSucc) z hz hreg
      obtain ⟨z', ⟨hz'U, hz'reg⟩, hz'Y, hz'D⟩ :=
        mem_closure_iff_nhds.mp hS3 _ (Filter.inter_mem (hUo.mem_nhds hzU) hev)
      rw [hDeq] at hz'D
      obtain ⟨y'', hy''U, hy''Y, hy''E⟩ := case1 z' hz'U hz'D hz'Y (hz'reg hz'Y)
      exact ⟨y'', hUN hy''U, hy''Y, hy''E⟩
    · obtain ⟨y'', hy''U, hy''Y, hy''E⟩ := case1 z hzU hD hz hreg
      exact ⟨y'', hUN hy''U, hy''Y, hy''E⟩

end Succession

end Hironaka.Manifold
