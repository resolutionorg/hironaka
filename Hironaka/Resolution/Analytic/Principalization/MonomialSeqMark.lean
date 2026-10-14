/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.MonomialTransport
public import Hironaka.Resolution.Analytic.Principalization.MonomialStep
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.BMO.SplitOrder
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bMeasure
import Hironaka.Resolution.Analytic.Principalization.MonomialSeq
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's formula at mark `m`: the residual identity along a sequence of order `≥ m`

Kollár's birational transform of a marked ideal, `π_*^{-1}(I, m) := (𝒪(mF) · π^*I, m)`
[Kol07, (60.1)], and the explicit formula of [Kol07, 72] at a general mark: along a sequence of
order `≥ m` for `(I, m, red F)` the pull-back of `I` to every stage is a boundary monomial in the
total transform of `F` with residual the marked transform at mark `m` — the exact division
`π⁻¹(J)_p = I_{F,p}^m · π_*^{-1}(J, m)_p` at one blowing-up, then stage by stage. The mark-`1`
case is `MonomialSeq.lean` (`stalkIdeal_totalTransform_eq_mul_birationalTransform`,
`map_germMap_stalkIdeal_markedTransformSeq`, `isBoundaryMonomialAt_stageMapAux`); the rounds of
the resolution run at the marks `d_U, …, 1` (the maximal order `d_i` of clause (2) of
[Hir64, Main Theorem II(N), p. 176]), so the residual identity at the round's own mark is what the
assembled resolution needs (the mark-`1` identity for the whole list has a non-unit residual when
`d_U ≥ 2`).

* `stalkIdeal_totalTransform_eq_pow_mul_birationalTransform` — (60.1) at mark `m`, exact, at one
  blowing-up (`isDivExceptional_birationalTransform` already carries the mark).
* `FiniteSuccession.map_germMap_stalkIdeal_markedTransformSeq_of_isOfOrderGe` — the same along a
  sequence of order `≥ m`, stage by stage.
* `FiniteSuccession.isBoundaryMonomialAt_stageMapAux_of_isOfOrderGe` — the residual identity at
  mark `m` ([Kol07, 72] with the residual kept; `isBoundaryMonomialAt_pullback` with `e := m`).
* `FiniteSuccession.isBoundaryMonomialAt_comap_stageMapAux` — a boundary monomial with residual
  pulls back along a sequence whose centres have only normal crossings with the boundary, the
  residual pulled back as it is (`isBoundaryMonomialAt_pullback` with `e := 0`).
* `FiniteSuccession.isOfOrderGe_zero_of_isOfOrderGe` — order `≥ m` gives order `≥ 0` for any
  ideal: at mark `0` only clause (3′) of [Kol07, Definition 66] remains.
* `BlowUpSequence.pullbackIsMonomialAtLast_of_isBoundaryMonomialAt` — `PullbackIsMonomialAtLast` is
  multiplicative in the ideal: if `J = (monomial in F) · R` at every point and the list makes `R`
  a boundary monomial at its last stage, it makes `J` one.

Used for the monomial clause of the assembled resolution
(`Hironaka/Resolution/Analytic/Wlo09/Monomial.lean`).
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section BlowUp

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M M' : AnalyticManifold.{u} 𝕜 E} {π : M' → M} {Y : Set M} {c : ℕ}

/-- Kollár's (60.1) at mark `m`, in its exact form [Kol07, (60.1)]: when `ord_Y J ≥ m`, the total
transform of `J` is the `m`-th power of the exceptional ideal times the marked transform at mark
`m` at every stalk, `π⁻¹(J)_p = I_{F,p}^m · π_*^{-1}(J, m)_p` — the marked transform's stalk is the
colon `(π⁻¹(J)_p : I_{F,p}^m)` (`isDivExceptional_birationalTransform`), `π⁻¹(J)_p ⊆ I_{F,p}^m`
because `J_a ⊆ I_{Y,a}^m` on the centre, and `I_{F,p}` is principal. The mark-`1` case is
`stalkIdeal_totalTransform_eq_mul_birationalTransform`. -/
theorem stalkIdeal_totalTransform_eq_pow_mul_birationalTransform (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (J : AnalyticManifold.IdealSheaf M) (m : ℕ)
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a) (p : M') :
    (J.pullback π h.contMDiff).stalkIdeal p =
      (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p ^ m *
        (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.stalkIdeal p := by
  have hdiv : (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.stalkIdeal p =
      ((J.pullback π h.contMDiff).stalkIdeal p).colon
        ↑((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p ^ m) :=
    isDivExceptional_birationalTransform hY h ⟨J, m⟩ hm p
  obtain ⟨u, hu⟩ :=
    (h.isClosedSubmanifold_preimage hY).exists_vanishingStalk_eq_span_singleton p
  have hexc : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p = Ideal.span {u} :=
    (h.stalkIdeal_exceptionalIdealSheaf_eq_vanishingStalk hY p).trans hu
  have hle : (J.pullback π h.contMDiff).stalkIdeal p ≤ Ideal.span {u ^ m} := by
    rw [← Ideal.span_singleton_pow, ← hexc]
    by_cases hpY : π p ∈ Y
    · rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback, ← Ideal.map_pow]
      exact Ideal.map_mono
        ((IdealSheaf.le_ordAlongIdeal_iff hY.idealSheaf J (π p) m).mp (hm (π p) hpY))
    · rw [stalkIdeal_exceptionalIdealSheaf_of_notMem hY h hpY, Ideal.top_pow]
      exact le_top
  rw [hdiv, hexc, Ideal.span_singleton_pow]
  exact (Ideal.span_singleton_mul_colon_of_le hle).symm

end BlowUp

end Hironaka.Manifold

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- Kollár's (60.1) at mark `m` along a sequence of order `≥ m` (clause (4′) of
[Kol07, Definition 66]): the marked transform `I_i` pulls back to the `m`-th power of the
exceptional ideal of `π_i` times `I_{i+1}` (the mark-`1` case is
`map_germMap_stalkIdeal_markedTransformSeq`). -/
theorem map_germMap_stalkIdeal_markedTransformSeq_of_isOfOrderGe
    {I E₀ : IdealSheaf M}
    {m : ℕ} (hge : S.IsOfOrderGe I m E₀) (i : Fin S.length) (x : S.stage i.succ) :
    Ideal.map (germMap (S.map i) (S.map i).contMDiff x)
        ((S.markedTransformSeq I m i.castSucc).stalkIdeal (S.map i x)) =
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑(S.map i) ⁻¹' (S.center i).support) x ^ m *
        (S.markedTransformSeq I m i.succ).stalkIdeal x := by
  have hm : ∀ a ∈ (S.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
      (S.isClosedSubmanifold_center i).idealSheaf (S.markedTransformSeq I m i.castSucc) a :=
    fun a ha => by
      rw [← IdealSheaf.ordAlongIdeal_congr_stalk_left _ _ _ (S.stalkIdeal_center_eq i a)]
      exact (hge i).2 a ha
  have e := stalkIdeal_totalTransform_eq_pow_mul_birationalTransform
    (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) (S.markedTransformSeq I m i.castSucc) m hm x
  rw [← (S.isBlowUp_map i).stalkIdeal_exceptionalIdealSheaf_eq_vanishingStalk
    (S.isClosedSubmanifold_center i) x]
  rw [IdealSheaf.stalkIdeal_pullback] at e
  exact e

/-- Kollár's formula [Kol07, 72] at mark `m`, stage by stage — the residual identity: along a
sequence of order `≥ m` for `(I, m, red F)`, the pull-back of `I` to the stage `i` is a boundary
monomial in the total transform of `F` at that stage with residual the marked transform at mark
`m` — the empty product at stage `0`, then the step of `MonomialStep.lean` with the exact division
`π_i⁻¹(I_i) = I_{F_i}^m · I_{i+1}`, the centre having snc with the boundary by clause (3′). The
mark-`1` case is `isBoundaryMonomialAt_stageMapAux`. -/
theorem isBoundaryMonomialAt_stageMapAux_of_isOfOrderGe {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    {I : IdealSheaf M} {m : ℕ}
    (hge : S.IsOfOrderGe I m (F.idealSheaf (𝕜 := 𝕜) (E := E))) :
    ∀ (i : ℕ) (hi : i < S.length + 1) (x : finStages M S.later ⟨i, hi⟩),
      (S.totalTransformSeqFromAux F i hi).IsBoundaryMonomialAt
        (I.pullback _ (S.stageMapAux i hi).contMDiff)
            (S.markedTransformSeqAux I m i hi) x
  | 0, _, x => ⟨∅, fun _ => 0, fun j hj => absurd hj (Finset.notMem_empty j), by
      rw [Finset.prod_empty, one_mul]
      change (IdealSheaf.pullback (𝕜 := 𝕜) (E' := E) (id : M → M) contMDiff_id I).stalkIdeal x =
        I.stalkIdeal x
      rw [IdealSheaf.pullback_id_eq_self]⟩
  | i + 1, hi, x => by
    have hi' : i < S.length := Nat.lt_of_succ_lt_succ hi
    have h3 : ∀ i' : Fin S.length,
        (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
          (S.center i') :=
      fun i' => (hge i').1
    have hFi : (S.totalTransformSeqFrom F (⟨i, hi'⟩ : Fin S.length).castSucc).IsSnc ψ :=
      (isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF _ fun i' _ => h3 i').1
    have hsnci := hasSncWith_totalTransformSeqFrom_center_of_forall_lt hF ⟨i, hi'⟩
      fun i' _ => h3 i'
    have hY := (S.isClosedSubmanifold_center ⟨i, hi'⟩).congr_chart ψ
    have hπ := (S.isBlowUp_map ⟨i, hi'⟩).congr_chart ψ
    have ih := isBoundaryMonomialAt_stageMapAux_of_isOfOrderGe hF hge i (Nat.lt_of_succ_lt hi)
      (S.map ⟨i, hi'⟩ x)
    have hR := S.map_germMap_stalkIdeal_markedTransformSeq_of_isOfOrderGe hge ⟨i, hi'⟩ x
    have e : I.pullback _ (S.stageMapAux (i + 1) hi).contMDiff =
        (I.pullback _ (S.stageMapAux i (Nat.lt_of_succ_lt hi)).contMDiff).pullback _ (S.map ⟨i,
            hi'⟩).contMDiff :=
      (IdealSheaf.pullback_comp I _ _).symm
    rw [e]
    exact isBoundaryMonomialAt_pullback hY hπ hFi hsnci ih hR

/-- A boundary monomial with residual pulls back along a sequence whose centres have only normal
crossings with the boundary (clause (3′) of [Kol07, Definition 66]): at a point of stage `i`, if
`J = (monomial in F) · R` at its image, then `π_i^* J = (monomial in the total transform of F)
· π_i^* R` — `isBoundaryMonomialAt_pullback` with `e := 0`, the residual pulled back as it is. -/
theorem isBoundaryMonomialAt_comap_stageMapAux {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    (h3 : ∀ i : Fin S.length,
      (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i.castSucc).HasOnlyNormalCrossingsWith
        (S.center i))
    {J R : IdealSheaf M} :
    ∀ (i : ℕ) (hi : i < S.length + 1) (x : finStages M S.later ⟨i, hi⟩),
      F.IsBoundaryMonomialAt J R (S.stageMapAux i hi x) →
      (S.totalTransformSeqFromAux F i hi).IsBoundaryMonomialAt
        (J.pullback _ (S.stageMapAux i hi).contMDiff)
        (R.pullback _ (S.stageMapAux i hi).contMDiff) x
  | 0, _, x, hJ => by
    obtain ⟨s, α, hs, hx⟩ := hJ
    refine ⟨s, α, hs, ?_⟩
    change (IdealSheaf.pullback (𝕜 := 𝕜) (E' := E) (id : M → M) contMDiff_id J).stalkIdeal x =
      _ * (IdealSheaf.pullback (𝕜 := 𝕜) (E' := E) (id : M → M) contMDiff_id R).stalkIdeal x
    rw [IdealSheaf.pullback_id_eq_self, IdealSheaf.pullback_id_eq_self]
    exact hx
  | i + 1, hi, x, hJ => by
    have hi' : i < S.length := Nat.lt_of_succ_lt_succ hi
    have hFi : (S.totalTransformSeqFrom F (⟨i, hi'⟩ : Fin S.length).castSucc).IsSnc ψ :=
      (isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF _ fun i' _ => h3 i').1
    have hsnci := hasSncWith_totalTransformSeqFrom_center_of_forall_lt hF ⟨i, hi'⟩
      fun i' _ => h3 i'
    have hY := (S.isClosedSubmanifold_center ⟨i, hi'⟩).congr_chart ψ
    have hπ := (S.isBlowUp_map ⟨i, hi'⟩).congr_chart ψ
    have ih := isBoundaryMonomialAt_comap_stageMapAux hF h3 i (Nat.lt_of_succ_lt hi)
      (S.map ⟨i, hi'⟩ x) hJ
    have eJ : J.pullback _ (S.stageMapAux (i + 1) hi).contMDiff =
        (J.pullback _ (S.stageMapAux i (Nat.lt_of_succ_lt hi)).contMDiff).pullback _ (S.map ⟨i,
            hi'⟩).contMDiff :=
      (IdealSheaf.pullback_comp J _ _).symm
    have eR : R.pullback _ (S.stageMapAux (i + 1) hi).contMDiff =
        (R.pullback _ (S.stageMapAux i (Nat.lt_of_succ_lt hi)).contMDiff).pullback _ (S.map ⟨i,
            hi'⟩).contMDiff :=
      (IdealSheaf.pullback_comp R _ _).symm
    have hR : Ideal.map (germMap (S.map ⟨i, hi'⟩) (S.map ⟨i, hi'⟩).contMDiff x)
        ((R.pullback _ (S.stageMapAux i (Nat.lt_of_succ_lt hi)).contMDiff).stalkIdeal
          (S.map ⟨i, hi'⟩ x)) =
        vanishingStalk (𝕜 := 𝕜) (E := E) (⇑(S.map ⟨i, hi'⟩) ⁻¹' (S.center ⟨i, hi'⟩).support) x ^ 0 *
          ((R.pullback _ (S.stageMapAux i (Nat.lt_of_succ_lt hi)).contMDiff).pullback _ (S.map ⟨i,
              hi'⟩).contMDiff).stalkIdeal
              x := by
      rw [pow_zero, one_mul]
      exact (IdealSheaf.stalkIdeal_pullback _ _ _ x).symm
    rw [eJ, eR]
    exact isBoundaryMonomialAt_pullback hY hπ hFi hsnci ih hR

/-- Order `≥ m` gives order `≥ 0` for any ideal: at mark `0` only clause (3′) of
[Kol07, Definition 66] — the centres have only normal crossings with the boundary — remains. -/
theorem isOfOrderGe_zero_of_isOfOrderGe {I I' E₀ : IdealSheaf M} {m : ℕ}
    (hge : S.IsOfOrderGe I m E₀) : S.IsOfOrderGe I' 0 E₀ := fun i =>
  ⟨(hge i).1, fun _ _ => by rw [Nat.cast_zero]; exact bot_le⟩

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- `PullbackIsMonomialAtLast` is multiplicative in the ideal: if `J = (monomial in F) · R` at
every point and the list makes `R` a boundary monomial at its last stage, it makes `J` one —
`isBoundaryMonomialAt_comap_stageMapAux` at the last stage, then the product of two boundary
monomials in the same family is one (the exponents add over the union of the index sets). -/
theorem pullbackIsMonomialAtLast_of_isBoundaryMonomialAt (L : BlowUpSequence ψ₀ M)
    {F : Manifold.HypersurfaceFamily M} (hF : F.IsSnc ψ₀)
    (h3 : ∀ i : Fin L.toSuccession.length,
      (L.toSuccession.boundarySeq F.idealSheaf i.castSucc).HasOnlyNormalCrossingsWith
        (L.toSuccession.center i))
    {J R : IdealSheaf M} (hJR : ∀ p, F.IsBoundaryMonomialAt J R p)
    (hR : L.PullbackIsMonomialAtLast F R) : L.PullbackIsMonomialAtLast F J := by
  classical
  intro x
  have hT : (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).IsBoundaryMonomialAt
      (J.pullback _ (L.toSuccession.stageMap (Fin.last _)).contMDiff)
      (R.pullback _ (L.toSuccession.stageMap (Fin.last _)).contMDiff) x :=
    L.toSuccession.isBoundaryMonomialAt_comap_stageMapAux hF h3 L.toSuccession.length
      (Nat.lt_succ_self _) x (hJR _)
  obtain ⟨s, α, hs, hx⟩ := hT
  obtain ⟨s', β, hs', hx'⟩ := hR x
  refine ⟨s ∪ s', fun j => (if j ∈ s then α j else 0) + (if j ∈ s' then β j else 0),
    fun j hj => ?_, ?_⟩
  · rcases Finset.mem_union.mp hj with h | h
    · exact hs j h
    · exact hs' j h
  · rw [hx, hx']
    simp_rw [pow_add]
    rw [Finset.prod_mul_distrib]
    congr 1
    · refine (Finset.prod_congr rfl fun j hj => ?_).trans
        (Finset.prod_subset Finset.subset_union_left fun j _ hj => ?_)
      · rw [ite_eq_left hj]
      · rw [ite_eq_right hj, pow_zero]
    · refine (Finset.prod_congr rfl fun j hj => ?_).trans
        (Finset.prod_subset Finset.subset_union_right fun j _ hj => ?_)
      · rw [ite_eq_left hj]
      · rw [ite_eq_right hj, pow_zero]

end AnalyticManifold.BlowUpSequence

end
