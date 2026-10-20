/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Transform.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.ChartGenericFibre
import Hironaka.Algebra.Local.TransformOrder
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Scheme.BlowUp.Composite.Transition
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUp.Transform.WeakTransform
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Exceptional
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.ChartRing
import Hironaka.Scheme.Smooth.LocalBlowUp
import Hironaka.Scheme.Smooth.SubschemeStalk
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.RingTheory.KrullDimension.Field

/-!
# The exceptional order of the total transform is `ord_Z I`

[Kol07, Definition 47]: `ord_Z I` "equals the multiplicity of `π^* I` along the exceptional
divisor"; [Kol07, Definition 60]: the birational transform `π_*^{-1}(I, m)` for `m ≤ ord_Z I`,
whose vanishing order along `Z` is "`m` less than the vanishing order of `I` along `Z`";
[Hau14, §6]: `f^* = h^k f^s` with `k` maximal, "the value of `k` is the order of `f^*` along `E`",
and [Hau14, Definition 6.8], the controlled transform `I^* = I_E^c · I^!`.

* Sharpness, globally: if `ord_Z I = m` exactly then `F^{m+1} ∤ I^*` (`not_pow_succ_dvd_comap`).
  The proof pulls the inequality `I^* ≤ F^{m+1}` back along the local blow-up at the generic point
  `η`, the base change of `B_Z X` along `Spec 𝒪_{X,η} → X` (`exists_isPullback_fromSpecStalk`,
  `Hironaka/Scheme/Smooth/LocalBlowUp.lean`), whose centre is the maximal ideal `𝔪_η = Z_η` (the
  centre is integral, so its local ring at `η` is a field), and then to the chart of the last
  coordinate `y_ρ` of a regular system of parameters (`affineBlowUp.chart`, `affineBlowUp.chart_π`
  and the `specIdealSheaf` calculus of `Hironaka/Scheme/BlowUp/AffineBlowUp/Universal`): on the
  chart ring `R' = 𝒪_{X,η}[𝔪_η/y_ρ]` it reads `I_η R' ≤ (y_ρ)^{m+1}`, which the local computation of
  `Hironaka/Algebra/Local/ChartGenericFibre.lean` (Kollár's expansion `y_ρ^{-m} f(y₁ y_ρ, …)` in the
  proof of [Kol07, Lemma 61]) refutes for an `f ∈ I_η` of order `m`. Only the contravariant
  pull-back of ideal sheaves along the base change is used, no isomorphism of stalks. That `𝒪_{X,η}`
  is not a field, `Z` not being a component, comes from the dimension formula
  `dim 𝒪_{X,η} + trdeg_k κ(η) = n` on `X` and on `Z`
  (`Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension` of
  `Hironaka/Algebra/RegularSmooth/SchemeForms.lean`; `ringKrullDim_stalk_ne_zero`).
* The exceptional order `sup {c : F^c ∣ I^*}` (`exceptionalOrderAlong`) is `ord_Z I`
  (`exceptionalOrderAlong_eq_ord`), from
  `Hironaka/Scheme/IdealSheaf/Order/Exceptional.lean` and the sharpness.
* For `m ≤ ord_Z I`, `F^m · π_*^{-1}(I, m) = I^*` (`pow_mul_controlledTransformAlong`), for
  `m = ord_Z I` the birational transform is the weak transform (`weakTransformAlong_eq`), and
  `F^c ∣ π_*^{-1}(I, m) ⟺ c + m ≤ ord_Z I` (`pow_dvd_controlledTransformAlong_iff`): the
  exceptional order drops by `m`.

Used for the order along a centre in a blow-up sequence
(`Hironaka/Scheme/BlowUpSequence/OrderAlongCenter.lean`).
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

section Generic

variable (Z : X.IdealSheafData) [IsIntegral Z.subscheme] {η : X}
  (hη : IsGenericPoint η (Z.support : Set X))

include hη

/-- The generic point of the subscheme of an integral center maps to the generic point of its
support. -/
theorem subschemeι_genericPoint_eq : Z.subschemeι (genericPoint Z.subscheme) = η := by
  have h1 := (genericPoint_spec Z.subscheme).image Z.subschemeι.continuous
  rw [Set.image_univ, Z.range_subschemeι, Z.support.isClosed.closure_eq] at h1
  exact h1.eq hη

/-- At the generic point of an integral center the ideal of the center is the maximal ideal: the
local ring of `Z` at its generic point is a field (Mathlib's function field). -/
theorem stalkIdeal_eq_maximalIdeal_of_isGenericPoint :
    Z.stalkIdeal η = maximalIdeal (X.presheaf.stalk η) := by
  have hp := subschemeι_genericPoint_eq Z hη
  have hfield : IsField (Z.subscheme.presheaf.stalk (genericPoint Z.subscheme)) :=
    Field.toIsField Z.subscheme.functionField
  have hq := (stalkQuotientEquiv Z (genericPoint Z.subscheme)).toMulEquiv.isField hfield
  have hmax := Ideal.Quotient.maximal_of_isField _ hq
  rw [← hp]
  exact IsLocalRing.eq_maximalIdeal hmax

end Generic

section Global

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n r : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
  [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hr : 1 ≤ r) (hrn : r ≤ n)
  (I : X.IdealSheafData) {η : X} (hη : IsGenericPoint η (Z.support : Set X))

include f n r hr hrn hη

omit I in
/-- `Z` is not a component of `X`: the local ring of `X` at the generic point of `Z` is not a field
(the dimension formula on `X` and on `Z`: `dim 𝒪_{X,η} = n − trdeg κ(η) = n − (n − r) = r ≥ 1`). -/
theorem ringKrullDim_stalk_ne_zero : ringKrullDim (X.presheaf.stalk η) ≠ 0 := by
  classical
  have hsm : Smooth (Z.subschemeι ≫ f) := SmoothOfRelativeDimension.smooth (n - r) _
  have hint : IsIntegral Z.subscheme := isIntegral_subscheme_of_smooth f Z hη
  have hp := subschemeι_genericPoint_eq Z hη
  set p := genericPoint Z.subscheme with hpdef
  subst hp
  let := f.stalkAlgebra (Z.subschemeι p)
  let := (Z.subschemeι ≫ f).stalkAlgebra p
  have hX := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension f n
    (Z.subschemeι p)
  have hZ := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension
    (Z.subschemeι ≫ f) (n - r) p
  have h0 : ringKrullDim (Z.subscheme.presheaf.stalk p) = 0 :=
    ringKrullDim_eq_zero_of_isField (Field.toIsField Z.subscheme.functionField)
  -- the residue fields are isomorphic `k`-algebras
  let e : ResidueField (X.presheaf.stalk (Z.subschemeι p)) ≃ₐ[k]
      ResidueField (Z.subscheme.presheaf.stalk p) :=
    AlgEquiv.ofRingEquiv (f := residueFieldStalkEquiv Z p) fun c => by
      change ResidueField.map (Z.subschemeι.stalkMap p).hom
        (residue _ (algebraMap k (X.presheaf.stalk (Z.subschemeι p)) c)) =
        residue _ (algebraMap k (Z.subscheme.presheaf.stalk p) c)
      rw [ResidueField.map_residue, stalkMap_subschemeι_algebraMap Z f p c]
  have htr := e.trdeg_eq
  intro hdim
  rw [hdim, zero_add, htr] at hX
  rw [h0, zero_add] at hZ
  rw [hZ] at hX
  have : n = n - r := by exact_mod_cast hX.symm
  omega

/-- Sharpness (the expansion in the proof of [Kol07, Lemma 61]; [Hau14, §6], `k` maximal): if
`ord_Z I = m` exactly then `F^{m+1}` does not divide `I^*`. -/
theorem not_pow_succ_dvd_comap (m : ℕ) (hm : I.ord η = m) :
    ¬ (Z.comap (blowUpπ Z)) ^ (m + 1) ∣ I.comap (blowUpπ Z) := by
  classical
  intro hdvd
  have hsmX : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hsm : Smooth (Z.subschemeι ≫ f) := SmoothOfRelativeDimension.smooth (n - r) _
  have hint : IsIntegral Z.subscheme := isIntegral_subscheme_of_smooth f Z hη
  have hle : I.comap (blowUpπ Z) ≤ (Z.comap (blowUpπ Z)) ^ (m + 1) := le_pow_of_pow_dvd hdvd
  obtain ⟨φ, H⟩ := exists_isPullback_fromSpecStalk Z η
  -- pull back along the local blow-up at `η`
  have h1 : (specIdealSheaf (I.stalkIdeal η)).comap (affineBlowUp.π (Z.stalkIdeal η)) ≤
      ((specIdealSheaf (Z.stalkIdeal η)).comap (affineBlowUp.π (Z.stalkIdeal η))) ^ (m + 1) := by
    have h : (I.comap (blowUpπ Z)).comap φ ≤ ((Z.comap (blowUpπ Z)) ^ (m + 1)).comap φ :=
      comap_mono φ hle
    rwa [comap_pow, ← comap_comp, ← comap_comp, H.w, comap_comp, comap_comp,
      comap_fromSpecStalk_eq_specIdealSheaf,
      comap_fromSpecStalk_eq_specIdealSheaf] at h
  -- adapted parameters at `η`; the center is `𝔪_η`
  obtain ⟨m', y, hm', hy, -⟩ := exists_adaptedParameters Z f n r hrn hη.mem
  have hZmax : Z.stalkIdeal η = maximalIdeal (X.presheaf.stalk η) :=
    stalkIdeal_eq_maximalIdeal_of_isGenericPoint Z hη
  have hm'pos : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h0 | h0
    · exfalso
      apply ringKrullDim_stalk_ne_zero f n r Z hr hrn hη
      rw [← hm', h0]
      rfl
    · exact h0
  let ρ : Fin m' := ⟨m' - 1, by omega⟩
  have hρ : ρ.val + 1 = m' := by
    change m' - 1 + 1 = m'
    omega
  have hcenter : Z.stalkIdeal η = chartCenter y ρ := by
    rw [hZmax, hy, chartCenter]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      change i.val ≤ m' - 1
      have := i.2
      omega
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  have hmem : y ρ ∈ Z.stalkIdeal η :=
    hcenter ▸ Ideal.subset_span ⟨ρ, show ρ ≤ ρ from le_rfl, rfl⟩
  -- restrict to the chart of `y_ρ`
  have h2 : ((specIdealSheaf (I.stalkIdeal η)).comap (affineBlowUp.π (Z.stalkIdeal η))).comap
        (affineBlowUp.chart (Z.stalkIdeal η) ⟨y ρ, hmem⟩) ≤
      (((specIdealSheaf (Z.stalkIdeal η)).comap (affineBlowUp.π (Z.stalkIdeal η))) ^ (m + 1)).comap
        (affineBlowUp.chart (Z.stalkIdeal η) ⟨y ρ, hmem⟩) :=
    comap_mono (affineBlowUp.chart (Z.stalkIdeal η) ⟨y ρ, hmem⟩) h1
  rw [comap_pow, ← comap_comp, ← comap_comp, affineBlowUp.chart_π, comap_specIdealSheaf_Spec_map,
    comap_specIdealSheaf_Spec_map, ← specIdealSheaf_pow, specIdealSheaf_le_iff] at h2
  -- an element of `I_η` of order `m`
  have hreg := isRegularLocalRing_stalk f η
  have hordI : IsLocalRing.ord (I.stalkIdeal η) = m := by
    rw [← ord_eq_ord_stalkIdeal]
    exact hm
  obtain ⟨g, hgI, hgm⟩ := exists_mem_ordElem_eq_of_ord_eq hordI
  have h3 := h2 (Ideal.mem_map_of_mem _ hgI)
  -- read on the chart ring
  have hC : affineBlowUpAlgebra (Z.stalkIdeal η) (y ρ) = chartRing y ρ := by
    rw [hcenter]
    exact affineBlowUpAlgebra_span_eq_chartRing y ρ
  have key : ∀ C : Subalgebra (X.presheaf.stalk η) (Localization.Away (y ρ)), C = chartRing y ρ →
      algebraMap _ C g ∉ ((Z.stalkIdeal η).map (algebraMap _ C)) ^ (m + 1) := by
    rintro C rfl h
    rw [hcenter, map_chartCenter] at h
    exact algebraMap_notMem_span_pow_succ y hy hm' ρ hρ g m hgm h
  exact key _ hC h3

/-- [Kol07, Definition 47]; [Hau14, §6]: the exceptional order of `I^*` — the largest `c` with
`F^c ∣ I^*` — is `ord_Z I`, for `I_η ≠ 0`. -/
theorem exceptionalOrderAlong_eq_ord (hI : I.ord η ≠ ⊤) :
    (exceptionalOrderAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) I : ℕ∞) = I.ord η := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hI
  rw [ENat.some_eq_natCast] at hm
  rw [← hm]
  congr 1
  unfold exceptionalOrderAlong
  refine IsGreatest.csSup_eq ⟨?_, ?_⟩
  · exact exceptionalDivisor_pow_dvd_comap_of_le_ord f n r Z hr hrn I hη m hm.le
  · intro c hc
    by_contra hlt
    exact not_pow_succ_dvd_comap f n r Z hr hrn I hη m hm.symm
      (dvd_trans (pow_dvd_pow _ (Nat.succ_le_of_lt (not_le.mp hlt))) hc)

/-- [Kol07, (60.1)]; [Hau14, Definition 6.8]: for `m ≤ ord_Z I`, `F^m · π_*^{-1}(I, m) = I^*`. -/
theorem pow_mul_controlledTransformAlong (m : ℕ) (hm : (m : ℕ∞) ≤ I.ord η) :
    (Z.comap (blowUpπ Z)) ^ m *
        I.controlledTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) m =
      I.comap (blowUpπ Z) :=
  pow_mul_colon_of_dvd _ _ _
    (exceptionalDivisor_pow_dvd_comap_of_le_ord f n r Z hr hrn I hη m hm)

/-- [Kol07, Definition 60]; [Hau14, Definition 6.8]: for `m = ord_Z I` the birational transform
is the weak transform. -/
theorem weakTransformAlong_eq (m : ℕ) (hm : I.ord η = m) :
    I.weakTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) =
      I.controlledTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) m := by
  unfold weakTransformAlong
  congr 1
  have h := exceptionalOrderAlong_eq_ord f n r Z hr hrn I hη
    (by rw [hm]; exact ENat.natCast_ne_top m)
  rw [hm] at h
  exact_mod_cast h

/-- [Kol07, Definition 60], "`m` less": for `m ≤ ord_Z I`, `F^c` divides `π_*^{-1}(I, m)` exactly
when `c + m ≤ ord_Z I`. -/
theorem pow_dvd_controlledTransformAlong_iff (m : ℕ) (hm : (m : ℕ∞) ≤ I.ord η) (c : ℕ) :
    (Z.comap (blowUpπ Z)) ^ c ∣
        I.controlledTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)) m ↔
      ((c + m : ℕ) : ℕ∞) ≤ I.ord η := by
  have hinv := (blowUp.isBlowUp Z).admissible
  have hFm := pow_mul_controlledTransformAlong f n r Z hr hrn I hη m hm
  constructor
  · rintro ⟨K, hK⟩
    have h1 : I.comap (blowUpπ Z) = (Z.comap (blowUpπ Z)) ^ (c + m) * K := by
      rw [← hFm, hK, pow_add, mul_comm ((Z.comap (blowUpπ Z)) ^ c) ((Z.comap (blowUpπ Z)) ^ m),
        mul_assoc]
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨m₀, hm₀⟩ := WithTop.ne_top_iff_exists.mp hlt.ne_top
    rw [ENat.some_eq_natCast] at hm₀
    have hlt' : m₀ < c + m := by
      rw [← hm₀] at hlt
      exact Nat.cast_lt.mp hlt
    exact not_pow_succ_dvd_comap f n r Z hr hrn I hη m₀ hm₀.symm
      (dvd_trans (pow_dvd_pow _ (Nat.succ_le_of_lt hlt')) ⟨K, h1⟩)
  · intro hle
    obtain ⟨K, hK⟩ := exceptionalDivisor_pow_dvd_comap_of_le_ord f n r Z hr hrn I hη (c + m) hle
    refine ⟨K, ?_⟩
    exact colon_pow_eq_of_mul_eq _ hinv m ((Z.comap (blowUpπ Z)) ^ c * K)
      (by rw [← mul_assoc, ← pow_add, Nat.add_comm m c, ← hK])

end Global

end AlgebraicGeometry
