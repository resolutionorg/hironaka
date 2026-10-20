/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.CoordinateSubspace.ReesInitial
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.Rees.DegreeZero

/-!
# The exceptional divisor of the model blow-up is `ℙ^{r-1}_L`

Setting: `R = A[x_0, …, x_{n-1}]`, `I = (x_0, …, x_{r-1})` with `r ≤ n`, `𝒪(L) = R/I`,
`B = Proj R̃` the model blow-up with charts `U_j = Spec R[I/x_j]`, and `F = V(I·𝒪_B)` the
exceptional divisor.  `Hironaka.Scheme.BlowUp.CoordinateSubspace.ReesInitial` built the graded ring
homomorphism `Φ : R̃ →+*ᵍ 𝒪(L)[u_0, …, u_{r-1}]`, `c t^k ↦ in_k(c)`, surjective in every degree
with kernel `I·R̃`.  This module takes `Proj` of it (Mathlib's `Proj.map`) and shows that
`g = Proj Φ : ℙ^{r-1}_L ⟶ B` is a closed immersion with kernel the exceptional ideal, so that
`F ≅ ℙ^{r-1}_L` (`exists_iso_exceptional_proj`): the exceptional divisor of a blow-up of `𝔸ⁿ` is
the projective space of directions [Hau14, Definitions 4.8–4.10], as in the point blow-up
[Hau14, Example 4.41].  The result is used for the exceptional divisor of a blow-up of a smooth
centre as a projective bundle (`Hironaka.Scheme.Smooth.ExceptionalBundle`).

Everything is checked on the chart cover `U_j`, `j < r`, of `B`:

* On the chart of `x_j` the map `g` is `Spec` of the ring map
  `ψ_j : R[I/x_j] ≅ (R̃_{x_j t})₀ → (𝒪(L)[u]_{u_j})₀`, `c/x_j^k ↦ in_k(c)/u_j^k`
  (`isPullback_chart`: the square is a pullback because `g⁻¹(U_j) = D₊(u_j)`, Mathlib's
  `Proj.awayι_comp_map` and `Proj.map_preimage_basicOpen`).
* `ψ_j` is surjective (`in_k` is surjective onto the forms of degree `k`) and its kernel is
  `x_j·R[I/x_j]`: `in_k(c) = 0` iff `c ∈ I^{k+1}` (`reesInitial_mk_monomial_eq_zero_iff`), i.e.
  iff `c/x_j^k = x_j · c/x_j^{k+1}` (`ker_chartInitialMap`, `ker_chartQuotientMap`); here `u_j`
  is a nonzerodivisor of the polynomial ring, so `F/u_j^k = 0` iff `F = 0`
  (`HomogeneousLocalization.Away.mk_eq_zero_iff_of_isRegular`).
* Hence `g` is a closed immersion (local on the target; `Spec` of a surjection), and its kernel
  agrees on every `U_j` with the exceptional ideal, which on `U_j` is `x_j·R[I/x_j]`
  (`affineBlowUp.comap_exceptionalIdeal_chart`).  Ideal sheaves agreeing on an affine cover agree
  (`le_of_iSup_eq_top`), so `g.ker = I·𝒪_B` (`ker_projInitial`).
* Two closed immersions with the same kernel are isomorphic over `B`
  (`IsClosedImmersion.isIso_lift`); the chart condition is `g⁻¹(U_j) = D₊(u_j)` and the
  compatibility with the projections is `Proj.map_toSpecZero` (`Hironaka.Scheme.BlowUp.Rees.Map`)
  together with `Φ(c) = c̄` on constants.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open Graded reesAlgebra Scheme.IdealSheafData

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A fraction `x / f ^ k` in the homogeneous localization away from a nonzerodivisor `f` is
zero iff `x = 0`. -/
theorem HomogeneousLocalization.Away.mk_eq_zero_iff_of_isRegular {σ A : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hreg : IsRegular f) (k : ℕ) (x : A) (hx : x ∈ 𝒜 (k • d)) :
    HomogeneousLocalization.Away.mk 𝒜 hf k x hx = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h' := congrArg HomogeneousLocalization.val h
    rw [Away.val_mk, val_zero, Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at h'
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := h'
    exact (hreg.pow m).left (show f ^ m * x = f ^ m * 0 by rw [hm, mul_zero])
  · rintro rfl
    exact mk_eq_zero_of_num _ rfl

namespace AlgebraicGeometry.CoordinateSubspace

variable (A : Type u) [CommRing A] (n r : ℕ) (hrn : r ≤ n)

/-! ### The chart of `x_j`: the ring map `R[I/x_j] → (𝒪(L)[u]_{u_j})₀` -/

section Chart

variable (a : centerIdeal A n r)

/-- The initial-form map on the chart ring of `a t`:
`(R̃_{a t})₀ → (𝒪(L)[u]_{Φ(a t)})₀`, `c t^k / (a t)^k ↦ in_k(c) / Φ(a t)^k`. -/
noncomputable def chartInitialMap :
    Away (grading (centerIdeal A n r)) (degreeOne (centerIdeal A n r) a) →+*
      Away (homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r))
        (reesInitialGraded A n r hrn (degreeOne (centerIdeal A n r) a)) :=
  HomogeneousLocalization.Away.map (reesInitialGraded A n r hrn) _

/-- The initial-form map on the chart of `a` is surjective: every form of degree `k` is the
initial form of an element of `I^k t^k`. -/
theorem chartInitialMap_surjective : Function.Surjective (chartInitialMap A n r hrn a) := by
  intro z
  obtain ⟨k, F, hF, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (map_mem (reesInitialGraded A n r hrn) (degreeOne_mem a)) z
  obtain ⟨p, hp, hpF⟩ := exists_reesInitial_eq A n r hrn hF
  refine ⟨HomogeneousLocalization.Away.mk _ (degreeOne_mem a) k p hp, ?_⟩
  rw [chartInitialMap, Away.map_mk]
  subst hpF
  rfl

/-- The initial-form map read on `R[I/a] ≅ (R̃_{a t})₀`: `c/a^k ↦ in_k(c)/Φ(a t)^k`. -/
noncomputable def chartQuotientMap :
    affineBlowUpAlgebra (centerIdeal A n r) a →+*
      Away (homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r))
        (reesInitialGraded A n r hrn (degreeOne (centerIdeal A n r) a)) :=
  (chartInitialMap A n r hrn a).comp (chartRingEquiv a).symm.toRingHom

theorem chartQuotientMap_surjective : Function.Surjective (chartQuotientMap A n r hrn a) :=
  (chartInitialMap_surjective A n r hrn a).comp (chartRingEquiv a).symm.surjective

variable (j : Fin n) (hj : j.val < r) (ha : (a : MvPolynomial (Fin n) A) = X j)
include hj ha

/-- `Φ(x_j t) = u_j` is a nonzerodivisor. -/
theorem isRegular_reesInitialGraded_degreeOne :
    IsRegular (reesInitialGraded A n r hrn (degreeOne (centerIdeal A n r) a)) := by
  obtain ⟨a, hamem⟩ := a
  subst ha
  rw [coe_reesInitialGraded, reesInitial_degreeOne_genX A n r hrn j hj]
  exact isRegular_X

/-- The kernel on the chart of `x_j`: `in_k(c)/u_j^k = 0` iff `c ∈ I^{k+1}` iff
`c t^k/(x_j t)^k` is a multiple of `x_j/1`. -/
theorem ker_chartInitialMap :
    RingHom.ker (chartInitialMap A n r hrn a) =
      Ideal.span
        {fromZeroRingHom (grading (centerIdeal A n r))
          (Submonoid.powers (degreeOne (centerIdeal A n r) a))
          ((gradingZeroEquiv (centerIdeal A n r)).symm (a : MvPolynomial (Fin n) A))} := by
  have hreg := isRegular_reesInitialGraded_degreeOne A n r hrn a j hj ha
  apply le_antisymm
  · intro z hz
    obtain ⟨k, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (degreeOne_mem a) z
    rw [RingHom.mem_ker, chartInitialMap, Away.map_mk,
      Away.mk_eq_zero_iff_of_isRegular _ _ hreg] at hz
    obtain ⟨hpc, hc⟩ := eq_monomial_of_mem_grading hp
    set c := ((p : reesAlgebra (centerIdeal A n r)) : Polynomial (MvPolynomial (Fin n) A)).coeff
      (k • 1) with hc_def
    have hp_eq : p = ⟨Polynomial.monomial (k • 1) c, reesAlgebra.monomial_mem.mpr hc⟩ :=
      Subtype.ext hpc
    have hc' : c ∈ centerIdeal A n r ^ (k • 1 + 1) := by
      rw [← reesInitial_mk_monomial_eq_zero_iff A n r hrn hc, ← hp_eq]
      exact hz
    have hk : (k + 1) • 1 = k • 1 + 1 := by simp
    refine Ideal.mem_span_singleton'.mpr
      ⟨HomogeneousLocalization.Away.mk _ (degreeOne_mem a) (k + 1)
        ⟨Polynomial.monomial (k • 1 + 1) c, reesAlgebra.monomial_mem.mpr hc'⟩
        (mem_grading_of_coe_eq_monomial (by rw [hk])), ?_⟩
    rw [HomogeneousLocalization.ext_iff_val, val_mul, Away.val_mk, Away.val_mk,
      reesAlgebra.val_fromZeroRingHom, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [Submonoid.coe_one, one_mul, mul_one, Subalgebra.coe_mul,
      Subalgebra.coe_pow, reesAlgebra.coe_degreeOne, reesAlgebra.coe_gradingZeroEquiv_symm, hpc,
      Polynomial.monomial_pow, Polynomial.monomial_mul_C, Polynomial.monomial_mul_monomial]
    rw [Polynomial.monomial_eq_monomial_iff]
    left
    refine ⟨?_, by ring⟩
    simp only [smul_eq_mul, mul_one]
    ring
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, chartInitialMap,
      Away.map_fromZeroRingHom]
    have h0 : GradedRingHom.zeroRingHom (reesInitialGraded A n r hrn)
        ((gradingZeroEquiv (centerIdeal A n r)).symm (a : MvPolynomial (Fin n) A)) = 0 := by
      apply Subtype.ext
      rw [GradedRingHom.coe_zeroRingHom_apply, ZeroMemClass.coe_zero]
      change reesInitial A n r hrn (algebraMap _ _ (a : MvPolynomial (Fin n) A)) = 0
      rw [reesInitial_algebraMap, Ideal.Quotient.eq_zero_iff_mem.mpr a.2, C_0]
    rw [h0, map_zero]

/-- On the chart `U_j = Spec R[I/x_j]` the kernel of the initial-form map is
`x_j · R[I/x_j]`. -/
theorem ker_chartQuotientMap :
    RingHom.ker (chartQuotientMap A n r hrn a) =
      Ideal.span
        {algebraMap (MvPolynomial (Fin n) A) (affineBlowUpAlgebra (centerIdeal A n r) a)
          (a : MvPolynomial (Fin n) A)} := by
  ext x
  rw [RingHom.mem_ker, chartQuotientMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, ← RingHom.mem_ker, ker_chartInitialMap A n r hrn a j hj ha,
    Ideal.mem_span_singleton', Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨chartRingEquiv a c, ?_⟩
    rw [← chartRingEquiv_fromZeroRingHom, ← map_mul, hc, RingEquiv.apply_symm_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨(chartRingEquiv a).symm c, ?_⟩
    rw [← chartRingEquiv_fromZeroRingHom, map_mul, RingEquiv.symm_apply_apply]

end Chart

/-! ### `Proj` of the initial-form map -/

/-- The morphism `ℙ^{r-1}_L = Proj 𝒪(L)[u] ⟶ B = Proj R̃`, `Proj` of the
initial-form map `Φ` (Mathlib's `Proj.map`). -/
noncomputable def projInitial :
    Proj (homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)) ⟶
      modelBlowUp A n r :=
  Proj.map (reesInitialGraded A n r hrn) (irrelevant_le_map_reesInitialGraded A n r hrn)

section Chart

variable (a : centerIdeal A n r)

/-- The chart square: on `D₊(Φ(a t))` the morphism `Proj Φ` is `Spec` of the chart-ring map. -/
theorem awayι_projInitial :
    Proj.awayι _ (reesInitialGraded A n r hrn (degreeOne (centerIdeal A n r) a))
        (map_mem (reesInitialGraded A n r hrn) (degreeOne_mem a)) one_pos ≫
      projInitial A n r hrn =
    Spec.map (CommRingCat.ofHom (chartQuotientMap A n r hrn a)) ≫
      affineBlowUp.chart (centerIdeal A n r) a := by
  rw [projInitial, Proj.awayι_comp_map _ _ one_pos _ (degreeOne_mem a), affineBlowUp.chart,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, chartIso,
    chartQuotientMap, chartInitialMap, RingEquiv.toCommRingCatIso_hom, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]

/-- `(Proj Φ)⁻¹(U_a) = D₊(Φ(a t))`. -/
theorem projInitial_preimage_opensRange_chart :
    projInitial A n r hrn ⁻¹ᵁ (affineBlowUp.chart (centerIdeal A n r) a).opensRange =
      (Proj.awayι _ (reesInitialGraded A n r hrn (degreeOne (centerIdeal A n r) a))
        (map_mem (reesInitialGraded A n r hrn) (degreeOne_mem a)) one_pos).opensRange := by
  rw [affineBlowUp.opensRange_chart, Proj.opensRange_awayι]
  exact Proj.map_preimage_basicOpen _ _ _

/-- The chart square is a pullback square. -/
theorem isPullback_chart :
    IsPullback (Spec.map (CommRingCat.ofHom (chartQuotientMap A n r hrn a)))
      (Proj.awayι _ (reesInitialGraded A n r hrn (degreeOne (centerIdeal A n r) a))
        (map_mem (reesInitialGraded A n r hrn) (degreeOne_mem a)) one_pos)
      (affineBlowUp.chart (centerIdeal A n r) a) (projInitial A n r hrn) :=
  IsOpenImmersion.isPullback _ _ _ _ (awayι_projInitial A n r hrn a)
    (projInitial_preimage_opensRange_chart A n r hrn a)

/-- The pullback of `Proj Φ` to the chart of `a` is a closed immersion. -/
theorem isClosedImmersion_pullback_snd_chart :
    IsClosedImmersion (pullback.snd (projInitial A n r hrn)
      (affineBlowUp.chart (centerIdeal A n r) a)) := by
  have H := (isPullback_chart A n r hrn a).flip
  have hsnd : pullback.snd (projInitial A n r hrn) (affineBlowUp.chart (centerIdeal A n r) a) =
      H.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom (chartQuotientMap A n r hrn a)) :=
    (Iso.eq_inv_comp _).mpr H.isoPullback_hom_snd
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (chartQuotientMap A n r hrn a))) :=
    IsClosedImmersion.spec_of_surjective _ (chartQuotientMap_surjective A n r hrn a)
  rw [hsnd]
  infer_instance

end Chart

/-- `Proj Φ : ℙ^{r-1}_L ⟶ B` is a closed immersion — it is one over every chart
`U_j`, `j < r`, where it is `Spec` of the surjection `R[I/x_j] → (𝒪(L)[u]_{u_j})₀`. -/
instance isClosedImmersion_projInitial : IsClosedImmersion (projInitial A n r hrn) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover
    (affineBlowUp.affineOpenCoverOfSpan (centerIdeal A n r) (X '' center n r) rfl).openCover).mpr
    fun y => ?_
  exact isClosedImmersion_pullback_snd_chart A n r hrn _

section Chart

variable (a : centerIdeal A n r) (j : Fin n) (hj : j.val < r)
  (ha : (a : MvPolynomial (Fin n) A) = X j)
include hj ha

/-- On the chart of `x_j`, the kernel of `Proj Φ` pulls back to the ideal `x_j · R[I/x_j]`
(`ker_chartQuotientMap` through the pullback square) — the same ideal as the exceptional ideal
(`affineBlowUp.ideal_comap_exceptionalIdeal_chart_top`). -/
theorem ideal_comap_ker_projInitial_chart_top :
    ((projInitial A n r hrn).ker.comap (affineBlowUp.chart (centerIdeal A n r) a)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {affineBlowUp.chartGenerator (centerIdeal A n r) a} := by
  have h1 : (projInitial A n r hrn).ker.comap (affineBlowUp.chart (centerIdeal A n r) a) =
      (Spec.map (CommRingCat.ofHom (chartQuotientMap A n r hrn a))).ker := by
    rw [← ker_fst_of_isClosedImmersion (projInitial A n r hrn),
      ← (isPullback_chart A n r hrn a).isoPullback_inv_fst, Scheme.Hom.ker_comp_of_isIso]
  rw [h1, Scheme.Hom.ker_apply]
  change RingHom.ker (Spec.map (CommRingCat.ofHom (chartQuotientMap A n r hrn a))).appTop.hom = _
  rw [ker_appTop_Spec_map, CommRingCat.hom_ofHom, ker_chartQuotientMap A n r hrn a j hj ha,
    Ideal.map_span, Set.image_singleton]

/-- The same on the sections over the image of the chart, `U_j = chart ''ᵁ ⊤`: the kernel of
`Proj Φ` and the exceptional ideal agree there. -/
theorem ker_projInitial_ideal_image_chart :
    (projInitial A n r hrn).ker.ideal
        ⟨affineBlowUp.chart (centerIdeal A n r) a ''ᵁ ⊤,
          (isAffineOpen_top _).image_of_isOpenImmersion _⟩ =
      (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).ideal
        ⟨affineBlowUp.chart (centerIdeal A n r) a ''ᵁ ⊤,
          (isAffineOpen_top _).image_of_isOpenImmersion _⟩ := by
  have hk := ideal_comap_of_isOpenImmersion (projInitial A n r hrn).ker
    (affineBlowUp.chart (centerIdeal A n r) a) ⟨⊤, isAffineOpen_top _⟩
  have he := ideal_comap_of_isOpenImmersion (affineBlowUp.exceptionalIdeal (centerIdeal A n r))
    (affineBlowUp.chart (centerIdeal A n r) a) ⟨⊤, isAffineOpen_top _⟩
  have hk' := (ideal_comap_ker_projInitial_chart_top A n r hrn a j hj ha).symm.trans hk
  have he' :=
    (affineBlowUp.ideal_comap_exceptionalIdeal_chart_top (centerIdeal A n r) a).symm.trans he
  have hf : Function.Surjective ((affineBlowUp.chart (centerIdeal A n r) a).appIso ⊤).inv.hom :=
    (ConcreteCategory.bijective_of_isIso _).2
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact ((SetLike.ext_iff.mp hk' y).trans Ideal.mem_comap).symm.trans
    ((SetLike.ext_iff.mp he' y).trans Ideal.mem_comap)

end Chart

/-- The kernel of `Proj Φ : ℙ^{r-1}_L ⟶ B` is the exceptional ideal `I·𝒪_B` — the
two ideal sheaves agree on the affine cover by the charts `U_j`, `j < r`. -/
theorem ker_projInitial :
    (projInitial A n r hrn).ker = affineBlowUp.exceptionalIdeal (centerIdeal A n r) := by
  have hcover : ⨆ y : X '' center n r,
      ((⟨affineBlowUp.chart (centerIdeal A n r) ⟨y.1, Ideal.subset_span y.2⟩ ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion _⟩ : (modelBlowUp A n r).affineOpens) :
          (modelBlowUp A n r).Opens) = ⊤ := by
    simp only [Scheme.Hom.image_top_eq_opensRange]
    exact affineBlowUp.iSup_opensRange_chart_of_span_eq (centerIdeal A n r) (X '' center n r) rfl
  have key : ∀ y : X '' center n r,
      (projInitial A n r hrn).ker.ideal
          ⟨affineBlowUp.chart (centerIdeal A n r) ⟨y.1, Ideal.subset_span y.2⟩ ''ᵁ ⊤,
            (isAffineOpen_top _).image_of_isOpenImmersion _⟩ =
        (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).ideal
          ⟨affineBlowUp.chart (centerIdeal A n r) ⟨y.1, Ideal.subset_span y.2⟩ ''ᵁ ⊤,
            (isAffineOpen_top _).image_of_isOpenImmersion _⟩ := by
    intro y
    obtain ⟨j, hj, hy⟩ := y.2
    exact ker_projInitial_ideal_image_chart A n r hrn ⟨y.1, Ideal.subset_span y.2⟩ j hj hy.symm
  exact le_antisymm (le_of_iSup_eq_top _ hcover fun y => (key y).le)
    (le_of_iSup_eq_top _ hcover fun y => (key y).ge)

/-- The compatibility with the projections: `Proj Φ` followed by the blow-up map
`π : B ⟶ Spec R` is the structure map `ℙ^{r-1}_L ⟶ L = Spec 𝒪(L)` followed by
`L ⟶ Spec R` (`Proj.map_toSpecZero`, and `Φ(c) = c̄` on constants). -/
theorem projInitial_π :
    projInitial A n r hrn ≫ affineBlowUp.π (centerIdeal A n r) =
      Proj.toSpecZero _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)
          (homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) 0))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal A n r))) := by
  rw [projInitial, affineBlowUp.π, Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  apply Subtype.ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    RingEquiv.toCommRingCatIso_hom, RingEquiv.coe_toRingHom,
    GradedRingHom.coe_zeroRingHom_apply, SetLike.GradeZero.coe_algebraMap,
    MvPolynomial.algebraMap_eq]
  exact reesInitial_algebraMap A n r hrn c

include hrn in
/-- **The exceptional divisor `F = V(I·𝒪_B)` of the model blow-up is `ℙ^{r-1}_L`**
[Hau14, Definitions 4.8–4.10]; [Hau14, Example 4.41]: an
isomorphism `F ≅ Proj 𝒪(L)[u_0, …, u_{r-1}]` under which the piece of `F` in the chart `U_j` is
`D₊(u_j)` and which is compatible with the structure maps to `L` and `Spec R`.  The isomorphism is
the lift of the closed immersion `Proj Φ` through `F ⟶ B`, an isomorphism because the two closed
immersions have the same kernel. -/
theorem exists_iso_exceptional_proj :
    ∃ e : (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subscheme ≅
        Proj (homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)),
      (∀ (j : Fin n) (hj : j.val < r),
        e.hom ''ᵁ ((affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι ⁻¹ᵁ
            (modelChart A n r j hj).opensRange) =
          Proj.basicOpen _ (X (⟨j, hj⟩ : Fin r))) ∧
      e.inv ≫ (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι ≫
          affineBlowUp.π (centerIdeal A n r) =
        Proj.toSpecZero _ ≫
          Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)
            (homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) 0))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal A n r))) := by
  have hker : (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι.ker =
      (projInitial A n r hrn).ker := by
    rw [ker_subschemeι, ker_projInitial]
  have : IsIso (IsClosedImmersion.lift
      (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι (projInitial A n r hrn)
      hker.le) :=
    IsClosedImmersion.isIso_lift _ _ hker
  refine ⟨(asIso (IsClosedImmersion.lift _ _ hker.le)).symm, fun j hj => ?_, ?_⟩
  · rw [← Scheme.Hom.inv_preimage, Iso.symm_inv, asIso_hom, ← Scheme.Hom.comp_preimage,
      IsClosedImmersion.lift_fac, opensRange_modelChart, affineBlowUp.opensRange_chart, projInitial,
      Proj.map_preimage_basicOpen, coe_reesInitialGraded, reesInitial_degreeOne_genX]
  · rw [Iso.symm_inv, asIso_hom, IsClosedImmersion.lift_fac_assoc, projInitial_π]

end AlgebraicGeometry.CoordinateSubspace
