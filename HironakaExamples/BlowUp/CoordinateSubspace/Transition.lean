/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.CoordinateSubspace.Charts

/-!
# The chart transitions of the model blow-up

The charts `U_j` and `U_ℓ` of `B_L 𝔸ⁿ_A` are glued along the transition map `x_i ↦ x_i/x_ℓ`
(`i ∈ J ∖ {j, ℓ}`), `x_j ↦ 1/x_ℓ`, `x_ℓ ↦ x_j x_ℓ`, `x_i ↦ x_i` (`i ∉ J`) [Hau14, Definition 4.12];
Hauser prints the first line as `x_i ↦ x_i/x_j`, the formula for the opposite direction, and the
form used here is the one for the coordinates of `U_ℓ` as functions on `D(x_ℓ) ⊆ U_j`.  Since the
blow-up is already glued (Mathlib's `Proj` of the Rees algebra), the statement is the
compatibility `Spec (A[x] → A[x]_{x_ℓ}) ≫ U_j = Spec (τ_{jℓ}) ≫ U_ℓ` on the overlap `D(x_ℓ) ⊆ U_j`
(`modelTransition_spec`).  The proof goes through Mathlib's chart of `D₊(f g)`, `f = x_j t`,
`g = x_ℓ t` (`Proj.SpecMap_awayMap_awayι`: the chart of `f g` is the chart of `f` restricted along
`awayMap`, and likewise for `g`): the ring `(R̃_{fg})₀` is the localization of `(R̃_f)₀ ≃ A[x]` at
`g/f ↦ x_ℓ` (`Away.isLocalization_mul`), which identifies it with `A[x]_{x_ℓ}` (`θ`); under `θ` the
restriction from the chart of `f` is the localization map (by construction), and the restriction
from the chart of `g` is Hauser's `τ_{jℓ}` — checked on the generators of `(R̃_g)₀ ≃ A[x]`, where
the only computation is `(x_i t / x_ℓ t) · (x_ℓ t / x_j t) = x_i t / x_j t` in `(R̃_{fg})₀`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.BlowUp.CoordinateSubspace

open AlgebraicGeometry.CoordinateSubspace

open affineBlowUpAlgebra reesAlgebra

variable (A : Type u) [CommRing A] (n r : ℕ)

section Setup

variable (j : Fin n) (hj : j.val < r)

/-- The generator `x_j` as an element of the center ideal. -/
noncomputable abbrev genX : centerIdeal A n r := ⟨X j, X_mem_centerIdeal A n r hj⟩

/-- The chart ring of `x_j`, `(R̃_{x_j t})₀ ≃ A[x]`, through the chart of the affine blow-up and the
identification of `Hironaka.Scheme.BlowUp.Model`. -/
noncomputable def chartAwayEquiv :
    Away (grading (centerIdeal A n r)) (degreeOne (centerIdeal A n r) (genX A n r j hj)) ≃+*
      MvPolynomial (Fin n) A :=
  (chartRingEquiv (genX A n r j hj)).trans
    (coordinateSubspaceEquiv A (center n r) j).toRingEquiv

theorem modelChart_eq :
    modelChart A n r j hj =
      Spec.map (CommRingCat.ofHom (chartAwayEquiv A n r j hj).toRingHom) ≫
        Proj.awayι (grading (centerIdeal A n r)) (degreeOne (centerIdeal A n r) (genX A n r j hj))
          (degreeOne_mem _) one_pos := by
  rw [modelChart, affineBlowUp.chart, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- `chartAwayEquiv` on the fraction `x_i t / x_j t`: the variable `x_i` (`i < r`, `i ≠ j`). -/
theorem chartAwayEquiv_isLocalizationElem {i : Fin n} (hi : i.val < r) (hij : i ≠ j) :
    chartAwayEquiv A n r j hj
        (Away.isLocalizationElem (degreeOne_mem (genX A n r j hj))
          (degreeOne_mem (genX A n r i hi))) = X i := by
  rw [chartAwayEquiv, RingEquiv.trans_apply, chartRingEquiv_isLocalizationElem,
    AlgEquiv.coe_ringEquiv, ratio_eq_frac A n r j i hj hi]
  exact coordinateSubspaceEquiv_frac A (center n r) j hi hij _

/-- `chartAwayEquiv` on a constant `p ∈ R`: the chart map `π_j` applied to `p`. -/
theorem chartAwayEquiv_fromZeroRingHom (p : MvPolynomial (Fin n) A) :
    chartAwayEquiv A n r j hj (fromZeroRingHom (grading (centerIdeal A n r)) _
      ((gradingZeroEquiv (centerIdeal A n r)).symm p)) = chartSubst A (center n r) j p := by
  rw [chartAwayEquiv, RingEquiv.trans_apply, chartRingEquiv_fromZeroRingHom, AlgEquiv.coe_ringEquiv]
  have := congrArg (fun φ : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) A => φ p)
    (chartRingIso_hom_comp_algebraMap A n r j)
  simpa [chartRingIso] using this

end Setup

section Gluing

/-- `mul_comm` stated over `[CommRing R]`, so that both sides carry the `Mul` instance path of a
`CommRing` binder — the path in the statements of Mathlib's `Proj` lemmas.  (Elaborating
`mul_comm` itself against such a statement on the Rees algebra, a `Subalgebra` of `A[x][t]`,
unifies the `CommMagma` path with the ring path and times out at the pinned Mathlib version.) -/
theorem mul_comm_commRing {R : Type*} [CommRing R] (a b : R) : a * b = b * a := mul_comm a b

/-- Mathlib's `Proj.SpecMap_awayMap_awayι` with the membership `x ∈ 𝒜 (m + m')` taken as a
hypothesis instead of transported along `hx` (`hx ▸ SetLike.mul_mem_graded f_deg g_deg`).  Stated
for variables `f g x`; instantiated at the generators of the Rees algebra its conclusion carries no
cast.  At the pinned Mathlib version the kernel, before using proof irrelevance on a stuck
`hx ▸ _`, tries to reduce it by K-reduction, which tests `x ≡ f * g` definitionally — for products
of the degree-one generators of the Rees algebra that test unfolds through `Polynomial`,
`AddMonoidAlgebra` and `Finsupp` and does not finish. -/
theorem specMap_awayMap_awayι' {σ B : Type*} [CommRing B] [SetLike σ B] [AddSubgroupClass σ B]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g x : B} {m m' : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (g_deg : g ∈ 𝒜 m') (hx : x = f * g) (hx' : x ∈ 𝒜 (m + m')) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) ≫ Proj.awayι 𝒜 f f_deg hm =
      Proj.awayι 𝒜 x hx' (hm.trans_le (m.le_add_right m')) :=
  Proj.SpecMap_awayMap_awayι 𝒜 f_deg hm g_deg hx

variable (j ℓ : Fin n) (hj : j.val < r) (hℓ : ℓ.val < r)

/-- Commutation of the two degree-one generators `x_j t`, `x_ℓ t` of the Rees algebra. -/
theorem degreeOne_mul_comm :
    degreeOne (centerIdeal A n r) (genX A n r j hj) *
        degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ) =
      degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ) *
        degreeOne (centerIdeal A n r) (genX A n r j hj) :=
  mul_comm_commRing _ _

/-- The element `t = x_ℓ t / x_j t` of the chart ring of `x_j`, at which the overlap chart ring is
the localization. -/
noncomputable abbrev overlapElem :
    Away (grading (centerIdeal A n r)) (degreeOne (centerIdeal A n r) (genX A n r j hj)) :=
  Away.isLocalizationElem (degreeOne_mem (genX A n r j hj)) (degreeOne_mem (genX A n r ℓ hℓ))

theorem chartAwayEquiv_overlapElem (hjℓ : j ≠ ℓ) :
    chartAwayEquiv A n r j hj (overlapElem A n r j ℓ hj hℓ) = X ℓ :=
  chartAwayEquiv_isLocalizationElem A n r j hj hℓ (Ne.symm hjℓ)

/-- The overlap chart ring `(R̃_{fg})₀`, `f = x_j t`, `g = x_ℓ t`. -/
noncomputable abbrev overlapAway : Type u :=
  Away (grading (centerIdeal A n r))
    (degreeOne (centerIdeal A n r) (genX A n r j hj) *
      degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ))

/-- The overlap chart ring as the localization of the chart ring of `x_j` at `t`. -/
noncomputable local instance overlapAlgebra :
    Algebra (Away (grading (centerIdeal A n r)) (degreeOne (centerIdeal A n r) (genX A n r j hj)))
      (overlapAway A n r j ℓ hj hℓ) :=
  (awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r ℓ hℓ)) rfl).toAlgebra

theorem isLocalization_overlap :
    IsLocalization.Away (overlapElem A n r j ℓ hj hℓ) (overlapAway A n r j ℓ hj hℓ) :=
  Away.isLocalization_mul (degreeOne_mem (genX A n r j hj)) (degreeOne_mem (genX A n r ℓ hℓ)) rfl
    one_ne_zero

theorem map_powers_overlapElem (hjℓ : j ≠ ℓ) :
    (Submonoid.powers (overlapElem A n r j ℓ hj hℓ)).map (chartAwayEquiv A n r j hj).toMonoidHom =
      Submonoid.powers (X ℓ : MvPolynomial (Fin n) A) := by
  rw [Submonoid.map_powers]
  congr 1
  exact chartAwayEquiv_overlapElem A n r j ℓ hj hℓ hjℓ

/-- The identification of the overlap chart ring with `A[x]_{x_ℓ}` (the functions on
`D(x_ℓ) ⊆ U_j`). -/
noncomputable def overlapEquiv (hjℓ : j ≠ ℓ) :
    overlapAway A n r j ℓ hj hℓ ≃+* Localization.Away (X ℓ : MvPolynomial (Fin n) A) :=
  have := isLocalization_overlap A n r j ℓ hj hℓ
  IsLocalization.ringEquivOfRingEquiv (overlapAway A n r j ℓ hj hℓ)
    (Localization.Away (X ℓ : MvPolynomial (Fin n) A)) (chartAwayEquiv A n r j hj)
    (map_powers_overlapElem A n r j ℓ hj hℓ hjℓ)

theorem overlapEquiv_awayMap (hjℓ : j ≠ ℓ)
    (z : Away (grading (centerIdeal A n r)) (degreeOne (centerIdeal A n r) (genX A n r j hj))) :
    overlapEquiv A n r j ℓ hj hℓ hjℓ
        (awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r ℓ hℓ)) rfl z) =
      algebraMap (MvPolynomial (Fin n) A) (Localization.Away (X ℓ : MvPolynomial (Fin n) A))
        (chartAwayEquiv A n r j hj z) := by
  have := isLocalization_overlap A n r j ℓ hj hℓ
  exact IsLocalization.ringEquivOfRingEquiv_eq (map_powers_overlapElem A n r j ℓ hj hℓ hjℓ) z

/-- The left-hand side of the gluing identity, written through `θ` and the restriction from the
chart of `x_j` to the chart of `f g`. -/
theorem left_factor (hjℓ : j ≠ ℓ) :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) A)
        (Localization.Away (X ℓ : MvPolynomial (Fin n) A)))) ≫ modelChart A n r j hj =
      Spec.map (CommRingCat.ofHom (overlapEquiv A n r j ℓ hj hℓ hjℓ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r ℓ hℓ)) rfl)) ≫
        Proj.awayι (grading (centerIdeal A n r)) (degreeOne (centerIdeal A n r) (genX A n r j hj))
          (degreeOne_mem _) one_pos := by
  rw [modelChart_eq, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (overlapEquiv_awayMap A n r j ℓ hj hℓ hjℓ z).symm

/-- `θ` on the constants of the overlap chart ring: through the chart ring of `x_j`. -/
theorem overlapEquiv_fromZeroRingHom (hjℓ : j ≠ ℓ) (c : grading (centerIdeal A n r) 0) :
    overlapEquiv A n r j ℓ hj hℓ hjℓ (fromZeroRingHom (grading (centerIdeal A n r)) _ c) =
      algebraMap (MvPolynomial (Fin n) A) (Localization.Away (X ℓ : MvPolynomial (Fin n) A))
        (chartAwayEquiv A n r j hj (fromZeroRingHom (grading (centerIdeal A n r)) _ c)) := by
  conv_lhs => rw [← awayMap_fromZeroRingHom (grading (centerIdeal A n r))
    (degreeOne_mem (genX A n r ℓ hℓ)) rfl c]
  exact overlapEquiv_awayMap A n r j ℓ hj hℓ hjℓ _

/-- The fraction `f/f` is `1`. -/
theorem isLocalizationElem_self {i : Fin n} (hi : i.val < r) :
    Away.isLocalizationElem (degreeOne_mem (genX A n r i hi)) (degreeOne_mem (genX A n r i hi)) =
      (1 : Away (grading (centerIdeal A n r))
        (degreeOne (centerIdeal A n r) (genX A n r i hi))) := by
  ext
  rw [val_one, Away.isLocalizationElem, Away.val_mk]
  exact Localization.mk_self
    (⟨degreeOne (centerIdeal A n r) (genX A n r i hi) ^ 1,
      Submonoid.pow_mem _ (Submonoid.mem_powers _) 1⟩ :
      Submonoid.powers (degreeOne (centerIdeal A n r) (genX A n r i hi)))

/-- The key computation in the overlap chart ring:
`(x_i t / x_ℓ t) · (x_ℓ t / x_j t) = x_i t / x_j t`. -/
theorem awayMap_isLocalizationElem_mul {i : Fin n} (hi : i.val < r) :
    awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r j hj))
        (degreeOne_mul_comm A n r j ℓ hj hℓ)
        (Away.isLocalizationElem (degreeOne_mem (genX A n r ℓ hℓ))
          (degreeOne_mem (genX A n r i hi))) *
      awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r ℓ hℓ)) rfl
        (overlapElem A n r j ℓ hj hℓ) =
      awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r ℓ hℓ)) rfl
        (Away.isLocalizationElem (degreeOne_mem (genX A n r j hj))
          (degreeOne_mem (genX A n r i hi))) := by
  ext
  rw [val_mul, overlapElem, Away.isLocalizationElem, Away.isLocalizationElem,
    Away.isLocalizationElem, Away.mk, Away.mk, Away.mk, val_awayMap_mk, val_awayMap_mk,
    val_awayMap_mk, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_one, Submonoid.coe_mul]
  ring

/-- `θ` on the image of the ratio `x_i t / x_ℓ t` of the chart ring of `x_ℓ`: `x_i / x_ℓ` for
`i ≠ j`, and `1/x_ℓ` for `i = j`. -/
theorem overlapEquiv_awayMap_isLocalizationElem (hjℓ : j ≠ ℓ) {i : Fin n} (hi : i.val < r) :
    overlapEquiv A n r j ℓ hj hℓ hjℓ
        (awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r j hj))
          (degreeOne_mul_comm A n r j ℓ hj hℓ)
          (Away.isLocalizationElem (degreeOne_mem (genX A n r ℓ hℓ))
            (degreeOne_mem (genX A n r i hi)))) =
      algebraMap (MvPolynomial (Fin n) A) (Localization.Away (X ℓ : MvPolynomial (Fin n) A))
          (chartAwayEquiv A n r j hj (Away.isLocalizationElem (degreeOne_mem (genX A n r j hj))
            (degreeOne_mem (genX A n r i hi)))) *
        IsLocalization.Away.invSelf (X ℓ : MvPolynomial (Fin n) A) := by
  have h := congrArg (overlapEquiv A n r j ℓ hj hℓ hjℓ)
    (awayMap_isLocalizationElem_mul A n r j ℓ hj hℓ hi)
  rw [map_mul, overlapEquiv_awayMap, overlapEquiv_awayMap,
    chartAwayEquiv_overlapElem A n r j ℓ hj hℓ hjℓ] at h
  rw [← h, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

/-- The core: under `θ`, the restriction from the chart of `x_ℓ` to the overlap is
Hauser's transition map, checked on the generators of the chart ring `(R̃_{x_ℓ t})₀ ≃ A[x]`. -/
theorem right_factor (hjℓ : j ≠ ℓ) :
    (modelTransition A n r j ℓ).toRingHom.comp (chartAwayEquiv A n r ℓ hℓ).toRingHom =
      (overlapEquiv A n r j ℓ hj hℓ hjℓ).toRingHom.comp
        (awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r j hj))
          (mul_comm _ _)) := by
  set θ := overlapEquiv A n r j ℓ hj hℓ hjℓ
  set ψℓ := chartAwayEquiv A n r ℓ hℓ
  set aw := awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r j hj))
    (degreeOne_mul_comm A n r j ℓ hj hℓ)
  -- it suffices to compare the two maps after precomposition with `ψℓ⁻¹`, on the generators
  suffices key : (modelTransition A n r j ℓ).toRingHom =
      (θ.toRingHom.comp aw).comp ψℓ.symm.toRingHom by
    refine RingHom.ext fun w => ?_
    have := RingHom.congr_fun key (ψℓ w)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
    rw [RingEquiv.symm_apply_apply] at this
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact this
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · -- constants
    have hψ : ψℓ.symm (C a) = fromZeroRingHom (grading (centerIdeal A n r)) _
        ((gradingZeroEquiv (centerIdeal A n r)).symm (C a)) := by
      rw [RingEquiv.symm_apply_eq, chartAwayEquiv_fromZeroRingHom, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [hψ, awayMap_fromZeroRingHom, overlapEquiv_fromZeroRingHom, chartAwayEquiv_fromZeroRingHom,
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  · -- generators
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [modelTransition_X]
    by_cases hiS : i.val < r ∧ i ≠ ℓ
    · -- `x_i`, `i < r`, `i ≠ ℓ`: the ratio `x_i t / x_ℓ t`
      have hψ : ψℓ.symm (X i) = Away.isLocalizationElem (degreeOne_mem (genX A n r ℓ hℓ))
          (degreeOne_mem (genX A n r i hiS.1)) := by
        rw [RingEquiv.symm_apply_eq]
        exact (chartAwayEquiv_isLocalizationElem A n r ℓ hℓ hiS.1 hiS.2).symm
      rw [hψ, overlapEquiv_awayMap_isLocalizationElem A n r j ℓ hj hℓ hjℓ hiS.1, ite_eq_right hiS.2]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, isLocalizationElem_self, map_one, map_one, one_mul]
      · rw [ite_eq_right hij, ite_eq_left hiS.1,
          chartAwayEquiv_isLocalizationElem A n r j hj hiS.1 hij]
    · -- `x_ℓ` and the variables outside the center: constants of the chart ring
      have hψ : ψℓ.symm (X i) = fromZeroRingHom (grading (centerIdeal A n r)) _
          ((gradingZeroEquiv (centerIdeal A n r)).symm (X i)) := by
        rw [RingEquiv.symm_apply_eq, chartAwayEquiv_fromZeroRingHom, chartSubst_X_of_not A _ ℓ hiS]
      rw [hψ, awayMap_fromZeroRingHom, overlapEquiv_fromZeroRingHom, chartAwayEquiv_fromZeroRingHom]
      by_cases hiℓ : i = ℓ
      · subst hiℓ
        rw [ite_eq_left rfl, chartSubst_X_of_mem A (center n r) j hℓ (Ne.symm hjℓ), mul_comm]
      · have hir : ¬ i.val < r := fun h => hiS ⟨h, hiℓ⟩
        have hij : i ≠ j := fun h => hir (h ▸ hj)
        rw [ite_eq_right hiℓ, ite_eq_right hij, ite_eq_right hir,
          chartSubst_X_of_not A (center n r) j (fun h => hir h.1)]

/-- The left-hand side of the gluing identity through the chart of `f g`. -/
theorem lhs_factor (hjℓ : j ≠ ℓ) :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) A)
        (Localization.Away (X ℓ : MvPolynomial (Fin n) A)))) ≫ modelChart A n r j hj =
      Spec.map (CommRingCat.ofHom (overlapEquiv A n r j ℓ hj hℓ hjℓ).toRingHom) ≫
        Proj.awayι (grading (centerIdeal A n r))
          (degreeOne (centerIdeal A n r) (genX A n r j hj) *
            degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ))
          (SetLike.mul_mem_graded (degreeOne_mem _) (degreeOne_mem _))
          (one_pos.trans_le (Nat.le_add_right 1 1)) := by
  rw [left_factor A n r j ℓ hj hℓ hjℓ, Proj.SpecMap_awayMap_awayι (grading (centerIdeal A n r))
    (degreeOne_mem (genX A n r j hj)) one_pos (degreeOne_mem (genX A n r ℓ hℓ)) rfl]

/-- The right factorization at the level of `CommRingCat` morphisms. -/
theorem ofHom_chartAwayEquiv_comp_ofHom_modelTransition (hjℓ : j ≠ ℓ) :
    CommRingCat.ofHom (chartAwayEquiv A n r ℓ hℓ).toRingHom ≫
        CommRingCat.ofHom (modelTransition A n r j ℓ).toRingHom =
      CommRingCat.ofHom (awayMap (grading (centerIdeal A n r)) (degreeOne_mem (genX A n r j hj))
          (degreeOne_mul_comm A n r j ℓ hj hℓ)) ≫
        CommRingCat.ofHom (overlapEquiv A n r j ℓ hj hℓ hjℓ).toRingHom := by
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
    CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
  exact right_factor A n r j ℓ hj hℓ hjℓ

/-- The right-hand side, rewritten through the chart of `x_ℓ`. -/
theorem rhs_step₁ :
    Spec.map (CommRingCat.ofHom (modelTransition A n r j ℓ).toRingHom) ≫ modelChart A n r ℓ hℓ =
      Spec.map (CommRingCat.ofHom (chartAwayEquiv A n r ℓ hℓ).toRingHom ≫
          CommRingCat.ofHom (modelTransition A n r j ℓ).toRingHom) ≫
        Proj.awayι (grading (centerIdeal A n r))
          (degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ)) (degreeOne_mem _) one_pos := by
  rw [modelChart_eq A n r ℓ hℓ, Spec.map_comp, Category.assoc]

/-- The right-hand side, through the overlap chart ring (first half). -/
theorem rhs_step₂ (hjℓ : j ≠ ℓ) :
    Spec.map (CommRingCat.ofHom (chartAwayEquiv A n r ℓ hℓ).toRingHom ≫
          CommRingCat.ofHom (modelTransition A n r j ℓ).toRingHom) ≫
        Proj.awayι (grading (centerIdeal A n r))
          (degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ)) (degreeOne_mem _) one_pos =
      Spec.map (CommRingCat.ofHom (overlapEquiv A n r j ℓ hj hℓ hjℓ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (awayMap (grading (centerIdeal A n r))
          (degreeOne_mem (genX A n r j hj)) (degreeOne_mul_comm A n r j ℓ hj hℓ))) ≫
        Proj.awayι (grading (centerIdeal A n r))
          (degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ)) (degreeOne_mem _) one_pos := by
  rw [ofHom_chartAwayEquiv_comp_ofHom_modelTransition A n r j ℓ hj hℓ hjℓ, Spec.map_comp,
    Category.assoc]

/-- The chart of `x_ℓ` restricted to the overlap is the chart of `f g` (Mathlib's
`Proj.SpecMap_awayMap_awayι`, instantiated). -/
theorem rhs_step₃ :
    Spec.map (CommRingCat.ofHom (awayMap (grading (centerIdeal A n r))
        (degreeOne_mem (genX A n r j hj)) (degreeOne_mul_comm A n r j ℓ hj hℓ))) ≫
      Proj.awayι (grading (centerIdeal A n r))
        (degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ)) (degreeOne_mem _) one_pos =
    Proj.awayι (grading (centerIdeal A n r))
      (degreeOne (centerIdeal A n r) (genX A n r j hj) *
        degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ))
      (SetLike.mul_mem_graded (degreeOne_mem _) (degreeOne_mem _))
      (one_pos.trans_le (Nat.le_add_right 1 1)) :=
  specMap_awayMap_awayι' _ (degreeOne_mem (genX A n r ℓ hℓ)) one_pos
    (degreeOne_mem (genX A n r j hj)) (degreeOne_mul_comm A n r j ℓ hj hℓ) _

theorem rhs_factor (hjℓ : j ≠ ℓ) :
    Spec.map (CommRingCat.ofHom (modelTransition A n r j ℓ).toRingHom) ≫ modelChart A n r ℓ hℓ =
      Spec.map (CommRingCat.ofHom (overlapEquiv A n r j ℓ hj hℓ hjℓ).toRingHom) ≫
        Proj.awayι (grading (centerIdeal A n r))
          (degreeOne (centerIdeal A n r) (genX A n r j hj) *
            degreeOne (centerIdeal A n r) (genX A n r ℓ hℓ))
          (SetLike.mul_mem_graded (degreeOne_mem _) (degreeOne_mem _))
          (one_pos.trans_le (Nat.le_add_right 1 1)) :=
  (rhs_step₁ A n r j ℓ hℓ).trans ((rhs_step₂ A n r j ℓ hj hℓ hjℓ).trans
    (by rw [rhs_step₃ A n r j ℓ hj hℓ]))

/-- **The gluing of the charts `U_j` and `U_ℓ` along the transition map** [Hau14, Definition 4.12]:
on the overlap `D(x_ℓ) ⊆ U_j` the charts `U_j` and `U_ℓ` agree through `τ_{jℓ}`, which verifies the
transition formula in the form stated in `Hironaka.Scheme.BlowUp.CoordinateSubspace.Charts`. -/
theorem modelTransition_spec (hjℓ : j ≠ ℓ) :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) A)
        (Localization.Away (X ℓ : MvPolynomial (Fin n) A)))) ≫ modelChart A n r j hj =
      Spec.map (CommRingCat.ofHom (modelTransition A n r j ℓ).toRingHom) ≫
        modelChart A n r ℓ hℓ :=
  (lhs_factor A n r j ℓ hj hℓ hjℓ).trans (rhs_factor A n r j ℓ hj hℓ hjℓ).symm

end Gluing

end Hironaka.BlowUp.CoordinateSubspace
