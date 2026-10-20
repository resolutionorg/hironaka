/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Model
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Chart

/-!
# The model blow-up: `𝔸ⁿ_A` along the coordinate subspace `L = V(x_0, …, x_{r-1})`

The blow-up of `W = 𝔸ⁿ` along the coordinate subspace `Z = V(x_j : j ∈ J)` is glued from the
affine charts `U_j = 𝔸ⁿ`, `j ∈ J`, along transition maps, with the blow-up map given on `U_j` by
the `x_j`-chart `π_j : x_i ↦ x_i x_j` (`i ∈ J ∖ {j}`), `x_i ↦ x_i` otherwise
[Hau14, Definition 4.12]; Kollár's chart (60.2) is the case `j = r` [Kol07, Definition 60].
Hauser prints the transition maps as `x_i ↦ x_i/x_j` (`i ∈ J ∖ {j, ℓ}`), `x_j ↦ 1/x_ℓ`,
`x_ℓ ↦ x_j x_ℓ`, `x_i ↦ x_i` (`i ∉ J`); for the direction used here, the coordinates of `U_ℓ` as
functions on `D(x_ℓ) ⊆ U_j`, the first line reads `x_i ↦ x_i/x_ℓ`
(`HironakaExamples.BlowUp.CoordinateSubspace.Transition` verifies this form).  Here the blow-up of
`Spec R` along `I` is Mathlib's `Proj` of the Rees algebra (`affineBlowUp I`) with the charts
`Spec R[I/a] ⟶ affineBlowUp I`; `R = A[x_0, …, x_{n-1}]`, `I = (x_0, …, x_{r-1})` (`centerIdeal`),
and `Hironaka.Scheme.BlowUp.Model` identifies `R[I/x_j]` with the polynomial ring `A[x]` (the
variable `x_i`, `i < r`, `i ≠ j`, standing for `x_i/x_j`).  This module defines

* `modelBlowUp A n r`, the affine blow-up of `𝔸ⁿ_A` along `L`;
* `modelChart A n r j hj : Spec A[x] ⟶ modelBlowUp A n r`, Hauser's chart `U_j`, the chart of
  `x_j` composed with `Spec` of the identification of `Hironaka.Scheme.BlowUp.Model`;
* `modelTransition A n r j ℓ : A[x] →ₐ[A] A[x][1/x_ℓ]`, Hauser's transition map from the
  coordinates of `U_ℓ` to the functions on the overlap `D(x_ℓ) ⊆ U_j`;

and proves the chart formulas: `modelChart_π` (over the base the chart is `Spec π_j`),
`iSup_opensRange_modelChart` (the charts cover), `modelChart_preimage_modelChart` (inside `U_j`
the chart `U_ℓ` is `D(x_ℓ)`), `modelTransition_X`.  The sibling modules prove the smoothness of
the model blow-up, the exceptional divisor in a chart and its identification with `ℙ^{r-1}_L`, and
the gluing identity; the charts are used for the étale-local structure of blow-ups of smooth
centres (`Hironaka.Scheme.Smooth.ChartEtale`) and in the worked examples
(`HironakaExamples.Sequence.Remark33Charts`).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace AlgebraicGeometry.CoordinateSubspace

variable (A : Type u) [CommRing A] (n r : ℕ)

/-- The index set `{0, …, r-1}` of the coordinates cutting out the center `L`. -/
abbrev center : Set (Fin n) := {i | i.val < r}

/-- The ideal `(x_0, …, x_{r-1})` of the coordinate subspace `L ⊆ 𝔸ⁿ_A`. -/
noncomputable abbrev centerIdeal : Ideal (MvPolynomial (Fin n) A) :=
  affineBlowUpAlgebra.coordinateIdeal A (center n r)

theorem X_mem_centerIdeal {j : Fin n} (hj : j.val < r) : X j ∈ centerIdeal A n r :=
  Ideal.subset_span (Set.mem_image_of_mem X hj)

/-- **The model blow-up** `B_L 𝔸ⁿ_A` [Hau14, Definition 4.12], the affine blow-up of
`Spec A[x_0, …, x_{n-1}]` along `(x_0, …, x_{r-1})`. -/
noncomputable abbrev modelBlowUp : Scheme.{u} := affineBlowUp (centerIdeal A n r)

/-- The identification `A[x][L/x_j] ≃ A[x]` of `Hironaka.Scheme.BlowUp.Model` (`x_i ↦ x_i/x_j` for
`i < r`, `i ≠ j`) as an isomorphism of `CommRingCat`. -/
noncomputable def chartRingIso (j : Fin n) :
    CommRingCat.of (affineBlowUpAlgebra (centerIdeal A n r) (X j)) ≅
      CommRingCat.of (MvPolynomial (Fin n) A) :=
  (affineBlowUpAlgebra.coordinateSubspaceEquiv A (center n r) j).toRingEquiv.toCommRingCatIso

/-- **The `x_j`-chart** `U_j = 𝔸ⁿ` of the model blow-up [Hau14, Definition 4.12];
[Kol07, Definition 60, (60.2)]: `Spec A[x] ⟶ B_L 𝔸ⁿ_A`, the chart of `x_j` of `affineBlowUp`
composed with `Spec` of the identification `A[x][L/x_j] ≃ A[x]` (`x_i`, `i < r`, `i ≠ j`, standing
for `x_i/x_j`). -/
noncomputable def modelChart (j : Fin n) (hj : j.val < r) :
    Spec (.of (MvPolynomial (Fin n) A)) ⟶ modelBlowUp A n r :=
  Spec.map (chartRingIso A n r j).hom ≫
    affineBlowUp.chart (centerIdeal A n r) ⟨X j, X_mem_centerIdeal A n r hj⟩

/-- The chart `U_j` is an open immersion (`Spec` of an isomorphism followed by a chart of
`affineBlowUp`).  An instance, so that the images `(modelChart …).opensRange` of the charts are
available. -/
instance isOpenImmersion_modelChart (j : Fin n) (hj : j.val < r) :
    IsOpenImmersion (modelChart A n r j hj) := by
  unfold modelChart
  infer_instance

/-- **The transition map** from the coordinates of the chart `U_ℓ` to the functions on the overlap
`D(x_ℓ) ⊆ U_j` [Hau14, Definition 4.12] (whose printed first line `x_i ↦ x_i/x_j` is the form for
the opposite direction): `x_i ↦ x_i/x_ℓ` (`i < r`, `i ≠ j, ℓ`), `x_j ↦ 1/x_ℓ`, `x_ℓ ↦ x_j x_ℓ`,
`x_i ↦ x_i` (`i ≥ r`). -/
noncomputable def modelTransition (j ℓ : Fin n) :
    MvPolynomial (Fin n) A →ₐ[A] Localization.Away (X ℓ : MvPolynomial (Fin n) A) :=
  aeval fun i => (if i = ℓ then
      algebraMap (MvPolynomial (Fin n) A) (Localization.Away (X ℓ : MvPolynomial (Fin n) A))
        (X j * X ℓ)
    else if i = j then IsLocalization.Away.invSelf (X ℓ : MvPolynomial (Fin n) A)
    else if i.val < r then
      algebraMap (MvPolynomial (Fin n) A) (Localization.Away (X ℓ : MvPolynomial (Fin n) A)) (X i) *
        IsLocalization.Away.invSelf (X ℓ : MvPolynomial (Fin n) A)
    else algebraMap (MvPolynomial (Fin n) A) (Localization.Away (X ℓ : MvPolynomial (Fin n) A))
      (X i) : Localization.Away (X ℓ : MvPolynomial (Fin n) A))

/-- The chart map `π_j` [Hau14, Definition 4.12] sends the centre ideal into `(x_j)`:
`x_i ↦ x_i x_j` for `i < r`, `i ≠ j`, and `x_j ↦ x_j`.  (So the exceptional divisor of the chart
maps to `L`.) -/
theorem centerIdeal_le_comap_chartSubst (j : Fin n) :
    centerIdeal A n r ≤
      (Ideal.span {(X j : MvPolynomial (Fin n) A)}).comap
        (affineBlowUpAlgebra.chartSubst A (center n r) j).toRingHom := by
  rw [centerIdeal, affineBlowUpAlgebra.coordinateIdeal, Ideal.span_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  by_cases hij : i = j
  · subst hij
    rw [affineBlowUpAlgebra.chartSubst_X_self]
    exact Ideal.mem_span_singleton_self _
  · rw [affineBlowUpAlgebra.chartSubst_X_of_mem A (center n r) j hi hij]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end AlgebraicGeometry.CoordinateSubspace

/-! ### The chart map and the cover -/

namespace AlgebraicGeometry.CoordinateSubspace

open affineBlowUpAlgebra

variable (A : Type u) [CommRing A] (n r : ℕ)

/-- The chart map `π_j` [Hau14, Definition 4.12] is `x_i ↦ x_i x_j` for `i < r`, `i ≠ j`, and
`x_i ↦ x_i` otherwise. -/
theorem chartSubst_X (j i : Fin n) :
    chartSubst A (center n r) j (X i) = if i.val < r ∧ i ≠ j then X i * X j else X i := by
  split_ifs with h
  · exact chartSubst_X_of_mem A (center n r) j h.1 h.2
  · exact chartSubst_X_of_not A (center n r) j h

/-- Read through `chartRingIso`: the identification `A[x][L/x_j] ≃ A[x]` composed with the
inclusion `A[x] → A[x][L/x_j]` is Hauser's chart map `π_j`. -/
theorem chartRingIso_hom_comp_algebraMap (j : Fin n) :
    (chartRingIso A n r j).hom.hom.comp
        (algebraMap (MvPolynomial (Fin n) A) (affineBlowUpAlgebra (centerIdeal A n r) (X j))) =
      (chartSubst A (center n r) j).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp only [chartRingIso, RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom,
      RingHom.comp_apply, AlgEquiv.coe_toRingEquiv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
      AlgHom.commutes]
  · simp only [chartRingIso, RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom,
      RingHom.comp_apply, AlgEquiv.coe_toRingEquiv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    by_cases h : i.val < r ∧ i ≠ j
    · rw [coordinateSubspaceEquiv_algebraMap_X_of_mem A (center n r) j h.1 h.2,
        chartSubst_X_of_mem A (center n r) j h.1 h.2]
    · rw [coordinateSubspaceEquiv_algebraMap_X_of_not A (center n r) j h,
        chartSubst_X_of_not A (center n r) j h]

/-- Over the base the chart `U_j` is `Spec` of the chart map `π_j` [Hau14, Definition 4.12];
[Kol07, Definition 60, (60.2)]. -/
theorem modelChart_π (j : Fin n) (hj : j.val < r) :
    modelChart A n r j hj ≫ affineBlowUp.π (centerIdeal A n r) =
      Spec.map (CommRingCat.ofHom (chartSubst A (center n r) j).toRingHom) := by
  rw [modelChart, Category.assoc, affineBlowUp.chart_π, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
  exact chartRingIso_hom_comp_algebraMap A n r j

/-- The image of the chart `U_j` is the image of the chart of `x_j` of `affineBlowUp`. -/
theorem opensRange_modelChart (j : Fin n) (hj : j.val < r) :
    (modelChart A n r j hj).opensRange =
      (affineBlowUp.chart (centerIdeal A n r) ⟨X j, X_mem_centerIdeal A n r hj⟩).opensRange :=
  Scheme.Hom.opensRange_comp_of_isIso _ _

/-- The charts `U_j`, `j < r`, cover the model blow-up [Hau14, Definition 4.12] — the variables
`x_j`, `j < r`, generate the centre ideal, and the charts of a generating set cover the affine
blow-up. -/
theorem iSup_opensRange_modelChart :
    ⨆ (j : Fin n) (hj : j.val < r), (modelChart A n r j hj).opensRange = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨⟨y, hy⟩, hx⟩ := affineBlowUp.exists_mem_opensRange_chart_of_span_eq
    (centerIdeal A n r) (X '' center n r) rfl x
  obtain ⟨j, hj, rfl⟩ := hy
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨j, TopologicalSpace.Opens.mem_iSup.mpr ⟨hj, ?_⟩⟩
  rw [opensRange_modelChart]
  exact hx

/-! ### Overlaps and the transition map on generators -/

/-- The ratio `x_ℓ/x_j ∈ A[x][L/x_j]` of the affine blow-up is the fraction `x_ℓ/x_j` of the affine
blow-up algebra. -/
theorem ratio_eq_frac (j ℓ : Fin n) (hj : j.val < r) (hℓ : ℓ.val < r) :
    affineBlowUpAlgebra.ratio (centerIdeal A n r) ⟨X j, X_mem_centerIdeal A n r hj⟩
        ⟨X ℓ, X_mem_centerIdeal A n r hℓ⟩ =
      frac (a := X j) (X_mem_centerIdeal A n r hℓ) :=
  Subtype.ext (coe_frac_eq_awayFrac _).symm

/-- Under the identification `A[x][L/x_j] ≃ A[x]`, the ratio `x_ℓ/x_j` is the variable `x_ℓ`
(`ℓ ≠ j`). -/
theorem chartRingIso_hom_ratio (j ℓ : Fin n) (hj : j.val < r) (hℓ : ℓ.val < r) (hjℓ : j ≠ ℓ) :
    (chartRingIso A n r j).hom.hom
        (affineBlowUpAlgebra.ratio (centerIdeal A n r) ⟨X j, X_mem_centerIdeal A n r hj⟩
          ⟨X ℓ, X_mem_centerIdeal A n r hℓ⟩) = X ℓ := by
  rw [ratio_eq_frac A n r j ℓ hj hℓ]
  exact coordinateSubspaceEquiv_frac A (center n r) j hℓ (Ne.symm hjℓ) _

/-- Inside the chart `U_j`, the chart `U_ℓ` (`ℓ ≠ j`) is the basic open `D(x_ℓ)`
[Hau14, Definition 4.13]. -/
theorem modelChart_preimage_modelChart (j ℓ : Fin n) (hj : j.val < r) (hℓ : ℓ.val < r)
    (hjℓ : j ≠ ℓ) :
    modelChart A n r j hj ⁻¹ᵁ (modelChart A n r ℓ hℓ).opensRange =
      PrimeSpectrum.basicOpen (X ℓ : MvPolynomial (Fin n) A) := by
  rw [opensRange_modelChart, modelChart, Scheme.Hom.comp_preimage,
    affineBlowUp.chart_preimage_chart, SpecMap_preimage_basicOpen,
    chartRingIso_hom_ratio A n r j ℓ hj hℓ hjℓ]

/-- The transition map on the generators [Hau14, Definition 4.12]. -/
theorem modelTransition_X (j ℓ : Fin n) (i : Fin n) :
    modelTransition A n r j ℓ (X i) =
      if i = ℓ then
        algebraMap (MvPolynomial (Fin n) A) (Localization.Away (X ℓ : MvPolynomial (Fin n) A))
          (X j * X ℓ)
      else if i = j then IsLocalization.Away.invSelf (X ℓ : MvPolynomial (Fin n) A)
      else if i.val < r then
        algebraMap (MvPolynomial (Fin n) A) (Localization.Away (X ℓ : MvPolynomial (Fin n) A))
            (X i) * IsLocalization.Away.invSelf (X ℓ : MvPolynomial (Fin n) A)
      else algebraMap (MvPolynomial (Fin n) A) (Localization.Away (X ℓ : MvPolynomial (Fin n) A))
        (X i) := by
  rw [modelTransition, aeval_X]

end AlgebraicGeometry.CoordinateSubspace
