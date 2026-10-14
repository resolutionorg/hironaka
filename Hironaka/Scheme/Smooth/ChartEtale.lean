/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.BaseChange
public import Hironaka.Scheme.Smooth.ChartDefs
import Hironaka.Scheme.Smooth.EtaleCoordinates

/-!
# The chart functions are étale coordinates

Kollár's coordinates (60.2) `y_i` "give local coordinates on a chart of `B_Z X`"
[Kol07, Definition 60]; here in the strong form that the chart functions are étale coordinates on
the chart. For a chart `E` of étale coordinates adapted to `Z` with coordinate ring map
`φ = aeval v : k[t] → Γ(U)` (étale, so flat), the chart ring `Γ(U)[J/x_j]` is the base change
`Γ(U) ⊗_{k[t]} k[t][L/t_j]` of the model chart ring (`tensorHom`, bijective by flatness), and
`k[t][L/t_j] ≃ k[y]` is the polynomial identification of the model chart
(`coordinateSubspaceEquiv`; the affine chart of [Hau14, Definition 4.12]), under which
`y_i ↦ x_i/x_j` (`i < r`, `i ≠ j`) and `y_i ↦ x_i` otherwise. Hence `k[y] → Γ(U)[J/x_j]`,
`y_i ↦ (the chart function y_i)`, is the base change of the étale `φ` along `k[t] → k[y]` and is
étale (`Algebra.Etale.baseChange`, `RingHom.Etale.respectsIso`).

`etale_aeval_aux` proves this with the `k[t]`-algebra structure of `Γ(U)` as an instance and the
ideal `J` and generator `x_j` as variables (`subst`-able), so that every term matches the codomain
of `tensorHom` syntactically; `etale_aeval_chartCoordinates` instantiates it for `E`. Not stated
in this form in the sources. Used to give the standard charts of a smooth blow-up their own
étale coordinates (`Hironaka/Scheme/Snc/ChartSncData.lean`).
-/

public section

open AlgebraicGeometry CategoryTheory affineBlowUpAlgebra CoordinateSubspace

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n r : ℕ}
  {Z : X.IdealSheafData} {x : X} (E : EtaleCoordinatesAdapted f n r Z x) {j : Fin n}
  (hj : j.val < r)

section Generic

variable [Algebra k Γ(X, E.U)] [Algebra (MvPolynomial (Fin n) k) Γ(X, E.U)]

omit [Algebra k Γ(X, E.U)] in
/-- The base change `k[t][L/t_j] → Γ(U)[J/x_j]` of the model chart ring along an étale
`k[t] → Γ(U)` is étale: through `tensorHom` (bijective by flatness) it is the inclusion of the
first factor into `k[t][L/t_j] ⊗_{k[t]} Γ(U)` (`Algebra.Etale.baseChange`). -/
theorem etale_baseChangeHom_centerIdeal [Algebra.Etale (MvPolynomial (Fin n) k) Γ(X, E.U)] :
    (baseChangeHom Γ(X, E.U) (MvPolynomial.X j) (centerIdeal k n r)).toRingHom.Etale := by
  let e₁ := AlgEquiv.ofBijective _
    (tensorHom_bijective_of_flat Γ(X, E.U) (MvPolynomial.X j) (centerIdeal k n r))
  have h2 := RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale
    (affineBlowUpAlgebra (centerIdeal k n r) (MvPolynomial.X (R := k) j))
    (affineBlowUpAlgebra (centerIdeal k n r) (MvPolynomial.X (R := k) j) ⊗[MvPolynomial (Fin n) k]
      Γ(X, E.U)))
  have h3 := RingHom.Etale.respectsIso.left _ (Algebra.TensorProduct.comm (MvPolynomial (Fin n) k)
    (affineBlowUpAlgebra (centerIdeal k n r) (MvPolynomial.X (R := k) j)) Γ(X, E.U)).toRingEquiv h2
  have h4 := RingHom.Etale.respectsIso.left _ e₁.toRingEquiv h3
  have h5 : (baseChangeHom Γ(X, E.U) (MvPolynomial.X j) (centerIdeal k n r)).toRingHom =
      (e₁.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.comm (MvPolynomial (Fin n) k)
        (affineBlowUpAlgebra (centerIdeal k n r) (MvPolynomial.X (R := k) j))
          Γ(X, E.U)).toRingEquiv.toRingHom).comp
        (algebraMap _ (affineBlowUpAlgebra (centerIdeal k n r) (MvPolynomial.X (R := k) j)
          ⊗[MvPolynomial (Fin n) k] Γ(X, E.U))) := by
    ext z
    simp [e₁, Algebra.TensorProduct.algebraMap_apply]
  rw [h5]
  exact h4

/-- The coordinate map `k[y] → Γ(U)[J/x_j]`, `y_i ↦ x_i/x_j` (`i < r`, `i ≠ j`), `y_i ↦ x_i`
otherwise, is the base change of the model chart composed with the identification
`k[y] ≃ k[t][L/t_j]` of the model chart (`coordinateSubspaceEquiv`). -/
theorem aeval_chartCoordinates_eq
    (hC : ∀ c : k, algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.C c) =
      algebraMap k Γ(X, E.U) c)
    (hv : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X i) = E.v i)
    (hbJ : algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j) ∈
      (centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
    (hvJ : ∀ i : Fin n, i.val < r →
      E.v i ∈ (centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U))) :
    letI : Algebra k (affineBlowUpAlgebra
        ((centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
        (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j))) :=
      ((algebraMap Γ(X, E.U) _).comp (algebraMap k Γ(X, E.U))).toAlgebra
    (MvPolynomial.aeval (R := k) fun i : Fin n =>
      if h : i.val < r ∧ i ≠ j then
        (ratio ((centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
          ⟨algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j), hbJ⟩
          ⟨E.v i, hvJ i h.1⟩ :
          affineBlowUpAlgebra
            ((centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
            (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j)))
      else algebraMap Γ(X, E.U) _ (E.v i)).toRingHom =
      (baseChangeHom Γ(X, E.U) (MvPolynomial.X j) (centerIdeal k n r)).toRingHom.comp
        (coordinateSubspaceEquiv k (center n r) j).symm.toRingEquiv.toRingHom := by
  let instC : Algebra k (affineBlowUpAlgebra ((centerIdeal k n r).map
      (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
      (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j))) :=
    ((algebraMap Γ(X, E.U) _).comp (algebraMap k Γ(X, E.U))).toAlgebra
  change (MvPolynomial.aeval (R := k) fun i : Fin n =>
      if h : i.val < r ∧ i ≠ j then
        (ratio ((centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
          ⟨algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j), hbJ⟩
          ⟨E.v i, hvJ i h.1⟩ :
          affineBlowUpAlgebra
            ((centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
            (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j)))
      else algebraMap Γ(X, E.U) _ (E.v i)).toRingHom = _
  let σ := (coordinateSubspaceEquiv k (center n r) j).symm
  have hst : IsScalarTower k (MvPolynomial (Fin n) k)
      (affineBlowUpAlgebra ((centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
        (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j))) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap Γ(X, E.U) _ (algebraMap k Γ(X, E.U) c) =
        algebraMap Γ(X, E.U) _ (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.C c))
      rw [hC]
  have hσ : ∀ i, σ (MvPolynomial.X i) = modelHom k (center n r) j (MvPolynomial.X i) := fun i => by
    simp only [σ, coordinateSubspaceEquiv, AlgEquiv.symm_symm]
    rfl
  have key : (MvPolynomial.aeval (R := k) fun i : Fin n =>
      if h : i.val < r ∧ i ≠ j then
        (ratio ((centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
          ⟨algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j), hbJ⟩
          ⟨E.v i, hvJ i h.1⟩ :
          affineBlowUpAlgebra
            ((centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)))
            (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j)))
      else algebraMap Γ(X, E.U) _ (E.v i)) =
      ((baseChangeHom Γ(X, E.U) (MvPolynomial.X j) (centerIdeal k n r)).restrictScalars k).comp
        σ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hσ,
      AlgHom.restrictScalars_apply]
    by_cases h : i.val < r ∧ i ≠ j
    · rw [dite_eq_left h]
      have hm : modelHom k (center n r) j (MvPolynomial.X i) =
          frac (a := MvPolynomial.X j) (X_mem_coordinateIdeal k (center n r) h.1) :=
        Subtype.ext (by rw [coe_modelHom, modelAux_X_of_mem k (center n r) j h.1 h.2, coe_frac])
      rw [hm, baseChangeHom_frac]
      exact Subtype.ext (by
        rw [coe_frac_eq_awayFrac]
        change awayFrac _ 1 (E.v i) = awayFrac _ 1 (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)
          (MvPolynomial.X i))
        rw [hv i])
    · rw [dite_eq_right h]
      have mem : algebraMap (MvPolynomial (Fin n) k) (Localization.Away (MvPolynomial.X (R := k) j))
          (MvPolynomial.X i) ∈
            affineBlowUpAlgebra (centerIdeal k n r) (MvPolynomial.X (R := k) j) :=
        Subalgebra.algebraMap_mem _ _
      have hm : modelHom k (center n r) j (MvPolynomial.X i) = ⟨_, mem⟩ :=
        Subtype.ext (by rw [coe_modelHom, modelAux_X_of_not k (center n r) j h])
      have hψ := congrArg (baseChangeHom Γ(X, E.U) (MvPolynomial.X j) (centerIdeal k n r)) hm
      refine Eq.trans ?_ hψ.symm
      have e1 : (baseChangeHom Γ(X, E.U) (MvPolynomial.X j) (centerIdeal k n r) ⟨_, mem⟩ :
          Localization.Away (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j))) =
          awayMapₐ Γ(X, E.U) (MvPolynomial.X j)
            (algebraMap (MvPolynomial (Fin n) k) (Localization.Away (MvPolynomial.X (R := k) j))
              (MvPolynomial.X i)) :=
        coe_baseChangeHom Γ(X, E.U) (MvPolynomial.X j) (centerIdeal k n r) ⟨_, mem⟩
      rewrite [awayMapₐ_algebraMap, hv i] at e1
      exact Subtype.ext e1.symm
  exact congrArg AlgHom.toRingHom key

/-- Generic form: for an étale `k[t]`-algebra structure on `Γ(U)` sending `t_i` to `v_i`, the map
`k[y] → Γ(U)[J/x_j]`, `y_i ↦ x_i/x_j` (`i < r`, `i ≠ j`), `y_i ↦ x_i` otherwise, is étale: the
base change of `k[t] → Γ(U)` along the identification of the model chart `k[t][L/t_j] ≃ k[y]`. -/
theorem etale_aeval_aux [Algebra.Etale (MvPolynomial (Fin n) k) Γ(X, E.U)]
    (hC : ∀ c : k, algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.C c) =
      algebraMap k Γ(X, E.U) c)
    (hv : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X i) = E.v i)
    (J : Ideal Γ(X, E.U)) (b : Γ(X, E.U))
    (hJ : (centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)) = J)
    (hb : algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U) (MvPolynomial.X j) = b) (hbJ : b ∈ J)
    (hvJ : ∀ i : Fin n, i.val < r → E.v i ∈ J) :
    letI : Algebra k (affineBlowUpAlgebra J b) :=
      ((algebraMap Γ(X, E.U) _).comp (algebraMap k Γ(X, E.U))).toAlgebra
    (MvPolynomial.aeval (R := k) fun i : Fin n =>
      if h : i.val < r ∧ i ≠ j then
        (ratio J ⟨b, hbJ⟩ ⟨E.v i, hvJ i h.1⟩ : affineBlowUpAlgebra J b)
      else algebraMap Γ(X, E.U) _ (E.v i)).toRingHom.Etale := by
  subst hJ hb
  rw [aeval_chartCoordinates_eq E hC hv hbJ hvJ]
  exact RingHom.Etale.respectsIso.right _ _ (etale_baseChangeHom_centerIdeal E)

end Generic

/-- On the chart of `x_j`, the chart functions `y_i = x_i/x_j` (`i < r`, `i ≠ j`) and `y_i = x_i`
(otherwise) are étale coordinates: `k[t] → Γ(U)[J/x_j]`, `t_i ↦ y_i`, is étale (the coordinates
(60.2) of [Kol07, Definition 60], which "give local coordinates on a chart"). -/
theorem etale_aeval_chartCoordinates :
    letI := f.sectionsAlgebra E.U.1
    letI : Algebra k (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) :=
      ((algebraMap Γ(X, E.U) _).comp (algebraMap k Γ(X, E.U))).toAlgebra
    (MvPolynomial.aeval (R := k) fun i : Fin n =>
      if h : i.val < r ∧ i ≠ j then
        (ratio E.centerIdeal (E.coord j hj) (E.coord i h.1) :
          affineBlowUpAlgebra E.centerIdeal (E.coord j hj))
      else algebraMap Γ(X, E.U) _ (E.v i)).toRingHom.Etale := by
  let _ := f.sectionsAlgebra E.U.1
  let φ : MvPolynomial (Fin n) k →+* Γ(X, E.U) := (MvPolynomial.aeval (R := k) E.v).toRingHom
  have hφ : φ.Etale := (etale_toAffineSpace_iff f E.U.2 E.v).mp E.etale
  let _ : Algebra (MvPolynomial (Fin n) k) Γ(X, E.U) := φ.toAlgebra
  have het : Algebra.Etale (MvPolynomial (Fin n) k) Γ(X, E.U) := hφ.toAlgebra
  have hI : (centerIdeal k n r).map (algebraMap (MvPolynomial (Fin n) k) Γ(X, E.U)) =
      E.centerIdeal := by
    rw [centerIdeal, coordinateIdeal, Ideal.map_span, EtaleCoordinatesAdapted.centerIdeal]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨⟨i, hi⟩, by simp [φ, RingHom.algebraMap_toAlgebra]⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, by simp [φ, RingHom.algebraMap_toAlgebra]⟩
  exact etale_aeval_aux E (fun c => by simp [φ, RingHom.algebraMap_toAlgebra])
    (fun i => by simp [φ, RingHom.algebraMap_toAlgebra]) E.centerIdeal (E.v j) hI
    (by simp [φ, RingHom.algebraMap_toAlgebra]) (E.v_mem_centerIdeal hj)
    (fun i hi => E.v_mem_centerIdeal hi)

end AlgebraicGeometry
