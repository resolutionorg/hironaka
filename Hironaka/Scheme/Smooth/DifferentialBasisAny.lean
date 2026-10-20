/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Stalk
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Algebra.RegularSmooth.Cotangent
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.DifferentialBasis
import Mathlib.Algebra.Module.SpanRankOperations

/-!
# The differential basis at an arbitrary point

Kollár's local coordinates at non-closed points: at any `x ∈ X` (smooth of relative dimension `n`
over the perfect field `k`), with `t = trdeg_k κ(x)`, a regular system of parameters
`y_0, …, y_{m-1}` of `𝒪_{X,x}` (`m = dim 𝒪_{X,x} = n − t`) together with lifts
`z_0, …, z_{t-1} ∈ 𝒪_{X,x}` of a separating transcendence basis of `κ(x)/k` has differentials
`1 ⊗ d y_i, 1 ⊗ d z_j` forming a basis of `κ(x) ⊗ Ω[𝒪_{X,x}⁄k]`
(`exists_basis_tensor_kaehlerDifferential_sum`). Not in the sources in this form.

The argument: the conormal sequence `0 → 𝔪/𝔪² → κ ⊗ Ω[𝒪⁄k] → Ω[κ⁄k] → 0` is exact
([Sta, Tag 00TV]; `κ` is formally smooth over the perfect `k`, see
`Hironaka/Algebra/RegularSmooth/Cotangent.lean`); the `d s_j` of a separating transcendence basis
`s` form a basis of `Ω[κ⁄k]`
(`exists_basis_kaehlerDifferential_of_isTranscendenceBasis`, the construction of
`Hironaka/Algebra/RegularSmooth/Trdeg.lean`: `Ω[k[s]⁄k]` is free on the `d s_j`, and `k(s)/k[s]` and
`κ/k(s)` are formally étale, [Sta, Tags 00RX, 030O]); the classes `ȳ_i` form a basis of `𝔪/𝔪²`
(Nakayama). Hence the family `1 ⊗ d y_i` (in the image of `𝔪/𝔪²`) and `1 ⊗ d z_j` (mapping to the
basis `d s_j`) is linearly independent of size `m + t`, and
`dim_κ κ ⊗ Ω = dim 𝔪/𝔪² + dim Ω[κ⁄k] = m + t`, so it is a basis. Used in
`Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean`.
-/

public section

namespace AlgebraicGeometry

open KaehlerDifferential TensorProduct IsLocalRing

open scoped IntermediateField.algebraAdjoinAdjoin

universe u v

section Field

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- For a separating transcendence basis `v` of `K/k`, the differentials `d (v i)` form a basis of
`Ω[K⁄k]` ([Sta, Tags 00RX, 030O]; the construction of `Hironaka/Algebra/RegularSmooth/Trdeg.lean`).
-/
theorem exists_basis_kaehlerDifferential_of_isTranscendenceBasis {ι : Type v} (v : ι → K)
    (hv : IsTranscendenceBasis k v)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range v)) K] :
    ∃ b : Module.Basis ι K Ω[K⁄k], ∀ i, b i = D k K (v i) := by
  classical
  set A := Algebra.adjoin k (Set.range v) with hA
  set F := IntermediateField.adjoin k (Set.range v) with hF
  let e : MvPolynomial ι k ≃ₐ[k] A := hv.1.aevalEquiv
  let _ : Algebra (MvPolynomial ι k) A := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  have : IsLocalization (⊥ : Submonoid (MvPolynomial ι k)) (MvPolynomial ι k) :=
    IsLocalization.of_le_isUnit bot_le
  have : IsLocalization (⊥ : Submonoid (MvPolynomial ι k)) A :=
    IsLocalization.isLocalization_of_algEquiv (⊥ : Submonoid (MvPolynomial ι k))
      (AlgEquiv.ofBijective (Algebra.ofId (MvPolynomial ι k) A) e.bijective)
  have : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := A) ⊥
  let bA : Module.Basis ι A Ω[A⁄k] :=
    ((mvPolynomialBasis k ι).baseChange A).map
      (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) A)
  let bF : Module.Basis ι F Ω[F⁄k] :=
    bA.ofIsLocalizedModule F (nonZeroDivisors A) (map k k A F)
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let bK : Module.Basis ι K Ω[K⁄k] :=
    (bF.baseChange K).map (tensorKaehlerEquivOfFormallyEtale k F K)
  refine ⟨bK, fun i => ?_⟩
  have he : algebraMap A K (e (MvPolynomial.X i)) = v i := by
    rw [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  simp only [bK, bF, bA, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    Module.Basis.ofIsLocalizedModule_apply, mvPolynomialBasis_apply,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D]
  rw [← he, IsScalarTower.algebraMap_apply A F K]
  rfl

end Field

section Stalk

open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (x : X)
include f n

/-- At any point `x`, the differentials of a regular system of parameters `y` of `𝒪_{X,x}` and of
lifts `z` of a separating transcendence basis of `κ(x)/k` form a basis of `κ(x) ⊗ Ω[𝒪_{X,x}⁄k]`
([Sta, Tag 00TV] for the conormal sequence, [Sta, Tag 00RX] for the differentials of the basis). -/
theorem exists_basis_tensor_kaehlerDifferential_sum (m t : ℕ) (y : Fin m → X.presheaf.stalk x)
    (hm : (m : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (hy : maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y))
    (z : Fin t → X.presheaf.stalk x)
    (hz : letI := f.stalkAlgebra x
      IsTranscendenceBasis k fun j => residue (X.presheaf.stalk x) (z j))
    (hsep : letI := f.stalkAlgebra x
      Algebra.IsSeparable
        (IntermediateField.adjoin k (Set.range fun j => residue (X.presheaf.stalk x) (z j)))
        (ResidueField (X.presheaf.stalk x))) :
    letI := f.stalkAlgebra x
    ∃ b : Module.Basis (Fin m ⊕ Fin t) (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]),
      (∀ i, b (Sum.inl i) = 1 ⊗ₜ D k (X.presheaf.stalk x) (y i)) ∧
      ∀ j, b (Sum.inr j) = 1 ⊗ₜ D k (X.presheaf.stalk x) (z j) := by
  classical
  let _ := f.stalkAlgebra x
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg := isRegularLocalRing_stalk f x
  have := essFiniteType_stalk f n x
  have := essFiniteType_residueField_stalk f n x
  have := finite_kaehlerDifferential_stalk f n x
  have hκs : Algebra.FormallySmooth k (ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallySmooth.of_perfectField
  -- the basis of `𝔪/𝔪²` and its image under the injective conormal map
  obtain ⟨c, hc⟩ := exists_basis_cotangentSpace_of_span_eq y hy hm
  have hinj := injective_cotangentSpaceToTensor k (X.presheaf.stalk x)
  have hexact := exact_cotangentSpaceToTensor_mapBaseChange k (X.presheaf.stalk x)
  -- the basis of `Ω[κ⁄k]` from the separating transcendence basis
  obtain ⟨d, hd⟩ := exists_basis_kaehlerDifferential_of_isTranscendenceBasis k
    (ResidueField (X.presheaf.stalk x)) (fun j => residue (X.presheaf.stalk x) (z j)) hz
  -- the two families
  set u : Fin m → ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k] :=
    fun i => 1 ⊗ₜ D k (X.presheaf.stalk x) (y i) with hu
  set w : Fin t → ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k] :=
    fun j => 1 ⊗ₜ D k (X.presheaf.stalk x) (z j) with hw
  have hφc : ∀ i, cotangentSpaceToTensor k (X.presheaf.stalk x) (c i) = u i := fun i => by
    rw [hc i, cotangentSpaceToTensor_toCotangent]
  have hψw : ∀ j, mapBaseChange k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)) (w j) =
      d j := fun j => by
    rw [hw]
    simp only [mapBaseChange_tmul, one_smul, map_D]
    rw [hd j]
    rfl
  have hψu : ∀ i, mapBaseChange k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)) (u i) =
      0 := fun i => by
    rw [← hφc i]
    exact hexact.apply_apply_eq_zero (c i)
  -- linear independence of `u`, of `w`, and disjointness of their spans
  have hu_li : LinearIndependent (ResidueField (X.presheaf.stalk x)) u := by
    have hcomp : cotangentSpaceToTensor k (X.presheaf.stalk x) ∘ c = u := funext hφc
    rw [← hcomp]
    exact c.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinj)
  have hw_li : LinearIndependent (ResidueField (X.presheaf.stalk x)) w := by
    refine LinearIndependent.of_comp
      (mapBaseChange k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))) ?_
    have : mapBaseChange k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)) ∘ w = d :=
      funext hψw
    rw [this]
    exact d.linearIndependent
  have hdisj : Disjoint (Submodule.span (ResidueField (X.presheaf.stalk x)) (Set.range u))
      (Submodule.span (ResidueField (X.presheaf.stalk x)) (Set.range w)) := by
    rw [Submodule.disjoint_def]
    intro a hau haw
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp haw
    have hψa : mapBaseChange k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))
        (∑ j, g j • w j) = 0 := by
      have : ∀ b ∈ Submodule.span (ResidueField (X.presheaf.stalk x)) (Set.range u),
          mapBaseChange k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)) b = 0 := by
        intro b hb
        induction hb using Submodule.span_induction with
        | mem b hb => obtain ⟨i, rfl⟩ := hb; exact hψu i
        | zero => exact map_zero _
        | add b₁ b₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
        | smul r b _ h => rw [map_smul, h, smul_zero]
      exact this _ hau
    rw [map_sum] at hψa
    simp only [map_smul, hψw] at hψa
    have hg : ∀ j, g j = 0 := Fintype.linearIndependent_iff.mp d.linearIndependent g hψa
    simp only [hg, zero_smul, Finset.sum_const_zero]
  have hli : LinearIndependent (ResidueField (X.presheaf.stalk x)) (Sum.elim u w) :=
    hu_li.sum_type hw_li hdisj
  -- the dimension count
  have hcard : Fintype.card (Fin m ⊕ Fin t) = Module.finrank (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]) := by
    rw [finrank_residueField_tensor_kaehlerDifferential k (X.presheaf.stalk x), Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin, Module.finrank_eq_card_basis d, Fintype.card_fin,
      ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := X.presheaf.stalk x)
    rw [← hm] at h
    have : (maximalIdeal (X.presheaf.stalk x)).spanFinrank = m := by exact_mod_cast h
    rw [this]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli hcard, fun i => ?_, fun j => ?_⟩
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inl]
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inr]

end Stalk

end AlgebraicGeometry
