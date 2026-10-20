/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Smooth.StandardSmooth
import Hironaka.Algebra.RegularSmooth.Cotangent
import Hironaka.Algebra.RegularSmooth.Polynomial
import Hironaka.Algebra.RegularSmooth.QuotientRegular
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Smooth at a prime implies regular

The last assertion of [Sta, Tag 00TT], "in this case the local ring `S_𝔮` is regular", for a
finite type algebra `S` over any field `k`. The argument is the Jacobian one, assembled from
[Sta, Tags 00T6, 00RX, 00RU, 00NQ]; the numbered steps below are followed by the Lean proof.

**The presentation.** By Mathlib's `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`,
smoothness at `𝔮` gives a `g ∉ 𝔮` with `S_g` standard smooth over `k` ([Sta, Tags 00TA, 00T7];
finite type over a field is finite presentation); since `S_𝔮 ≅ (S_g)_{𝔮 S_g}` and regularity is
invariant under ring isomorphism, we may assume `S` itself standard smooth: `S ≅ A/(f_1, …, f_c)`
with `A = k[x_1, …, x_N]` and the Jacobian minor `Δ = det(∂f_j/∂x_{m(i)})` a unit of `S`
(Mathlib's `SubmersivePresentation`, whose `map : σ → ι` picks the `c` distinguished variables).
For such `S`, `Ω[S⁄k]` is free of rank `N - c` ([Sta, Tag 00T7, (2)]; `rank_kaehlerDifferential`),
so `κ(𝔮) ⊗[S] Ω[S⁄k]` has dimension `N - c` at every prime.

**The Jacobian argument.** (1) Let `Q ⊆ A` be the preimage of `𝔮` and `P = A_Q`, a regular local
ring (`Hironaka/Algebra/RegularSmooth/Polynomial.lean`). (2) The localized surjection `φ : P → S_𝔮`
has kernel `(f_1, …, f_c)P`, so `S_𝔮 ≅ P/(f_1, …, f_c)`.
(3) In the basis `1 ⊗ d x_i` of `κ ⊗[P] Ω[P⁄k]` the vector `1 ⊗ d f_j` has coordinates
`∂f_j/∂x_i mod Q`, and the `c × c` minor on the distinguished variables is `Δ mod Q ≠ 0` (a unit of
`S` does not lie in `𝔮`), so the `1 ⊗ d f_j` are linearly independent over `κ`.
(4) The conormal map `𝔪_P/𝔪_P² → κ ⊗ Ω[P⁄k]` sends the class of `f_j` to `1 ⊗ d f_j`, so the
classes of the `f_j` are linearly independent in `𝔪_P/𝔪_P²` (no injectivity of the conormal map is
used, only that it is a well-defined linear map).
(5) By [Sta, Tag 00NQ] (`Hironaka/Algebra/RegularSmooth/QuotientRegular.lean`), `P/(f_1, …, f_c)` is
a regular local ring, and so is `S_𝔮`.
-/

public section

universe u

open IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace Algebra

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]

/-- If the finite type `k`-algebra `S` is smooth at `𝔮` over `k`, there is `g ∉ 𝔮` with `S_g`
standard smooth over `k` (the first sentence of the proof of (1) ⇒ (3) in [Sta, Tag 00TT];
[Sta, Tag 00TA]). Mathlib's statement for finitely presented algebras, with finite type over a
field giving finite presentation. -/
theorem IsSmoothAt.exists_notMem_isStandardSmooth_of_finiteType [Algebra.FiniteType k S]
    (𝔮 : Ideal S) [𝔮.IsPrime] [Algebra.IsSmoothAt k 𝔮] :
    ∃ g ∉ 𝔮, Algebra.IsStandardSmooth k (Localization.Away g) := by
  have : Algebra.FinitePresentation k S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.IsSmoothAt.exists_notMem_isStandardSmooth (R := k) 𝔮

/-- For `S` standard smooth of relative dimension `d` over `k`, `Ω[S⁄k]` is free of rank `d`, so
`κ(𝔮) ⊗[S] Ω[S⁄k]` has dimension `d` at every prime `𝔮` ([Sta, Tag 00T7, (2)]; [Sta, Tag 02G1]). -/
theorem IsStandardSmoothOfRelativeDimension.finrank_residueField_tensor_kaehlerDifferential
    (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d k S] (𝔮 : Ideal S) [𝔮.IsPrime] :
    Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[S] Ω[S⁄k]) = d := by
  have : Nontrivial S := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact ‹𝔮.IsPrime›.ne_top (Subsingleton.elim _ _)
  obtain ⟨ι, σ, _, _, ⟨P, -⟩⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension d k S›
  have : Module.Free S Ω[S⁄k] := P.free_kaehlerDifferential
  rw [Module.finrank_baseChange]
  exact Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := S) d)

/-- If `S` is standard smooth over the field `k`, then `S_𝔮` is a regular local ring at every prime
`𝔮`: the Jacobian argument, steps (1)–(5) of the module docstring. -/
theorem IsStandardSmooth.isRegularLocalRing_localization_atPrime [Algebra.IsStandardSmooth k S]
    (𝔮 : Ideal S) [𝔮.IsPrime] : IsRegularLocalRing (Localization.AtPrime 𝔮) := by
  classical
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth k S›.out
  let : Fintype σ := Fintype.ofFinite σ
  -- the presentation `A = k[x_i] → S`, the prime `Q` of `A` over `𝔮`, and `Pl = A_Q`
  set A := P.Ring with hA
  have hsurj : Function.Surjective (algebraMap A S) := P.algebraMap_surjective
  set Q : Ideal A := 𝔮.comap (algebraMap A S) with hQ
  have : Q.IsPrime := Ideal.IsPrime.comap _
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    MvPolynomial.isRegularLocalRing_localization_atPrime (k := k) (ι := ι) Q
  -- the localized surjection `φ : A_Q → S_𝔮`
  set φ : Localization.AtPrime Q →+* Localization.AtPrime 𝔮 :=
    Localization.localRingHom Q 𝔮 (algebraMap A S) rfl with hφ
  have hφsurj : Function.Surjective φ := by
    intro z
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z
    dsimp only
    obtain ⟨y', rfl⟩ := hsurj y
    obtain ⟨s', hs'⟩ := hsurj (s : S)
    have hs'Q : s' ∈ Q.primeCompl := by
      change s' ∉ Q
      rw [hQ, Ideal.mem_comap, hs']
      exact s.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime Q) y' ⟨s', hs'Q⟩, ?_⟩
    rw [hφ, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  -- the relations, moved to `A_Q`
  set f : σ → Localization.AtPrime Q :=
    fun j => algebraMap A (Localization.AtPrime Q) (P.relation j) with hf_def
  have hrel : ∀ j, algebraMap A S (P.relation j) = 0 := fun j =>
    (RingHom.mem_ker).mp (P.relation_mem_ker j)
  have hker : RingHom.ker φ = Ideal.span (Set.range f) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
      dsimp only at hx ⊢
      rw [RingHom.mem_ker, hφ, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
      obtain ⟨⟨t, ht⟩, ht0⟩ := hx
      obtain ⟨t', rfl⟩ := hsurj t
      have ht' : t' ∈ Q.primeCompl := by
        change t' ∉ Q
        rw [hQ, Ideal.mem_comap]
        exact ht
      have hmem : t' * a ∈ Ideal.span (Set.range P.relation) := by
        rw [P.span_range_relation_eq_ker]
        change t' * a ∈ RingHom.ker (algebraMap A S)
        rw [RingHom.mem_ker, map_mul]
        exact ht0
      have hx' : IsLocalization.mk' (Localization.AtPrime Q) a s =
          algebraMap A (Localization.AtPrime Q) (t' * a) *
            IsLocalization.mk' (Localization.AtPrime Q) (1 : A) (⟨t', ht'⟩ * s) := by
        rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_iff_eq]
        simp only [Submonoid.coe_mul]
        congr 1
        ring
      rw [hx']
      refine Ideal.mul_mem_right _ _ ?_
      have := Ideal.mem_map_of_mem (algebraMap A (Localization.AtPrime Q)) hmem
      rwa [Ideal.map_span, ← Set.range_comp] at this
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      change φ (f j) = 0
      rw [hf_def, hφ, Localization.localRingHom_to_map, hrel, map_zero]
  -- the relations lie in the maximal ideal of `A_Q`
  have hf : ∀ j, f j ∈ maximalIdeal (Localization.AtPrime Q) := fun j => by
    rw [mem_maximalIdeal, mem_nonunits_iff, hf_def,
      IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q]
    change ¬ P.relation j ∉ Q
    rw [not_not, hQ, Ideal.mem_comap, hrel]
    exact zero_mem _
  -- step (3): the vectors `1 ⊗ d f_j` are linearly independent over `κ(Q)`
  set κ := Q.ResidueField with hκ
  set bκ := residueFieldTensorMvPolynomialLocalizationBasis (k := k) (ι := ι) Q with hbκ
  let π : (κ ⊗[Localization.AtPrime Q] Ω[Localization.AtPrime Q⁄k]) →ₗ[κ] (σ → κ) :=
    LinearMap.pi fun j => Finsupp.lapply (P.map j) ∘ₗ bκ.repr.toLinearMap
  let M : Matrix σ σ κ :=
    fun j i => algebraMap A κ (MvPolynomial.pderiv (P.map i) (P.relation j))
  have hπ : ∀ j, π (1 ⊗ₜ D k (Localization.AtPrime Q) (f j)) = M.row j := fun j => by
    funext i
    simp only [π, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Finsupp.lapply_apply, M, hf_def]
    exact residueFieldTensorMvPolynomialLocalizationBasis_repr_tmul_D (k := k) (ι := ι) Q
      (P.relation j) (P.map i)
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hMeq : M = (P.jacobiMatrix.map (algebraMap A κ)).transpose := by
      ext j i
      simp [M, Matrix.transpose_apply, Matrix.map_apply,
        PreSubmersivePresentation.jacobiMatrix_apply]
    rw [hMeq, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
    intro hdet
    have hunit := P.jacobian_isUnit
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det] at hunit
    exact ‹𝔮.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hdet) hunit)
  have hli' : LinearIndependent κ fun j =>
      (1 : κ) ⊗ₜ[Localization.AtPrime Q] D k (Localization.AtPrime Q) (f j) := by
    refine LinearIndependent.of_comp π ?_
    have := Matrix.linearIndependent_row_iff_isUnit.mpr hM
    convert this using 1
    funext j
    exact hπ j
  -- step (4): the classes of the `f_j` in `𝔪/𝔪²` are linearly independent
  have hli : LinearIndependent κ fun j =>
      (maximalIdeal (Localization.AtPrime Q)).toCotangent ⟨f j, hf j⟩ := by
    refine LinearIndependent.of_comp (cotangentSpaceToTensor k (Localization.AtPrime Q)) ?_
    convert hli' using 1
    funext j
    exact cotangentSpaceToTensor_toCotangent k (Localization.AtPrime Q) ⟨f j, hf j⟩
  -- step (5): the quotient is regular, and it is `S_𝔮`
  obtain ⟨hreg, -⟩ := IsRegularLocalRing.quotient_span_range_of_linearIndependent f hf hli
  rw [← hker] at hreg
  exact IsRegularLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφsurj)

/-- If the finite type `k`-algebra `S` is smooth at `𝔮` over `k`, then `S_𝔮` is a regular local
ring, for any field `k` (the last sentence of [Sta, Tag 00TT], assembled from [Sta, Tags 00T6,
00RX, 00RU, 00NQ]). Standard smoothness of some `S_g` with `g ∉ 𝔮`, then the Jacobian argument on
`S_g`, whose localization at `𝔮 S_g` is `S_𝔮`. -/
theorem IsSmoothAt.isRegularLocalRing [Algebra.FiniteType k S] (𝔮 : Ideal S) [𝔮.IsPrime]
    [Algebra.IsSmoothAt k 𝔮] : IsRegularLocalRing (Localization.AtPrime 𝔮) := by
  obtain ⟨g, hg, hsm⟩ := IsSmoothAt.exists_notMem_isStandardSmooth_of_finiteType (k := k) 𝔮
  set T := Localization.Away g with hT
  set 𝔮' : Ideal T := 𝔮.map (algebraMap S T) with h𝔮'
  have hdisj : Disjoint (Submonoid.powers g : Set S) (𝔮 : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hg
  have : 𝔮'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) T 𝔮 ‹_› hdisj
  have hcomap : 𝔮'.comap (algebraMap S T) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) T ‹𝔮.IsPrime› hdisj
  have hcompl : (𝔮'.comap (algebraMap S T)).primeCompl = 𝔮.primeCompl :=
    Submonoid.ext fun x => by
      change x ∉ 𝔮'.comap (algebraMap S T) ↔ x ∉ 𝔮
      rw [hcomap]
  have hloc : IsLocalization 𝔮.primeCompl (Localization.AtPrime 𝔮') := by
    have := IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers g) 𝔮'
    rwa [IsLocalization.AtPrime, hcompl] at this
  have : IsRegularLocalRing (Localization.AtPrime 𝔮') :=
    IsStandardSmooth.isRegularLocalRing_localization_atPrime (k := k) 𝔮'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv 𝔮.primeCompl (Localization.AtPrime 𝔮')
      (Localization.AtPrime 𝔮)).toRingEquiv

end Algebra
