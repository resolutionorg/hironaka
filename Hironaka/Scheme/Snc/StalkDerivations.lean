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
import Hironaka.Scheme.Snc.RelativeDimension

/-!
# Derivations dual to a regular system of parameters at any point

The input for [Hau14, Proposition 5.4 (6)] at a non-closed point
(`Hironaka.Scheme.Snc.InducedCoordinates`): at a point `x` of a scheme `X` smooth over a perfect
field `k`, a regular system of parameters `z_1, …, z_n` of `𝒪_{X,x}` admits dual derivations
`D_1, …, D_n : 𝒪_{X,x} → 𝒪_{X,x}` over `k` with `D_i z_j = δ_{ij}` (`exists_derivation_dual`). At a
closed point this is the route of `Hironaka.Scheme.Snc.EtaleParameters` through étale coordinates;
at a general point it needs the injectivity of the conormal map
(`Hironaka.Algebra.RegularSmooth.Cotangent`):

* `Ω[𝒪_{X,x}⁄k]` is free of finite rank — the base change of `Ω[Γ(V)⁄k]` for a standard smooth
  affine neighbourhood `V` of `x` (`exists_affineOpen_isStandardSmooth` of
  `Hironaka.Scheme.Snc.RelativeDimension`; `free_finite_kaehlerDifferential_stalk`);
* the conormal map `𝔪_x/𝔪_x² → κ(x) ⊗ Ω[𝒪_{X,x}⁄k]` is injective because `κ(x)` is formally smooth
  over the perfect field `k` ([Sta, Tag 00TU]; `injective_cotangentSpaceToTensor`, with Mathlib's
  `Algebra.FormallySmooth.of_perfectField`), so the classes of `dz_1, …, dz_n` are linearly
  independent in `κ(x) ⊗ Ω` (the `z_i` are a basis of `𝔪_x/𝔪_x²`);
* a linear map `𝒪^n → Ω` into a finite free module over a local ring which is injective modulo the
  maximal ideal is a split injection (Mathlib's
  `IsLocalRing.split_injective_iff_lTensor_residueField_injective`); the retraction composed with
  the universal derivation `d` and the coordinate projections gives the `D_i`.

Sources: [Hau14, Proposition 5.4 (6)]; [Hau03, Appendix C (7)]; [Sta, Tag 00TU].
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal
open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `Ω[𝒪_{X,x}⁄k]` is a finite free module at every point of a scheme smooth over `k`: the base
change of `Ω[Γ(V)⁄k]`, free and finite on a standard smooth affine neighbourhood `V ∋ x`. -/
theorem free_finite_kaehlerDifferential_stalk [Smooth f] (x : X) :
    letI := f.stalkAlgebra x
    Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧
      Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := by
  obtain ⟨U, hU, hxU, hstd⟩ := exists_affineOpen_isStandardSmooth f x
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_sectionsAlgebra hU
  set e := (IsLocalizedModule.isBaseChange (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk x))).equiv
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- The stalk of a scheme smooth over `k` is essentially of finite type over `k` (the form of
`essFiniteType_stalk` without a relative dimension). -/
theorem essFiniteType_stalk_of_smooth [Smooth f] (x : X) :
    letI := f.stalkAlgebra x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_sectionsAlgebra hU
  have : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp k Γ(X, U) (X.presheaf.stalk x)

/-- The residue field of the stalk is essentially of finite type over `k`. -/
theorem essFiniteType_residueField_stalk_of_smooth [Smooth f] (x : X) :
    letI := f.stalkAlgebra x
    Algebra.EssFiniteType k (ResidueField (X.presheaf.stalk x)) := by
  let _ := f.stalkAlgebra x
  have := essFiniteType_stalk_of_smooth f x
  have : Algebra.EssFiniteType (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)) :=
    inferInstanceAs (Algebra.EssFiniteType (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x)))
  exact Algebra.EssFiniteType.comp k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))

/-- At any point `x` of `X` smooth over the perfect field `k`, a regular system of parameters `z` of
`𝒪_{X,x}` has dual derivations over `k`: `D_i z_j = δ_{ij}` ([Sta, Tag 00TU] for the injectivity of
the conormal map). -/
theorem exists_derivation_dual [PerfectField k] [Smooth f] (x : X) {n : ℕ}
    (z : Fin n → X.presheaf.stalk x)
    (hz : maximalIdeal (X.presheaf.stalk x) = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) :
    letI := f.stalkAlgebra x
    ∃ D : Fin n → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x),
      ∀ i j, D i (z j) = if i = j then 1 else 0 := by
  classical
  let _ := f.stalkAlgebra x
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f x
  obtain ⟨hfree, hfin⟩ := free_finite_kaehlerDifferential_stalk f x
  -- the classes of the `z_i` form a basis of the cotangent space
  obtain ⟨b, hb⟩ := exists_basis_cotangentSpace_of_span_eq z hz hn
  have := essFiniteType_residueField_stalk_of_smooth f x
  have hfs : Algebra.FormallySmooth k (ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallySmooth.of_perfectField
  have hinj := KaehlerDifferential.injective_cotangentSpaceToTensor k (X.presheaf.stalk x)
  -- hence the `1 ⊗ dz_i` are linearly independent in `κ ⊗ Ω`
  have hli : LinearIndependent (ResidueField (X.presheaf.stalk x)) fun i =>
      (1 : ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
        KaehlerDifferential.D k (X.presheaf.stalk x) (z i) := by
    have h := b.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinj)
    have hfun : (⇑(KaehlerDifferential.cotangentSpaceToTensor k (X.presheaf.stalk x)) ∘ ⇑b) =
        fun i => (1 : ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
          KaehlerDifferential.D k (X.presheaf.stalk x) (z i) := by
      funext i
      simp only [Function.comp_apply, hb, KaehlerDifferential.cotangentSpaceToTensor_toCotangent]
    rw [hfun] at h
    exact h
  -- the linear map `e_i ↦ dz_i` and its base change
  set l : (Fin n → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k] :=
    (Pi.basisFun (X.presheaf.stalk x) (Fin n)).constr ℕ fun i =>
      KaehlerDifferential.D k (X.presheaf.stalk x) (z i) with hl_def
  have hl : ∀ i, l (Pi.single i 1) = KaehlerDifferential.D k (X.presheaf.stalk x) (z i) := by
    intro i
    have := (Pi.basisFun (X.presheaf.stalk x) (Fin n)).constr_basis ℕ
      (fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) i
    rwa [Pi.basisFun_apply] at this
  set bκ :=
    (Pi.basisFun (X.presheaf.stalk x) (Fin n)).baseChange (ResidueField (X.presheaf.stalk x))
    with hbκ
  have hval : ∀ i, (l.baseChange (ResidueField (X.presheaf.stalk x))) (bκ i) =
      (1 : ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
        KaehlerDifferential.D k (X.presheaf.stalk x) (z i) := by
    intro i
    rw [hbκ, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, Pi.basisFun_apply, hl]
  have hinj' : Function.Injective (l.baseChange (ResidueField (X.presheaf.stalk x))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : (l.baseChange (ResidueField (X.presheaf.stalk x)))
        (∑ i, bκ.repr v i • bκ i) = 0 := by
      rwa [bκ.sum_repr v]
    simp only [map_sum, map_smul, hval] at hv'
    have h0 := (Fintype.linearIndependent_iff.mp hli) (fun i => bκ.repr v i) hv'
    exact bκ.repr.map_eq_zero_iff.mp (Finsupp.ext h0)
  have hinj'' : Function.Injective (l.lTensor (ResidueField (X.presheaf.stalk x))) := by
    rw [← LinearMap.baseChange_eq_lTensor]
    exact hinj'
  obtain ⟨l', hl'⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).mpr hinj''
  refine ⟨fun i => (LinearMap.proj i ∘ₗ l').compDer (KaehlerDifferential.D k (X.presheaf.stalk x)),
    fun i j => ?_⟩
  change (LinearMap.proj i ∘ₗ l') (KaehlerDifferential.D k (X.presheaf.stalk x) (z j)) = _
  have h := LinearMap.congr_fun hl' (Pi.single j 1)
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h
  rw [← hl j, LinearMap.comp_apply, h, LinearMap.proj_apply, Pi.single_apply]

end AlgebraicGeometry
