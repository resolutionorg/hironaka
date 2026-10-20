/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Stalk
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Algebra.RegularSmooth.Cotangent
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Algebra.RegularSmooth.Trdeg
import Hironaka.Algebra.Smooth.SpreadOut
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Mathlib.Algebra.Module.SpanRankOperations

/-!
# Differentials of a regular system of parameters at a closed point

`f : X ⟶ Spec k` smooth of relative dimension `n` over a perfect field, `x ∈ X` a closed point,
`𝒪 = 𝒪_{X,x}`, `κ = κ(x)`. The main theorem: for a regular system of parameters `y_0, …, y_{n-1}`
of `𝒪`, the classes `1 ⊗ d y_i` form a basis of `κ ⊗_𝒪 Ω[𝒪⁄k]`
(`exists_basis_tensor_kaehlerDifferential_of_span_eq_maximalIdeal`), the differentials of Kollár's
local coordinates at a point of a smooth variety ([Kol07, Definition 24]). The argument assembles
the comparison of regular and smooth points of `Hironaka/Algebra/RegularSmooth/`: the conormal map
`𝔪/𝔪² → κ ⊗ Ω[𝒪⁄k]`, `ȳ ↦ 1 ⊗ d y`, is injective because `κ` is formally smooth over the perfect
`k` ([Sta, Tag 00TU]; `injective_cotangentSpaceToTensor`); the classes of the `y_i` form a basis
of `𝔪/𝔪²` (Nakayama, `Hironaka/Algebra/Local/RegularSystem.lean`); and
`dim_κ κ ⊗ Ω[𝒪⁄k] = dim_κ 𝔪/𝔪² + dim_κ Ω[κ⁄k] = n + 0` (the conormal sequence of [Sta, Tag 00TV];
`𝔪/𝔪²` has dimension `dim 𝒪 = n` at a closed point by regularity, and `Ω[κ⁄k] = 0` because
`trdeg_k κ = 0` there). An injective map from an `n`-dimensional space to an `n`-dimensional
space carries a basis to a basis.

Used to spread adapted parameters out to étale coordinates on an affine neighbourhood
(`Hironaka/Scheme/Smooth/EtaleLocal.lean`, `EtaleCoordinatesAdapted.lean`,
`CoordinateSystemPair.lean`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing KaehlerDifferential TensorProduct

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

section Arithmetic

/-- `n + t = n` in `WithBot ℕ∞` forces `t = 0`. -/
theorem enat_eq_zero_of_natCast_add_eq {n : ℕ} {t : ℕ∞}
    (h : (n : WithBot ℕ∞) + (t : WithBot ℕ∞) = (n : WithBot ℕ∞)) : t = 0 := by
  have ht : t ≠ ⊤ := by
    rintro rfl
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, add_top] at h
    exact ENat.top_ne_natCast n (WithBot.coe_inj.mp h)
  lift t to ℕ using ht with t' ht'
  have h1 : n + t' = n := by exact_mod_cast h
  have h2 : t' = 0 := by omega
  exact_mod_cast h2

end Arithmetic

section Stalk

variable (n : ℕ) [SmoothOfRelativeDimension n f] (x : X)
include f n

/-- The stalk of a scheme locally of finite type over `k` is essentially of finite type over
`k`. -/
theorem essFiniteType_stalk :
    letI := f.stalkAlgebra x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
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
theorem essFiniteType_residueField_stalk :
    letI := f.stalkAlgebra x
    Algebra.EssFiniteType k (ResidueField (X.presheaf.stalk x)) := by
  let _ := f.stalkAlgebra x
  have := essFiniteType_stalk f n x
  have : Algebra.EssFiniteType (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)) :=
    inferInstanceAs (Algebra.EssFiniteType (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x)))
  exact Algebra.EssFiniteType.comp k (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))

/-- `Ω[𝒪_{X,x}⁄k]` is a finite `𝒪_{X,x}`-module (the localization of the finite module
`Ω[Γ(U)⁄k]` of a standard smooth affine chart). -/
theorem finite_kaehlerDifferential_stalk :
    letI := f.stalkAlgebra x
    Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := by
  obtain ⟨U, hU, hxU, hstd⟩ := f.exists_affineOpen_isStandardSmoothOfRelativeDimension n x
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := k)
  exact Algebra.finite_kaehlerDifferential_of_isLocalization (k := k)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl

variable [PerfectField k] {x} (hx : IsClosed ({x} : Set X))
include hx

/-- At a closed point the residue field is algebraic over `k`: `trdeg_k κ(x) = 0` (the dimension
formula `dim 𝒪_{X,x} + trdeg_k κ(x) = n` with `dim 𝒪_{X,x} = n`). -/
theorem trdeg_residueField_stalk_eq_zero_of_isClosed :
    letI := f.stalkAlgebra x
    Algebra.trdeg k (ResidueField (X.presheaf.stalk x)) = 0 := by
  let _ := f.stalkAlgebra x
  have h := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension f n x
  have hd := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed f n hx
  rw [hd] at h
  exact Cardinal.toENat_eq_zero.mp (enat_eq_zero_of_natCast_add_eq h)

/-- At a closed point `dim_κ 𝔪_x/𝔪_x² = n` (regularity of the stalk and `dim 𝒪_{X,x} = n`). -/
theorem finrank_cotangentSpace_stalk_of_isClosed :
    Module.finrank (ResidueField (X.presheaf.stalk x)) (CotangentSpace (X.presheaf.stalk x)) =
      n := by
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg := isRegularLocalRing_stalk f x
  have hd := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed f n hx
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := X.presheaf.stalk x)
  rw [hd] at h
  exact_mod_cast h

/-- At a closed point `dim_κ κ(x) ⊗ Ω[𝒪_{X,x}⁄k] = n` (the short exact conormal sequence, with
`Ω[κ(x)⁄k] = 0`). -/
theorem finrank_residueField_tensor_kaehler_stalk_of_isClosed :
    letI := f.stalkAlgebra x
    Module.finrank (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]) = n := by
  let _ := f.stalkAlgebra x
  have := essFiniteType_stalk f n x
  have := essFiniteType_residueField_stalk f n x
  have : Algebra.FormallySmooth k (ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallySmooth.of_perfectField
  rw [finrank_residueField_tensor_kaehlerDifferential k (X.presheaf.stalk x),
    finrank_cotangentSpace_stalk_of_isClosed f n hx]
  have h0 : Module.rank (ResidueField (X.presheaf.stalk x))
      Ω[ResidueField (X.presheaf.stalk x)⁄k] = ((0 : ℕ) : Cardinal) := by
    rw [Algebra.rank_kaehlerDifferential_eq_trdeg_of_perfectField,
      trdeg_residueField_stalk_eq_zero_of_isClosed f n hx, Nat.cast_zero]
  rw [Module.finrank_eq_of_rank_eq h0, add_zero]

/-- The differentials of a regular system of parameters at a closed point form a basis of
`κ(x) ⊗ Ω[𝒪_{X,x}⁄k]` ([Sta, Tag 00TU]; the local coordinates of [Kol07, Definition 24] at a
closed point). -/
theorem exists_basis_tensor_kaehlerDifferential_of_span_eq_maximalIdeal
    (y : Fin n → X.presheaf.stalk x)
    (hy : maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y)) :
    letI := f.stalkAlgebra x
    ∃ b : Module.Basis (Fin n) (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]),
      ∀ i, b i = 1 ⊗ₜ D k (X.presheaf.stalk x) (y i) := by
  let _ := f.stalkAlgebra x
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg := isRegularLocalRing_stalk f x
  have hd := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed f n hx
  obtain ⟨c, hc⟩ := exists_basis_cotangentSpace_of_span_eq y hy hd.symm
  have := essFiniteType_stalk f n x
  have := essFiniteType_residueField_stalk f n x
  have := finite_kaehlerDifferential_stalk f n x
  have : Algebra.FormallySmooth k (ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallySmooth.of_perfectField
  have hinj := injective_cotangentSpaceToTensor k (X.presheaf.stalk x)
  have hli : LinearIndependent (ResidueField (X.presheaf.stalk x))
      (cotangentSpaceToTensor k (X.presheaf.stalk x) ∘ c) :=
    c.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinj)
  have hcard : Fintype.card (Fin n) = Module.finrank (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]) := by
    rw [Fintype.card_fin, finrank_residueField_tensor_kaehler_stalk_of_isClosed f n hx]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli hcard, fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', Function.comp_apply, hc i,
    cotangentSpaceToTensor_toCotangent]

end Stalk

end AlgebraicGeometry
