/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.SmoothDivisor
public import Hironaka.Algebra.RegularSmooth.SmoothAt
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.RegularSmooth.Cotangent
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular
import Hironaka.Algebra.RegularSmooth.Trdeg
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.SubschemeStalk
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Smooth divisors are smooth of relative dimension `n − 1`

The converse of `isSmoothDivisor_of_smoothOfRelativeDimension`
(`Hironaka.Scheme.Snc.SmoothDivisor`): a smooth divisor `D` of `X`, smooth of relative dimension `n`
over the perfect field `k`, is smooth of relative dimension `n − 1` over `k` — for every `n`, with
`n − 1` the truncated difference (at `n = 0` the stalks are fields and a smooth divisor is empty).
The closed subscheme `V(D)` is regular, hence smooth over `k`
(`Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv`); its relative dimension is read off at one
point of each affine chart: for a standard smooth `k`-algebra `S` the module `Ω[S⁄k]` is free, so
its rank is `dim_κ κ(𝔮) ⊗ Ω[S⁄k]` at any prime `𝔮`, which is `dim S_𝔮 + trdeg_k κ(𝔮)` (the dimension
count of `Hironaka.Algebra.RegularSmooth.Dimension`), and Mathlib's
`IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` turns the rank into the relative
dimension. At a point `z` of `V(D)` over `x ∈ X` the local ring is `𝒪_{X,x}/(a)` with `a ∈ 𝔪_x ∖
𝔪_x²`, of dimension `dim 𝒪_{X,x} − 1`, with the residue field of `x`, and `dim 𝒪_{X,x} + trdeg_k
κ(x) = n` (`ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension`). Together the
two directions are the equivalence "`D` is a smooth divisor iff `V(D)` is smooth of relative
dimension `n − 1`", which the passage to a hypersurface of maximal contact
(`Hironaka.Resolution.Algebraic.MaximalContact.GoingDown`) and the dimension bookkeeping of
`Hironaka.Stage` use. -/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace AlgebraicGeometry

section Ring

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]

/-- A standard smooth algebra over a perfect field whose local ring at a prime `𝔮` satisfies
`dim S_𝔮 + trdeg_k κ(𝔮) = m` is standard smooth of relative dimension `m`: `Ω[S⁄k]` is free of rank
`dim_κ κ(𝔮) ⊗ Ω[S⁄k] = dim_κ 𝔪/𝔪² + dim_κ Ω[κ(𝔮)⁄k]`, which is `dim S_𝔮 + trdeg` since `S_𝔮` is
regular (the dimension count of `Hironaka.Algebra.RegularSmooth.Dimension`). -/
theorem isStandardSmoothOfRelativeDimension_of_ringKrullDim_add_trdeg [PerfectField k]
    [Algebra.IsStandardSmooth k S] [Nontrivial S] (𝔮 : Ideal S) [𝔮.IsPrime] (m : ℕ)
    (h : ringKrullDim (Localization.AtPrime 𝔮) +
      ((Cardinal.toENat (Algebra.trdeg k 𝔮.ResidueField) : ℕ∞) : WithBot ℕ∞) = m) :
    Algebra.IsStandardSmoothOfRelativeDimension m k S := by
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth m]
  have hreg : IsRegularLocalRing (Localization.AtPrime 𝔮) :=
    Algebra.IsStandardSmooth.isRegularLocalRing_localization_atPrime (k := k) 𝔮
  have : Algebra.FiniteType k S := Algebra.FiniteType.of_finitePresentation
  have : Algebra.EssFiniteType k (Localization.AtPrime 𝔮) :=
    Algebra.EssFiniteType.comp k S (Localization.AtPrime 𝔮)
  have : Algebra.EssFiniteType k 𝔮.ResidueField := Algebra.EssFiniteType.comp k S 𝔮.ResidueField
  have : Algebra.FormallySmooth k 𝔮.ResidueField := Algebra.FormallySmooth.of_perfectField
  have hcount :=
    _root_.KaehlerDifferential.finrank_residueField_tensor_kaehlerDifferential k
      (Localization.AtPrime 𝔮)
  have hdim : ringKrullDim (Localization.AtPrime 𝔮) =
      (Module.finrank 𝔮.ResidueField (CotangentSpace (Localization.AtPrime 𝔮)) : WithBot ℕ∞) := by
    rw [← hreg.spanFinrank_maximalIdeal, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  have htr : ((Cardinal.toENat (Algebra.trdeg k 𝔮.ResidueField) : ℕ∞) : WithBot ℕ∞) =
      (Module.finrank 𝔮.ResidueField Ω[𝔮.ResidueField⁄k] : WithBot ℕ∞) := by
    rw [← Algebra.rank_kaehlerDifferential_eq_trdeg_of_perfectField k 𝔮.ResidueField,
      ← Module.finrank_eq_rank, Cardinal.toENat_nat]
    norm_cast
  rw [hdim, htr, ← Nat.cast_add, ← hcount] at h
  have hm : Module.finrank 𝔮.ResidueField
      (𝔮.ResidueField ⊗[Localization.AtPrime 𝔮] Ω[Localization.AtPrime 𝔮⁄k]) = m := by
    exact_mod_cast h
  have : Algebra.FormallyEtale S (Localization.AtPrime 𝔮) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.AtPrime 𝔮) 𝔮.primeCompl
  let e₁ := tensorKaehlerEquivOfFormallyEtale k S (Localization.AtPrime 𝔮)
  let e₂ := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl 𝔮.ResidueField 𝔮.ResidueField) e₁
  let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange S (Localization.AtPrime 𝔮)
    𝔮.ResidueField 𝔮.ResidueField Ω[S⁄k]
  rw [(e₂.symm.trans e₃).finrank_eq, Module.finrank_baseChange] at hm
  rw [← Module.finrank_eq_rank, hm]

end Ring

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The converse of `Scheme.Hom.exists_affineOpen_isStandardSmoothOfRelativeDimension`: a morphism
to `Spec k` such that every point has an affine neighbourhood `V` with `Γ(X, V)` standard smooth of
relative dimension `m` over `k` (the `k`-algebra structure through `f`) is smooth of relative
dimension `m`. -/
theorem smoothOfRelativeDimension_of_forall_exists_affineOpen (f : X ⟶ Spec (.of k))
    (m : ℕ) (h : ∀ x : X, ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      letI := f.sectionsAlgebra V
      Algebra.IsStandardSmoothOfRelativeDimension m k Γ(X, V)) :
    SmoothOfRelativeDimension m f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨V, hV, hxV, hstd⟩ := h x
  refine ⟨⊤, isAffineOpen_top _, V, hV, hxV, le_top, ?_⟩
  let := f.sectionsAlgebra V
  have h1 : RingHom.IsStandardSmoothOfRelativeDimension m (algebraMap k Γ(X, V)) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap m).mpr hstd
  exact ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := m)).cancel_left_isIso
    (Scheme.ΓSpecIso (.of k)).inv (f.appLE ⊤ V le_top)).mp h1

/-- A scheme smooth over `k` is covered by affine opens whose section rings are standard smooth
`k`-algebras (through `f`); the `Smooth` analogue of
`exists_affineOpen_isStandardSmoothOfRelativeDimension`. -/
theorem exists_affineOpen_isStandardSmooth (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      letI := f.sectionsAlgebra V
      Algebra.IsStandardSmooth k Γ(X, V) := by
  obtain ⟨U', hU', V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  have hU'top : U' = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro y
    rw [Subsingleton.elim (α := PrimeSpectrum k) y (f x)]
    exact e hxV
  subst hU'top
  refine ⟨V, hV, hxV, ?_⟩
  let := f.sectionsAlgebra V
  exact RingHom.isStandardSmooth_respectsIso.2 (f.appLE ⊤ V e).hom
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hstd

/-- Cancellation in `WithBot ℕ∞`: from `r + t = n` with `r, n` finite and `p + 1 = r`,
`p + t = n − 1`. -/
theorem natCast_add_eq_natCast_sub_one {p r n : ℕ} {t : ℕ∞}
    (hX : ((r : ℕ) : WithBot ℕ∞) + (t : WithBot ℕ∞) = (n : WithBot ℕ∞)) (hpr : p + 1 = r) :
    ((p : ℕ) : WithBot ℕ∞) + (t : WithBot ℕ∞) = ((n - 1 : ℕ) : WithBot ℕ∞) := by
  have ht : t ≠ ⊤ := by
    rintro rfl
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, add_top, ← WithBot.coe_natCast] at hX
    exact ENat.top_ne_natCast n (WithBot.coe_inj.mp hX)
  lift t to ℕ using ht with t' ht'
  have h1 : r + t' = n := by exact_mod_cast hX
  have h2 : p + t' = n - 1 := by omega
  rw [WithBot.coe_natCast, ← Nat.cast_add, h2]

/-- A smooth divisor of `X`, smooth of relative dimension `n` over the perfect field `k`, is smooth
of relative dimension `n − 1` over `k` (for every `n`, `n − 1` truncated): the converse of
`isSmoothDivisor_of_smoothOfRelativeDimension`. -/
theorem smoothOfRelativeDimension_of_isSmoothDivisor [PerfectField k] (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (D : X.IdealSheafData) (hD : IsSmoothDivisor D) :
    SmoothOfRelativeDimension (n - 1) (D.subschemeι ≫ f) := by
  have hsX : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hsD : Smooth (D.subschemeι ≫ f) :=
    (AlgebraicGeometry.Scheme.smooth_iff_isRegular (D.subschemeι ≫ f)).mpr hD.1
  refine smoothOfRelativeDimension_of_forall_exists_affineOpen _ _ fun z => ?_
  obtain ⟨V, hV, hzV, hstd⟩ := exists_affineOpen_isStandardSmooth (D.subschemeι ≫ f) z
  refine ⟨V, hV, hzV, ?_⟩
  let := (D.subschemeι ≫ f).sectionsAlgebra V
  have hstd' : Algebra.IsStandardSmooth k Γ(D.subscheme, V) := hstd
  set 𝔮 := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal with h𝔮
  have h𝔮p : 𝔮.IsPrime := (hV.primeIdealOf ⟨z, hzV⟩).isPrime
  have hnt : Nontrivial Γ(D.subscheme, V) :=
    nontrivial_of_ne 0 1 fun h => h𝔮p.ne_top ((Ideal.eq_top_iff_one _).mpr (h ▸ 𝔮.zero_mem))
  refine isStandardSmoothOfRelativeDimension_of_ringKrullDim_add_trdeg 𝔮 (n - 1) ?_
  -- transport to the stalk of `V(D)` at `z`
  let := (D.subschemeι ≫ f).stalkAlgebra z
  let := D.subscheme.presheaf.algebra_section_stalk ⟨z, hzV⟩
  have := hV.isLocalization_stalk ⟨z, hzV⟩
  have := (D.subschemeι ≫ f).isScalarTower_sectionsAlgebra_stalk V hzV
  let e : Localization.AtPrime 𝔮 ≃ₐ[k] D.subscheme.presheaf.stalk z :=
    (IsLocalization.algEquiv 𝔮.primeCompl (Localization.AtPrime 𝔮)
      (D.subscheme.presheaf.stalk z)).restrictScalars k
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, (IsLocalRing.ResidueField.mapAlgEquiv e).trdeg_eq,
    trdeg_residueField_stalk_subschemeι D f z]
  -- the stalk of `V(D)` at `z` is `𝒪_{X,x}/(a)`, `a ∈ 𝔪_x ∖ 𝔪_x²`
  have hxD : D.subschemeι z ∈ D.support :=
    (Set.ext_iff.mp D.range_subschemeι _).mp (Set.mem_range_self z)
  obtain ⟨a, ha, ha2, hDa⟩ := hD.2 (D.subschemeι z) hxD
  have hregX := isRegularLocalRing_stalk f (D.subschemeι z)
  have hq := IsRegularLocalRing.quotient_span_singleton
    (R := X.presheaf.stalk (D.subschemeι z)) ha ha2
  have hqe : ringKrullDim (D.subscheme.presheaf.stalk z) =
      ringKrullDim (X.presheaf.stalk (D.subschemeι z) ⧸ Ideal.span {a}) := by
    rw [← ringKrullDim_eq_of_ringEquiv (D.stalkQuotientEquiv z),
      ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hDa)]
  have hX := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension f n
    (D.subschemeι z)
  have := hq.1
  obtain ⟨p, hp⟩ := exists_ringKrullDim_eq_natCast
    (X.presheaf.stalk (D.subschemeι z) ⧸ Ideal.span {a})
  obtain ⟨r, hr⟩ :=
    exists_ringKrullDim_eq_natCast (X.presheaf.stalk (D.subschemeι z))
  rw [hqe, hp]
  rw [hp, hr] at hq
  rw [hr] at hX
  have hpr : p + 1 = r := by exact_mod_cast hq.2
  exact natCast_add_eq_natCast_sub_one hX hpr

end Scheme

end AlgebraicGeometry
