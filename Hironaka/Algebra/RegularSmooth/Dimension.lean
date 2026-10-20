/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Smooth.StandardSmooth
import Hironaka.Algebra.RegularSmooth.Cotangent
import Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular
import Hironaka.Algebra.RegularSmooth.Trdeg
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# The dimension of a smooth local ring

For `S` standard smooth of relative dimension `n` over a perfect field `k` and a prime `𝔮`, with
`R = S_𝔮` and `κ = κ(𝔮)`: `R` is regular
(`Hironaka/Algebra/RegularSmooth/SmoothImpliesRegular.lean`), so `dim R = dim_κ 𝔪/𝔪²`; the conormal
sequence is short exact (`Cotangent.lean`), so `dim_κ 𝔪/𝔪² + dim_κ Ω[κ⁄k] = dim_κ κ ⊗[R] Ω[R⁄k]`;
and `κ ⊗[R] Ω[R⁄k] = κ ⊗[S] Ω[S⁄k]` has dimension `n` (`Ω[S⁄k]` is free of rank `n`; `Ω[R⁄k] = R
⊗[S] Ω[S⁄k]` because a localization is formally étale). Hence `dim R + dim_κ Ω[κ⁄k] = n`. With
`dim_κ Ω[κ⁄k] = trdeg_k κ` (`Trdeg.lean`) this is the formula `dim S_𝔮 + trdeg_k κ(𝔮) = n` of [Sta,
Tag 0A21, (10)]; at a maximal ideal `κ` is finite over `k` (Zariski's lemma, Mathlib's
`finite_of_finite_type_of_isJacobsonRing`), hence separable algebraic over the perfect field `k`, so
`Ω[κ⁄k] = 0` and `dim S_𝔮 = n`. The dimension arithmetic is additive in `WithBot ℕ∞`, the
transcendence degree entering through `Cardinal.toENat`. The scheme forms are in
`Hironaka/Algebra/RegularSmooth/SchemeForms.lean`.
-/

public section

universe u

open IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace Algebra.IsStandardSmoothOfRelativeDimension

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]

/-- The core count: for `S` standard smooth of relative dimension `n` over a perfect field `k` and
`𝔮` a prime, `dim S_𝔮 + dim_κ Ω[κ(𝔮)⁄k] = n`, with `κ = κ(𝔮)` the residue field. -/
theorem ringKrullDim_localization_add_finrank_kaehlerDifferential_residueField [PerfectField k]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k S] (𝔮 : Ideal S) [𝔮.IsPrime] :
    ringKrullDim (Localization.AtPrime 𝔮) +
      (Module.finrank 𝔮.ResidueField Ω[𝔮.ResidueField⁄k] : WithBot ℕ∞) = n := by
  have : Algebra.IsStandardSmooth k S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := k)
  have hreg : IsRegularLocalRing (Localization.AtPrime 𝔮) :=
    Algebra.IsStandardSmooth.isRegularLocalRing_localization_atPrime (k := k) 𝔮
  have hdim : ringKrullDim (Localization.AtPrime 𝔮) =
      (Module.finrank 𝔮.ResidueField (CotangentSpace (Localization.AtPrime 𝔮)) : WithBot ℕ∞) := by
    rw [← hreg.spanFinrank_maximalIdeal, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  have : Algebra.EssFiniteType k (Localization.AtPrime 𝔮) :=
    Algebra.EssFiniteType.comp k S (Localization.AtPrime 𝔮)
  have : Algebra.EssFiniteType k 𝔮.ResidueField := Algebra.EssFiniteType.comp k S 𝔮.ResidueField
  have : Algebra.FormallySmooth k 𝔮.ResidueField := Algebra.FormallySmooth.of_perfectField
  have hcount :=
    _root_.KaehlerDifferential.finrank_residueField_tensor_kaehlerDifferential k
      (Localization.AtPrime 𝔮)
  have hn : Module.finrank 𝔮.ResidueField
      (𝔮.ResidueField ⊗[Localization.AtPrime 𝔮] Ω[Localization.AtPrime 𝔮⁄k]) = n := by
    have : Algebra.FormallyEtale S (Localization.AtPrime 𝔮) :=
      Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.AtPrime 𝔮) 𝔮.primeCompl
    let e₁ := tensorKaehlerEquivOfFormallyEtale k S (Localization.AtPrime 𝔮)
    let e₂ := TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl 𝔮.ResidueField 𝔮.ResidueField) e₁
    let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange S (Localization.AtPrime 𝔮)
      𝔮.ResidueField 𝔮.ResidueField Ω[S⁄k]
    rw [(e₂.symm.trans e₃).finrank_eq]
    exact
      Algebra.IsStandardSmoothOfRelativeDimension.finrank_residueField_tensor_kaehlerDifferential
        n 𝔮
  rw [hdim, ← Nat.cast_add, ← hcount, hn]

/-- For `k` perfect and `S` standard smooth of relative dimension `n` over `k`,
`dim S_𝔮 + trdeg_k κ(𝔮) = n` at every prime `𝔮` [Sta, Tag 0A21, (10)]. -/
theorem ringKrullDim_localization_add_trdeg_residueField [PerfectField k] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k S] (𝔮 : Ideal S) [𝔮.IsPrime] :
    ringKrullDim (Localization.AtPrime 𝔮) +
      ((Cardinal.toENat (Algebra.trdeg k 𝔮.ResidueField) : ℕ∞) : WithBot ℕ∞) = n := by
  rw [← ringKrullDim_localization_add_finrank_kaehlerDifferential_residueField (k := k) n 𝔮]
  congr 1
  have : Algebra.IsStandardSmooth k S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := k)
  have : Algebra.FiniteType k S := Algebra.FiniteType.of_finitePresentation
  have : Algebra.EssFiniteType k 𝔮.ResidueField := Algebra.EssFiniteType.comp k S 𝔮.ResidueField
  rw [← Algebra.rank_kaehlerDifferential_eq_trdeg_of_perfectField k 𝔮.ResidueField,
    ← Module.finrank_eq_rank, Cardinal.toENat_nat]
  norm_cast

/-- For `k` perfect, `S` standard smooth of relative dimension `n` over `k` and `𝔮` a maximal
ideal, `dim S_𝔮 = n`: the residue field is finite over `k` by Zariski's lemma. -/
theorem ringKrullDim_localization_of_isMaximal [PerfectField k] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k S] (𝔮 : Ideal S) [𝔮.IsMaximal] :
    ringKrullDim (Localization.AtPrime 𝔮) = n := by
  have h := ringKrullDim_localization_add_finrank_kaehlerDifferential_residueField (k := k) n 𝔮
  have : Algebra.IsStandardSmooth k S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := k)
  have : Algebra.FiniteType k S := Algebra.FiniteType.of_finitePresentation
  let : Field (S ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have : Module.Finite k (S ⧸ 𝔮) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ 𝔮)
  have : Module.Finite k 𝔮.ResidueField :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom k (S ⧸ 𝔮) 𝔮.ResidueField).toLinearMap
      (Ideal.bijective_algebraMap_quotient_residueField 𝔮).surjective
  have : Subsingleton Ω[𝔮.ResidueField⁄k] :=
    Algebra.subsingleton_kaehlerDifferential_of_isSeparable k 𝔮.ResidueField
  rwa [Module.finrank_zero_of_subsingleton, Nat.cast_zero, add_zero] at h

end Algebra.IsStandardSmoothOfRelativeDimension
