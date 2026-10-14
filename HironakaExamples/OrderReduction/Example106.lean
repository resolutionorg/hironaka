/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.Balanced.Example106
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.Smooth.Graph
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import Hironaka.Scheme.Smooth.Origin
import HironakaExamples.Sequence.CosuppForcing
import HironakaExamples.Sequence.Remark33Warning63
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Kollár's Example 106 for the order-reduction functor: the affine space and its origin

[Kol07, Example 106] follows the principalization of the ideal `I = (x³ − y², x⁴ + xz² − w³)` of a
subvariety `X ⊂ 𝔸⁴`: `ord I = 2`, `H = (y = 0)` is a hypersurface of maximal contact, and the first
blow-up is that of the origin. This module and
`HironakaExamples/OrderReduction/Example106BlowUp.lean`, `Example106Length.lean` follow the
order-reduction functor `BO_{4,2}` of [Kol07, Theorem 103] on the triple `(𝔸⁴_ℚ, I, ∅)`. The
statements are about any smooth blow-up sequence with the three properties of the functor's values,
an order-`2` sequence ([Kol07, Definition 66]), no empty centre ([Kol07, 32]) and final maximal
order `< 2` (clause (1) of Theorem 103), through the cosupport forcing of
`HironakaExamples/Sequence/CosuppForcing.lean`: at each stage the next centre is supported at the
order-`2` locus of the current ideal. The computations are made at every scheme point of
`𝔸⁴_ℚ = Spec ℚ[x, y, z, w]`, not only at its `ℚ`-points. This module treats the first stage:

* the cosupport `{p : ord_p I ≥ 2}` is the origin alone (`two_le_ord_iff`): by the derivative
  criterion `c ≤ ord_p I ⟺ D^{c−1}(I) ⊆ 𝔭` ([Kol07, Lemma 74 (3)]) and
  `D(I) = (x², y, z², xz, w²)` (`HironakaExamples/Balanced/Example106.lean`), a prime containing
  `D(I)` contains every coordinate;
* `max-ord I ≤ 2` at every point (`maxOrd_le_two`): `D²(I) = (1)`, since `∂y/∂y = 1`;
* the reduced origin is the ideal sheaf of `(x, y, z, w)` (`vanishingIdeal_singleton_origin`):
  the maximal ideal is prime, hence radical, with support the origin;
* the forcing applied (`exists_eq_cons_specIdealSheaf_m0`): every order-`2` sequence for `(I, ∅)`
  on `𝔸⁴_ℚ` with no empty centre and final maximal order `< 2` begins with the blow-up of the
  origin, Kollár's "thus the first step is to blow up the origin in `𝔸⁴`";
* the inputs making `(𝔸⁴_ℚ, I, ∅)` a triple (`isNonzeroEverywhere_I106`, the smoothness of
  `𝔸⁴_ℚ → Spec ℚ`; the normal crossings of the empty boundary are
  `Hironaka/Scheme/Snc/EmptyFamily.lean`);
* Kollár's closing sentences as printed (`strictTransform_meets_plane_ideal`; see also
  [Kol07, Warning 23]): in the `x`-chart the strict transform `X₁ = (x₁ − y₁², x₁ + z₁² − w₁³)`
  meets the plane `(x₁ = y₁ = 0)` in the cuspidal curve `(x₁ = y₁ = z₁² − w₁³ = 0)`.

The worked example is completed in `HironakaExamples/KollarExample106Run.lean`, where these
facts are applied to the sequence produced by the functor `Hironaka.BO.data 4 2`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence Hironaka.Examples.Example106

namespace Hironaka.Examples.Example106BO

/-- `x = X 0` in `ℚ[x, y, z, w]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y = X 1` in `ℚ[x, y, z, w]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 4) ℚ)
/-- `z = X 2` in `ℚ[x, y, z, w]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 4) ℚ)
/-- `w = X 3` in `ℚ[x, y, z, w]`. -/
local notation "w" => (X 3 : MvPolynomial (Fin 4) ℚ)
/-- The affine space `𝔸⁴_ℚ`. -/
local notation "𝔸⁴" => Spec (CommRingCat.of (MvPolynomial (Fin 4) ℚ))

/-! ### The origin -/

/-- The ideal `𝔪₀ = (x, y, z, w)` is the prime ideal of the origin of `𝔸⁴_ℚ`. -/
theorem m0_eq_origin_asIdeal : m0 = (origin ℚ 4).asIdeal :=
  le_antisymm
    (Ideal.span_le.mpr (by rintro g (rfl | rfl | rfl | rfl) <;> exact X_mem_origin_asIdeal ℚ 4 _))
    (origin_asIdeal_le_of_forall_X_mem ℚ 4 m0 fun i =>
      Ideal.subset_span (by fin_cases i <;> simp))

/-- The origin is a closed point of `𝔸⁴_ℚ`: its prime ideal is maximal. -/
theorem isClosed_singleton_origin : IsClosed ({origin ℚ 4} : Set 𝔸⁴) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (isMaximal_ratPoint_asIdeal _)

/-! ### The cosupport of `(I, 2)` and the max-order -/

/-- At every scheme point `p` of `𝔸⁴_ℚ`, `ord_p I ≥ 2` iff `p` is the origin ([Kol07, Example 106]:
"`ord I = 2` … the first step is to blow up the origin"): the derivative criterion of
[Kol07, Lemma 74 (3)] with `D(I) = (x², y, z², xz, w²)`; a prime containing `x²`, `y`, `z²`, `w²`
contains the four coordinates. -/
theorem two_le_ord_iff (p : 𝔸⁴) :
    ((2 : ℕ) : ℕ∞) ≤ (specIdealSheaf I106).ord p ↔ p = origin ℚ 4 := by
  rw [le_ord_specIdealSheaf_iff I106 p one_le_two]
  have h1 : Ideal.derivativeIter ℚ (2 - 1) I106 = D106 := by
    rw [show (2 : ℕ) - 1 = 0 + 1 from rfl, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero,
      derivative_example106]
  rw [h1, eq_origin_iff_forall_X_mem]
  constructor
  · intro h i
    fin_cases i
    · exact p.isPrime.mem_of_pow_mem 2 (h x_sq_mem_D106)
    · exact h y_mem_D106
    · exact p.isPrime.mem_of_pow_mem 2 (h z_sq_mem_D106)
    · exact p.isPrime.mem_of_pow_mem 2 (h w_sq_mem_D106)
  · intro h
    exact D106_le_m0.trans (Ideal.span_le.mpr (by rintro g (rfl | rfl | rfl | rfl) <;> exact h _))

/-- `max-ord I ≤ 2` on `𝔸⁴_ℚ` at every scheme point ([Kol07, Example 106]: "`ord I = 2`"):
`D²(I) = (1)`, because `y ∈ D(I)` and `∂y/∂y = 1`, so no prime contains `D²(I)`. -/
theorem maxOrd_le_two : (specIdealSheaf I106).maxOrd ≤ ((2 : ℕ) : ℕ∞) := by
  refine (maxOrd_le_iff _).mpr fun p => ?_
  by_contra h
  have h3 : ((3 : ℕ) : ℕ∞) ≤ (specIdealSheaf I106).ord p := by
    exact_mod_cast Order.add_one_le_of_lt (not_le.mp h)
  rw [le_ord_specIdealSheaf_iff I106 p (by norm_num)] at h3
  have h1 : Ideal.derivativeIter ℚ (3 - 1) I106 = Ideal.derivative ℚ D106 := by
    rw [show (3 : ℕ) - 1 = 0 + 1 + 1 from rfl, Ideal.derivativeIter_succ, Ideal.derivativeIter_succ,
      Ideal.derivativeIter_zero, derivative_example106]
  rw [h1] at h3
  have hone : (1 : MvPolynomial (Fin 4) ℚ) ∈ Ideal.derivative ℚ D106 := by
    have := Ideal.derivation_apply_mem_derivative (pderiv (1 : Fin 4)) y_mem_D106
    rwa [pderiv_X_self] at this
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (h3 hone))

/-! ### The reduced origin -/

/-- The support of the ideal sheaf of `𝔪₀` is the origin. -/
theorem support_specIdealSheaf_m0 :
    (specIdealSheaf m0).support = ⟨{origin ℚ 4}, isClosed_singleton_origin⟩ := by
  ext p
  simp only [SetLike.mem_coe, Closeds.coe_mk, Set.mem_singleton_iff]
  rw [mem_support_specIdealSheaf_iff, eq_origin_iff_forall_X_mem]
  constructor
  · intro h i
    exact h (Ideal.subset_span (by fin_cases i <;> simp))
  · intro h
    exact Ideal.span_le.mpr (by rintro g (rfl | rfl | rfl | rfl) <;> exact h _)

/-- The vanishing ideal sheaf of the origin is the ideal sheaf of `𝔪₀ = (x, y, z, w)`, the reduced
origin: a prime ideal is radical. -/
theorem vanishingIdeal_singleton_origin :
    vanishingIdeal ⟨{origin ℚ 4}, isClosed_singleton_origin⟩ = specIdealSheaf m0 := by
  rw [← support_specIdealSheaf_m0, vanishingIdeal_support]
  have hbij : Function.Bijective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 4) ℚ))).inv.hom :=
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 4) ℚ))).symm.commRingCatIsoToRingEquiv.bijective
  have : m0.IsPrime := by rw [m0_eq_origin_asIdeal]; exact (origin ℚ 4).isPrime
  have hprime : (m0.map (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 4) ℚ))).inv.hom).IsPrime :=
    Ideal.map_isPrime_of_surjective hbij.2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hbij.1]; exact bot_le)
  rw [eq_specIdealSheaf (specIdealSheaf m0).radical]
  congr 1
  rw [radical_ideal, specIdealSheaf_ideal_top, hprime.radical, Ideal.comap_map_of_bijective _ hbij]

/-! ### The forcing applied to the first stage -/

/-- Every smooth blow-up sequence of order `2` for `(𝔸⁴_ℚ, I, E)` with no empty centre whose final
weak transform has maximal order `< 2` begins with the blow-up of the reduced origin
([Kol07, Example 106]: "thus the first step is to blow up the origin in `𝔸⁴`"): the cosupport
forcing of `HironakaExamples/Sequence/CosuppForcing.lean` at `two_le_ord_iff`. -/
theorem exists_eq_cons_specIdealSheaf_m0 (S : BlowUpSequence 𝔸⁴) (E : DivisorFamily 𝔸⁴)
    (hS : S.IsOrderSeq (affineSpaceToSpec ℚ 4) (specIdealSheaf I106) E 2) (hne : S.NoEmptyCenters)
    (hend : (S.weakTransformSeq (specIdealSheaf I106) (Fin.last _)).maxOrd < ((2 : ℕ) : ℕ∞)) :
    ∃ rest : BlowUpSequence (specIdealSheaf m0).blowUp,
      S = cons 𝔸⁴ (specIdealSheaf m0) rest := by
  have : SmoothOfRelativeDimension 4 (affineSpaceToSpec ℚ 4) :=
    CoordinateSubspace.smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial ℚ 4
  have : Smooth (affineSpaceToSpec ℚ 4) := SmoothOfRelativeDimension.smooth 4 _
  exact exists_eq_cons_of_ord_le_iff_of_eq_vanishingIdeal S (affineSpaceToSpec ℚ 4)
    (specIdealSheaf I106) E 2 hS hne hend isClosed_singleton_origin two_le_ord_iff
    vanishingIdeal_singleton_origin

/-! ### Well-formedness inputs -/

/-- `I ≠ 0`: the generator `x³ − y²` has coefficient `1` at `x³`. -/
theorem I106_ne_bot : I106 ≠ ⊥ := by
  intro h
  have hmem : x ^ 3 - y ^ 2 ∈ I106 := Ideal.subset_span (by simp)
  rw [h, Ideal.mem_bot] at hmem
  have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single (0 : Fin 4) 3)) hmem
  simp [coeff_X_pow, Finsupp.single_eq_single_iff] at this

/-- `I` is nonzero on every irreducible component of `𝔸⁴_ℚ` ([Kol07, Notation 64 (2)]): its stalk
at every point is the image of the nonzero ideal `I` under the injective localisation map of the
domain `ℚ[x, y, z, w]`. -/
theorem isNonzeroEverywhere_I106 : IsNonzeroEverywhere (specIdealSheaf I106) := by
  intro p
  rw [stalkIdeal_specIdealSheaf]
  obtain ⟨q, rfl⟩ : ∃ q : PrimeSpectrum (MvPolynomial (Fin 4) ℚ), q = p := ⟨p, rfl⟩
  have hinj : Function.Injective (StructureSheaf.toStalk (MvPolynomial (Fin 4) ℚ) q).hom :=
    IsLocalization.injective ((Spec.structureSheaf (MvPolynomial (Fin 4) ℚ)).presheaf.stalk q)
      (Ideal.primeCompl_le_nonZeroDivisors q.asIdeal)
  exact fun h => I106_ne_bot ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)

/-- `𝔸⁴_ℚ → Spec ℚ` is smooth of relative dimension `4`. -/
theorem smoothOfRelativeDimension_affineSpaceToSpec :
    SmoothOfRelativeDimension 4 (affineSpaceToSpec ℚ 4) :=
  CoordinateSubspace.smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial ℚ 4

/-- `𝔸⁴_ℚ → Spec ℚ` is smooth. -/
theorem smooth_affineSpaceToSpec : Smooth (affineSpaceToSpec ℚ 4) :=
  have := smoothOfRelativeDimension_affineSpaceToSpec
  SmoothOfRelativeDimension.smooth 4 _

/-! ### Kollár's closing sentences, as printed -/

/-- Kollár's closing sentences as printed ([Kol07, Example 106]; see also [Kol07, Warning 23]): in
the `x`-chart `ℚ[x₁, y₁, z₁, w₁]` (the variables `X 0, …, X 3`) the strict transform
`X₁ = (x₁ − y₁², x₁ + z₁² − w₁³)` meets the plane `(x₁ = y₁ = 0)` in the cuspidal curve
`(x₁ = y₁ = z₁² − w₁³ = 0)`. -/
theorem strictTransform_meets_plane_ideal :
    Ideal.span {x - y ^ 2, x + z ^ 2 - w ^ 3} ⊔ Ideal.span {x, y} =
      (Ideal.span {x, y, z ^ 2 - w ^ 3} : Ideal (MvPolynomial (Fin 4) ℚ)) := by
  apply le_antisymm
  · refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro g (rfl | rfl)
      · exact Ideal.sub_mem _ (Ideal.subset_span (by simp))
          (Ideal.pow_mem_of_mem _ (Ideal.subset_span (by simp)) 2 two_pos)
      · rw [add_sub_assoc]
        exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    · rintro g (rfl | rfl) <;> exact Ideal.subset_span (by simp)
  · refine Ideal.span_le.mpr ?_
    rintro g (rfl | rfl | rfl)
    · exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
    · exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
    · have : z ^ 2 - w ^ 3 = (x + z ^ 2 - w ^ 3) - x := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.subset_span (by simp)))
        (Ideal.mem_sup_right (Ideal.subset_span (by simp)))

end Hironaka.Examples.Example106BO
