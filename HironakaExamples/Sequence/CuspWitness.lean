/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.Sequence.CuspModel
public import Hironaka.Scheme.BlowUpSequence.Basic
public import Hironaka.Scheme.Smooth.Graph
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.ExceptionalModel
import HironakaExamples.Local.SingularQuotient
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The blow-up of the origin restricted to the cusp

"The restriction of a smooth blow-up sequence need not be a smooth blow-up sequence" [Kol07, 30.2].
On the model of `HironakaExamples/Sequence/CuspModel.lean` (`X = 𝔸²_k`, `Z = V(x, y)`,
`S = V(y² − x³)`):

* `isSmooth_seqOrigin`: blowing up the origin is a smooth blow-up sequence; its center
  `V(x, y) ≅ Spec k` is smooth over `k` (`smooth_origin_subschemeι`: the subscheme is
  `Spec (k[x, y]/(x, y))` and `k → k[x, y]/(x, y)` is an isomorphism, every polynomial being
  congruent to its constant term), the ambient `𝔸²_k` being smooth over `k`
  (`smooth_affineSpaceToSpec_two`);
* `not_smooth_cusp`: the restricted sequence starts at `S`, which is not smooth over `k`. If it
  were, the local ring `𝒪_{S,0} = 𝒪_{𝔸²,0}/(y² − x³)` would be regular; but `𝒪_{𝔸²,0}` is
  regular, `y² − x³` is a nonzero element of `𝔪²` at the origin (`x, y ∈ 𝔪`), and the quotient of
  a regular local ring by a nonzero element of `𝔪²` is never regular
  (`HironakaExamples/Local/SingularQuotient.lean`).

The predicate `IsSmooth` is Kollár's clause on the centers; the ambient clause of
[Kol07, Notation 19], the smoothness of the stages, is the one that fails here.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial Scheme.BlowUpSequence
  Hironaka.Sequence IsLocalRing

namespace Hironaka.Sequence.Cusp

open AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The affine plane is smooth over `k` (of relative dimension `2`). -/
theorem smooth_affineSpaceToSpec_two : Smooth (affineSpaceToSpec k 2) :=
  have := CoordinateSubspace.smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial k 2
  SmoothOfRelativeDimension.smooth 2 _

/-- `1 ∉ (x, y)`. -/
theorem one_notMem_originIdeal : (1 : MvPolynomial (Fin 2) k) ∉ originCenterIdeal k := by
  rw [originCenterIdeal, ← Set.image_univ, mem_ideal_span_X_image]
  intro h
  obtain ⟨i, -, hi⟩ := h 0 (by rw [mem_support_iff, coeff_one]; simp)
  exact hi rfl

/-- Every polynomial is congruent to its constant term modulo `(x, y)`. -/
theorem sub_C_constantCoeff_mem_originIdeal (p : MvPolynomial (Fin 2) k) :
    p - C (constantCoeff p) ∈ originCenterIdeal k := by
  rw [originCenterIdeal, ← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra h
  have hm0 : m = 0 := Finsupp.ext fun i => by
    by_contra hne
    exact h ⟨i, Set.mem_univ i, hne⟩
  rw [mem_support_iff, hm0, coeff_sub, coeff_zero_C, ← constantCoeff_eq, sub_self] at hm
  exact hm rfl

/-- The composite `k → k[x, y] → k[x, y]/(x, y)` is bijective. -/
theorem bijective_mk_comp_algebraMap :
    Function.Bijective
      ((Ideal.Quotient.mk (originCenterIdeal k)).comp (algebraMap k (MvPolynomial (Fin 2) k))) := by
  have : Nontrivial (MvPolynomial (Fin 2) k ⧸ originCenterIdeal k) :=
    nontrivial_of_ne 0 1 (Ideal.Quotient.zero_ne_one_iff.mpr
      fun h => one_notMem_originIdeal k (h ▸ Submodule.mem_top))
  set φ := (Ideal.Quotient.mk (originCenterIdeal k)).comp (algebraMap k (MvPolynomial (Fin 2) k))
    with hφ
  refine ⟨?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    rcases Ideal.eq_bot_or_top (RingHom.ker φ) with h | h
    · exact h
    · have h1 : (1 : k) ∈ RingHom.ker φ := h ▸ Submodule.mem_top
      rw [RingHom.mem_ker, map_one] at h1
      exact absurd h1 one_ne_zero
  · intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨constantCoeff p, ?_⟩
    rw [RingHom.comp_apply, algebraMap_eq, Ideal.Quotient.eq]
    have := sub_C_constantCoeff_mem_originIdeal k p
    rw [← neg_mem_iff, neg_sub] at this
    exact this

/-- The origin `V(x, y) ⊂ 𝔸²_k` is smooth over `k`: its subscheme is `Spec (k[x, y]/(x, y))`, and
`k → k[x, y]/(x, y)` is an isomorphism. -/
theorem smooth_origin_subschemeι :
    Smooth ((originCenter k).subschemeι ≫ affineSpaceToSpec k 2) := by
  have : MorphismProperty.RespectsIso (@Smooth) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f hf => by
      have : IsIso f := hf
      infer_instance
  rw [prop_subschemeι_comp_iff_of_eq_specIdealSheaf (originCenterIdeal k) (@Smooth)
    (originCenter k) rfl, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : IsIso (CommRingCat.ofHom
      ((Ideal.Quotient.mk (originCenterIdeal k)).comp (algebraMap k (MvPolynomial (Fin 2) k)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_mk_comp_algebraMap k)
  infer_instance

/-- Blowing up the origin of `𝔸²_k` is a smooth blow-up sequence. -/
theorem isSmooth_seqOrigin : (seqOrigin k).IsSmooth (affineSpaceToSpec k 2) := by
  rw [seqOrigin, isSmooth_cons_iff]
  exact ⟨smooth_origin_subschemeι k, isSmooth_nil _⟩

/-- `y² − x³ ≠ 0`. -/
theorem cuspPoly_ne_zero : (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) ≠ 0 := by
  intro h
  have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single 1 2)) h
  rw [coeff_sub, coeff_X_pow, coeff_X_pow, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  simp [Finsupp.single_eq_single_iff] at this

/-- The cuspidal cubic is not smooth over `k`: the scheme at which the restricted sequence of
[Kol07, 30.2] starts is singular. -/
theorem not_smooth_cusp : ¬ Smooth ((cusp k).subschemeι ≫ affineSpaceToSpec k 2) := by
  intro hS
  have : Smooth (affineSpaceToSpec k 2) := smooth_affineSpaceToSpec_two k
  -- the origin, as a point of the scheme and as a prime of the polynomial ring
  let p : PrimeSpectrum (MvPolynomial (Fin 2) k) := ratPoint (fun _ : Fin 2 => (0 : k))
  let x : affine2 k := ratPoint (fun _ : Fin 2 => (0 : k))
  -- the stalk `𝒪_{𝔸²,0}`, a localization of `k[x, y]` at the origin
  let R := (affine2 k).presheaf.stalk x
  let _alg : Algebra (MvPolynomial (Fin 2) k) R :=
    StructureSheaf.stalkAlgebra (MvPolynomial (Fin 2) k) p
  have _loc : IsLocalization.AtPrime R p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (MvPolynomial (Fin 2) k) p
  let gS : R := algebraMap (MvPolynomial (Fin 2) k) R (X 1 ^ 2 - X 0 ^ 3)
  have hstalk : (cusp k).stalkIdeal x = Ideal.span {gS} := by
    rw [cusp, stalkIdeal_specIdealSheaf, cuspIdeal, Ideal.map_span, Set.image_singleton]
    rfl
  -- the germ lies in `𝔪²`: `x, y` vanish at the origin
  have hX : ∀ i : Fin 2, algebraMap (MvPolynomial (Fin 2) k) R (X i) ∈ maximalIdeal R := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R p.asIdeal _).mpr
      ((mem_ratPoint_asIdeal_iff _ _).mpr (by simp))
  have hg2 : gS ∈ maximalIdeal R ^ 2 := by
    have h1 : algebraMap (MvPolynomial (Fin 2) k) R (X 1) ^ 2 ∈ maximalIdeal R ^ 2 :=
      Ideal.pow_mem_pow (hX 1) 2
    have h0 : algebraMap (MvPolynomial (Fin 2) k) R (X 0) ^ 3 ∈ maximalIdeal R ^ 2 :=
      Ideal.pow_le_pow_right (by norm_num) (Ideal.pow_mem_pow (hX 0) 3)
    have : gS = algebraMap (MvPolynomial (Fin 2) k) R (X 1) ^ 2 -
        algebraMap (MvPolynomial (Fin 2) k) R (X 0) ^ 3 := by
      simp [gS]
    rw [this]
    exact Ideal.sub_mem _ h1 h0
  have hx : x ∈ (cusp k).support := by
    rw [Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal, hstalk,
      Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_le_self two_ne_zero hg2
  have hR : IsRegularLocalRing R := isRegularLocalRing_stalk (affineSpaceToSpec k 2) x
  have hQ := isRegularLocalRing_quotient_stalkIdeal (cusp k) (affineSpaceToSpec k 2) hx
  rw [hstalk] at hQ
  have hM : p.asIdeal.primeCompl ≤ nonZeroDivisors (MvPolynomial (Fin 2) k) :=
    p.asIdeal.primeCompl_le_nonZeroDivisors
  have hg0 : gS ∈ nonZeroDivisors R := by
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => cuspPoly_ne_zero k ?_
    exact IsLocalization.injective R hM (by rw [map_zero]; exact h0)
  exact Hironaka.Local.not_isRegularLocalRing_quotient_span_singleton hg0 hg2 hQ

end Hironaka.Sequence.Cusp
