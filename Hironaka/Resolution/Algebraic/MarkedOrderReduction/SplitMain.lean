/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitOrder
import Hironaka.Resolution.Algebraic.Snc.ComponentStalks
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.BlowUp.Transform.WeakTransform
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.ParameterAlgebra
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The monomial split, III: the factorisation and its uniqueness

The split `I = M(I) · N(I)` of [Kol07, Definition–Lemma 110] in its fine form (one exponent per
irreducible component; `Hironaka/Resolution/Algebraic/MarkedOrderReduction/MonomialPart.lean`):
`M(I) = ∏_D 𝓘_D^{ord_D I}` divides `I` because at every point `x` the ideal `I_x` lies in
`(z_c)^{ord_D I}` for every component `D` through `x` ([Kol07, Definition 47] propagated from the
generic point, `stalkIdeal_le_pow_of_specializes`) and the powers of the distinct parameters `z_c`
multiply (`prod_dvd_of_forall_dvd_of_pairwise`); the quotient `N(I) = (I : M(I))` then satisfies
`M(I) · N(I) = I` (the division by an invertible ideal sheaf), has order `0` at every generic
point (`ord_η I = ord_η I + ord_η N(I)`, orders adding at the generic point of a component), is
nonzero on every component (`N(I) ⊇ I`), and the factorisation is unique (the exponents are read
off as orders at the generic points, the cofactor is the colon). The monomial part absorbs
monomials and the nonmonomial part ignores them (Kollár's "differ … only in their monomial part",
[Kol07, 111, Step 1]), and for `E = ∅` the nonmonomial part is `I` (the last paragraph of
[Kol07, 111]).

* `monomial_congr`, `monomial_add`, `isNonzeroEverywhere_nonmonomialPart_of`,
  `nonmonomialPart_of_isEmpty_of` for any family, and in the setting of a normal-crossings family
  on a smooth Noetherian scheme (`Hironaka.BMO.Snc`): `le_monomialPart`, `monomialPart_dvd`,
  `monomialPart_mul_nonmonomialPart`, `ord_monomial_mul_genericPoint`,
  `ord_monomialPart_of_mem_genericPoints`, `ord_nonmonomialPart_eq_zero`,
  `monomial_eq_monomialPart_of_mul_eq`, `monomialPart_monomial_mul`, `nonmonomialPart_monomial_mul`.
  The statements on a triple are in
  `Hironaka/Resolution/Algebraic/MarkedOrderReduction/SplitTriple.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData Scheme.IdealSheafData
  IsLocalRing Ideal

namespace Hironaka.BMO

section Monomial

variable {X : Scheme.{u}} (E : DivisorFamily X)

/-- A monomial depends on its exponents only at the generic points of the members' components. -/
theorem monomial_congr {a b : X → ℕ}
    (h : ∀ i : E.ι, ∀ η ∈ (E.component i).support.genericPoints, a η = b η) :
    E.monomial a = E.monomial b := by
  unfold DivisorFamily.monomial
  exact Finset.prod_congr rfl fun i _ => finprod_mem_congr rfl fun η hη => by rw [h i η hη]

/-- Exponents add: `𝒪_X(−∑ (a_D + b_D) D) = 𝒪_X(−∑ a_D D) · 𝒪_X(−∑ b_D D)`. -/
theorem monomial_add (hfin : ∀ i : E.ι, ((E.component i).support.genericPoints).Finite)
    (a b : X → ℕ) : E.monomial (a + b) = E.monomial a * E.monomial b := by
  unfold DivisorFamily.monomial
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← finprod_mem_mul_distrib (hfin i)]
  exact finprod_mem_congr rfl fun η _ => by rw [Pi.add_apply, pow_add]

end Monomial

section Split

/-- `N(I)` is nonzero on every component when `I` is, since `N(I) ⊇ I` ([Kol07, Notation 64 (2)]
for the nonmonomial part). -/
theorem isNonzeroEverywhere_nonmonomialPart_of {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : IsNonzeroEverywhere I) (E : DivisorFamily X) :
    IsNonzeroEverywhere (nonmonomialPart I E) := by
  intro x hN
  apply hI x
  have hle : I ≤ nonmonomialPart I E := le_colon_self _ _
  exact le_bot_iff.mp ((stalkIdeal_mono hle x).trans (le_of_eq hN))

/-- For the empty family the monomial part is the empty product `𝒪_X` and the nonmonomial part is
`I` (the last paragraph of [Kol07, 111]: "if `E = ∅` then `N(I) = I`"). -/
theorem nonmonomialPart_of_isEmpty_of {X : Scheme.{u}} (I : X.IdealSheafData) (E : DivisorFamily X)
    (h : IsEmpty E.ι) : nonmonomialPart I E = I := by
  rw [nonmonomialPart_eq_colon, monomialPart_eq_monomial]
  unfold DivisorFamily.monomial
  have := h
  rw [Finset.univ_eq_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top, colon_top]

namespace Snc

open AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
  [NoetherianSpace X] (E : DivisorFamily X) (hE : E.IsSnc)

include f hE

/-- `I ⊆ M(I)` ([Kol07, Definition 47] and [Kol07, Definition–Lemma 110]): at a point `x`, in
Kollár's coordinates, `I_x ⊆ (z_c)^{ord_D I}` for each member through `x`
(`stalkIdeal_le_pow_of_specializes`), and the powers of the distinct parameters multiply. -/
theorem le_monomialPart (I : X.IdealSheafData) : I ≤ monomialPart I E := by
  classical
  refine le_of_stalkIdeal_le fun x => ?_
  rw [monomialPart_eq_monomial, stalkIdeal_monomial E (genericPoints_component_finite E) _ x]
  have hreg := isRegularLocalRing_stalk f x
  obtain ⟨n, z, hz, c, hc, hstalk⟩ := hE.2 x
  have hs : ∀ i (h : x ∈ (E.component i).support),
      (E.component i).stalkIdeal x = Ideal.span {z (c ⟨i, h⟩)} := fun i h => hstalk ⟨i, h⟩
  have hη : ∀ i (h : x ∈ (E.component i).support),
      Classical.choose (exists_genericPoint_specializes _ h) ∈
          (E.component i).support.genericPoints ∧
        Classical.choose (exists_genericPoint_specializes _ h) ⤳ x :=
    fun i h => Classical.choose_spec (exists_genericPoint_specializes _ h)
  let q : E.ι → X.presheaf.stalk x := fun i =>
    if h : x ∈ (E.component i).support then
      z (c ⟨i, h⟩) ^ (I.ord (Classical.choose (exists_genericPoint_specializes _ h))).toNat
    else 1
  have hF : ∀ i, ∏ᶠ η ∈ (E.component i).support.genericPoints,
      ((vanishingIdeal (Closeds.closure {η})).stalkIdeal x) ^ (I.ord η).toNat =
        Ideal.span {q i} := by
    intro i
    by_cases h : x ∈ (E.component i).support
    · rw [finprod_stalk_eq_of_specializes E hE (hη i h).1 (hη i h).2, hs i h,
        Ideal.span_singleton_pow]
      simp only [q, dite_eq_left h]
    · rw [finprod_stalk_eq_one_of_notMem E h]
      simp only [q, dite_eq_right h, Ideal.span_singleton_one, Ideal.one_eq_top]
  rw [Finset.prod_congr rfl fun i _ => hF i, Ideal.prod_span_singleton]
  intro g hg
  rw [Ideal.mem_span_singleton]
  refine prod_dvd_of_forall_dvd_of_pairwise Finset.univ q ?_ ?_
  · intro d _
    by_cases hd : x ∈ (E.component d).support
    · refine Or.inr ⟨z (c ⟨d, hd⟩), prime_of_parameters hz.1.symm hz.2 _,
        ⟨(I.ord (Classical.choose (exists_genericPoint_specializes _ hd))).toNat, by
          simp only [q, dite_eq_left hd]⟩, ?_⟩
      intro i _ hid
      by_cases hi : x ∈ (E.component i).support
      · simp only [q, dite_eq_left hi]
        intro hdvd
        exact not_dvd_of_ne hz.1.symm hz.2 (fun e => hid (congrArg Subtype.val (hc e)).symm)
          ((prime_of_parameters hz.1.symm hz.2 _).dvd_of_dvd_pow hdvd)
      · simp only [q, dite_eq_right hi]
        exact (prime_of_parameters hz.1.symm hz.2 _).not_dvd_one
    · exact Or.inl (by simp only [q, dite_eq_right hd]; exact isUnit_one)
  · intro i _
    by_cases hi : x ∈ (E.component i).support
    · simp only [q, dite_eq_left hi]
      have := stalkIdeal_le_pow_of_specializes f E hE I (hη i hi).1 (hη i hi).2 hg
      rwa [hs i hi, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
    · simp only [q, dite_eq_right hi]
      exact one_dvd g

/-- `M(I)` divides `I`: `I ⊆ M(I)` and `M(I)` is invertible. -/
theorem monomialPart_dvd (I : X.IdealSheafData) : monomialPart I E ∣ I := by
  have h := pow_dvd_of_le_pow_of_isInvertible (I := I) (isInvertible_monomial f E hE _) (c := 1)
    (by rw [pow_one]; exact le_monomialPart f E hE I)
  rwa [pow_one] at h

/-- The split `I = M(I) · N(I)` of [Kol07, Definition–Lemma 110]. -/
theorem monomialPart_mul_nonmonomialPart (I : X.IdealSheafData) :
    monomialPart I E * nonmonomialPart I E = I := by
  have h := pow_mul_colon_of_dvd (I := I) (monomialPart I E) 1
    (by rw [pow_one]; exact monomialPart_dvd f E hE I)
  rwa [pow_one, ← nonmonomialPart_eq_colon] at h

variable [CharZero k]

/-- The exponent bookkeeping at a generic point: for a monomial `K = 𝒪_X(−∑ a_D D)` and any `J`,
`ord_η (K · J) = a_D + ord_η J` at the generic point `η` of `D`. -/
theorem ord_monomial_mul_genericPoint {i : E.ι} {η : X}
    (hη : η ∈ (E.component i).support.genericPoints) (a : X → ℕ) (J : X.IdealSheafData) :
    (E.monomial a * J).ord η = (a η : ℕ∞) + J.ord η := by
  rw [ord_eq_ord_stalkIdeal, stalkIdeal_mul, stalkIdeal_monomial_genericPoint f E hE hη,
    ord_stalkIdeal_component_pow_mul f E hE hη, ← ord_eq_ord_stalkIdeal]

/-- The order of `M(I)` at the generic point of a component is the component's exponent
`ord_D I`. -/
theorem ord_monomialPart_of_mem_genericPoints {I : X.IdealSheafData} (hI : IsNonzeroEverywhere I)
    {i : E.ι} {η : X} (hη : η ∈ (E.component i).support.genericPoints) :
    (monomialPart I E).ord η = I.ord η := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  rw [monomialPart_eq_monomial, ord_monomial_genericPoint f E hE hη,
    ENat.natCast_toNat (ord_ne_top_of_isNonzeroEverywhere hI η)]

/-- `ord_D N(I) = 0` at every component: "`cosupp N(I)` does not contain any of the `E^i`" of
[Kol07, Definition–Lemma 110], in the fine form. -/
theorem ord_nonmonomialPart_eq_zero {I : X.IdealSheafData} (hI : IsNonzeroEverywhere I) {i : E.ι}
    {η : X} (hη : η ∈ (E.component i).support.genericPoints) :
    (nonmonomialPart I E).ord η = 0 := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have h1 : I.ord η = ((I.ord η).toNat : ℕ∞) + (nonmonomialPart I E).ord η := by
    conv_lhs => rw [← monomialPart_mul_nonmonomialPart f E hE I]
    rw [monomialPart_eq_monomial, ord_monomial_mul_genericPoint f E hE hη]
  have hN := ord_ne_top_of_isNonzeroEverywhere (isNonzeroEverywhere_nonmonomialPart_of hI E) η
  have h2 := congrArg ENat.toNat h1
  rw [ENat.toNat_add (ENat.natCast_ne_top _) hN, ENat.toNat_natCast] at h2
  have h3 : (nonmonomialPart I E).ord η = (((nonmonomialPart I E).ord η).toNat : ℕ∞) :=
    (ENat.natCast_toNat hN).symm
  rw [h3]
  have h4 : ((nonmonomialPart I E).ord η).toNat = 0 := by omega
  rw [h4]
  rfl

/-- The uniqueness of the split ([Kol07, Definition–Lemma 110]: "uniquely"): the exponents are the
orders at the generic points and the cofactor is the colon. -/
theorem monomial_eq_monomialPart_of_mul_eq (I : X.IdealSheafData) {a : X → ℕ}
    {N : X.IdealSheafData} (h : E.monomial a * N = I)
    (hN : ∀ i : E.ι, ∀ η ∈ (E.component i).support.genericPoints, N.ord η = 0) :
    E.monomial a = monomialPart I E ∧ N = nonmonomialPart I E := by
  have hexp : ∀ i : E.ι, ∀ η ∈ (E.component i).support.genericPoints,
      a η = (I.ord η).toNat := by
    intro i η hη
    have h1 : I.ord η = (a η : ℕ∞) + N.ord η := by
      rw [← h, ord_monomial_mul_genericPoint f E hE hη]
    rw [hN i η hη, add_zero] at h1
    rw [h1, ENat.toNat_natCast]
  have hM : E.monomial a = monomialPart I E := by
    rw [monomialPart_eq_monomial]
    exact monomial_congr E hexp
  refine ⟨hM, ?_⟩
  rw [nonmonomialPart_eq_colon, ← hM]
  have h' : E.monomial a ^ 1 * N = I := by rw [pow_one]; exact h
  have := colon_pow_eq_of_mul_eq (I := I) (isInvertible_monomial f E hE a) 1 N h'
  rw [pow_one] at this
  exact this.symm

/-- The monomial part absorbs monomials ([Kol07, 111, Step 1]: the two transforms "differ … only in
their monomial part"). -/
theorem monomialPart_monomial_mul (a : X → ℕ) (J : X.IdealSheafData)
    (hJ : IsNonzeroEverywhere J) :
    monomialPart (E.monomial a * J) E = E.monomial a * monomialPart J E := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  rw [monomialPart_eq_monomial, monomialPart_eq_monomial,
    ← monomial_add E (genericPoints_component_finite E)]
  refine monomial_congr E fun i η hη => ?_
  rw [Pi.add_apply, ord_monomial_mul_genericPoint f E hE hη,
    ENat.toNat_add (ENat.natCast_ne_top _) (ord_ne_top_of_isNonzeroEverywhere hJ η),
    ENat.toNat_natCast]

/-- The nonmonomial part ignores monomials ([Kol07, 111, Step 1]). -/
theorem nonmonomialPart_monomial_mul (a : X → ℕ) (J : X.IdealSheafData)
    (hJ : IsNonzeroEverywhere J) :
    nonmonomialPart (E.monomial a * J) E = nonmonomialPart J E := by
  rw [nonmonomialPart_eq_colon, nonmonomialPart_eq_colon, monomialPart_monomial_mul f E hE a J hJ,
    ← colon_colon]
  congr 1
  have h' : E.monomial a ^ 1 * J = E.monomial a * J := by rw [pow_one]
  have := colon_pow_eq_of_mul_eq (I := E.monomial a * J) (isInvertible_monomial f E hE a) 1 J h'
  rwa [pow_one] at this

end Snc

end Split

end Hironaka.BMO
