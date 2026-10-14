/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Basic
public import Hironaka.Analytic.Weierstrass.Exponents
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Hironaka.Analytic.Rueckert.Irreducible
import Hironaka.Analytic.Rueckert.MonicDivisor
import Hironaka.Analytic.Rueckert.Noetherian
import Hironaka.Analytic.Rueckert.Quotient
import Hironaka.Analytic.Rueckert.Subst
import Hironaka.Analytic.Rueckert.WeierstrassPolynomial
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# `Conv K m` is a unique factorization domain

The ring of convergent power series is a unique factorization domain [GR65, Chapter II, §B],
[Nar66, Chapter II]. Induction on `m`. `Conv K 0 ≅ K` is a field. For `m + 1`, by
`UniqueFactorizationMonoid.of_exists_prime_factors` it suffices to factor every nonzero `a` into
primes up to a unit. A unit is the empty product. A nonunit becomes, after a linear change of
variables (`substEquiv`, `Subst.lean`), regular of order `d ≥ 1`, hence `u · W(x_0)` with `W` a
Weierstrass polynomial over `Conv K m` (the preparation theorem). `W(x_0)` is a product of primes
of `Conv K (m+1)` by strong induction on `d` (`exists_prime_factors_convPolyEval_weierstrass`): if
`W` is irreducible in `(Conv K m)[X]`, it is prime there (Gauss's lemma and the induction
hypothesis on `m`), so `Conv K (m+1) ⧸ (W(x_0)) ≃ (Conv K m)[X] ⧸ (W)` (`Quotient.lean`) is a
domain and `W(x_0)` is prime; otherwise `W = a' b'` with `a', b'` monic nonunits (normalizing the
leading coefficients, which are units since their product is `1`), both Weierstrass by
`MonicDivisor.lean` and of smaller degree. Transporting back along the automorphism gives the
factorization of `a` (primes are preserved by ring isomorphisms). The route by strong induction on
the degree replaces the direct appeal to the factorization in `(Conv K m)[X]` of the textbooks.

Mathlib has `UniqueFactorizationMonoid (PowerSeries k)` in one variable only; nothing for
`MvPowerSeries`. Unique factorization gives the integral closedness of the base ring in the
parametrization theorem (`MinpolyDvd.lean`) and the square-free reduction of the hypersurface
Nullstellensatz (`Hypersurface.lean`).

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open MvPowerSeries Polynomial

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

variable (K) in
/-- `(Conv K m)[X]` is a unique factorization domain when `Conv K m` is (Gauss's lemma, Mathlib's
`Polynomial.uniqueFactorizationMonoid`). -/
theorem uniqueFactorizationMonoid_polynomial_conv [UniqueFactorizationMonoid (Conv K m)] :
    UniqueFactorizationMonoid (Polynomial (Conv K m)) :=
  Polynomial.uniqueFactorizationMonoid

/-- `Conv K 0` is a unique factorization domain (a field). -/
theorem uniqueFactorizationMonoid_conv_zero : UniqueFactorizationMonoid (Conv K 0) := by
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun a ha => ⟨0, by simp, ?_⟩
  rw [Multiset.prod_zero]
  exact (associated_one_iff_isUnit.mpr (isUnit_of_ne_zero_conv_zero ha)).symm

/-- A Weierstrass polynomial prime in `(Conv K m)[X]` evaluates to a prime of `Conv K (m+1)` (the
quotients are isomorphic, `Quotient.lean`). -/
theorem prime_convPolyEval_of_prime {d : ℕ} {c : Fin d → Conv K m}
    (hc : ∀ j, constantCoeff (c j : MvPowerSeries (Fin m) K) = 0)
    (hp : Prime (weierstrassPolynomial d c)) :
    Prime (convPolyEval K (weierstrassPolynomial d c)) := by
  have hP0 : convPolyEval K (weierstrassPolynomial d c) ≠ 0 := fun h =>
    hp.ne_zero (convPolyEval_injective (by rw [h, map_zero]))
  rw [← Ideal.span_singleton_prime hP0, ← Ideal.Quotient.isDomain_iff_prime]
  obtain ⟨e, -⟩ := exists_ringEquiv_quotient_weierstrass hc
  have hdom : IsDomain (Polynomial (Conv K m) ⧸ Ideal.span {weierstrassPolynomial d c}) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)
  exact Function.Injective.isDomain e.toRingHom e.injective

section Succ

variable [UniqueFactorizationMonoid (Conv K m)]

/-- The evaluation of a Weierstrass polynomial is a product of primes of `Conv K (m+1)`, by strong
induction on the degree. -/
theorem exists_prime_factors_convPolyEval_weierstrass (d : ℕ) :
    ∀ (c : Fin d → Conv K m), (∀ j, constantCoeff (c j : MvPowerSeries (Fin m) K) = 0) →
      ∃ f : Multiset (Conv K (m + 1)), (∀ b ∈ f, Prime b) ∧
        f.prod = convPolyEval K (weierstrassPolynomial d c) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro c hc
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    exact ⟨0, by simp, by rw [Multiset.prod_zero, weierstrassPolynomial_zero_eq_one, map_one]⟩
  set W : Polynomial (Conv K m) := weierstrassPolynomial d c with hW
  have hWm : W.Monic := monic_weierstrassPolynomial d c
  have hWu : ¬ IsUnit W := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [hW, natDegree_weierstrassPolynomial] at this
    omega
  by_cases hirr : Irreducible W
  · refine ⟨{convPolyEval K W}, fun b hb => ?_, by rw [Multiset.prod_singleton]⟩
    rw [Multiset.mem_singleton] at hb
    subst hb
    exact prime_convPolyEval_of_prime hc
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  · rw [irreducible_iff, not_and, not_forall] at hirr
    obtain ⟨a, ha⟩ := hirr hWu
    rw [not_forall] at ha
    obtain ⟨b, hab⟩ := ha
    rw [Classical.not_imp, not_or] at hab
    obtain ⟨hWab, hau, hbu⟩ := hab
    -- the leading coefficients are units (their product is `1`)
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hWab]
      exact hWm
    have hua : IsUnit a.leadingCoeff :=
      ⟨⟨a.leadingCoeff, b.leadingCoeff, hlc, (mul_comm _ _).trans hlc⟩, rfl⟩
    set a' : Polynomial (Conv K m) := Polynomial.C (↑hua.unit⁻¹ : Conv K m) * a with ha'
    set b' : Polynomial (Conv K m) := Polynomial.C a.leadingCoeff * b with hb'
    have hab' : W = a' * b' := by
      rw [ha', hb', hWab]
      calc a * b = (Polynomial.C ((↑hua.unit⁻¹ : Conv K m) * a.leadingCoeff)) * (a * b) := by
            rw [hua.val_inv_mul, Polynomial.C_1, one_mul]
        _ = Polynomial.C (↑hua.unit⁻¹ : Conv K m) * a * (Polynomial.C a.leadingCoeff * b) := by
            rw [Polynomial.C_mul]
            ring
    have ha'm : a'.Monic := by
      rw [Polynomial.Monic, ha', Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        hua.val_inv_mul]
    have hb'm : b'.Monic := ha'm.of_mul_monic_left (hab' ▸ hWm)
    have ha'u : ¬ IsUnit a' := fun h => hau (IsUnit.mul_iff.mp h).2
    have hb'u : ¬ IsUnit b' := fun h => hbu (IsUnit.mul_iff.mp h).2
    have hdeg : a'.natDegree + b'.natDegree = d := by
      rw [← ha'm.natDegree_mul hb'm, ← hab', hW, natDegree_weierstrassPolynomial]
    have ha'd : 0 < a'.natDegree := by
      rcases Nat.eq_zero_or_pos a'.natDegree with h0 | h0
      · exact absurd (eq_one_of_monic_natDegree_eq_zero ha'm h0 ▸ isUnit_one) ha'u
      · exact h0
    have hb'd : 0 < b'.natDegree := by
      rcases Nat.eq_zero_or_pos b'.natDegree with h0 | h0
      · exact absurd (eq_one_of_monic_natDegree_eq_zero hb'm h0 ▸ isUnit_one) hb'u
      · exact h0
    obtain ⟨d₁, c₁, hc₁, ha'W⟩ :=
      exists_weierstrassPolynomial_of_monic_dvd hc ha'm (Dvd.intro _ hab'.symm)
    obtain ⟨d₂, c₂, hc₂, hb'W⟩ :=
      exists_weierstrassPolynomial_of_monic_dvd hc hb'm (Dvd.intro_left _ hab'.symm)
    have hd₁ : d₁ < d := by
      have : a'.natDegree = d₁ := by rw [ha'W, natDegree_weierstrassPolynomial]
      omega
    have hd₂ : d₂ < d := by
      have : b'.natDegree = d₂ := by rw [hb'W, natDegree_weierstrassPolynomial]
      omega
    obtain ⟨f₁, hf₁, hf₁prod⟩ := ih d₁ hd₁ c₁ hc₁
    obtain ⟨f₂, hf₂, hf₂prod⟩ := ih d₂ hd₂ c₂ hc₂
    refine ⟨f₁ + f₂, fun x hx => ?_, ?_⟩
    · rcases Multiset.mem_add.mp hx with hx | hx
      · exact hf₁ x hx
      · exact hf₂ x hx
    · rw [Multiset.prod_add, hf₁prod, hf₂prod, ← map_mul, ← ha'W, ← hb'W, ← hab']

/-- The inductive step: if `Conv K m` is a unique factorization domain, so is `Conv K (m+1)`
[GR65, Chapter II, §B]. -/
theorem uniqueFactorizationMonoid_conv_succ : UniqueFactorizationMonoid (Conv K (m + 1)) := by
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun a ha => ?_
  by_cases hu : IsUnit a
  · exact ⟨0, by simp, by rw [Multiset.prod_zero]; exact (associated_one_iff_isUnit.mpr hu).symm⟩
  obtain ⟨L, hreg⟩ := exists_substEquiv_isRegularIn ha
  obtain ⟨u, c, hu', hc, hg⟩ := exists_preparation_conv hreg
  obtain ⟨f, hf, hprod⟩ := exists_prime_factors_convPolyEval_weierstrass _ c hc
  refine ⟨f.map (substEquiv L).symm, fun b hb => ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hb
    exact (MulEquiv.prime_iff (substEquiv L).symm).mpr (hf p hp)
  · rw [← map_multiset_prod, hprod]
    have ha' : a = (substEquiv L).symm u *
        (substEquiv L).symm (convPolyEval K (weierstrassPolynomial _ c)) := by
      rw [← map_mul, ← hg]
      exact ((substEquiv L).symm_apply_apply a).symm
    have h1 := (associated_unit_mul_left ((substEquiv L).symm
      (convPolyEval K (weierstrassPolynomial _ c))) _ (hu'.map (substEquiv L).symm)).symm
    rwa [← ha'] at h1

end Succ

variable (K) in
/-- `Conv K m` is a unique factorization domain [GR65, Chapter II, §B], [Nar66, Chapter II], by
induction on `m`. -/
theorem uniqueFactorizationMonoid_conv {m : ℕ} : UniqueFactorizationMonoid (Conv K m) := by
  induction m with
  | zero => exact uniqueFactorizationMonoid_conv_zero
  | succ m ih => exact @uniqueFactorizationMonoid_conv_succ K _ m ih

variable (K) in
/-- Unique factorization as an instance (the theorem `uniqueFactorizationMonoid_conv` registered
for instance search). -/
instance instUniqueFactorizationMonoidConv {m : ℕ} : UniqueFactorizationMonoid (Conv K m) :=
  uniqueFactorizationMonoid_conv K

end Analytic
