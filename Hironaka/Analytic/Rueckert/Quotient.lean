/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Basic
public import Hironaka.Analytic.Weierstrass.Exponents
import Hironaka.Analytic.Rueckert.MonicDivisor
import Hironaka.Analytic.Rueckert.Slices
import Hironaka.Analytic.Weierstrass.Division
import Hironaka.Analytic.Weierstrass.Poly
import Hironaka.Analytic.Weierstrass.Regular
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The quotient by a Weierstrass polynomial

For a Weierstrass polynomial `W ∈ (Conv K m)[X]` (monic of degree `d`, lower coefficients
vanishing at `0`), `P := convPolyEval W ∈ Conv K (m+1)` is `x_0`-regular of order `d`
(`isRegularIn_convPolyEval_weierstrassPolynomial`), and evaluation at `x_0` induces a ring
isomorphism `(Conv K m)[X] ⧸ (W) ≃+* Conv K (m+1) ⧸ (P)` (`exists_ringEquiv_quotient_weierstrass`,
stated with the inverse direction and the compatibility `e (mk (convPolyEval q)) = mk q`): it is
surjective because the Weierstrass division writes every element as `q P + r` with `r` of
`x_0`-degree `< d`, and `r` is the evaluation of the polynomial of its slices; it is injective
because a polynomial `Q` with `convPolyEval Q ∈ (P)` has remainder `Q %ₘ W` whose evaluation is
both `q' P + 0` and `0 · P + (itself)`, so by uniqueness of the division it vanishes, and
`convPolyEval` is injective on polynomials (`convPolyEval_injective`: the `x_0`-slices of
`convPolyEval Q` are the coefficients of `Q`). This is the convergent analogue of Mathlib's
`Polynomial.IsDistinguishedAt.algEquivQuotient` for formal power series, and a standard step of
the theory of [GR65, Chapter II, §B]; the unique factorization argument (`UFD.lean`) rests on it.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open MvPowerSeries Polynomial

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

section Eval

/-- `convPolyEval Q` as the finite sum of its terms. -/
theorem coe_convPolyEval_eq_sum (Q : Polynomial (Conv K m)) :
    (convPolyEval K Q : MvPowerSeries (Fin (m + 1)) K) =
      ∑ k ∈ Finset.range (Q.natDegree + 1),
        liftTail (Q.coeff k : MvPowerSeries (Fin m) K) * X 0 ^ k := by
  change ((Polynomial.eval₂RingHom (convTail K).toRingHom (convX K 0) Q : Conv K (m + 1)) :
    MvPowerSeries (Fin (m + 1)) K) = _
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  push_cast
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_convTail, coe_convX]

/-- The `x_0`-slices of `convPolyEval Q` are the coefficients of `Q`. -/
theorem coeff_splitFirst_convPolyEval (Q : Polynomial (Conv K m)) (k : ℕ) :
    PowerSeries.coeff k (splitFirst K m (convPolyEval K Q : MvPowerSeries (Fin (m + 1)) K)) =
      (Q.coeff k : MvPowerSeries (Fin m) K) := by
  rw [coe_convPolyEval_eq_sum, map_sum]
  simp only [splitFirst_liftTail_mul_X_pow, map_sum, PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (Q.natDegree + 1)) k]
  split_ifs with hk
  · rfl
  · rw [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    rfl

/-- `convPolyEval` is injective. -/
theorem convPolyEval_injective :
    Function.Injective (convPolyEval K : Polynomial (Conv K m) → Conv K (m + 1)) := by
  intro Q Q' h
  refine Polynomial.ext fun k => ?_
  apply Subtype.ext
  have := congrArg (fun F : Conv K (m + 1) =>
    PowerSeries.coeff k (splitFirst K m (F : MvPowerSeries (Fin (m + 1)) K))) h
  simpa only [coeff_splitFirst_convPolyEval] using this

/-- A polynomial of degree `< d` evaluates to a series of `x_0`-degree `< d`. -/
theorem coeff_convPolyEval_eq_zero_of_degree_lt {Q : Polynomial (Conv K m)} {d : ℕ}
    (hQ : Q.degree < d) {ν : Fin (m + 1) →₀ ℕ} (hν : d ≤ ν 0) :
    coeff ν (convPolyEval K Q : MvPowerSeries (Fin (m + 1)) K) = 0 := by
  rw [← Finsupp.cons_tail ν, ← MvPowerSeries.coeff_coeff_finSuccEquiv]
  change coeff ν.tail (PowerSeries.coeff (ν 0) (splitFirst K m _)) = 0
  have hz : Q.coeff (ν 0) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hQ (by exact_mod_cast hν))
  rw [coeff_splitFirst_convPolyEval, hz]
  simp

/-- `convPolyEval` sends the Weierstrass polynomial over `Conv K m` to the series
`weierstrassPoly`. -/
theorem coe_convPolyEval_weierstrassPolynomial (d : ℕ) (c : Fin d → Conv K m) :
    (convPolyEval K (weierstrassPolynomial d c) : MvPowerSeries (Fin (m + 1)) K) =
      weierstrassPoly d fun j => (c j : MvPowerSeries (Fin m) K) := by
  apply (splitFirst K m).injective
  rw [splitFirst_weierstrassPoly]
  refine PowerSeries.ext fun k => ?_
  rw [coeff_splitFirst_convPolyEval, Polynomial.coeff_coe]
  have := congrArg (fun p : Polynomial (MvPowerSeries (Fin m) K) => p.coeff k)
    (map_weierstrassPolynomial (Conv K m).val.toRingHom d c)
  simp only [Polynomial.coeff_map] at this
  exact this

/-- A Weierstrass polynomial with coefficients vanishing at `0` is `x_0`-regular of order `d` (the
printed condition `μ_0(c_j) ≥ j` of [BM88, proof of Theorem 4.4, p. 24, item (2)]). -/
theorem isRegularIn_weierstrassPoly {d : ℕ} {c : Fin d → MvPowerSeries (Fin m) K}
    (hc : ∀ j, constantCoeff (c j) = 0) : IsRegularIn (weierstrassPoly d c) d := by
  rw [isRegularIn_iff]
  have hsum : ∀ k, (∑ j : Fin d, if k = d - 1 - (j : ℕ) then coeff (0 : Fin m →₀ ℕ) (c j) else 0) =
      0 := fun k => Finset.sum_eq_zero fun j _ => by
    split_ifs
    · rw [coeff_zero_eq_constantCoeff_apply, hc]
    · rfl
  constructor
  · intro k hk
    rw [← cons_zero_eq_single, coeff_cons_weierstrassPoly, ite_eq_right (fun h => by omega),
      zero_add, hsum]
  · rw [← cons_zero_eq_single, coeff_cons_weierstrassPoly, ite_eq_left ⟨rfl, rfl⟩, hsum, add_zero]
    exact one_ne_zero

theorem isRegularIn_convPolyEval_weierstrassPolynomial {d : ℕ} {c : Fin d → Conv K m}
    (hc : ∀ j, constantCoeff (c j : MvPowerSeries (Fin m) K) = 0) :
    IsRegularIn (convPolyEval K (weierstrassPolynomial d c) : MvPowerSeries (Fin (m + 1)) K) d := by
  rw [coe_convPolyEval_weierstrassPolynomial]
  exact isRegularIn_weierstrassPoly hc

end Eval

section Quotient

/-- For a Weierstrass polynomial `W` over `Conv K m`, `Conv K (m+1) ⧸ (W(x_0))` is isomorphic to
`(Conv K m)[X] ⧸ (W)`, compatibly with the evaluation at `x_0` [GR65, Chapter II, §B] (the
convergent analogue of Mathlib's `Polynomial.IsDistinguishedAt.algEquivQuotient`), from the
convergent Weierstrass division. -/
theorem exists_ringEquiv_quotient_weierstrass {d : ℕ} {c : Fin d → Conv K m}
    (hc : ∀ j, constantCoeff (c j : MvPowerSeries (Fin m) K) = 0) :
    ∃ e : (Conv K (m + 1) ⧸ Ideal.span {convPolyEval K (weierstrassPolynomial d c)}) ≃+*
        (Polynomial (Conv K m) ⧸ Ideal.span {weierstrassPolynomial d c}),
      ∀ q : Polynomial (Conv K m),
        e (Ideal.Quotient.mk _ (convPolyEval K q)) = Ideal.Quotient.mk _ q := by
  have hreg₀ := isRegularIn_convPolyEval_weierstrassPolynomial hc
  have hmonic₀ := monic_weierstrassPolynomial d c
  have hdeg₀ := natDegree_weierstrassPolynomial d c
  generalize hW : weierstrassPolynomial d c = W at hreg₀ hmonic₀ hdeg₀ ⊢
  generalize hP : convPolyEval K W = P at hreg₀ ⊢
  have hle : Ideal.span {W} ≤ Ideal.comap (convPolyEval K) (Ideal.span {P}) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hP]
    exact Ideal.mem_span_singleton_self _
  let Φ : Polynomial (Conv K m) ⧸ Ideal.span {W} →+* Conv K (m + 1) ⧸ Ideal.span {P} :=
    Ideal.quotientMap (Ideal.span {P}) (convPolyEval K) hle
  have hΦmk : ∀ q : Polynomial (Conv K m),
      Φ (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk _ (convPolyEval K q) := fun q =>
    Ideal.quotientMap_mk
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨q, r, hdeg, hF⟩ := exists_division_conv (f := F) (g := P) hreg₀
    refine ⟨Ideal.Quotient.mk _ (∑ j : Fin d,
      Polynomial.C (sliceConv r (d - 1 - j)) * Polynomial.X ^ (d - 1 - (j : ℕ))), ?_⟩
    rw [hΦmk, Ideal.Quotient.eq]
    have hr : convPolyEval K (∑ j : Fin d,
        Polynomial.C (sliceConv r (d - 1 - j)) * Polynomial.X ^ (d - 1 - (j : ℕ))) = r := by
      rw [map_sum]
      simp only [map_mul, map_pow, convPolyEval_C, convPolyEval_X K]
      exact (eq_sum_convTail_sliceConv hdeg).symm
    rw [hr, hF, Ideal.mem_span_singleton]
    exact ⟨-q, by ring⟩
  have key : ∀ Q : Polynomial (Conv K m), P ∣ convPolyEval K Q → W ∣ Q := by
    intro Q hy
    obtain ⟨A, hA⟩ := hy
    have hdiv := Polynomial.modByMonic_add_div Q W
    have hdegR : (Q %ₘ W).degree < d := by
      have := Polynomial.degree_modByMonic_lt Q hmonic₀
      rwa [Polynomial.degree_eq_natDegree hmonic₀.ne_zero, hdeg₀] at this
    have hRP : convPolyEval K (Q %ₘ W) = (A - convPolyEval K (Q /ₘ W)) * P := by
      have h1 : convPolyEval K Q = convPolyEval K (Q %ₘ W) + P * convPolyEval K (Q /ₘ W) := by
        rw [← hP, ← map_mul, ← map_add, hdiv]
      rw [h1] at hA
      linear_combination hA
    obtain ⟨q0, r0, -, -, -, -, huniq⟩ :=
      exists_unique_weierstrassDivision (convPolyEval K (Q %ₘ W)).2 P.2 hreg₀
    have h1 := huniq
      ((A - convPolyEval K (Q /ₘ W) : Conv K (m + 1)) : MvPowerSeries (Fin (m + 1)) K) 0
      (fun ν _ => by simp) (by rw [add_zero, ← Subalgebra.coe_mul, ← hRP])
    have h2 := huniq 0 (convPolyEval K (Q %ₘ W) : MvPowerSeries (Fin (m + 1)) K)
      (fun ν hν => coeff_convPolyEval_eq_zero_of_degree_lt hdegR hν) (by rw [zero_mul, zero_add])
    have hzero : convPolyEval K (Q %ₘ W) = 0 := by
      apply Subtype.ext
      rw [h2.2, ← h1.2]
      rfl
    have hmod : Q %ₘ W = 0 := convPolyEval_injective (by rw [hzero, map_zero])
    have hQ : W * (Q /ₘ W) = Q := by
      conv_rhs => rw [← hdiv]
      rw [hmod, zero_add]
    exact Dvd.intro _ hQ
  have hinj : Function.Injective Φ := by
    intro y y' hyy'
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨Q', rfl⟩ := Ideal.Quotient.mk_surjective y'
    rw [hΦmk, hΦmk, Ideal.Quotient.eq, ← map_sub, Ideal.mem_span_singleton] at hyy'
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact key (Q - Q') hyy'
  let e : (Polynomial (Conv K m) ⧸ Ideal.span {W}) ≃+* (Conv K (m + 1) ⧸ Ideal.span {P}) :=
    RingEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  refine ⟨e.symm, fun q => ?_⟩
  apply e.injective
  rw [RingEquiv.apply_symm_apply]
  exact (hΦmk q).symm

end Quotient

end Analytic
