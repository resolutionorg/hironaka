/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Hironaka.Analytic.Weierstrass.Exponents
public import Hironaka.Analytic.Weierstrass.Basic
import Hironaka.Analytic.Weierstrass.AdicComplete

/-!
# Weierstrass polynomials: coefficients, order, and the polynomial over the tail ring

A Weierstrass polynomial `x_0^d + ∑_{j<d} c_j(x') x_0^{d-1-j}` (`weierstrassPoly`, a series in
`m + 1` variables) corresponds under `splitFirst K m` to the polynomial `X^d + ∑ C(c_j) X^{d-1-j}`
over the tail ring (`weierstrassPolynomial`, defined over any commutative ring), which is monic of
degree `d`, and distinguished
when the `c_j` vanish at `0`. Its coefficients are read off exponent by exponent
(`coeff_cons_weierstrassPoly`): the terms have distinct `x_0`-degrees, so there is no
cancellation, and the order is `d` exactly when `μ_0(c_j) ≥ j + 1` for every `j`; since our `c_j`
is the printed `c_{j+1}`, this is the printed condition `μ_0(c_j) ≥ j` on the coefficients
[BM88, proof of Theorem 4.4, p. 24, item (2)]. A series of `x_0`-degree `< d` is its own
truncation, hence a polynomial of degree `< d` over the tail ring: this is how the convergent
remainders enter Mathlib's `IsWeierstrassDivision`.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

/-! ### Coefficients of lifted series and Weierstrass polynomials -/

theorem coeff_cons_liftTail (a : MvPowerSeries (Fin m) K) (k : ℕ) (x : Fin m →₀ ℕ) :
    coeff (Finsupp.cons k x) (liftTail a : MvPowerSeries (Fin (m + 1)) K) =
      if k = 0 then coeff x a else 0 := by
  split_ifs with hk
  · subst hk
    have h := coeff_embDomain_rename (Fin.succEmb m) a x
    rw [embDomain_succEmb] at h
    exact h
  · apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    have h0 : (Finsupp.mapDomain Fin.succ y) 0 = (Finsupp.cons k x) 0 :=
      congrArg (fun μ : Fin (m + 1) →₀ ℕ => μ 0) hy
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨j, hj⟩; exact Fin.succ_ne_zero j hj),
      Finsupp.cons_zero] at h0
    exact hk h0.symm

theorem coeff_cons_liftTail_mul_X_pow (a : MvPowerSeries (Fin m) K) (n k : ℕ) (x : Fin m →₀ ℕ) :
    coeff (Finsupp.cons k x) (liftTail a * X 0 ^ n : MvPowerSeries (Fin (m + 1)) K) =
      if k = n then coeff x a else 0 := by
  rw [X_pow_eq, coeff_mul_monomial]
  have hle : (Finsupp.single (0 : Fin (m + 1)) n ≤ Finsupp.cons k x) ↔ n ≤ k := by
    rw [Finsupp.single_le_iff, Finsupp.cons_zero]
  by_cases h : n ≤ k
  · rw [ite_eq_left (hle.mpr h), cons_sub_single_zero, coeff_cons_liftTail, mul_one]
    by_cases hk : k = n
    · rw [ite_eq_left hk, ite_eq_left (by omega)]
    · rw [ite_eq_right hk, ite_eq_right (by omega)]
  · rw [ite_eq_right (fun h' => h (hle.mp h')), ite_eq_right (by omega)]

theorem coeff_cons_X_pow (d k : ℕ) (x : Fin m →₀ ℕ) :
    coeff (Finsupp.cons k x) (X 0 ^ d : MvPowerSeries (Fin (m + 1)) K) =
      if k = d ∧ x = 0 then 1 else 0 := by
  classical
  rw [coeff_X_pow, ← cons_zero_eq_single]
  by_cases h : k = d ∧ x = 0
  · rw [ite_eq_left h, ite_eq_left (cons_eq_cons_iff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (cons_eq_cons_iff.mp h'))]

/-- The coefficient of `x_0^k x'^x` in a Weierstrass polynomial: the terms have distinct
`x_0`-degrees, so the coefficient is read off term by term. -/
theorem coeff_cons_weierstrassPoly (d : ℕ) (c : Fin d → MvPowerSeries (Fin m) K) (k : ℕ)
    (x : Fin m →₀ ℕ) :
    coeff (Finsupp.cons k x) (weierstrassPoly d c) =
      (if k = d ∧ x = 0 then 1 else 0) +
        ∑ j : Fin d, if k = d - 1 - (j : ℕ) then coeff x (c j) else 0 := by
  unfold weierstrassPoly
  rw [map_add, map_sum, coeff_cons_X_pow]
  simp only [coeff_cons_liftTail_mul_X_pow]

/-! ### The order of a Weierstrass polynomial -/

/-- `μ_0(P) ≤ d`, the coefficient of `x_0^d` being `1`. -/
theorem order_weierstrassPoly_le (d : ℕ) (c : Fin d → MvPowerSeries (Fin m) K) :
    (weierstrassPoly d c).order ≤ d := by
  have h : coeff (Finsupp.single 0 d) (weierstrassPoly d c) ≠ 0 := by
    rw [← cons_zero_eq_single, coeff_cons_weierstrassPoly, ite_eq_left ⟨rfl, rfl⟩,
      Finset.sum_eq_zero fun j _ => ite_eq_right (by omega), add_zero]
    exact one_ne_zero
  have := order_le h
  rwa [Finsupp.degree_single] at this

/-- `μ_0(P) = d` iff `μ_0(c_j) ≥ j + 1` for all `j` (no cancellation between terms of distinct
`x_0`-degree): the printed `μ_0(c_j) ≥ j` of [BM88, proof of Theorem 4.4, p. 24, item (2)], our
`c_j` being the printed `c_{j+1}`. -/
theorem order_weierstrassPoly_eq_iff (d : ℕ) (c : Fin d → MvPowerSeries (Fin m) K) :
    (weierstrassPoly d c).order = d ↔ ∀ j : Fin d, ((j : ℕ) + 1 : ℕ∞) ≤ (c j).order := by
  constructor
  · intro hord j
    by_contra hlt
    rw [not_le] at hlt
    have hfin : (c j).order.toNat = (c j).order := ENat.natCast_toNat (ne_top_of_lt hlt)
    obtain ⟨x, hx, hxo⟩ := exists_coeff_ne_zero_and_order hfin
    have hdeg : Finsupp.degree x ≤ (j : ℕ) := by
      rw [← hxo] at hlt
      have : Finsupp.degree x < (j : ℕ) + 1 := by exact_mod_cast hlt
      omega
    have hcoeff : coeff (Finsupp.cons (d - 1 - j) x) (weierstrassPoly d c) ≠ 0 := by
      rw [coeff_cons_weierstrassPoly, ite_eq_right (fun h => by have := h.1; omega), zero_add,
        Finset.sum_eq_single j (fun i _ hi => ite_eq_right fun h => hi (Fin.ext (by omega)))
          (fun h => absurd (Finset.mem_univ j) h), ite_eq_left rfl]
      exact hx
    apply hcoeff
    apply coeff_of_lt_order
    rw [hord, degree_cons]
    exact_mod_cast (by omega : d - 1 - (j : ℕ) + Finsupp.degree x < d)
  · intro hc
    refine le_antisymm (order_weierstrassPoly_le d c) (nat_le_order fun μ hμ => ?_)
    have hμ' : μ 0 + Finsupp.degree μ.tail < d := by
      rw [← degree_cons, Finsupp.cons_tail]; exact hμ
    rw [← Finsupp.cons_tail μ, coeff_cons_weierstrassPoly,
      ite_eq_right (fun h => by have := h.1; omega), zero_add]
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · apply coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (hc j)
      exact_mod_cast (by omega : Finsupp.degree μ.tail < (j : ℕ) + 1)
    · rfl

/-! ### The polynomial over the tail ring

The polynomial `weierstrassPolynomial d c` is defined over an arbitrary commutative ring; here it is
compared with the series `weierstrassPoly d c` through `splitFirst`. -/

section CoefficientRing

variable {R : Type*} [CommRing R]

end CoefficientRing

theorem splitFirst_X_zero : splitFirst K m (X 0) = PowerSeries.X :=
  MvPowerSeries.finSuccEquiv_X_zero

theorem splitFirst_liftTail (a : MvPowerSeries (Fin m) K) :
    splitFirst K m (liftTail a) = PowerSeries.C a := by
  ext k x
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_cons_liftTail]
  split_ifs
  · rfl
  · exact (map_zero _).symm

theorem splitFirst_liftTail_mul_X_pow (a : MvPowerSeries (Fin m) K) (k : ℕ) :
    splitFirst K m (liftTail a * X 0 ^ k) = PowerSeries.C a * PowerSeries.X ^ k := by
  rw [map_mul, map_pow, splitFirst_liftTail, splitFirst_X_zero]

/-- Under `splitFirst`, the Weierstrass polynomial in `m + 1` variables is the polynomial over the
tail ring. -/
theorem splitFirst_weierstrassPoly (d : ℕ) (c : Fin d → MvPowerSeries (Fin m) K) :
    splitFirst K m (weierstrassPoly d c) = (weierstrassPolynomial d c : _) := by
  unfold weierstrassPoly weierstrassPolynomial
  rw [map_add, map_pow, map_sum, splitFirst_X_zero, ← Polynomial.coeToPowerSeries.ringHom_apply,
    map_add, map_pow, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_pow, splitFirst_liftTail_mul_X_pow]

/-- A Weierstrass polynomial whose coefficients vanish at `0` is distinguished at the maximal
ideal of the tail ring (monic, lower coefficients in `𝔪`). -/
theorem isDistinguishedAt_weierstrassPolynomial (d : ℕ) (c : Fin d → MvPowerSeries (Fin m) K)
    (hc : ∀ j, constantCoeff (c j) = 0) :
    (weierstrassPolynomial d c).IsDistinguishedAt
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin m) K)) :=
  ⟨⟨fun {n} hn => by
    rw [natDegree_weierstrassPolynomial] at hn
    rw [coeff_weierstrassPolynomial_of_lt d c hn, mem_maximalIdeal_iff]
    exact hc _⟩, monic_weierstrassPolynomial d c⟩

/-! ### Series of bounded `x_0`-degree are polynomials over the tail ring -/

theorem coeff_splitFirst_eq_zero_of_le {r : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hr : ∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r = 0) {k : ℕ} (hk : d ≤ k) :
    PowerSeries.coeff k (splitFirst K m r) = 0 := by
  ext x
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, map_zero]
  exact hr _ (by rw [Finsupp.cons_zero]; exact hk)

theorem splitFirst_eq_trunc {r : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hr : ∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r = 0) :
    splitFirst K m r = (PowerSeries.trunc d (splitFirst K m r) : _) := by
  refine PowerSeries.ext fun k => ?_
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · exact coeff_splitFirst_eq_zero_of_le hr (not_lt.mp h)

theorem coe_trunc_eq_sum (f : PowerSeries (MvPowerSeries (Fin m) K)) (d : ℕ) :
    (PowerSeries.trunc d f : PowerSeries (MvPowerSeries (Fin m) K)) =
      ∑ j : Fin d, PowerSeries.C (PowerSeries.coeff (d - 1 - j) f) *
        PowerSeries.X ^ (d - 1 - (j : ℕ)) := by
  refine PowerSeries.ext fun n => ?_
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow]
  by_cases hn : n < d
  · rw [ite_eq_left hn, Finset.sum_eq_single ⟨d - 1 - n, by omega⟩]
    · rw [ite_eq_left (by change n = d - 1 - (d - 1 - n); omega)]
      congr 2
      change n = d - 1 - (d - 1 - n)
      omega
    · intro b _ hb
      rw [ite_eq_right]
      intro h
      apply hb
      ext
      change (b : ℕ) = d - 1 - n
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hn]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    omega

/-- `x_0^d - r`, for `r` of `x_0`-degree `< d`, is the Weierstrass polynomial with coefficients
the negated `x_0`-coefficients of `r`. -/
theorem X_pow_sub_eq_weierstrassPoly {r : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hr : ∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r = 0) :
    X 0 ^ d - r =
      weierstrassPoly d fun j => -(PowerSeries.coeff (d - 1 - j) (splitFirst K m r)) := by
  apply (splitFirst K m).injective
  have hsum := (splitFirst_eq_trunc hr).trans (coe_trunc_eq_sum _ d)
  rw [map_sub, map_pow, splitFirst_X_zero, splitFirst_weierstrassPoly]
  unfold weierstrassPolynomial
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_pow, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_pow]
  conv_lhs => rw [hsum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_neg, neg_mul]

/-- A convergent-style division datum `f = q g + r`, `r` of `x_0`-degree `< d`, is a Weierstrass
division in Mathlib's sense over the tail ring. -/
theorem isWeierstrassDivision_of_eq {f g q r : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hg : IsRegularIn g d) (hr : ∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r = 0)
    (hfq : f = q * g + r) :
    (splitFirst K m f).IsWeierstrassDivision (splitFirst K m g) (splitFirst K m q)
      (PowerSeries.trunc d (splitFirst K m r)) := by
  constructor
  · have hd : ((splitFirst K m g).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (MvPowerSeries (Fin m) K)))).order = d := hg
    rw [hd, ENat.toNat_natCast]
    exact PowerSeries.degree_trunc_lt _ _
  · rw [hfq, map_add, map_mul, mul_comm, ← splitFirst_eq_trunc hr]

/-- The `toNat` of the order of the residue image of a regular series is its regularity order. -/
theorem toNat_order_map_residue {g : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hg : IsRegularIn g d) :
    ((splitFirst K m g).map (IsLocalRing.residue (MvPowerSeries (Fin m) K))).order.toNat = d := by
  unfold IsRegularIn at hg
  rw [hg, ENat.toNat_natCast]

end Analytic
