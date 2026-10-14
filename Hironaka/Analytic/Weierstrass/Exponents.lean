/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Radius
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.EReal.Operations
import Mathlib.Basic.NNReal.Basic
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation  -- shake: keep (used only by `example`s)

/-!
# Exponents, weights and the Weierstrass polynomial over a commutative ring

Lemmas about exponents, radius vectors and the Weierstrass polynomial over an arbitrary
commutative ring that do not depend on the coefficient field: the weight `ρ^ν` of a monomial
under a shift of the distinguished exponent or a scaling of the tail radii; the exponents of
series in one variable and the embedding of the distinguished coordinate; the exponents
`cons k x` of a split monomial `x_0^k x'^x` and their weights; the polynomial
`weierstrassPolynomial d c = X^d + ∑_{j<d} C(c_j) X^{d-1-j}` over a commutative ring, with its
coefficients, its monicity and degree and its evaluation; and a common positive lower bound for
finitely many radius vectors.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MvPowerSeries Filter

namespace Analytic

variable {m n : ℕ}

/-! ### Weights of exponents under the splitting operators and the tail scaling -/

variable {m : ℕ}

/-- The weight of `x^{ν + d e_0}` is `ρ_0^d` times the weight of `x^ν`. -/
theorem monomialEval_add_single_zero (ρ : Fin (m + 1) → ℝ≥0) (ν : Fin (m + 1) →₀ ℕ) (d : ℕ) :
    monomialEval ρ (ν + Finsupp.single 0 d) = monomialEval ρ ν * ρ 0 ^ d := by
  rw [monomialEval_add]
  congr 1
  simp [monomialEval]

/-- Shrinking the tail radii by `t ≤ 1` multiplies the weight of a monomial containing a tail
variable `x_j` by at most `t`. -/
theorem monomialEval_tailScale_le (ρ : Fin (m + 1) → ℝ≥0) {t : ℝ≥0} (ht : t ≤ 1)
    {ν : Fin (m + 1) →₀ ℕ} {j : Fin (m + 1)} (hj : j ≠ 0) (hν : ν j ≠ 0) :
    monomialEval (fun k => if k = 0 then ρ 0 else t * ρ k) ν ≤ t * monomialEval ρ ν := by
  classical
  unfold monomialEval Finsupp.prod
  have hjs : j ∈ ν.support := Finsupp.mem_support_iff.mpr hν
  calc ∏ k ∈ ν.support, (if k = 0 then ρ 0 else t * ρ k) ^ ν k
      ≤ ∏ k ∈ ν.support, (if k = j then t else 1) * ρ k ^ ν k := by
        refine Finset.prod_le_prod₀ (fun k _ => zero_le) fun k _ => ?_
        split_ifs with hk0 hkj hkj
        · exact absurd (hkj.symm.trans hk0) hj
        · rw [hk0, one_mul]
        · rw [mul_pow]
          exact mul_le_mul' (pow_le_of_le_one (zero_le) ht (hkj ▸ hν)) le_rfl
        · rw [mul_pow, one_mul]
          exact mul_le_of_le_one_left (zero_le) (pow_le_one₀ (zero_le) ht)
    _ = t * ∏ k ∈ ν.support, ρ k ^ ν k := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', ite_eq_left hjs]

/-- A monomial exponent with no tail variable is a pure `x_0`-power. -/
theorem eq_single_zero_of_tail_eq_zero {ν : Fin (m + 1) →₀ ℕ} (hν : ∀ j, j ≠ 0 → ν j = 0) :
    ν = Finsupp.single 0 (ν 0) := by
  ext i
  by_cases hi : i = 0
  · rw [hi, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne hi, hν i hi]

/-! ### Exponents in one variable and the distinguished coordinate -/

variable {m : ℕ}

/-- An exponent in one variable is a pure power. -/
theorem Fin1.eq_single (ν : Fin 1 →₀ ℕ) : ν = Finsupp.single 0 (ν 0) :=
  Finsupp.ext fun i => by rw [Subsingleton.elim i 0, Finsupp.single_eq_same]

theorem Fin1.eq_zero_iff (ν : Fin 1 →₀ ℕ) : ν = 0 ↔ ν 0 = 0 := by
  constructor
  · intro h; rw [h, Finsupp.zero_apply]
  · intro h; rw [Fin1.eq_single ν, h, Finsupp.single_zero]

theorem Fin1.single_apply_injective :
    Function.Injective fun ν : Fin 1 →₀ ℕ => Finsupp.single (0 : Fin (m + 1)) (ν 0) := by
  intro ν μ h
  have h' : ν 0 = μ 0 := Finsupp.single_injective 0 h
  rw [Fin1.eq_single ν, Fin1.eq_single μ, h']

theorem monomialEval_fin1 {R : Type*} [CommMonoid R] (y : Fin 1 → R) (ν : Fin 1 →₀ ℕ) :
    monomialEval y ν = y 0 ^ ν 0 := by
  conv_lhs => rw [Fin1.eq_single ν]
  exact monomialEval_single_pow _ _ _

/-- The embedding of the single variable onto the distinguished coordinate. -/
def embFirst (m : ℕ) : Fin 1 ↪ Fin (m + 1) := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

/-! ### Split exponents `cons k x` and the Weierstrass polynomial over a commutative ring -/

variable {m : ℕ}

theorem cons_zero_eq_single (k : ℕ) :
    Finsupp.cons k (0 : Fin m →₀ ℕ) = Finsupp.single 0 k := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Finsupp.cons_succ, Fin.succ_ne_zero]

theorem cons_eq_cons_iff {k k' : ℕ} {x x' : Fin m →₀ ℕ} :
    Finsupp.cons k x = Finsupp.cons k' x' ↔ k = k' ∧ x = x' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 : (Finsupp.cons k x) 0 = (Finsupp.cons k' x') 0 :=
        congrArg (fun μ : Fin (m + 1) →₀ ℕ => μ 0) h
      rwa [Finsupp.cons_zero, Finsupp.cons_zero] at h0
    · have ht := congrArg Finsupp.tail h
      rwa [Finsupp.tail_cons, Finsupp.tail_cons] at ht
  · rintro ⟨rfl, rfl⟩; rfl

theorem degree_cons (k : ℕ) (x : Fin m →₀ ℕ) :
    Finsupp.degree (Finsupp.cons k x) = k + Finsupp.degree x := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero]
  simp only [Finsupp.cons_succ]

theorem embDomain_succEmb (x : Fin m →₀ ℕ) :
    Finsupp.embDomain (Fin.succEmb m) x = Finsupp.cons 0 x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Finsupp.cons_zero, Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_of_notMem_range]
    rintro ⟨j, hj⟩
    exact Fin.succ_ne_zero j hj
  · rw [Finsupp.cons_succ, Finsupp.embDomain_eq_mapDomain]
    exact Finsupp.mapDomain_apply_of_injective (Fin.succEmb m).injective x j

theorem cons_sub_single_zero (k n : ℕ) (x : Fin m →₀ ℕ) :
    Finsupp.cons k x - Finsupp.single 0 n = Finsupp.cons (k - n) x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Finsupp.tsub_apply]
  · simp [Finsupp.tsub_apply, Finsupp.cons_succ, Fin.succ_ne_zero]

section CoefficientRing

variable {R : Type*} [CommRing R]

/-- The Weierstrass polynomial `X^d + ∑_{j<d} C(c_j) X^{d-1-j}` over a commutative ring `R`
(used over the tail ring of power series and, pointwise, over the coefficient field). -/
noncomputable def weierstrassPolynomial (d : ℕ) (c : Fin d → R) : Polynomial R :=
  Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (c j) * Polynomial.X ^ (d - 1 - (j : ℕ))

theorem coeff_weierstrassPolynomial_of_lt (d : ℕ) (c : Fin d → R) {n : ℕ}
    (hn : n < d) : (weierstrassPolynomial d c).coeff n = c ⟨d - 1 - n, by omega⟩ := by
  unfold weierstrassPolynomial
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_right hn.ne, zero_add,
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨d - 1 - n, by omega⟩]
  · rw [ite_eq_left (by change n = d - 1 - (d - 1 - n); omega)]
  · intro b _ hb
    rw [ite_eq_right]
    intro h
    apply hb
    ext
    change (b : ℕ) = d - 1 - n
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coeff_weierstrassPolynomial_rev (d : ℕ) (c : Fin d → R)
    (j : Fin d) : (weierstrassPolynomial d c).coeff (d - 1 - j) = c j := by
  rw [coeff_weierstrassPolynomial_of_lt d c (by omega)]
  congr 1
  ext
  change d - 1 - (d - 1 - (j : ℕ)) = (j : ℕ)
  omega

theorem coeff_weierstrassPolynomial_self (d : ℕ) (c : Fin d → R) :
    (weierstrassPolynomial d c).coeff d = 1 := by
  unfold weierstrassPolynomial
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_left rfl, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_zero fun j _ => ite_eq_right (by omega), add_zero]

theorem coeff_weierstrassPolynomial_of_gt (d : ℕ) (c : Fin d → R) {n : ℕ} (hn : d < n) :
    (weierstrassPolynomial d c).coeff n = 0 := by
  unfold weierstrassPolynomial
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_right hn.ne', Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_zero fun j _ => ite_eq_right (by omega), add_zero]

theorem degree_weierstrassPolynomial_sum_lt (d : ℕ) (c : Fin d → R) :
    (∑ j : Fin d, Polynomial.C (c j) * Polynomial.X ^ (d - 1 - (j : ℕ))).degree <
      (d : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun j _ => ?_
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact WithBot.coe_lt_coe.mpr (show d - 1 - (j : ℕ) < d by omega)

theorem monic_weierstrassPolynomial [Nontrivial R] (d : ℕ) (c : Fin d → R) :
    (weierstrassPolynomial d c).Monic :=
  (Polynomial.monic_X_pow d).add_of_left
    (by rw [Polynomial.degree_X_pow]; exact degree_weierstrassPolynomial_sum_lt d c)

theorem natDegree_weierstrassPolynomial [Nontrivial R] (d : ℕ) (c : Fin d → R) :
    (weierstrassPolynomial d c).natDegree = d := by
  unfold weierstrassPolynomial
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact degree_weierstrassPolynomial_sum_lt d c

theorem eval_weierstrassPolynomial (d : ℕ) (c : Fin d → R) (t : R) :
    (weierstrassPolynomial d c).eval t = t ^ d + ∑ j : Fin d, c j * t ^ (d - 1 - (j : ℕ)) := by
  unfold weierstrassPolynomial
  rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

end CoefficientRing

/-! ### Weights of split exponents -/

variable {m : ℕ}

theorem cons_injective (k : ℕ) :
    Function.Injective fun x : Fin m →₀ ℕ => Finsupp.cons k x := fun _ _ h =>
  (cons_eq_cons_iff.mp h).2

/-! ### A common radius vector -/

variable {m : ℕ}

/-- A finite family of radius vectors has a common positive lower bound. -/
theorem Radius.exists_le_forall {ι : Type*} [Finite ι] (s : ι → Radius m) :
    ∃ ρ : Radius m, ∀ i k, ρ k ≤ s i k := by
  classical
  cases nonempty_fintype ι
  refine ⟨⟨fun k => ∏ i, Min.min 1 (s i k), fun k => Finset.prod_pos fun i _ =>
    lt_min one_pos ((s i).pos k)⟩, fun i k => ?_⟩
  change ∏ i', Min.min 1 (s i' k) ≤ s i k
  calc ∏ i', Min.min 1 (s i' k) ≤ Min.min 1 (s i k) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        exact mul_le_of_le_one_right zero_le
          (Finset.prod_le_one₀ (fun _ _ => zero_le) fun _ _ => _root_.min_le_left _ _)
    _ ≤ s i k := _root_.min_le_right _ _

end Analytic
