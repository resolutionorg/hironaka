/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Eval
public import Mathlib.Algebra.MvPolynomial.Eval
import Hironaka.Analytic.ConvSeries.Banach
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Linarith.NNRealPreprocessor  -- shake: keep (used only by `example`s)

/-!
# From analytic functions to convergent series, and uniqueness of coefficients

Mathlib's `AnalyticAt` is stated over any nontrivially normed field; over `K = ℝ` or `ℂ` an
analytic function on `Fin m → K` near `a` is the function of a convergent power series in
`x - a`, and two convergent series with the same function near `0` are equal. Together with
`Eval.lean` this identifies the ring of convergent series with the ring of germs of analytic
functions, an identification the sources take for granted [GR71, Kapitel I]; Mathlib has only the
one-variable uniqueness (`HasFPowerSeriesAt.eq_formalMultilinearSeries`), so the arguments are
given here.

**The coefficients.** If `f` has the power series `p` at `a` on a ball of radius `r`, the `n`-th
term `p n` is a continuous multilinear map; expanding each argument `y = ∑_j y_j e_j` in the
coordinate basis (`ContinuousMultilinearMap.map_sum_finset`, `map_smul_univ`) gives
`p n (y, …, y) = ∑_{k : Fin n → Fin m} (∏_i y_{k i}) · p n (e_{k 1}, …, e_{k n})`, and grouping
the tuples `k` by their count vector `ν(k) = ∑_i single (k i) 1` gives `∑_{|ν| = n} c_ν y^ν` with
`c_ν = ∑_{ν(k) = ν} p n (e_k)`. No symmetry of `p n` is used.

**The norm.** `‖c_ν‖ ≤ #{k : ν(k) = ν} · ‖p n‖`, and the fibre counts over `|ν| = n` add up to
`m^n`, so at the constant radius `r' = r / (2 (m + 1))` the degree-`n` slice of the majorant norm
is at most `‖p n‖ (m r')^n`, summable because `m r' < r ≤ p.radius`.

**Uniqueness.** Two convergent series whose functions agree near `0` have the same iterated
derivatives at `0`; by `factorial_smul_sum_eq_iteratedFDeriv` the homogeneous parts agree as
functions, hence as polynomials (`MvPolynomial.funext`, `K` is infinite), hence coefficientwise.


-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-! ## Expanding a multilinear term in the coordinate basis -/

/-- `y = ∑_j y_j • e_j` in `Fin m → K`. -/
theorem eq_sum_smul_single (y : Fin m → K) :
    y = ∑ j, y j • (Pi.single j (1 : K) : Fin m → K) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

/-- A multilinear term on the diagonal, expanded in the coordinate basis. -/
theorem fms_apply_diag_eq_sum (p : FormalMultilinearSeries K (Fin m → K) K) (n : ℕ)
    (y : Fin m → K) :
    p n (fun _ => y)
      = ∑ k : Fin n → Fin m, (∏ i, y (k i)) * p n (fun i => Pi.single (k i) (1 : K)) := by
  classical
  conv_lhs => rw [eq_sum_smul_single y]
  rw [(p n).map_sum_finset (fun (_ : Fin n) j => y j • (Pi.single j (1 : K) : Fin m → K))
    (fun _ => Finset.univ), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

/-- The coefficients read off a power series, `c_ν = ∑_{ν(k) = ν} p |ν| (e_k)`. -/
noncomputable def coeffOfFMS (p : FormalMultilinearSeries K (Fin m → K) K) :
    MvPowerSeries (Fin m) K :=
  fun ν => ∑ k ∈ (Finset.univ : Finset (Fin ν.degree → Fin m)).filter
    (fun k => countVec k = ν), p ν.degree (fun i => Pi.single (k i) (1 : K))

theorem coeff_coeffOfFMS (p : FormalMultilinearSeries K (Fin m → K) K) {n : ℕ} {ν : Fin m →₀ ℕ}
    (h : ν.degree = n) :
    coeff ν (coeffOfFMS p) = ∑ k ∈ (Finset.univ : Finset (Fin n → Fin m)).filter
      (fun k => countVec k = ν), p n (fun i => Pi.single (k i) (1 : K)) := by
  subst h
  rfl

/-- The multilinear term on the diagonal is the degree-`n` part of the series with coefficients
`coeffOfFMS p`. -/
theorem fms_apply_diag_eq_sum_coeff (p : FormalMultilinearSeries K (Fin m → K) K) (n : ℕ)
    (y : Fin m → K) :
    p n (fun _ => y) = ∑ ν ∈ degreeSet m n, coeff ν (coeffOfFMS p) * monomialEval y ν := by
  classical
  rw [fms_apply_diag_eq_sum, ← Finset.sum_fiberwise_of_maps_to (g := countVec)
    (t := degreeSet m n) (fun k _ => mem_degreeSet.mpr (degree_countVec k))]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [coeff_coeffOfFMS p (mem_degreeSet.mp hν), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : countVec k = ν := (Finset.mem_filter.mp hk).2
  rw [← hk', monomialEval_countVec, mul_comm]

/-- `‖c_ν‖ ≤ #{k : ν(k) = ν} · ‖p n‖`. -/
theorem norm_coeff_coeffOfFMS_le (p : FormalMultilinearSeries K (Fin m → K) K) {n : ℕ}
    {ν : Fin m →₀ ℕ} (h : ν.degree = n) :
    ‖coeff ν (coeffOfFMS p)‖ ≤ ((Finset.univ : Finset (Fin n → Fin m)).filter
      (fun k => countVec k = ν)).card * ‖p n‖ := by
  classical
  rw [coeff_coeffOfFMS p h]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Nat.cast_one, one_mul]
  refine ((p n).le_opNorm _).trans ?_
  simp [Pi.norm_single]

/-! ## The bridge -/

/-- The degree-`n` slice of the majorant norm of `coeffOfFMS p` at a constant radius `r'` is at
most `‖p n‖ (m r')^n`. -/
theorem sum_norm_coeffOfFMS_le (p : FormalMultilinearSeries K (Fin m → K) K) (r' : ℝ≥0) (n : ℕ) :
    ∑ ν ∈ degreeSet m n, ‖coeff ν (coeffOfFMS p)‖ * (monomialEval (fun _ => r') ν : ℝ)
      ≤ ‖p n‖ * ((m : ℝ) * r') ^ n := by
  classical
  have hpow : ∀ ν ∈ degreeSet m n, (monomialEval (fun _ => r') ν : ℝ) = (r' : ℝ) ^ n := by
    intro ν hν
    rw [coe_monomialEval, Finsupp.prod_fintype _ _ fun _ => pow_zero _, Finset.prod_pow_eq_pow_sum,
      ← Finsupp.degree_eq_sum, mem_degreeSet.mp hν]
  calc ∑ ν ∈ degreeSet m n, ‖coeff ν (coeffOfFMS p)‖ * (monomialEval (fun _ => r') ν : ℝ)
      ≤ ∑ ν ∈ degreeSet m n, (((Finset.univ : Finset (Fin n → Fin m)).filter
          (fun k => countVec k = ν)).card : ℝ) * ‖p n‖ * (r' : ℝ) ^ n := by
        refine Finset.sum_le_sum fun ν hν => ?_
        rw [hpow ν hν]
        exact mul_le_mul_of_nonneg_right (norm_coeff_coeffOfFMS_le p (mem_degreeSet.mp hν))
          (pow_nonneg r'.2 _)
    _ = (m : ℝ) ^ n * ‖p n‖ * (r' : ℝ) ^ n := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, sum_card_fiber_countVec]
    _ = ‖p n‖ * ((m : ℝ) * r') ^ n := by rw [mul_pow]; ring

/-- A `K`-analytic function at `a` agrees near `a` with the function of a convergent series in
`x - a`. -/
theorem _root_.AnalyticAt.exists_conv_coeff {f : (Fin m → K) → K} {a : Fin m → K}
    (hf : AnalyticAt K f a) :
    ∃ (ρ : Radius m) (c : MvPowerSeries (Fin m) K), ConvNorm ρ c ≠ ⊤ ∧
      ∀ x : Fin m → K, (∀ k, ‖x k‖ < ρ k) → f (a + x) = evalSeries c x := by
  obtain ⟨p, r, hp⟩ := hf
  -- the constant radius `r' = r / (2 (m + 1))` in `ℝ≥0`, with `m r' < r` and `r' < r`
  obtain ⟨r₀, hr₀pos, hr₀r⟩ : ∃ r₀ : ℝ≥0, 0 < r₀ ∧ (r₀ : ℝ≥0∞) < r := by
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos with ⟨r₀, h0, hr⟩
    exact ⟨r₀, by exact_mod_cast h0, hr⟩
  set r' : ℝ≥0 := r₀ / (2 * (m + 1)) with hr'
  have hr'pos : 0 < r' := by positivity
  have hmr' : (m : ℝ≥0) * r' < r₀ := by
    rw [hr', mul_div_assoc']
    refine (div_lt_iff₀ (by positivity)).mpr ?_
    have : (m : ℝ≥0) < 2 * (m + 1) := by
      have h1 : (m : ℝ≥0) < m + 1 := lt_add_one _
      have h2 : (m : ℝ≥0) + 1 ≤ 2 * (m + 1) := by nlinarith
      exact h1.trans_le h2
    calc (m : ℝ≥0) * r₀ = r₀ * m := mul_comm _ _
      _ < r₀ * (2 * (m + 1)) := mul_lt_mul_of_pos_left this hr₀pos
  have hr'r₀ : r' < r₀ := by
    rw [hr']
    refine (div_lt_iff₀ (by positivity)).mpr ?_
    have : (1 : ℝ≥0) < 2 * (m + 1) := by
      have : (0 : ℝ≥0) ≤ m := zero_le
      nlinarith
    calc r₀ = r₀ * 1 := (mul_one _).symm
      _ < r₀ * (2 * (m + 1)) := mul_lt_mul_of_pos_left this hr₀pos
  set ρ : Radius m := ⟨fun _ => r', fun _ => hr'pos⟩ with hρ
  set c := coeffOfFMS p with hc
  -- finiteness of the norm at the constant radius
  have hsum : Summable fun n => ∑ ν ∈ degreeSet m n, ‖coeff ν c‖ * (monomialEval ρ ν : ℝ) := by
    have hrad : ((m : ℝ≥0) * r' : ℝ≥0∞) < p.radius := lt_of_lt_of_le
      (by exact_mod_cast hmr') (hr₀r.le.trans hp.r_le)
    refine (p.summable_norm_mul_pow hrad).of_nonneg_of_le
      (fun n => Finset.sum_nonneg fun ν _ => mul_nonneg (norm_nonneg _) (monomialEval ρ ν).2)
      fun n => ?_
    have := sum_norm_coeffOfFMS_le p r' n
    simpa [hρ, hc] using this
  have hw : Summable fun ν : Fin m →₀ ℕ => ‖coeff ν c‖ * (monomialEval ρ ν : ℝ) :=
    summable_of_summable_sum_degreeSet
      (fun ν => mul_nonneg (norm_nonneg _) (monomialEval ρ ν).2) hsum
  have hnorm : ConvNorm ρ c ≠ ⊤ := by
    rw [convNorm_eq_tsum_coe]
    refine ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp ?_)
    convert hw using 1
    funext ν
    rw [NNReal.coe_mul, coe_nnnorm]
  refine ⟨ρ, c, hnorm, fun x hx => ?_⟩
  -- the two sums agree: the power series at `x` and the regrouped evaluation
  have hxr : ‖x‖ < r' := by
    rw [pi_norm_lt_iff (by exact_mod_cast hr'pos)]
    exact hx
  have hxball : x ∈ Metric.eball (0 : Fin m → K) r := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    calc ((‖x‖₊ : ℝ≥0) : ℝ≥0∞) < r' := by exact_mod_cast hxr
      _ < r₀ := by exact_mod_cast hr'r₀
      _ < r := hr₀r
  have h1 : HasSum (fun n => p n fun _ => x) (f (a + x)) := hp.hasSum hxball
  have hxρ : ∀ k, ‖x k‖ ≤ ρ k := fun k => (hx k).le
  have h2 : HasSum (fun n => ∑ ν ∈ degreeSet m n, coeff ν c * monomialEval x ν) (evalSeries c x) :=
    hasSum_sum_degreeSet (hasSum_evalSeries hnorm hxρ)
  simp_rw [fms_apply_diag_eq_sum_coeff p] at h1
  exact h1.unique h2

/-! ## Uniqueness of coefficients -/

/-- The homogeneous part of degree `n` as a polynomial. -/
noncomputable def homogeneousPoly (f : MvPowerSeries (Fin m) K) (n : ℕ) : MvPolynomial (Fin m) K :=
  ∑ ν ∈ degreeSet m n, MvPolynomial.monomial ν (coeff ν f)

theorem eval_homogeneousPoly (f : MvPowerSeries (Fin m) K) (n : ℕ) (x : Fin m → K) :
    MvPolynomial.eval x (homogeneousPoly f n)
      = ∑ ν ∈ degreeSet m n, coeff ν f * monomialEval x ν := by
  rw [homogeneousPoly, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [MvPolynomial.eval_monomial]
  rfl

theorem coeff_homogeneousPoly (f : MvPowerSeries (Fin m) K) {n : ℕ} {ν : Fin m →₀ ℕ}
    (hν : ν.degree = n) : (homogeneousPoly f n).coeff ν = coeff ν f := by
  classical
  rw [homogeneousPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (degreeSet m n) ν, ite_eq_left (mem_degreeSet.mpr hν)]

/-- Uniqueness of coefficients: two convergent series whose functions agree on a neighbourhood of
`0` are equal. -/
theorem eq_of_evalSeries_eventuallyEq {f g : MvPowerSeries (Fin m) K} (hf : f ∈ Conv K m)
    (hg : g ∈ Conv K m) (h : evalSeries f =ᶠ[𝓝 0] evalSeries g) : f = g := by
  obtain ⟨ρf, hρf⟩ := hf
  obtain ⟨ρg, hρg⟩ := hg
  have hf' : ConvNorm (ρf.min ρg) f ≠ ⊤ := BanachSeries.mono (ρf.min_le_left ρg) hρf
  have hg' : ConvNorm (ρf.min ρg) g ≠ ⊤ := BanachSeries.mono (ρf.min_le_right ρg) hρg
  -- the homogeneous parts agree as functions
  have hparts : ∀ n, homogeneousPoly f n = homogeneousPoly g n := by
    intro n
    refine MvPolynomial.funext fun x => ?_
    rw [eval_homogeneousPoly, eval_homogeneousPoly]
    have hd : iteratedFDeriv K n (evalSeries f) 0 = iteratedFDeriv K n (evalSeries g) 0 :=
      (h.iteratedFDeriv K n).eq_of_nhds
    have hn : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    apply mul_left_cancel₀ hn
    have e1 := factorial_smul_sum_eq_iteratedFDeriv hf' n x
    have e2 := factorial_smul_sum_eq_iteratedFDeriv hg' n x
    rw [nsmul_eq_mul] at e1 e2
    rw [e1, e2, hd]
  ext ν
  have := congrArg (AddMonoidAlgebra.coeff · ν) (hparts ν.degree)
  rwa [coeff_homogeneousPoly f rfl, coeff_homogeneousPoly g rfl] at this

end Analytic

/-! ## Series centred at a point -/

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- The norm-polydisc of radius `ρ` around `a` is a neighbourhood of `a`. -/
theorem eventually_norm_sub_lt (a : Fin m → K) (ρ : Radius m) :
    ∀ᶠ x : Fin m → K in 𝓝 a, ∀ k, ‖(x - a) k‖ < (ρ k : ℝ) := by
  rw [Filter.eventually_all]
  intro k
  have hcont : ContinuousAt (fun x : Fin m → K => ‖(x - a) k‖) a :=
    ((continuous_apply k).comp (continuous_id.sub continuous_const)).norm.continuousAt
  have h0 : ‖(a - a) k‖ < (ρ k : ℝ) := by
    rw [sub_self, Pi.zero_apply, norm_zero]
    exact NNReal.coe_pos.mpr (ρ.2 k)
  exact hcont.eventually_lt continuousAt_const h0

/-- The expansion centred at `a`: an analytic `f` agrees near `a` with the sum of a series of
finite majorant norm in `x - a`. -/
theorem _root_.AnalyticAt.exists_eventuallyEq_evalSeries {f : (Fin m → K) → K} {a : Fin m → K}
    (hf : AnalyticAt K f a) :
    ∃ (ρ : Radius m) (c : MvPowerSeries (Fin m) K), ConvNorm ρ c ≠ ⊤ ∧
      f =ᶠ[𝓝 a] fun x => evalSeries c (x - a) := by
  obtain ⟨ρ, c, hc, hfc⟩ := AnalyticAt.exists_conv_coeff hf
  refine ⟨ρ, c, hc, (eventually_norm_sub_lt a ρ).mono fun x hx => ?_⟩
  change f x = evalSeries c (x - a)
  rw [← hfc (x - a) hx, add_sub_cancel]

end Analytic
