/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Bridge
public import Hironaka.Analytic.Weierstrass.Axis
import Hironaka.Analytic.ConvSeries.Mul
import Hironaka.Analytic.ConvSeries.Order
import Hironaka.Analytic.ConvSeries.Rescale
import Hironaka.Analytic.Germ.Base
import Hironaka.Analytic.Weierstrass.FunctionLevel
import Hironaka.Analytic.Weierstrass.Splitting
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Generic linear changes and the order on the axis

"There are local coordinates `x = (x_1, …, x_m)` centered at `a` such that
`f_a(0, …, 0, x_m) ∼ x_m^e`, where `e = μ_a(f)`" [BM88, proof of Theorem 4.4, p. 24]. The
degree-`e` homogeneous part of a nonzero series of order `e` is a nonzero polynomial
(`homogeneousPoly` of `Hironaka/Analytic/ConvSeries/Bridge.lean`), hence nonzero at some
direction `v` since the field is infinite (`MvPolynomial.funext`); a linear automorphism `L` with
`L e_0 = v` exists (a coordinate swap followed by `x ↦ x + x_k (v - e_k)`); and the restriction
of `f` to the line `K v` is the one-variable series `dirSeries f v` whose degree-`d` coefficient
is the degree-`d` part at `v`. Its leading term is `t^e · h_e(v)` with `h_e(v) ≠ 0`, which is the
hypothesis form of the function-level preparation theorem.

Second, restricting to the `x_0`-axis (`axis`) never lowers the order, with equality iff the
coefficient of `x_0^{μ(f)}` is nonzero; orders add under products on both sides (`order_mul`),
so equality for a product forces equality for every factor: the printed "each
`ℓ_{i,a}(0, …, 0, x_m) ∼ x_m`" of the same passage. Bierstone and Milman use both parts to choose
the coordinates of that proof.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open MvPowerSeries
open scoped Topology ENNReal NNReal

namespace Analytic

variable {K : Type*} [RCLike K]

variable {n : ℕ}

/-! ### Linear changes sending `e_0` to a given vector -/

/-- `x ↦ x + x_k • (v - e_k)`: fixes `e_j` for `j ≠ k` and sends `e_k` to `v`; a linear
automorphism when `v_k ≠ 0`. -/
noncomputable def replaceBasis (k : Fin n) (v : Fin n → K) (hv : v k ≠ 0) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) where
  toFun x := x + x k • (v - Pi.single k 1)
  invFun y := y - ((v k)⁻¹ * y k) • (v - Pi.single k 1)
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' c x := by
    ext j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv x := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
    by_cases hj : j = k
    · subst hj
      simp only [Pi.single_eq_same]
      field_simp
      ring
    · simp only [Pi.single_eq_of_ne hj]
      field_simp
      ring
  right_inv y := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
    by_cases hj : j = k
    · subst hj
      simp only [Pi.single_eq_same]
      field_simp
      ring
    · simp only [Pi.single_eq_of_ne hj]
      field_simp
      ring

theorem replaceBasis_single (k : Fin n) (v : Fin n → K) (hv : v k ≠ 0) :
    replaceBasis k v hv (Pi.single k 1) = v := by
  change Pi.single k 1 + (Pi.single k (1 : K) : Fin n → K) k • (v - Pi.single k 1) = v
  rw [Pi.single_eq_same, one_smul, add_sub_cancel]

variable (K) in
/-- The coordinate swap `0 ↔ k` as a linear automorphism of `K^{n+1}`. -/
noncomputable def swapCoord (k : Fin (n + 1)) : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.swap 0 k)

theorem swapCoord_single_zero (k : Fin (n + 1)) :
    swapCoord K k (Pi.single 0 1) = Pi.single k 1 := by
  ext i
  change (Pi.single (0 : Fin (n + 1)) (1 : K) : Fin (n + 1) → K) (Equiv.swap 0 k i) =
    (Pi.single k (1 : K) : Fin (n + 1) → K) i
  simp only [Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

/-- The linear change: every nonzero vector is `L e_0` for a linear automorphism `L`. -/
theorem exists_continuousLinearEquiv_single_eq {v : Fin (n + 1) → K} (hv : v ≠ 0) :
    ∃ L : (Fin (n + 1) → K) ≃L[K] (Fin (n + 1) → K), L (Pi.single 0 1) = v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  refine ⟨((swapCoord K k).trans (replaceBasis k v hk)).toContinuousLinearEquiv, ?_⟩
  change ((swapCoord K k).trans (replaceBasis k v hk)) (Pi.single 0 1) = v
  rw [LinearEquiv.trans_apply, swapCoord_single_zero, replaceBasis_single]

/-! ### The leading homogeneous part -/

/-- The leading homogeneous part of a nonzero series is nonzero at some direction (the field is
infinite). -/
theorem exists_eval_homogeneousPoly_ne_zero {f : MvPowerSeries (Fin n) K} (hf : f ≠ 0) :
    ∃ v : Fin n → K, MvPolynomial.eval v (homogeneousPoly f f.order.toNat) ≠ 0 := by
  by_contra h
  push Not at h
  have hP : homogeneousPoly f f.order.toNat = 0 :=
    MvPolynomial.funext fun v => by rw [h v, map_zero]
  have hfin : (f.order.toNat : ℕ∞) = f.order := ne_zero_iff_order_finite.mp hf
  obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
  have hdeg' : d.degree = f.order.toNat := by
    exact_mod_cast hdeg.trans hfin.symm
  have h2 := coeff_homogeneousPoly f hdeg'
  rw [hP, AddMonoidAlgebra.coeff_zero] at h2
  exact hd h2.symm

/-- Evaluating a monomial on a multiple of `v`: `(t v)^ν = t^{|ν|} v^ν`. -/
theorem monomialEval_smul (t : K) (v : Fin n → K) (ν : Fin n →₀ ℕ) :
    monomialEval (t • v) ν = t ^ Finsupp.degree ν * monomialEval v ν := by
  unfold monomialEval
  rw [Finsupp.prod_pow, Finsupp.prod_pow, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_pow]

/-- The sum of a convergent series along the line `t v`, regrouped by degree. -/
theorem hasSum_evalSeries_smul {ρ : Radius n} {f : MvPowerSeries (Fin n) K}
    (hf : ConvNorm ρ f ≠ ⊤) {t : K} {v : Fin n → K} (h : ∀ k, ‖t * v k‖ ≤ ρ k) :
    HasSum (fun d : ℕ => t ^ d * MvPolynomial.eval v (homogeneousPoly f d))
      (evalSeries f (t • v)) := by
  have h1 := hasSum_sum_degreeSet (hasSum_evalSeries hf (x := t • v) fun k => by
    rw [Pi.smul_apply, smul_eq_mul]; exact h k)
  convert h1 using 1
  funext d
  rw [eval_homogeneousPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [monomialEval_smul, mem_degreeSet.mp hν]
  ring

/-! ### The restriction of a series to a line -/

/-- The restriction of `f` to the line `K v`, as a series in one variable: its degree-`d`
coefficient is the degree-`d` homogeneous part of `f` at `v`. -/
noncomputable def dirSeries (f : MvPowerSeries (Fin n) K) (v : Fin n → K) :
    MvPowerSeries (Fin 1) K :=
  fun μ => MvPolynomial.eval v (homogeneousPoly f (μ 0))

theorem coeff_dirSeries (f : MvPowerSeries (Fin n) K) (v : Fin n → K) (μ : Fin 1 →₀ ℕ) :
    coeff μ (dirSeries f v) = MvPolynomial.eval v (homogeneousPoly f (μ 0)) := rfl

theorem coeff_single_dirSeries (f : MvPowerSeries (Fin n) K) (v : Fin n → K) (d : ℕ) :
    coeff (Finsupp.single 0 d) (dirSeries f v) = MvPolynomial.eval v (homogeneousPoly f d) := by
  rw [coeff_dirSeries, Finsupp.single_eq_same]

theorem evalSeries_dirSeries {ρ : Radius n} {f : MvPowerSeries (Fin n) K}
    (hf : ConvNorm ρ f ≠ ⊤) {t : K} {v : Fin n → K} (h : ∀ k, ‖t * v k‖ ≤ ρ k) :
    evalSeries (dirSeries f v) (fun _ => t) = evalSeries f (t • v) := by
  rw [← (hasSum_evalSeries_smul hf h).tsum_eq]
  unfold evalSeries
  rw [← natEquivFin1.tsum_eq]
  refine tsum_congr fun d => ?_
  rw [natEquivFin1_apply, coeff_single_dirSeries, monomialEval_single_pow, mul_comm]

/-- `|v^ν| r^{|ν|} ≤ ρ^ν` when `r |v_k| ≤ ρ_k` for every `k`. -/
theorem nnnorm_monomialEval_mul_pow_le {ρ : Fin n → ℝ≥0} {r : ℝ≥0} {v : Fin n → K}
    (hrv : ∀ k, r * ‖v k‖₊ ≤ ρ k) {d : ℕ} {ν : Fin n →₀ ℕ} (hν : ν.degree = d) :
    ‖monomialEval v ν‖₊ * r ^ d ≤ monomialEval ρ ν := by
  rw [← hν, Finsupp.degree_eq_sum, monomialEval, Finsupp.prod_pow, nnnorm_prod, monomialEval,
    Finsupp.prod_fintype _ _ (fun k => pow_zero _), ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod fun k _ => ?_
  rw [nnnorm_pow, ← mul_pow, mul_comm]
  exact pow_le_pow_left' (hrv k) _

/-- The restriction to a line converges on the radius `r` when `r |v_k| ≤ ρ_k`:
`‖dirSeries f v‖_r ≤ ‖f‖_ρ`. -/
theorem convNorm_dirSeries_le {ρ : Fin n → ℝ≥0} {r : ℝ≥0} {v : Fin n → K}
    (hrv : ∀ k, r * ‖v k‖₊ ≤ ρ k) (f : MvPowerSeries (Fin n) K) :
    ConvNorm (fun _ => r) (dirSeries f v) ≤ ConvNorm ρ f := by
  unfold ConvNorm
  rw [ennreal_tsum_eq_tsum_sum_degreeSet (fun ν => ‖coeff ν f‖ₑ * (monomialEval ρ ν : ℝ≥0∞)),
    ← natEquivFin1.tsum_eq]
  refine ENNReal.tsum_le_tsum fun d => ?_
  rw [natEquivFin1_apply, coeff_single_dirSeries, monomialEval_single_pow, eval_homogeneousPoly]
  calc ‖∑ ν ∈ degreeSet n d, coeff ν f * monomialEval v ν‖ₑ * ((r ^ d : ℝ≥0) : ℝ≥0∞)
      ≤ (∑ ν ∈ degreeSet n d, ‖coeff ν f‖ₑ * ‖monomialEval v ν‖ₑ) * ((r ^ d : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
        rw [enorm_mul]
    _ = ∑ ν ∈ degreeSet n d, ‖coeff ν f‖ₑ * ((‖monomialEval v ν‖₊ * r ^ d : ℝ≥0) : ℝ≥0∞) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [ENNReal.coe_mul, mul_assoc, enorm_eq_nnnorm (monomialEval v ν)]
    _ ≤ ∑ ν ∈ degreeSet n d, ‖coeff ν f‖ₑ * (monomialEval ρ ν : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun ν hν => ?_
        gcongr
        exact nnnorm_monomialEval_mul_pow_le hrv (mem_degreeSet.mp hν)

/-- A radius `r > 0` with `r |v_k| ≤ ρ_k` for all `k`. -/
theorem exists_radius_smul_le (ρ : Radius n) (v : Fin n → K) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ k, r * ‖v k‖₊ ≤ ρ k := by
  obtain ⟨r, hr0, hr⟩ := Radius.exists_le
    (⟨fun k => ρ k / (‖v k‖₊ + 1), fun k => div_pos (ρ.pos k) (by positivity)⟩ : Radius n)
  refine ⟨r, hr0, fun k => ?_⟩
  have h1 : r ≤ ρ k / (‖v k‖₊ + 1) := hr k
  calc r * ‖v k‖₊ ≤ (ρ k / (‖v k‖₊ + 1)) * (‖v k‖₊ + 1) :=
        mul_le_mul' h1 (le_add_right le_rfl)
    _ = ρ k := div_mul_cancel₀ _ (by positivity)

/-! ### The generic linear change -/

theorem homogeneousPoly_eq_zero_of_lt_order {f : MvPowerSeries (Fin n) K} {d : ℕ}
    (hd : (d : ℕ∞) < f.order) : homogeneousPoly f d = 0 := by
  unfold homogeneousPoly
  refine Finset.sum_eq_zero fun ν hν => ?_
  rw [coeff_of_lt_order (by rw [mem_degreeSet.mp hν]; exact hd)]
  exact (MvPolynomial.monomial ν).map_zero

/-- A homogeneous part of positive degree vanishes at the origin. -/
theorem eval_zero_homogeneousPoly_of_pos (f : MvPowerSeries (Fin n) K) {d : ℕ} (hd : 0 < d) :
    MvPolynomial.eval (0 : Fin n → K) (homogeneousPoly f d) = 0 := by
  rw [eval_homogeneousPoly]
  refine Finset.sum_eq_zero fun ν hν => ?_
  have hν0 : ν ≠ 0 := by
    rintro rfl
    have h := mem_degreeSet.mp hν
    rw [map_zero] at h
    omega
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hν0
  rw [monomialEval, Finsupp.prod_pow, Finset.prod_eq_zero (Finset.mem_univ k), mul_zero]
  rw [Pi.zero_apply, zero_pow (Finsupp.mem_support_iff.mp hk)]

/-- The remainder part of the line restriction below the order vanishes. -/
theorem wR_dirSeries_eq_zero {f : MvPowerSeries (Fin n) K} (v : Fin n → K) :
    wR f.order.toNat (dirSeries f v) = 0 := by
  ext μ
  rw [coeff_wR, (coeff μ).map_zero]
  split_ifs with h
  · have hlt : ((μ 0 : ℕ) : ℕ∞) < f.order :=
      lt_of_lt_of_le (by exact_mod_cast h) (ENat.natCast_toNat_le_self _)
    rw [coeff_dirSeries, homogeneousPoly_eq_zero_of_lt_order hlt, map_zero]
  · rfl

variable (K) in
/-- The map `t ↦ (t, …, t) : K → K^1` as a continuous linear map. -/
noncomputable def constCLM : K →L[K] (Fin 1 → K) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id K K

theorem constCLM_apply (t : K) : constCLM K t = fun _ => t := rfl

theorem eventually_abs_lt_real (r : ℝ≥0) (hr : 0 < r) : ∀ᶠ t : K in 𝓝 0, ‖t‖ < (r : ℝ) := by
  filter_upwards [Metric.ball_mem_nhds (0 : K) (show (0 : ℝ) < r by exact_mod_cast hr)] with t ht
  rwa [mem_ball_zero_iff] at ht

/-- After a linear change, a nonzero convergent `f` of order `e` is `x_0`-regular of order `e` on
the axis, in the hypothesis form of the function-level preparation theorem: the printed "there
are local coordinates … such that `f_a(0, …, 0, x_m) ∼ x_m^e`" of [BM88, proof of Theorem 4.4,
p. 24]. -/
theorem exists_linearChange_axis_regular {m : ℕ} {f : MvPowerSeries (Fin (m + 1)) K}
    (hf : f ∈ Conv K (m + 1)) (hf0 : f ≠ 0) :
    ∃ L : (Fin (m + 1) → K) ≃L[K] (Fin (m + 1) → K), ∃ e : K → K,
      AnalyticAt K e 0 ∧ e 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 (0 : K), evalSeries f (L (Pi.single 0 t)) = t ^ f.order.toNat * e t := by
  obtain ⟨ρ, hρ⟩ := hf
  have hρ' : ConvNorm ρ f ≠ ⊤ := hρ
  obtain ⟨v, hv⟩ := exists_eval_homogeneousPoly_ne_zero hf0
  rcases Nat.eq_zero_or_pos f.order.toNat with h0 | hpos
  · -- order zero: the constant coefficient is nonzero and the identity is trivial
    refine ⟨ContinuousLinearEquiv.refl K _, fun t => evalSeries f (Pi.single 0 t), ?_, ?_, ?_⟩
    · have han : AnalyticAt K (evalSeries f) (Pi.single (0 : Fin (m + 1)) (0 : K)) := by
        rw [Pi.single_zero]
        exact analyticOnNhd_evalSeries hρ' 0 (mem_polydisc_iff.mpr fun k => by
          rw [Pi.zero_apply, norm_zero]; exact_mod_cast ρ.pos k)
      exact han.comp ((ContinuousLinearMap.single K (fun _ : Fin (m + 1) => K) 0).analyticAt 0)
    · change evalSeries f (Pi.single 0 0) ≠ 0
      rw [Pi.single_zero, evalSeries_zero_eq]
      have h1 : f.order = 0 := by
        have := ne_zero_iff_order_finite.mp hf0
        rw [h0, Nat.cast_zero] at this
        exact this.symm
      exact fun hc => order_ne_zero_iff_constCoeff_eq_zero.mpr hc h1
    · rw [h0]
      exact Filter.Eventually.of_forall fun t => by
        simp only [pow_zero, one_mul, ContinuousLinearEquiv.coe_refl', id_eq]
  · -- positive order: the leading part vanishes at `0`, so `v ≠ 0`
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv (eval_zero_homogeneousPoly_of_pos f hpos)
    obtain ⟨L, hL⟩ := exists_continuousLinearEquiv_single_eq hv0
    obtain ⟨r, hr0, hrv⟩ := exists_radius_smul_le ρ v
    set r1 : Radius 1 := ⟨fun _ => r, fun _ => hr0⟩ with hr1
    have hD : ConvNorm r1 (dirSeries f v) ≠ ⊤ :=
      ne_top_of_le_ne_top hρ' (convNorm_dirSeries_le hrv f)
    have hsplit : dirSeries f v = X 0 ^ f.order.toNat * wQ f.order.toNat (dirSeries f v) := by
      have h := X_pow_mul_wQ_add_wR f.order.toNat (dirSeries f v)
      rw [wR_dirSeries_eq_zero, add_zero] at h
      exact h.symm
    set E := wQ f.order.toNat (dirSeries f v) with hE
    have hEB : ConvNorm r1 E ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hD) (convNorm_wQ_le r1 _ _)
    refine ⟨L, fun t => evalSeries E (fun _ => t), ?_, ?_, ?_⟩
    · have han : AnalyticAt K (evalSeries E) (constCLM K 0) :=
        analyticOnNhd_evalSeries hEB (constCLM K 0) (mem_polydisc_iff.mpr fun k => by
          change ‖(0 : K)‖ < (r : ℝ); rw [norm_zero]; exact_mod_cast hr0)
      exact han.comp ((constCLM K).analyticAt 0)
    · change evalSeries E (fun _ => (0 : K)) ≠ 0
      have h1 : (fun _ : Fin 1 => (0 : K)) = 0 := rfl
      rw [h1, evalSeries_zero_eq, hE, ← coeff_zero_eq_constantCoeff_apply, coeff_wQ,
        zero_add (Finsupp.single (0 : Fin 1) f.order.toNat), coeff_single_dirSeries]
      exact hv
    · filter_upwards [eventually_abs_lt_real r hr0] with t ht
      have htv : ∀ k, ‖t * v k‖ ≤ ρ k := fun k => by
        rw [norm_mul]
        calc ‖t‖ * ‖v k‖ ≤ (r : ℝ) * ‖v k‖ :=
              mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)
          _ ≤ ρ k := by
              have := hrv k
              rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm] at this
              exact this
      have hLt : L (Pi.single 0 t) = t • v := by
        rw [← hL, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
      rw [hLt, ← evalSeries_dirSeries hρ' htv, hsplit,
        evalSeries_mul (convNorm_X_pow_ne_top r1 0 _) hEB (fun _ => ht.le), evalSeries_X_pow]

/-! ### The order on the axis -/

/-- The order does not drop under restriction to the axis. -/
theorem order_le_order_axis {m : ℕ} (f : MvPowerSeries (Fin (m + 1)) K) :
    f.order ≤ (axis f).order := by
  refine le_order fun d hd => ?_
  rw [coeff_axis]
  apply coeff_of_lt_order
  rwa [Finsupp.degree_single, ← degree_fin1]

/-- The degree-`e` homogeneous part at `e_0` is the coefficient of `x_0^e`. -/
theorem eval_single_homogeneousPoly {m : ℕ} (f : MvPowerSeries (Fin (m + 1)) K) (e : ℕ) :
    MvPolynomial.eval (Pi.single 0 1) (homogeneousPoly f e) = coeff (Finsupp.single 0 e) f := by
  rw [eval_homogeneousPoly, Finset.sum_eq_single (Finsupp.single 0 e)]
  · rw [monomialEval_single_pow, Pi.single_eq_same, one_pow, mul_one]
  · intro ν hν hne
    rw [monomialEval_pi_single, ite_eq_right, mul_zero]
    intro h
    apply hne
    have h1 := mem_degreeSet.mp hν
    rw [h, Finsupp.degree_single] at h1
    rw [h, h1]
  · intro h
    exact absurd (mem_degreeSet.mpr (by rw [Finsupp.degree_single])) h

/-- Equality of orders on the axis iff the coefficient of `x_0^{μ(f)}` is nonzero. -/
theorem order_axis_eq_iff {m : ℕ} {f : MvPowerSeries (Fin (m + 1)) K} (hf : f ≠ 0) :
    (axis f).order = f.order ↔ coeff (Finsupp.single 0 f.order.toNat) f ≠ 0 := by
  have hfin : (f.order.toNat : ℕ∞) = f.order := ne_zero_iff_order_finite.mp hf
  constructor
  · intro h
    obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_order (f := axis f) (by
      rw [h]; exact hfin)
    have hd0 : d 0 = f.order.toNat := by
      rw [← degree_fin1]
      exact_mod_cast hdeg.trans (h.trans hfin.symm)
    rwa [coeff_axis, hd0] at hd
  · intro h
    refine le_antisymm ?_ (order_le_order_axis f)
    have h1 := order_le (f := axis f) (d := Finsupp.single 0 f.order.toNat)
      (by rw [coeff_single_axis]; exact h)
    rwa [Finsupp.degree_single, hfin] at h1

/-- For two factors: if the order of `f g` is preserved on the axis, so are the orders of `f` and
`g` (orders add on both sides). -/
theorem order_axis_eq_of_mul {m : ℕ} {f g : MvPowerSeries (Fin (m + 1)) K} (hf : f ≠ 0)
    (hg : g ≠ 0) (h : (axis (f * g)).order = (f * g).order) :
    (axis f).order = f.order ∧ (axis g).order = g.order := by
  rw [axis_mul, order_mul, order_mul] at h
  have h1 := order_le_order_axis f
  have h2 := order_le_order_axis g
  have hf' : f.order ≠ ⊤ := by rwa [Ne, order_eq_top_iff]
  have hg' : g.order ≠ ⊤ := by rwa [Ne, order_eq_top_iff]
  have hsum : (axis f).order + (axis g).order ≠ ⊤ := by
    rw [h]; exact WithTop.add_ne_top.mpr ⟨hf', hg'⟩
  have haf : (axis f).order ≠ ⊤ := fun ht => hsum (by rw [ht, top_add])
  have hag : (axis g).order ≠ ⊤ := fun ht => hsum (by rw [ht, add_top])
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hf'
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hg'
  obtain ⟨a', ha'⟩ := ENat.ne_top_iff_exists.mp haf
  obtain ⟨b', hb'⟩ := ENat.ne_top_iff_exists.mp hag
  rw [← ha, ← hb, ← ha', ← hb'] at h
  rw [← ha, ← ha'] at h1
  rw [← hb, ← hb'] at h2
  rw [← ha, ← hb, ← ha', ← hb']
  norm_cast at h h1 h2 ⊢
  exact ⟨by omega, by omega⟩

/-- If the order of a product is preserved on the axis, so is the order of every factor: the
printed "each `ℓ_{i,a}(0, …, 0, x_m) ∼ x_m`" of [BM88, proof of Theorem 4.4, p. 24]. -/
theorem order_axis_eq_of_prod {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries (Fin (m + 1)) K) (hne : ∀ i ∈ s, f i ≠ 0)
    (h : (axis (∏ i ∈ s, f i)).order = (∏ i ∈ s, f i).order) :
    ∀ i ∈ s, (axis (f i)).order = (f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => intro i hi; exact absurd hi (Finset.notMem_empty i)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    have hprod : ∏ i ∈ s, f i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hne i (Finset.mem_insert_of_mem hi)
    obtain ⟨h1, h2⟩ := order_axis_eq_of_mul (hne a (Finset.mem_insert_self a s)) hprod h
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h1
    · exact ih (fun j hj => hne j (Finset.mem_insert_of_mem hj)) h2 i hi

end Analytic
