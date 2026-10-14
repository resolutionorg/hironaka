/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Eval
public import Hironaka.Analytic.Weierstrass.Axis
import Hironaka.Analytic.ConvSeries.Bridge
import Hironaka.Analytic.ConvSeries.Mul
import Hironaka.Analytic.ConvSeries.Rescale
import Hironaka.Analytic.Weierstrass.Poly
import Hironaka.Analytic.Weierstrass.Preparation
import Hironaka.Analytic.Weierstrass.Regular
import Hironaka.Analytic.Weierstrass.Tail
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Function-level Weierstrass preparation on a product polydisc

An analytic `f` near `0 ∈ K^{m+1}` whose restriction to the `x_0`-axis is `t^d · e(t)` with
`e(0) ≠ 0` (the printed `f(0, …, 0, x_m) ∼ x_m^d`) is the function of a convergent series `F`
(`Hironaka/Analytic/ConvSeries/Bridge.lean`); the restriction of `F` to the axis is `x_0^d E`
with `E` the series of `e` (uniqueness of the coefficients of a one-variable series), so `F` is
`x_0`-regular of order `d`. Convergent preparation (`Preparation.lean`) gives
`F = U · (x_0^d + ∑ c_j x_0^{d-1-j})`; on a polydisc where all the series converge and the sum of
`U` does not vanish, evaluation is multiplicative and additive, which gives the product form
`f = u · P` on `V × D` with which Bierstone and Milman open their proof ("By the Weierstrass
preparation theorem, we can assume that `U = V × D`", [BM88, proof of Theorem 4.4, p. 24]).

This function-level form is the one used by the Taylor expansion of germs on a manifold
(`Hironaka/Manifold/Germ`) and by the local models of Oka's coherence theorem
(`Hironaka/AnalyticSpace/Oka`).

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

public section

open scoped ENNReal NNReal Topology
open MvPowerSeries Filter

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

/-! ### Evaluation of monomials, sums, lifts and axis restrictions -/

theorem evalSeries_add {ρ : Radius m} {f g : MvPowerSeries (Fin m) K} (hf : ConvNorm ρ f ≠ ⊤)
    (hg : ConvNorm ρ g ≠ ⊤) {x : Fin m → K} (hx : ∀ k, ‖x k‖ ≤ ρ k) :
    evalSeries (f + g) x = evalSeries f x + evalSeries g x := by
  have h := (hasSum_evalSeries hf hx).add (hasSum_evalSeries hg hx)
  have h' : HasSum (fun ν => coeff ν (f + g) * monomialEval x ν)
      (evalSeries f x + evalSeries g x) := by
    convert h using 1
    funext ν
    rw [map_add, add_mul]
  exact h'.tsum_eq

theorem evalSeries_sum {ρ : Radius m} {ι : Type*} (s : Finset ι) {F : ι → MvPowerSeries (Fin m) K}
    (hF : ∀ i ∈ s, ConvNorm ρ (F i) ≠ ⊤) {x : Fin m → K} (hx : ∀ k, ‖x k‖ ≤ ρ k) :
    evalSeries (∑ i ∈ s, F i) x = ∑ i ∈ s, evalSeries (F i) x := by
  have h := hasSum_sum fun i hi => hasSum_evalSeries (hF i hi) hx
  have h' : HasSum (fun ν => coeff ν (∑ i ∈ s, F i) * monomialEval x ν)
      (∑ i ∈ s, evalSeries (F i) x) := by
    convert h using 1
    funext ν
    rw [map_sum, Finset.sum_mul]
  exact h'.tsum_eq

/-- Evaluating a lifted tail series forgets the first coordinate. -/
theorem evalSeries_liftTail (a : MvPowerSeries (Fin m) K) (x : Fin (m + 1) → K) :
    evalSeries (liftTail a) x = evalSeries a (Fin.tail x) := by
  unfold evalSeries
  refine (Function.Injective.tsum_eq (f := fun μ : Fin (m + 1) →₀ ℕ =>
    coeff μ (liftTail a) * monomialEval x μ) (cons_injective 0) ?_).symm.trans
    (tsum_congr fun y => ?_)
  · intro μ hμ
    by_contra hμ'
    apply hμ
    have h0 : μ 0 ≠ 0 := fun h => hμ' ⟨μ.tail, by
      beta_reduce
      rw [← h, Finsupp.cons_tail]⟩
    have : coeff μ (liftTail a : MvPowerSeries (Fin (m + 1)) K) = 0 := by
      rw [← Finsupp.cons_tail μ, coeff_cons_liftTail, ite_eq_right h0]
    simp [this]
  · rw [coeff_cons_liftTail, ite_eq_left rfl, monomialEval_cons, pow_zero, one_mul]

theorem monomialEval_pi_single (t : K) (ν : Fin (m + 1) →₀ ℕ) :
    monomialEval (Pi.single 0 t) ν = if ν = Finsupp.single 0 (ν 0) then t ^ ν 0 else 0 := by
  split_ifs with h
  · conv_lhs => rw [h]
    rw [monomialEval_single_pow, Pi.single_eq_same]
  · have : ∃ j, j ≠ 0 ∧ ν j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h (eq_single_zero_of_tail_eq_zero hcon)
    obtain ⟨j, hj, hνj⟩ := this
    unfold monomialEval Finsupp.prod
    exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hνj)
      (by simp [Pi.single_eq_of_ne hj, hνj])

/-- Evaluating the axis restriction is evaluating on the axis. -/
theorem evalSeries_axis (F : MvPowerSeries (Fin (m + 1)) K) (y : Fin 1 → K) :
    evalSeries (axis F) y = evalSeries F (Pi.single 0 (y 0)) := by
  unfold evalSeries
  refine (tsum_congr fun ν => ?_).trans (Function.Injective.tsum_eq
    (f := fun μ : Fin (m + 1) →₀ ℕ => coeff μ F * monomialEval (Pi.single 0 (y 0)) μ)
    Fin1.single_apply_injective ?_)
  · rw [coeff_axis, monomialEval_fin1, monomialEval_single_pow, Pi.single_eq_same]
  · intro μ hμ
    have hμ' : monomialEval (Pi.single (0 : Fin (m + 1)) (y 0)) μ ≠ 0 := fun h => hμ (by simp [h])
    rw [monomialEval_pi_single] at hμ'
    have hμeq : μ = Finsupp.single 0 (μ 0) := by
      by_contra h
      exact hμ' (ite_eq_right h)
    exact ⟨Finsupp.single 0 (μ 0), by
      beta_reduce
      rw [Finsupp.single_eq_same, ← hμeq]⟩

/-! ### Regularity from the axis restriction -/

/-- If `F(x_0, 0) = x_0^d E(x_0)` with `E(0) ≠ 0`, then `F` is `x_0`-regular of order `d`. -/
theorem isRegularIn_of_axis_eq {F : MvPowerSeries (Fin (m + 1)) K} {E : MvPowerSeries (Fin 1) K}
    {d : ℕ} (h : axis F = X 0 ^ d * E) (hE : constantCoeff E ≠ 0) : IsRegularIn F d := by
  rw [isRegularIn_iff]
  have key : ∀ k, coeff (Finsupp.single 0 k) F =
      if d ≤ k then coeff (Finsupp.single 0 (k - d)) E else 0 := fun k => by
    rw [← coeff_single_axis, h, X_pow_eq, coeff_monomial_mul]
    by_cases hdk : d ≤ k
    · rw [ite_eq_left (Finsupp.single_le_iff.mpr (by rwa [Finsupp.single_eq_same])),
        ite_eq_left hdk, one_mul, ← Finsupp.single_tsub]
    · rw [ite_eq_right (fun h' => hdk (by simpa using Finsupp.single_le_iff.mp h')),
        ite_eq_right hdk]
  refine ⟨fun k hk => by rw [key, ite_eq_right (not_le.mpr hk)], ?_⟩
  rw [key, ite_eq_left le_rfl, tsub_self, Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply]
  exact hE

/-! ### Preparation at function level -/

/-- Function-level preparation on a product polydisc: an analytic `f` near `0` whose restriction
to the `x_0`-axis is `t^d` times an analytic unit is `u · P` on a polydisc, with `u` analytic and
nonvanishing there and the coefficients `c_j` of the Weierstrass polynomial `P` analytic on the
tail polydisc and vanishing at `0` [BM88, proof of Theorem 4.4, p. 24]. -/
theorem _root_.AnalyticAt.exists_weierstrass_product_nhd {f : (Fin (m + 1) → K) → K}
    (hf : AnalyticAt K f 0) {d : ℕ}
    (hd : ∃ e : K → K, AnalyticAt K e 0 ∧ e 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 (0 : K), f (Pi.single 0 t) = t ^ d * e t) :
    ∃ (ρ : Radius (m + 1)) (u : (Fin (m + 1) → K) → K) (c : Fin d → (Fin m → K) → K),
      AnalyticOnNhd K u (polydisc K ρ) ∧ (∀ x ∈ polydisc K ρ, u x ≠ 0) ∧
      (∀ j, AnalyticOnNhd K (c j)
        (polydisc K (⟨fun k => ρ k.succ, fun k => ρ.pos k.succ⟩ : Radius m))) ∧
      (∀ j, c j 0 = 0) ∧
      ∀ x ∈ polydisc K ρ,
        f x = u x * (x 0 ^ d + ∑ j : Fin d, c j (Fin.tail x) * x 0 ^ (d - 1 - (j : ℕ))) := by
  obtain ⟨e, he, he0, hfe⟩ := hd
  -- the series of `f`
  obtain ⟨ρF, F, hF, hfF⟩ := AnalyticAt.exists_conv_coeff hf
  simp only [zero_add] at hfF
  have hFConv : F ∈ Conv K (m + 1) := ⟨ρF, hF⟩
  -- the series of `e`, as a series in one variable
  have he' : AnalyticAt K (fun y : Fin 1 → K => e (y 0)) 0 := by
    have hproj : AnalyticAt K (fun y : Fin 1 → K => y 0) 0 :=
      (ContinuousLinearMap.proj (R := K) (φ := fun _ : Fin 1 => K) (0 : Fin 1)).analyticAt 0
    exact he.comp_of_eq hproj rfl
  obtain ⟨ρE, E, hE, hEe⟩ := AnalyticAt.exists_conv_coeff he'
  simp only [zero_add] at hEe
  have hEConv : E ∈ Conv K 1 := ⟨ρE, hE⟩
  have hE0 : constantCoeff E ≠ 0 := by
    rw [← evalSeries_zero_eq, ← hEe 0 fun k => by
      rw [Pi.zero_apply, norm_zero]; exact_mod_cast ρE.pos k]
    exact he0
  -- the restriction of `F` to the axis is `x_0^d E`
  have haxis : axis F = X 0 ^ d * E := by
    refine eq_of_evalSeries_eventuallyEq (axis_mem_conv hFConv)
      (mul_mem (pow_mem (X_mem_conv 0) d) hEConv) ?_
    have hproj0 : Tendsto (fun y : Fin 1 → K => y 0) (𝓝 0) (𝓝 0) :=
      (continuous_apply (0 : Fin 1)).tendsto (0 : Fin 1 → K)
    have h1 : ∀ᶠ y in 𝓝 (0 : Fin 1 → K), f (Pi.single 0 (y 0)) = (y 0) ^ d * e (y 0) :=
      hproj0.eventually hfe
    filter_upwards [h1, eventually_abs_lt ρE,
      eventually_abs_lt (⟨fun _ => ρF 0, fun _ => ρF.pos 0⟩ : Radius 1)] with y hy hyE hyF
    have hx : ∀ k, ‖(Pi.single (0 : Fin (m + 1)) (y 0) : Fin (m + 1) → K) k‖ < (ρF k : ℝ) :=
        fun k => by
      by_cases hk : k = 0
      · subst hk
        rw [Pi.single_eq_same]
        exact hyF 0
      · rw [Pi.single_eq_of_ne hk, norm_zero]
        exact_mod_cast ρF.pos k
    calc evalSeries (axis F) y = evalSeries F (Pi.single 0 (y 0)) := evalSeries_axis F y
      _ = f (Pi.single 0 (y 0)) := (hfF _ hx).symm
      _ = (y 0) ^ d * e (y 0) := hy
      _ = evalSeries (X 0 ^ d : MvPowerSeries (Fin 1) K) y * evalSeries E y := by
        rw [evalSeries_X_pow, hEe y hyE]
      _ = evalSeries (X 0 ^ d * E) y :=
        (evalSeries_mul (convNorm_X_pow_ne_top ρE 0 d) hE fun k => (hyE k).le).symm
  have hreg : IsRegularIn F d := isRegularIn_of_axis_eq haxis hE0
  -- convergent preparation
  obtain ⟨U, C, hUConv, hU0, hC, hFU, -⟩ := exists_unique_weierstrassPreparation hFConv hreg
  obtain ⟨ρU, hρU⟩ := hUConv
  choose ρj hρj using fun j => (hC j).1
  obtain ⟨ρC, hρC⟩ := Radius.exists_le_forall ρj
  have hCj : ∀ j, ConvNorm ρC (C j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (hρj j) (ConvNorm_mono (hρC j) _)
  set ρC' : Radius (m + 1) := ⟨Fin.cons 1 ρC, fun k => by
    refine Fin.cases ?_ (fun j => ?_) k
    · exact one_pos
    · exact ρC.pos j⟩ with hρC'
  -- nonvanishing of `u` near `0`
  have hUcont : ContinuousAt (evalSeries U) 0 := by
    refine ((analyticOnNhd_evalSeries hρU) 0 ?_).continuousAt
    intro k
    rw [Pi.zero_apply, norm_zero]
    exact_mod_cast ρU.pos k
  have hU0' : evalSeries U 0 ≠ 0 := by rw [evalSeries_zero_eq]; exact hU0
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp (hUcont.eventually_ne hU0')
  set ρδ : Radius (m + 1) := ⟨fun _ => Real.toNNReal δ, fun _ => Real.toNNReal_pos.mpr hδ0⟩
    with hρδ
  -- the common radius
  set ρ : Radius (m + 1) := ((ρF.min ρU).min ρC').min ρδ with hρ
  have hρF : ∀ k, ρ k ≤ ρF k := fun k =>
    ((Radius.min_le_left _ _ k).trans (Radius.min_le_left _ _ k)).trans (Radius.min_le_left _ _ k)
  have hρU' : ∀ k, ρ k ≤ ρU k := fun k =>
    ((Radius.min_le_left _ _ k).trans (Radius.min_le_left _ _ k)).trans (Radius.min_le_right _ _ k)
  have hρC'' : ∀ k, ρ k ≤ ρC' k := fun k =>
    (Radius.min_le_left _ _ k).trans (Radius.min_le_right _ _ k)
  have hρδ' : ∀ k, ρ k ≤ ρδ k := fun k => Radius.min_le_right _ _ k
  have hU : ConvNorm ρ U ≠ ⊤ := ne_top_of_le_ne_top hρU (ConvNorm_mono hρU' U)
  have hCj' : ∀ j, ConvNorm (fun k => ρ k.succ) (C j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (hCj j) (ConvNorm_mono (fun k => hρC'' k.succ) _)
  have hlift : ∀ j, ConvNorm ρ (liftTail (C j)) ≠ ⊤ := fun j => by
    rw [convNorm_liftTail]; exact hCj' j
  have hterm : ∀ j : Fin d, ConvNorm ρ (liftTail (C j) * X 0 ^ (d - 1 - (j : ℕ))) ≠ ⊤ :=
    fun j => by
      change _ ∈ BanachSeries K ρ
      exact mul_mem (hlift j) (convNorm_X_pow_ne_top ρ 0 _)
  have hsum : ConvNorm ρ (∑ j : Fin d, liftTail (C j) * X 0 ^ (d - 1 - (j : ℕ))) ≠ ⊤ := by
    change _ ∈ BanachSeries K ρ
    exact sum_mem fun j _ => hterm j
  have hP : ConvNorm ρ (weierstrassPoly d C) ≠ ⊤ := by
    change weierstrassPoly d C ∈ BanachSeries K ρ
    unfold weierstrassPoly
    exact add_mem (convNorm_X_pow_ne_top ρ 0 d) hsum
  refine ⟨ρ, evalSeries U, fun j => evalSeries (C j), analyticOnNhd_evalSeries hU, ?_,
    fun j => analyticOnNhd_evalSeries (hCj' j), fun j => ?_, ?_⟩
  · intro x hx
    rw [mem_polydisc_iff] at hx
    refine hδ ?_
    rw [dist_zero_right, pi_norm_lt_iff hδ0]
    intro k
    calc ‖x k‖ < ρ k := hx k
      _ ≤ ρδ k := by exact_mod_cast hρδ' k
      _ = δ := Real.coe_toNNReal δ hδ0.le
  · change evalSeries (C j) 0 = 0
    rw [evalSeries_zero_eq]
    exact (hC j).2
  · intro x hx
    rw [mem_polydisc_iff] at hx
    have hxle : ∀ k, ‖x k‖ ≤ ρ k := fun k => (hx k).le
    have hxF : ∀ k, ‖x k‖ < ρF k := fun k => lt_of_lt_of_le (hx k) (by exact_mod_cast hρF k)
    rw [hfF x hxF, hFU, evalSeries_mul hU hP hxle]
    congr 1
    unfold weierstrassPoly
    rw [evalSeries_add (convNorm_X_pow_ne_top ρ 0 d) hsum hxle, evalSeries_X_pow,
      evalSeries_sum _ (fun j _ => hterm j) hxle]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evalSeries_mul (hlift j) (convNorm_X_pow_ne_top ρ 0 _) hxle, evalSeries_liftTail,
      evalSeries_X_pow]

end Analytic
