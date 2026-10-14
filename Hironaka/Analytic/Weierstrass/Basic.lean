/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Radius
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Weierstrass division: the distinguished variable, regularity and the splitting operators

The Weierstrass preparation theorem, in the form Bierstone and Milman use it, prepares a germ `f`
with `f(0, …, 0, x_m) ∼ x_m^e` in a distinguished last variable [BM88, proof of Theorem 4.4, p. 24].
Here the distinguished variable is the coordinate `0` of `Fin (m + 1)` and the remaining variables
are the `Fin.succ j`, because Mathlib's isomorphism `MvPowerSeries.finSuccEquiv` between
`MvPowerSeries (Fin (m + 1)) R` and `PowerSeries (MvPowerSeries (Fin m) R)` singles out the first
variable: the printed `x_m` is our `x_0` and the printed `x̃` our `x_1, …, x_m`. This relabelling
of the coordinates is the convention of every module of the Weierstrass theory and of the germ
theory built on it.

* `splitFirst K m` is that isomorphism; `liftTail c` embeds a series in the tail variables and
  `liftFirst e` a series in `x_0` alone into the series in all variables.
* `IsRegularIn g d`: `g(x_0, 0, …, 0) = x_0^d · e(x_0)` with `e(0) ≠ 0`, stated as the hypothesis
  of Mathlib's Weierstrass division: the image of `splitFirst K m g` in the residue field of the
  tail ring `MvPowerSeries (Fin m) K` has `PowerSeries.order` exactly `d`.
* `wQ d F` and `wR d F` are the splitting operators: `F = x_0^d · wQ d F + wR d F` with `wR d F`
  of `x_0`-degree `< d`, coefficientwise (the norm bounds are in `Splitting.lean`). They are the
  operators of the Banach-algebra proof of the division theorem [GR71, Kapitel I].
* `weierstrassPoly d c = x_0^d + ∑_{j < d} c_j x_0^{d - 1 - j}` for coefficients `c_j` in the tail
  variables, the printed `x_m^d + ∑_{j=1}^d c_j(x̃) x_m^{d-j}`.
* `polydisc K ρ` is the open polydisc `{x | ∀ k, ‖x_k‖ < ρ_k}` of a radius vector
  (`mem_polydisc_iff`; it contains a neighbourhood of `0`, `eventually_abs_lt`), and
  `TailVanishes h` says that `h` has no pure `x_0`-monomials, i.e. `h(x_0, 0, …, 0) = 0`.

The coefficient field `K` is `ℝ` or `ℂ` (`[RCLike K]`).
-/

@[expose] public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K]

variable {m : ℕ}

variable (K) in
/-- The split of the distinguished variable `x_0` (Mathlib's `finSuccEquiv`). -/
noncomputable abbrev splitFirst (m : ℕ) :
    MvPowerSeries (Fin (m + 1)) K ≃ₐ[K] PowerSeries (MvPowerSeries (Fin m) K) :=
  MvPowerSeries.finSuccEquiv K m

/-- A series in the tail variables `x_1, …, x_m`, as a series in all variables. -/
noncomputable def liftTail (c : MvPowerSeries (Fin m) K) : MvPowerSeries (Fin (m + 1)) K :=
  MvPowerSeries.rename Fin.succ c

/-- `g` is `x_0`-regular of order `d`: `g(x_0, 0, …, 0) = x_0^d e(x_0)` with `e(0) ≠ 0`, i.e. the
image of `splitFirst K m g` in the residue field of the tail ring `MvPowerSeries (Fin m) K` has
order exactly `d` (Mathlib's Weierstrass hypothesis `g.map (IsLocalRing.residue A) ≠ 0` with the
order made explicit). This is the printed condition `f_a(0, …, 0, x_m) ∼ x_m^e` of
[BM88, proof of Theorem 4.4, p. 24]. -/
def IsRegularIn (g : MvPowerSeries (Fin (m + 1)) K) (d : ℕ) : Prop :=
  ((splitFirst K m g).map (IsLocalRing.residue (MvPowerSeries (Fin m) K))).order = d

/-- The quotient part of the splitting `F = x_0^d · wQ d F + wR d F`: the terms of `x_0`-degree
`≥ d`, divided by `x_0^d`. -/
noncomputable def wQ (d : ℕ) (F : MvPowerSeries (Fin (m + 1)) K) : MvPowerSeries (Fin (m + 1)) K :=
  fun ν => coeff (ν + Finsupp.single 0 d) F

/-- The remainder part of the splitting: the terms of `x_0`-degree `< d`. -/
noncomputable def wR (d : ℕ) (F : MvPowerSeries (Fin (m + 1)) K) : MvPowerSeries (Fin (m + 1)) K :=
  fun ν => if ν 0 < d then coeff ν F else 0

theorem coeff_wQ (d : ℕ) (F : MvPowerSeries (Fin (m + 1)) K) (ν : Fin (m + 1) →₀ ℕ) :
    coeff ν (wQ d F) = coeff (ν + Finsupp.single 0 d) F := rfl

theorem coeff_wR (d : ℕ) (F : MvPowerSeries (Fin (m + 1)) K) (ν : Fin (m + 1) →₀ ℕ) :
    coeff ν (wR d F) = if ν 0 < d then coeff ν F else 0 := rfl

/-- The splitting identity `F = x_0^d · wQ d F + wR d F`. -/
theorem X_pow_mul_wQ_add_wR (d : ℕ) (F : MvPowerSeries (Fin (m + 1)) K) :
    X 0 ^ d * wQ d F + wR d F = F := by
  classical
  ext ν
  rw [map_add, coeff_wR, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, coeff_wQ]
  by_cases h : d ≤ ν 0
  · have h1 : Finsupp.single (0 : Fin (m + 1)) d ≤ ν := by
      intro i
      by_cases hi : i = 0
      · subst hi; simpa using h
      · simp [Ne.symm hi]
    rw [ite_eq_left h1, ite_eq_right (not_lt.mpr h), add_zero, one_mul, tsub_add_cancel_of_le h1]
  · have h1 : ¬ Finsupp.single (0 : Fin (m + 1)) d ≤ ν := fun hle => h (by simpa using hle 0)
    rw [ite_eq_right h1, ite_eq_left (not_le.mp h), zero_add]

/-- `wR d F` has `x_0`-degree `< d`: its coefficients vanish where `ν 0 ≥ d`. -/
theorem coeff_wR_of_le (d : ℕ) (F : MvPowerSeries (Fin (m + 1)) K) {ν : Fin (m + 1) →₀ ℕ}
    (h : d ≤ ν 0) : coeff ν (wR d F) = 0 := by
  rw [coeff_wR, ite_eq_right (not_lt.mpr h)]

/-- The Weierstrass polynomial `x_0^d + ∑_{j < d} c_j x_0^{d - 1 - j}` with coefficients in the
tail variables: the printed `x_m^d + ∑_{j=1}^d c_j(x̃) x_m^{d-j}` of [BM88, Theorem 4.4, proof,
p. 24]. -/
noncomputable def weierstrassPoly (d : ℕ) (c : Fin d → MvPowerSeries (Fin m) K) :
    MvPowerSeries (Fin (m + 1)) K :=
  X 0 ^ d + ∑ j : Fin d, liftTail (c j) * X 0 ^ (d - 1 - (j : ℕ))

/-- A series in the single variable `x_0`, as a series in all variables. -/
noncomputable def liftFirst (e : MvPowerSeries (Fin 1) K) : MvPowerSeries (Fin (m + 1)) K :=
  MvPowerSeries.rename (fun _ => 0) e

variable (K) in
/-- The open polydisc `{x | ∀ k, ‖x_k‖ < ρ_k}` of a radius vector. -/
def polydisc (ρ : Radius m) : Set (Fin m → K) := {x | ∀ k, ‖x k‖ < (ρ k : ℝ)}

/-- A series `h` in all variables with `h(x_0, 0, …, 0) = 0`: no pure `x_0`-monomials. -/
def TailVanishes (h : MvPowerSeries (Fin (m + 1)) K) : Prop :=
  ∀ k : ℕ, coeff (Finsupp.single 0 k) h = 0

open scoped Topology in
/-- Every radius vector bounds the coordinates of the points near `0`. -/
theorem eventually_abs_lt (ρ : Radius m) :
    ∀ᶠ y : Fin m → K in 𝓝 0, ∀ k, ‖y k‖ < (ρ k : ℝ) := by
  obtain ⟨r, hr0, hr⟩ := ρ.exists_le
  filter_upwards [Metric.ball_mem_nhds (0 : Fin m → K) (show (0 : ℝ) < r by exact_mod_cast hr0)]
    with y hy k
  rw [mem_ball_zero_iff] at hy
  calc ‖y k‖ ≤ ‖y‖ := norm_le_pi_norm y k
    _ < r := hy
    _ ≤ ρ k := by exact_mod_cast hr k

/-- Membership in the open polydisc, unfolded. -/
@[simp]
theorem mem_polydisc_iff {ρ : Radius m} {x : Fin m → K} :
    x ∈ polydisc K ρ ↔ ∀ k, ‖x k‖ < (ρ k : ℝ) := by
  exact Iff.rfl

end Analytic
