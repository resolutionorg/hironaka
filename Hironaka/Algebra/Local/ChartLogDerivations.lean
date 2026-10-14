/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
public import Hironaka.Algebra.Local.TransformLogDeriv
import Hironaka.Algebra.Local.ChartCoords
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The chart logarithmic derivations are logarithmic along the strict transform

In the chart of the blow-up of `P = (x₀, …, x_r)` dividing by `x_r`, for the hypersurface
coordinate `x_h`, `h < r`, the strict transform of `S = (x_h)` is `S₁ = (y_h)`, `y_h = x_h / x_r`;
its ideal in the chart ring, as read off the stalk of the blow-up
(`Hironaka/Resolution/Algebraic/Kol07/Theorem88BlowUp.lean`), is the `x_r`-saturation `⋃ᵢ ((φ x_h) :
x_rⁱ)` of the total transform `(φ x_h) = (x_r y_h)` (`chartSat`). The logarithmic chart derivations
`y_h ∂'_h` and `∂'_i`, `i ≠ h`, of `Hironaka/Algebra/Local/TransformLogDeriv.lean` preserve it: a
derivation `δ` with `δ(g) ∈ (g)^{sat}` preserves `(g)^{sat}` whatever `δ(x_r)` is
(`preservesIdeal_chartSat_of_apply_mem`), and `∂'_i (x_r y_h) ∈ {0, y_h}`,
`y_h ∂'_h (x_r y_h) = x_r y_h` (`chartDerivRing_chartYR`). For `k`-linear coordinates the chart
derivations are `k`-derivations (`chartDerivRingOver`), so the chart logarithmic derivative ideal
`D'(−log S₁)` (`chartDlog`) lies in the logarithmic derivative ideal `D(−log (x_r y_h)^{sat})` for
all `k`-derivations (`Ideal.logDerivative`,
`Hironaka/Scheme/IdealSheaf/Derivative/Logarithmic.lean`): `chartDlog_le_logDerivative`, iterated as
`chartDlogpow_le_logDerivativeIter`. This is the bridge from the chart-level inclusion `⊆` of
[Kol07, (88.1)] (`Hironaka/Algebra/Local/TransformDerivNormalForm.lean`) to the stalks of the
blow-up in the proof of [Kol07, Theorem 88] for one blow-up
(`Hironaka/Resolution/Algebraic/Kol07/Theorem88BlowUp.lean`).
-/

@[expose] public section

namespace IsLocalRing

section ChartYR

variable {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) (r : Fin n)

/-- The chart coordinate `y_r` is `x_r` itself. -/
theorem chartYR_self_eq_algebraMap : chartYR x r r = algebraMap R (chartRing x r) (x r) := by
  apply Subtype.ext
  rw [coe_chartYROf, chartYOf_self]
  rfl

end ChartYR

namespace RegularCoords

variable {k : Type*} [CommRing k] {R : Type*} [CommRing R] [Algebra k R] [IsRegularLocalRing R]
  [Algebra ℚ R] {n : ℕ} (c : RegularCoords R n) (r : Fin n)

/-! ### The chart derivations as `k`-derivations -/

/-- A chart derivation kills the image of an element of `R` killed by all coordinate
derivations: `∂'_j (φ a) = 0` if every `∂_i a = 0` (from the formulas defining `chartDeriv` in
`Hironaka/Algebra/Local/Chart.lean`). -/
theorem chartDerivRing_algebraMap_eq_zero {a : R} (ha : ∀ i, c.pderiv i a = 0) (j : Fin n) :
    c.chartDerivRing r j (algebraMap R (chartRing c.x r) a) = 0 := by
  apply Subtype.ext
  rw [coe_chartDerivRing, Subalgebra.coe_algebraMap, Subalgebra.coe_zero]
  rcases lt_trichotomy j r with hj | hjr | hj
  · rw [c.chartDeriv_of_lt r hj, Derivation.smul_apply, awayPderiv_algebraMap, ha, map_zero,
      smul_zero]
  · rw [hjr, c.chartDeriv_self r, Derivation.add_apply, Derivation.finset_sum_apply,
      awayPderiv_algebraMap, ha, map_zero, zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Derivation.smul_apply, awayPderiv_algebraMap, ha, map_zero, smul_zero]
  · rw [c.chartDeriv_of_gt r hj, awayPderiv_algebraMap, ha, map_zero]

/-- The chart derivations as `k`-derivations, for `k`-linear coordinates (`derivationOver`,
`Hironaka/Algebra/Local/CoordsOver.lean`). -/
noncomputable def chartDerivRingOver (hk : c.IsLinearOver k) (j : Fin n) :
    Derivation k (chartRing c.x r) (chartRing c.x r) :=
  derivationOver (c.chartDerivRing r j) fun a => by
    rw [IsScalarTower.algebraMap_apply k R (chartRing c.x r)]
    exact c.chartDerivRing_algebraMap_eq_zero r (fun i => hk i a) j

@[simp] theorem chartDerivRingOver_apply (hk : c.IsLinearOver k) (j : Fin n)
    (z : chartRing c.x r) : c.chartDerivRingOver r hk j z = c.chartDerivRing r j z := rfl

/-! ### The `x_r`-saturation of a principal ideal -/

/-- `⋃ᵢ ((g) : x_rⁱ)`, the `x_r`-saturation of the principal ideal `(g)` of the chart ring; for
`g = φ x_h`, the chart ideal of the strict transform of `(x_h)`. -/
noncomputable def chartSat (g : chartRing c.x r) : Ideal (chartRing c.x r) :=
  ⨆ i : ℕ, (Ideal.span {g}).colon
    ((Ideal.span {algebraMap R (chartRing c.x r) (c.x r)} ^ i : Ideal (chartRing c.x r)) :
      Set (chartRing c.x r))

theorem mem_chartSat_iff {g z : chartRing c.x r} :
    z ∈ c.chartSat r g ↔
      ∃ i : ℕ, algebraMap R (chartRing c.x r) (c.x r) ^ i * z ∈ Ideal.span {g} := by
  have hmono : Monotone fun i : ℕ => (Ideal.span {g}).colon
      ((Ideal.span {algebraMap R (chartRing c.x r) (c.x r)} ^ i : Ideal (chartRing c.x r)) :
        Set (chartRing c.x r)) :=
    fun i j hij => Submodule.colon_mono le_rfl (Ideal.pow_le_pow_right hij)
  rw [chartSat, Submodule.mem_iSup_of_directed _ hmono.directed_le]
  refine exists_congr fun i => ?_
  rw [Ideal.span_singleton_pow]
  constructor
  · intro hz
    have := Submodule.mem_colon.mp hz _ (Ideal.mem_span_singleton_self _)
    rwa [smul_eq_mul, mul_comm] at this
  · intro hz
    refine Submodule.mem_colon.mpr fun w hw => ?_
    rw [SetLike.mem_coe] at hw
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    rw [smul_eq_mul, mul_left_comm, mul_comm z]
    exact Ideal.mul_mem_left _ _ hz

theorem span_singleton_le_chartSat (g : chartRing c.x r) : Ideal.span {g} ≤ c.chartSat r g :=
  fun _ hz => (c.mem_chartSat_iff r).mpr ⟨0, by rwa [pow_zero, one_mul]⟩

theorem mem_chartSat_of_pow_mul_mem {g z : chartRing c.x r} {i : ℕ}
    (hz : algebraMap R (chartRing c.x r) (c.x r) ^ i * z ∈ c.chartSat r g) :
    z ∈ c.chartSat r g := by
  obtain ⟨i', hi'⟩ := (c.mem_chartSat_iff r).mp hz
  exact (c.mem_chartSat_iff r).mpr ⟨i' + i, by rwa [pow_add, mul_assoc]⟩

/-- A derivation with `δ g ∈ (g)^{sat}` preserves the saturation `(g)^{sat}`, whatever `δ(x_r)` is:
from `x_rⁱ z = a g`, `x_rⁱ δz = δ(a g) − i x_r^{i−1} δ(x_r) z ∈ (g)^{sat}`. -/
theorem preservesIdeal_chartSat_of_apply_mem
    (δ : Derivation k (chartRing c.x r) (chartRing c.x r)) {g : chartRing c.x r}
    (hδ : δ g ∈ c.chartSat r g) : δ.PreservesIdeal (c.chartSat r g) := by
  intro z hz
  obtain ⟨i, hi⟩ := (c.mem_chartSat_iff r).mp hz
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hi
  have h1 : δ (algebraMap R (chartRing c.x r) (c.x r) ^ i * z) ∈ c.chartSat r g := by
    rw [← ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hδ)
      (Ideal.mul_mem_right _ _ (c.span_singleton_le_chartSat r g (Ideal.mem_span_singleton_self g)))
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have h2 : z * δ (algebraMap R (chartRing c.x r) (c.x r) ^ i) ∈ c.chartSat r g :=
    Ideal.mul_mem_right _ _ hz
  exact c.mem_chartSat_of_pow_mul_mem r ((Ideal.add_mem_iff_left _ h2).mp h1)

/-! ### The chart logarithmic derivations preserve the strict transform's ideal -/

variable (hk : c.IsLinearOver k) {h : Fin n}

/-- `y_h ∂'_h` preserves `(x_r y_h)^{sat}`: `y_h ∂'_h (x_r y_h) = x_r y_h`. -/
theorem preservesIdeal_chartSat_smul_chartDerivRingOver (hh : h < r) :
    (chartYR c.x r h • c.chartDerivRingOver r hk h).PreservesIdeal
      (c.chartSat r (algebraMap R (chartRing c.x r) (c.x h))) := by
  refine c.preservesIdeal_chartSat_of_apply_mem r _ ?_
  have hval : (chartYR c.x r h • c.chartDerivRingOver r hk h)
      (algebraMap R (chartRing c.x r) (c.x h)) = algebraMap R (chartRing c.x r) (c.x h) := by
    rw [Derivation.smul_apply, chartDerivRingOver_apply, algebraMap_x_eq_mul_chartYR c.x r hh,
      Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [c.chartDerivRing_chartYR r, ite_eq_left rfl, mul_one,
      ← chartYR_self_eq_algebraMap c.x r, c.chartDerivRing_chartYR r, ite_eq_right hh.ne, mul_zero,
      add_zero]
    exact mul_comm _ _
  rw [hval]
  exact c.span_singleton_le_chartSat r _ (Ideal.mem_span_singleton_self _)

/-- `∂'_i`, `i ≠ h`, preserves `(x_r y_h)^{sat}`: `∂'_i (x_r y_h) = y_h` if `i = r`, `0` otherwise,
and `y_h ∈ (x_r y_h)^{sat}`. -/
theorem preservesIdeal_chartSat_chartDerivRingOver (hh : h < r) {i : Fin n} (hi : i ≠ h) :
    (c.chartDerivRingOver r hk i).PreservesIdeal
      (c.chartSat r (algebraMap R (chartRing c.x r) (c.x h))) := by
  refine c.preservesIdeal_chartSat_of_apply_mem r _ ?_
  have hval : c.chartDerivRingOver r hk i (algebraMap R (chartRing c.x r) (c.x h)) =
      if i = r then chartYR c.x r h else 0 := by
    rw [chartDerivRingOver_apply, algebraMap_x_eq_mul_chartYR c.x r hh, Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [c.chartDerivRing_chartYR r, ite_eq_right hi, mul_zero, zero_add,
      ← chartYR_self_eq_algebraMap c.x r, c.chartDerivRing_chartYR r]
    split_ifs <;> simp
  rw [hval]
  split_ifs
  · exact (c.mem_chartSat_iff r).mpr ⟨1, by
      rw [pow_one, ← algebraMap_x_eq_mul_chartYR c.x r hh]
      exact Ideal.mem_span_singleton_self _⟩
  · exact zero_mem _

include hk in
/-- `D'(−log S₁)(K)` (`chartDlog`) lies in `D(−log (x_r y_h)^{sat})(K)` (`Ideal.logDerivative`):
the chart logarithmic derivations are `k`-derivations preserving the strict transform's chart
ideal. -/
theorem chartDlog_le_logDerivative (hh : h < r) (K : Ideal (chartRing c.x r)) :
    c.chartDlog r h K ≤
      Ideal.logDerivative k (c.chartSat r (algebraMap R (chartRing c.x r) (c.x h))) K := by
  refine (c.chartDlog_le_iff r h).mpr
    ⟨Ideal.le_logDerivative _ _, fun z hz => ?_, fun i hi z hz => ?_⟩
  · exact Ideal.derivation_apply_mem_logDerivative
      (c.preservesIdeal_chartSat_smul_chartDerivRingOver r hk hh) hz
  · exact Ideal.derivation_apply_mem_logDerivative
      (c.preservesIdeal_chartSat_chartDerivRingOver r hk hh hi) hz

include hk in
/-- The iterate: `D'^t(−log S₁)(K) ⊆ D^t(−log (x_r y_h)^{sat})(K)`. -/
theorem chartDlogpow_le_logDerivativeIter (hh : h < r) (t : ℕ) (K : Ideal (chartRing c.x r)) :
    c.chartDlogpow r h t K ≤
      Ideal.logDerivativeIter k (c.chartSat r (algebraMap R (chartRing c.x r) (c.x h))) t K := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [chartDlogpow_succ, Ideal.logDerivativeIter_succ]
    exact (c.chartDlog_le_logDerivative r hk hh _).trans (Ideal.logDerivative_mono ih)

end RegularCoords

end IsLocalRing
