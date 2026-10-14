/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.Radius
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The majorant norms `‖f‖_ρ` and the convergent series over `K = ℝ` or `ℂ`

The ring of germs of `K`-analytic functions at `0 ∈ K^m`, `K ∈ {ℝ, ℂ}` (`[RCLike K]`), is
modelled by the ring of convergent power series in `m` variables: a formal series
`f = ∑_ν a_ν x^ν ∈ MvPowerSeries (Fin m) K` is convergent when for some radius vector
`ρ ∈ (0, ∞)^m` its **majorant norm** `‖f‖_ρ = ∑_ν ‖a_ν‖ ρ^ν` (an `ℝ≥0∞`-valued sum over
`Fin m →₀ ℕ`) is finite. This is the classical construction of the local ring of convergent power
series through the Banach algebras of series with finite majorant norm [GR71, Kapitel I]; for
`K = ℝ` it models the local ring `𝒪_a` of germs of analytic functions of [BM88, p. 23].

* `ConvNorm ρ f` is the norm, for a radius vector `ρ : Fin m → ℝ≥0`; it is subadditive,
  homogeneous, submultiplicative (`ConvNorm_mul_le`, the Cauchy-product bound through
  `MvPowerSeries.coeff_mul`), equal to `1` on `1`, and monotone in `ρ`.
* `BanachSeries K ρ` (written `B_ρ` in the docstrings, for `ρ : Radius m`) is the subalgebra of
  series with `‖f‖_ρ < ∞`; its Banach algebra structure is in `Banach.lean`.
* `Conv K m` is the union of the `BanachSeries K ρ` over all `ρ : Radius m`: the ring of
  convergent power series, a subalgebra of `MvPowerSeries (Fin m) K` because two radius vectors
  have a common smaller one and the norm is monotone. The monomials and the coordinates are
  convergent (`convNorm_monomial`, `monomial_mem_conv`, `X_mem_conv`).

Every proof is coefficientwise on the majorant norm. The field `K` is explicit in
`BanachSeries K ρ` and `Conv K m` (no argument carries it) and implicit everywhere else. The real
instances of these declarations, under the same names in namespace `Hironaka.Analytic`, are
restated in `Hironaka/Analytic/ConvSeries/ConvNorm.lean`; the field-free material (radius
vectors, exponents, monomials) is in `Hironaka/Analytic/ConvSeries/Radius.lean`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- The majorant norm `‖f‖_ρ = ∑_ν ‖a_ν‖ ρ^ν` of a formal power series, as an `ℝ≥0∞`-valued sum
over all exponents [GR71, Kapitel I]. -/
noncomputable def ConvNorm (ρ : Fin m → ℝ≥0) (f : MvPowerSeries (Fin m) K) : ℝ≥0∞ :=
  ∑' ν : Fin m →₀ ℕ, ‖coeff ν f‖ₑ * (monomialEval ρ ν : ℝ≥0∞)

theorem ConvNorm_zero (ρ : Fin m → ℝ≥0) : ConvNorm ρ (0 : MvPowerSeries (Fin m) K) = 0 := by
  simp [ConvNorm]

theorem ConvNorm_one (ρ : Fin m → ℝ≥0) : ConvNorm ρ (1 : MvPowerSeries (Fin m) K) = 1 := by
  classical
  unfold ConvNorm
  rw [tsum_eq_single 0]
  · simp
  · intro ν hν
    simp [MvPowerSeries.coeff_one, hν]

theorem ConvNorm_neg (ρ : Fin m → ℝ≥0) (f : MvPowerSeries (Fin m) K) :
    ConvNorm ρ (-f) = ConvNorm ρ f := by
  simp [ConvNorm]

theorem ConvNorm_add_le (ρ : Fin m → ℝ≥0) (f g : MvPowerSeries (Fin m) K) :
    ConvNorm ρ (f + g) ≤ ConvNorm ρ f + ConvNorm ρ g := by
  unfold ConvNorm
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun ν => ?_
  rw [← add_mul, map_add]
  exact mul_le_mul' (enorm_add_le _ _) le_rfl

theorem ConvNorm_smul (ρ : Fin m → ℝ≥0) (c : K) (f : MvPowerSeries (Fin m) K) :
    ConvNorm ρ (c • f) = ‖c‖ₑ * ConvNorm ρ f := by
  unfold ConvNorm
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [MvPowerSeries.coeff_smul, enorm_mul, mul_assoc]

/-- The scalar `c`, as the constant series, has norm `‖c‖`. -/
theorem ConvNorm_algebraMap (ρ : Fin m → ℝ≥0) (c : K) :
    ConvNorm ρ (algebraMap K (MvPowerSeries (Fin m) K) c) = ‖c‖ₑ := by
  rw [Algebra.algebraMap_eq_smul_one, ConvNorm_smul, ConvNorm_one, mul_one]

/-- The norm is monotone in the radius vector. -/
theorem ConvNorm_mono {ρ ρ' : Fin m → ℝ≥0} (h : ∀ k, ρ k ≤ ρ' k) (f : MvPowerSeries (Fin m) K) :
    ConvNorm ρ f ≤ ConvNorm ρ' f :=
  ENNReal.tsum_le_tsum fun ν =>
    mul_le_mul' le_rfl (ENNReal.coe_le_coe.mpr (monomialEval_le_monomialEval h ν))

/-- The Cauchy-product bound `‖f g‖_ρ ≤ ‖f‖_ρ ‖g‖_ρ`: the coefficient of `x^ν` in `f g` is the sum
over the antidiagonal of `ν` (`MvPowerSeries.coeff_mul`), each term is bounded by
`‖a_μ‖ ρ^μ · ‖b_{ν-μ}‖ ρ^{ν-μ}`, and the double sum over all antidiagonals is the product of the
two norms. -/
theorem ConvNorm_mul_le (ρ : Fin m → ℝ≥0) (f g : MvPowerSeries (Fin m) K) :
    ConvNorm ρ (f * g) ≤ ConvNorm ρ f * ConvNorm ρ g := by
  classical
  set F : (Fin m →₀ ℕ) → ℝ≥0∞ := fun μ => ‖coeff μ f‖ₑ * (monomialEval ρ μ : ℝ≥0∞) with hF
  set G : (Fin m →₀ ℕ) → ℝ≥0∞ := fun μ => ‖coeff μ g‖ₑ * (monomialEval ρ μ : ℝ≥0∞) with hG
  -- termwise bound by the antidiagonal sum of products
  have hterm : ∀ ν : Fin m →₀ ℕ, ‖coeff ν (f * g)‖ₑ * (monomialEval ρ ν : ℝ≥0∞)
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν, F p.1 * G p.2 := by
    intro ν
    rw [MvPowerSeries.coeff_mul]
    refine le_trans (mul_le_mul' (enorm_sum_le _ _) le_rfl) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' : p.1 + p.2 = ν := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [← hp', monomialEval_add, ENNReal.coe_mul, enorm_mul, hF, hG]
    dsimp only
    ring_nf
    exact le_rfl
  -- regroup the double sum over pairs by the sum of the exponents
  have hregroup : ∑' ν : Fin m →₀ ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν, F p.1 * G p.2
      = ∑' p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ), F p.1 * G p.2 := by
    have h1 : ∀ ν : Fin m →₀ ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν, F p.1 * G p.2
        = ∑' p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ), if p.1 + p.2 = ν then F p.1 * G p.2 else 0 := by
      intro ν
      rw [tsum_eq_sum (s := Finset.HasAntidiagonal.antidiagonal ν)]
      · exact Finset.sum_congr rfl fun p hp => by
          rw [ite_eq_left (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)]
      · intro p hp
        rw [ite_eq_right fun h => hp (Finset.HasAntidiagonal.mem_antidiagonal.mpr h)]
    simp_rw [h1]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun p => by
      rw [tsum_eq_single (p.1 + p.2) fun ν hν => ite_eq_right (Ne.symm hν)]
      exact ite_eq_left rfl
  calc ∑' ν : Fin m →₀ ℕ, ‖coeff ν (f * g)‖ₑ * (monomialEval ρ ν : ℝ≥0∞)
      ≤ ∑' ν : Fin m →₀ ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν, F p.1 * G p.2 :=
        ENNReal.tsum_le_tsum hterm
    _ = ∑' p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ), F p.1 * G p.2 := hregroup
    _ = (∑' μ, F μ) * ∑' ν, G ν := by
        rw [ENNReal.tsum_prod']
        simp_rw [ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_right]

variable (K)

/-- The series of finite `ρ`-norm form a subalgebra `B_ρ` of the formal series (closed under
sums, products and scalars by the norm inequalities above). -/
def BanachSeries (ρ : Radius m) : Subalgebra K (MvPowerSeries (Fin m) K) where
  carrier := {f | ConvNorm ρ f ≠ ⊤}
  mul_mem' {f g} hf hg :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hf hg) (ConvNorm_mul_le ρ f g)
  one_mem' := by simp [ConvNorm_one]
  add_mem' {f g} hf hg :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (ConvNorm_add_le ρ f g)
  zero_mem' := by simp [ConvNorm_zero]
  algebraMap_mem' c := by simp [ConvNorm_algebraMap]

variable {K}

theorem mem_banachSeries {ρ : Radius m} {f : MvPowerSeries (Fin m) K} :
    f ∈ BanachSeries K ρ ↔ ConvNorm ρ f ≠ ⊤ := Iff.rfl

theorem BanachSeries.mono {ρ ρ' : Radius m} (h : ∀ k, ρ k ≤ ρ' k) :
    BanachSeries K ρ' ≤ BanachSeries K ρ := fun _ hf =>
  ne_top_of_le_ne_top hf (ConvNorm_mono h _)

variable (K)

/-- The ring `Conv K m` of convergent power series: the series with finite `ρ`-norm for some
radius vector with positive entries, the model of the ring of germs of `K`-analytic functions at
`0 ∈ K^m` (for `K = ℝ` the local ring `𝒪_a` of [BM88, p. 23]). It is a subalgebra because two
radius vectors have a common lower bound and the norm is monotone in the radius. -/
def Conv (m : ℕ) : Subalgebra K (MvPowerSeries (Fin m) K) where
  carrier := {f | ∃ ρ : Radius m, f ∈ BanachSeries K ρ}
  mul_mem' {f g} := by
    rintro ⟨ρ, hf⟩ ⟨ρ', hg⟩
    exact ⟨ρ.min ρ', mul_mem (BanachSeries.mono (ρ.min_le_left ρ') hf)
      (BanachSeries.mono (ρ.min_le_right ρ') hg)⟩
  one_mem' := ⟨Radius.one m, one_mem _⟩
  add_mem' {f g} := by
    rintro ⟨ρ, hf⟩ ⟨ρ', hg⟩
    exact ⟨ρ.min ρ', add_mem (BanachSeries.mono (ρ.min_le_left ρ') hf)
      (BanachSeries.mono (ρ.min_le_right ρ') hg)⟩
  zero_mem' := ⟨Radius.one m, zero_mem _⟩
  algebraMap_mem' c := ⟨Radius.one m, algebraMap_mem _ c⟩

variable {K}

theorem mem_conv {f : MvPowerSeries (Fin m) K} :
    f ∈ Conv K m ↔ ∃ ρ : Radius m, ConvNorm ρ f ≠ ⊤ := Iff.rfl

theorem BanachSeries.le_conv (ρ : Radius m) : BanachSeries K ρ ≤ Conv K m := fun _ hf => ⟨ρ, hf⟩

/-! ### Monomials -/

/-- The majorant norm of a monomial `a x^ν` is `‖a‖ ρ^ν`. -/
theorem convNorm_monomial (ρ : Fin m → ℝ≥0) (ν : Fin m →₀ ℕ) (a : K) :
    ConvNorm ρ (monomial ν a) = ‖a‖ₑ * (monomialEval ρ ν : ℝ≥0∞) := by
  classical
  unfold ConvNorm
  rw [tsum_eq_single ν]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro μ hμ
    rw [coeff_monomial, ite_eq_right hμ, enorm_zero, zero_mul]

/-- Monomials are convergent. -/
theorem monomial_mem_conv (ν : Fin m →₀ ℕ) (a : K) : monomial ν a ∈ Conv K m :=
  ⟨Radius.one m, by
    rw [mem_banachSeries, convNorm_monomial]
    exact ENNReal.mul_ne_top (enorm_ne_top) ENNReal.coe_ne_top⟩

/-- The coordinates are convergent. -/
theorem X_mem_conv (k : Fin m) : (X k : MvPowerSeries (Fin m) K) ∈ Conv K m := by
  rw [X_def]
  exact monomial_mem_conv _ _

end Analytic
