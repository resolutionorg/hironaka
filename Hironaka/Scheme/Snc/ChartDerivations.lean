/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.ChartRing
import Hironaka.Algebra.Local.Chart
import Hironaka.Scheme.Snc.EtaleParameters
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Derivations of the chart ring dual to the chart functions

On the chart ring `R' = R[x_i/x_r : i < r] ⊆ R[1/x_r]` of the blow-up of `R` along `(x_0, …, x_r)`
[Kol07, Definition 60], the chart functions are `y_i = x_i/x_r` (`i < r`), `y_r = x_r`, and
`y_m = x_m` (`m > r`). Given derivations `D_i` of `R` over `k` dual to the regular system of
parameters `x` (`D_i x_j = δ_{ij}`, supplied at a stalk by `Hironaka.Scheme.Snc.StalkDerivations`),
the chart ring carries derivations dual to the chart functions (`chartRingDer`,
`chartRingDer_chartYR`):

* `D_m` for `m > r` extends to `R[1/x_r]` (the quotient rule) and kills every `y_i = x_i/x_r`,
  `i < r`, since it kills `x_i` and `x_r`;
* `x_r · D_i` for `i < r` sends `y_j` to `δ_{ij}` — from `y_j x_r = x_j` and the Leibniz rule,
  `x_r D_i(y_j) = D_i(x_j) − y_j D_i(x_r) = δ_{ij}` — and `x_m` (`m ≥ r`) to `0`;
* `E = D_r + ∑_{l < r} y_l D_l` sends `y_j` to `0` (`x_r E(y_j) = −y_j + y_j = 0`), `x_r` to `1` and
  `x_m` (`m > r`) to `0`.

Each of these preserves the subalgebra `R'` (checked on the generators `y_i` and the constants, then
by the Leibniz rule along `Algebra.adjoin_induction`), so restricts to `R'`
(`Derivation.restrictSubalgebra`), and localizes to `R'_𝔮` at any prime `𝔮`. Consequently the chart
functions lying in the maximal ideal of a regular localization `R'_𝔮` have linearly independent
classes in the cotangent space and extend to a regular system of parameters
(`exists_span_eq_maximalIdeal_extend_chartYR`; the argument of
`Hironaka.Scheme.Snc.EtaleParameters`). This is the coordinate content of [Hau14, Proposition 5.4
(6)] and [Hau03, Appendix C (7)] at an arbitrary point of the chart.
-/

@[expose] public section

open IsLocalRing Ideal

namespace AlgebraicGeometry

section Restrict

variable {k R L : Type*} [CommRing k] [CommRing R] [CommRing L] [Algebra k R] [Algebra R L]
  [Algebra k L] [IsScalarTower k R L]

/-- A derivation of `L` over `k` preserving an `R`-subalgebra `S` restricts to a derivation of
`S`. -/
noncomputable def _root_.Derivation.restrictSubalgebra (D : Derivation k L L) (S : Subalgebra R L)
    (hS : ∀ a ∈ S, D a ∈ S) : Derivation k S S where
  toFun a := ⟨D a, hS a a.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)
  map_one_eq_zero' := Subtype.ext (by simp)
  leibniz' a b := Subtype.ext (by simp [Derivation.leibniz])

theorem _root_.Derivation.coe_restrictSubalgebra_apply (D : Derivation k L L) (S : Subalgebra R L)
    (hS : ∀ a ∈ S, D a ∈ S) (a : S) : (D.restrictSubalgebra S hS a : L) = D a := rfl

end Restrict

section Chart

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ} (x : Fin n → R) (r : Fin n)
  (D : Fin n → Derivation k R R)

/-- The extension of `D_i` to `R[1/x_r]` (the quotient rule). -/
noncomputable abbrev awayDer (i : Fin n) :
    Derivation k (Localization.Away (x r)) (Localization.Away (x r)) :=
  (D i).localization (Submonoid.powers (x r))

theorem awayDer_algebraMap (i : Fin n) (a : R) :
    awayDer x r D i (algebraMap R (Localization.Away (x r)) a) =
      algebraMap R (Localization.Away (x r)) (D i a) :=
  Derivation.localization_algebraMap _ _ a

/-- `y_j · x_r = x_j` in `R[1/x_r]` for `j < r`. -/
theorem chartY_mul_algebraMap {j : Fin n} (hj : j < r) :
    chartY x r j * algebraMap R (Localization.Away (x r)) (x r) =
      algebraMap R (Localization.Away (x r)) (x j) := by
  change chartYOf x r (x r) j * _ = _
  rw [chartYOf_of_lt x r (x r) hj, Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec _ (x j) ⟨x r, Submonoid.mem_powers (x r)⟩

theorem isUnit_algebraMap_self : IsUnit (algebraMap R (Localization.Away (x r)) (x r)) :=
  IsLocalization.map_units (Localization.Away (x r)) ⟨x r, Submonoid.mem_powers (x r)⟩

/-- The Leibniz relation for the chart function `y_j = x_j / x_r`:
`x_r · D(y_j) = D(x_j) − y_j · D(x_r)`. -/
theorem awayDer_chartY_mul (i : Fin n) {j : Fin n} (hj : j < r) :
    awayDer x r D i (chartY x r j) * algebraMap R (Localization.Away (x r)) (x r) =
      algebraMap R (Localization.Away (x r)) (D i (x j)) -
        chartY x r j * algebraMap R (Localization.Away (x r)) (D i (x r)) := by
  have h := congrArg (awayDer x r D i) (chartY_mul_algebraMap x r hj)
  rw [Derivation.leibniz, awayDer_algebraMap, awayDer_algebraMap, smul_eq_mul, smul_eq_mul] at h
  rw [mul_comm]
  exact eq_sub_of_add_eq' h

variable (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
include hD

/-- The derivations of `R[1/x_r]` dual to the chart functions: `x_r · D_i` for the fibre
coordinates `i < r`, `D_r + ∑_{l < r} y_l D_l` for `x_r`, and `D_m` for `m > r`. -/
noncomputable def chartDer (i : Fin n) :
    Derivation k (Localization.Away (x r)) (Localization.Away (x r)) :=
  if i < r then algebraMap R (Localization.Away (x r)) (x r) • awayDer x r D i
  else if i = r then awayDer x r D r +
    ∑ l ∈ Finset.univ.filter (· < r), chartY x r l • awayDer x r D l
  else awayDer x r D i

omit hD in
theorem chartDer_of_lt {i : Fin n} (hi : i < r) :
    chartDer x r D i = algebraMap R (Localization.Away (x r)) (x r) • awayDer x r D i :=
  ite_eq_left hi

omit hD in
theorem chartDer_self :
    chartDer x r D r = awayDer x r D r +
      ∑ l ∈ Finset.univ.filter (· < r), chartY x r l • awayDer x r D l := by
  rw [chartDer, ite_eq_right (lt_irrefl r), ite_eq_left rfl]

omit hD in
theorem chartDer_of_gt {i : Fin n} (hi : ¬ i < r) (hir : i ≠ r) :
    chartDer x r D i = awayDer x r D i := by
  rw [chartDer, ite_eq_right hi, ite_eq_right hir]

/-- The chart derivations are dual to the chart functions: `chartDer i (y_j) = δ_{ij}`. -/
theorem chartDer_chartY (i j : Fin n) :
    chartDer x r D i (chartY x r j) = if i = j then 1 else 0 := by
  classical
  have hu := isUnit_algebraMap_self x r
  by_cases hj : j < r
  · -- a fibre coordinate `y_j = x_j / x_r`
    have hL := awayDer_chartY_mul x r D i hj
    by_cases hi : i < r
    · rw [chartDer_of_lt x r D hi, Derivation.smul_apply, smul_eq_mul, mul_comm, hL, hD, hD,
        ite_eq_right (ne_of_lt hi)]
      simp only [map_zero, mul_zero, sub_zero]
      split_ifs <;> simp
    · by_cases hir : i = r
      · subst hir
        rw [chartDer_self, Derivation.add_apply, Derivation.finset_sum_apply,
          ite_eq_right (ne_of_gt hj)]
        refine hu.mul_left_cancel ?_
        rw [mul_zero, mul_add, Finset.mul_sum, mul_comm, hL, hD, hD, ite_eq_right (ne_of_gt hj),
          ite_eq_left rfl]
        have hsum : ∀ l ∈ Finset.univ.filter (· < i),
            algebraMap R (Localization.Away (x i)) (x i) *
              (chartY x i l • awayDer x i D l) (chartY x i j) =
              if l = j then chartY x i j else 0 := by
          intro l hl
          rw [Finset.mem_filter] at hl
          rw [Derivation.smul_apply, smul_eq_mul, mul_left_comm,
            mul_comm (algebraMap R (Localization.Away (x i)) (x i))
              (awayDer x i D l (chartY x i j)),
            awayDer_chartY_mul x i D l hj, hD, hD, ite_eq_right (ne_of_lt hl.2)]
          simp only [map_zero, mul_zero, sub_zero]
          split_ifs with h
          · subst h; simp
          · simp
        rw [Finset.sum_congr rfl hsum, Finset.sum_ite_eq' _ j, ite_eq_left (by simpa using hj)]
        simp
      · rw [chartDer_of_gt x r D hi hir, ite_eq_right (fun h : i = j => hi (h ▸ hj))]
        refine hu.mul_left_cancel ?_
        rw [mul_zero, mul_comm, hL, hD, hD, ite_eq_right hir,
          ite_eq_right (fun h : i = j => hi (h ▸ hj))]
        simp
  · -- `y_j = x_j`, `j ≥ r`
    have hy : chartY x r j = algebraMap R (Localization.Away (x r)) (x j) :=
      chartYOf_of_not_lt x r (x r) hj
    by_cases hi : i < r
    · rw [chartDer_of_lt x r D hi, Derivation.smul_apply, hy, awayDer_algebraMap, hD,
        ite_eq_right (fun h : i = j => hj (h ▸ hi)), ite_eq_right (fun h : i = j => hj (h ▸ hi))]
      simp
    · by_cases hir : i = r
      · subst hir
        rw [chartDer_self, Derivation.add_apply, Derivation.finset_sum_apply, hy,
          awayDer_algebraMap, hD]
        have hsum : ∀ l ∈ Finset.univ.filter (· < i),
            (chartY x i l • awayDer x i D l)
              (algebraMap R (Localization.Away (x i)) (x j)) = 0 := by
          intro l hl
          rw [Finset.mem_filter] at hl
          rw [Derivation.smul_apply, awayDer_algebraMap, hD,
            ite_eq_right (fun h : l = j => hj (h ▸ hl.2))]
          simp
        rw [Finset.sum_congr rfl hsum, Finset.sum_const_zero, add_zero]
        split_ifs <;> simp
      · rw [chartDer_of_gt x r D hi hir, hy, awayDer_algebraMap, hD]
        split_ifs <;> simp

/-- The chart derivations preserve the chart ring `R' = R[y_i : i < r]`. -/
theorem chartDer_mem (i : Fin n) : ∀ a ∈ chartRing x r, chartDer x r D i a ∈ chartRing x r := by
  classical
  intro a ha
  have hconst : ∀ c : R, chartDer x r D i (algebraMap R (Localization.Away (x r)) c) ∈
      chartRing x r := by
    intro c
    by_cases hi : i < r
    · rw [chartDer_of_lt x r D hi, Derivation.smul_apply, awayDer_algebraMap, smul_eq_mul,
        ← map_mul]
      exact Subalgebra.algebraMap_mem _ _
    · by_cases hir : i = r
      · subst hir
        rw [chartDer_self, Derivation.add_apply, Derivation.finset_sum_apply, awayDer_algebraMap]
        refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ ?_)
        intro l _
        rw [Derivation.smul_apply, awayDer_algebraMap, smul_eq_mul]
        exact Subalgebra.mul_mem _ (chartY_mem x i l) (Subalgebra.algebraMap_mem _ _)
      · rw [chartDer_of_gt x r D hi hir, awayDer_algebraMap]
        exact Subalgebra.algebraMap_mem _ _
  refine Algebra.adjoin_induction (p := fun a _ => chartDer x r D i a ∈ chartRing x r) ?_ hconst
    ?_ ?_ ha
  · rintro _ ⟨j, hj, rfl⟩
    have : chartDer x r D i (chartY x r j) ∈ chartRing x r := by
      rw [chartDer_chartY x r D hD]
      split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    rwa [show chartY x r j = Localization.mk (x j) ⟨x r, Submonoid.mem_powers (x r)⟩ from
      chartYOf_of_lt x r (x r) hj] at this
  · intro a b _ _ ha hb
    rw [map_add]
    exact Subalgebra.add_mem _ ha hb
  · intro a b hab hbb ha hb
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hab hb) (Subalgebra.mul_mem _ hbb ha)

/-- The derivations of the chart ring dual to the chart functions `y_i ∈ R'`. -/
noncomputable def chartRingDer (i : Fin n) : Derivation k (chartRing x r) (chartRing x r) :=
  (chartDer x r D i).restrictSubalgebra (chartRing x r) (chartDer_mem x r D hD i)

theorem chartRingDer_chartYR (i j : Fin n) :
    chartRingDer x r D hD i (chartYR x r j) = if i = j then 1 else 0 := by
  apply Subtype.ext
  change chartDer x r D i (chartY x r j) = _
  rw [chartDer_chartY x r D hD]
  split_ifs <;> rfl

/-- The coordinate content of [Hau14, Proposition 5.4 (6)] on the chart ring: at a prime `𝔮` of the
chart ring with `R'_𝔮` regular, the chart functions lying in the maximal ideal of `R'_𝔮` extend to a
regular system of parameters. -/
theorem exists_span_eq_maximalIdeal_extend_chartYR (𝔮 : Ideal (chartRing x r)) [𝔮.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime 𝔮)] :
    ∃ (m : ℕ) (z' : Fin m → Localization.AtPrime 𝔮),
      (span (Set.range z') = maximalIdeal (Localization.AtPrime 𝔮) ∧
        (m : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime 𝔮)) ∧
      ∃ σ : {i : Fin n // algebraMap (chartRing x r) (Localization.AtPrime 𝔮) (chartYR x r i) ∈
          maximalIdeal (Localization.AtPrime 𝔮)} → Fin m,
        Function.Injective σ ∧
          ∀ i, z' (σ i) =
            algebraMap (chartRing x r) (Localization.AtPrime 𝔮) (chartYR x r i.1) := by
  classical
  set w : {i : Fin n // algebraMap (chartRing x r) (Localization.AtPrime 𝔮) (chartYR x r i) ∈
      maximalIdeal (Localization.AtPrime 𝔮)} → Localization.AtPrime 𝔮 :=
    fun i => algebraMap (chartRing x r) (Localization.AtPrime 𝔮) (chartYR x r i.1) with hw
  have hli := linearIndependent_toCotangent_of_derivations (k := k) w (fun i => i.2)
    (fun i => (chartRingDer x r D hD i.1).localization 𝔮.primeCompl) (fun i j => by
      change (chartRingDer x r D hD i.1).localization 𝔮.primeCompl
        (algebraMap (chartRing x r) (Localization 𝔮.primeCompl) (chartYR x r j.1)) = _
      rw [Derivation.localization_algebraMap, chartRingDer_chartYR]
      by_cases h : i = j
      · subst h; simp
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (Subtype.ext h'))]
        simp)
  exact exists_span_eq_maximalIdeal_of_linearIndependent w (fun i => i.2) hli

end Chart

end AlgebraicGeometry
