/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.ChartRing
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem

/-!
# The chart ring: injectivity, the transformed derivations, the presentation, the origin

`R` is a regular local ring, `x : Fin n → R` a regular system of parameters, `r : Fin n`, and
`R' = R[xᵢ/x_r : i < r] ⊆ R[1/x_r]` the chart ring of `Hironaka/Algebra/Local/ChartRing.lean`: the
ring of Kollár's chart (60.2) of the blow-up of `(x₁ = ⋯ = x_r = 0)` [Kol07, Definition 60].  This
file proves its basic properties: the injectivity of `R → R'`, the extension of derivations to
`R[1/a]`, the identities `∂'ⱼ yₖ = δⱼₖ` for the transformed derivations and the stability of
`R'` under them, the surjectivity of the presentation `R[Y_i : i < r] → R'`, and the origin `𝔪'`
of the chart together with the other rational points `𝔪'_a` of the exceptional fibre (maximal
ideals lying over `𝔪` with the same residue field).

## The algebra map is injective

`R` is a domain (`isDomain_of_isRegularLocalRing`) and `x_r ≠ 0` (it is not even in `𝔪²`), so
`R → R[1/x_r]` is injective (`IsLocalization.injective`), and `R → R'` is its restriction.

## Extension of derivations

`D.extendAway a` is `Derivation.localization` at `Submonoid.powers a`; it restricts to `D`, it
is the unique such derivation, and on `f/aᵐ` it is given by the quotient rule
`(a · D f − m · f · D a)/aᵐ⁺¹`: the general formula `(s · D f − f · D s)/s²` with `s = aᵐ` and
`D(aᵐ) = m aᵐ⁻¹ D a`, cleared of the common factor `aᵐ⁻¹`.

## The transformed derivations

Write `u = 1/x_r ∈ R[1/x_r]`, so `x_r u = 1`, `yₖ = xₖ u` for `k < r` and `yₖ = xₖ` for `k ≥ r`.
Each extended coordinate derivation `∂ⱼ` satisfies `∂ⱼ u = −u² ∂ⱼ(x_r) = −δⱼᵣ u²`
(`Derivation.leibniz_of_mul_eq_one`), hence, by Leibniz, `∂ⱼ yₖ = δⱼₖ u − δⱼᵣ xₖ u²` for `k < r`
and `∂ⱼ yₖ = δⱼₖ` for `k ≥ r`.  The transformed derivations `∂'ⱼ = x_r ∂ⱼ` (`j < r`),
`∂'_r = ∂_r + ∑_{i<r} yᵢ ∂ᵢ`, `∂'ⱼ = ∂ⱼ` (`j > r`) then give `∂'ⱼ yₖ = δⱼₖ` by the identity
`x_r u = 1`: for `j < r` the factor `x_r` cancels the `u`; for `j = r` and `k < r` the term
`−xₖ u²` of `∂_r yₖ` is cancelled by the single surviving term `yₖ ∂ₖ yₖ = xₖ u · u` of the sum
(the table of derivatives in the proof of [Wlo05, Lemma 2.6.3]; [BM08, Lemma 3.1]).  Each `∂'ⱼ`
maps `R'` into `R'`
because it maps the generators `yₖ` (`k < r`) and the image of `R` into `R'` (`∂'ⱼ(a) = x_r ∂ⱼ a`,
`∂_r a + ∑ yᵢ ∂ᵢ a` or `∂ⱼ a`) and `R'` is closed under sums and Leibniz products
(`Algebra.adjoin_induction`).

## The presentation is surjective

`R[Y_i : i < r] → R'` has range `Algebra.adjoin R {yᵢ : i < r}` (`MvPolynomial.aeval_range`),
which is all of `R'` by definition of the chart ring.  The kernel (the Koszul relations) is
computed in `Hironaka/Algebra/Local/ChartPresentation.lean`.

## The origin and the other points of the fibre

`𝔪' = ⟨y₁, …, yₙ⟩ R'` is a maximal ideal lying over `𝔪` with residue field `K`: Kollár's "`p'`,
the origin of the chart" in the proof of [Kol07, Lemma 61].  The shifted coordinates
`x'ᵢ = xᵢ − ãᵢ x_r` define the same chart ring with the point `𝔪'_a` as origin: Kollár's linear
change of the `(x₁, …, x_r)`-coordinates that "moves the origin of the chart" in the same
proof.  The transformed derivations, packaged as derivations of `R'` (`chartDerivRing`), are the
coordinate derivations of the chart used in `Hironaka/Algebra/Local/ChartCoords.lean` and
`Hironaka/Algebra/Local/TransformDeriv.lean`.
-/

@[expose] public section

namespace Derivation

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- A finite sum of derivations, applied. -/
theorem finset_sum_apply {ι M : Type*} [AddCommGroup M] [Module k M] [Module A M]
    (s : Finset ι) (D : ι → Derivation k A M) (z : A) :
    (∑ i ∈ s, D i) z = ∑ i ∈ s, D i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

/-- `D.extendAway a` restricts to `D`. -/
theorem extendAway_algebraMap (D : Derivation k A A) (a f : A) :
    D.extendAway a (algebraMap A (Localization.Away a) f) =
      algebraMap A (Localization.Away a) (D f) :=
  D.localization_algebraMap _ f

/-- Uniqueness of the extension. -/
theorem eq_extendAway_of_algebraMap (D : Derivation k A A) (a : A)
    (D' : Derivation k (Localization.Away a) (Localization.Away a))
    (h : ∀ f, D' (algebraMap A (Localization.Away a) f) =
      algebraMap A (Localization.Away a) (D f)) :
    D' = D.extendAway a :=
  D.eq_localization_of_algebraMap _ D' h

/-- The quotient rule `D(f/aᵐ) = (a · D f − m · f · D a)/aᵐ⁺¹`. -/
theorem extendAway_mk (D : Derivation k A A) (a f : A) (m : ℕ) :
    D.extendAway a (Localization.mk f ⟨a ^ m, pow_mem (Submonoid.mem_powers a) m⟩) =
      Localization.mk (a * D f - (m : A) * f * D a)
        ⟨a ^ (m + 1), pow_mem (Submonoid.mem_powers a) (m + 1)⟩ := by
  rw [extendAway, Derivation.localization_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, Submonoid.coe_one, one_mul]
  cases m with
  | zero => simp
  | succ m =>
    rw [Derivation.leibniz_pow, Nat.succ_sub_one, nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring

end Derivation

namespace IsLocalRing

open IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

section Injective

variable [IsRegularLocalRing R] (x : Fin n → R) (r : Fin n)

/-- A member of a regular system of parameters is nonzero (it is not even in `𝔪²`). -/
theorem x_ne_zero_of_span_eq (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (i : Fin n) : x i ≠ 0 :=
  fun h => notMem_sq_of_span_eq x hx hn i (h ▸ zero_mem _)

/-- `R → R[1/x_r]` is injective. -/
theorem algebraMap_away_injective (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) :
    Function.Injective (algebraMap R (Localization.Away (x r))) :=
  IsLocalization.injective (Localization.Away (x r))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (x_ne_zero_of_span_eq x hx hn r))

/-- The algebra map `R → R'` into the chart ring is injective. -/
theorem algebraMap_chartRing_injective (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) :
    Function.Injective (algebraMap R (chartRing x r)) := by
  intro a b hab
  apply algebraMap_away_injective x r hx hn
  have := congrArg (fun z : chartRing x r => (z : Localization.Away (x r))) hab
  simpa using this

end Injective

section Presentation

variable (x : Fin n → R) (r : Fin n)

/-- The presentation `R[Y_i : i < r] → R'` is surjective. -/
theorem chartPresentation_surjective : Function.Surjective (chartPresentation x r) := by
  rw [← AlgHom.range_eq_top, chartPresentation, MvPolynomial.aeval_range, eq_top_iff]
  rintro ⟨z, hz⟩ -
  refine Algebra.adjoin_induction
    (p := fun z hz => (⟨z, hz⟩ : chartRing x r) ∈
      Algebra.adjoin R (Set.range fun i : Fin r => chartYR x r (Fin.castLE r.2.le i)))
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨i, hi, rfl⟩
    refine Algebra.subset_adjoin ⟨⟨i, hi⟩, Subtype.ext ?_⟩
    simp [chartYOf_of_lt _ _ _ hi]
  · intro a
    exact Subalgebra.algebraMap_mem _ a
  · intro z w _ _ hz' hw'
    exact Subalgebra.add_mem _ hz' hw'
  · intro z w _ _ hz' hw'
    exact Subalgebra.mul_mem _ hz' hw'

end Presentation

section Family

variable (x : Fin n → R) (r : Fin n)

/-- `u = 1/x_r` in `R[1/x_r]`. -/
noncomputable abbrev invX : Localization.Away (x r) :=
  Localization.mk 1 ⟨x r, Submonoid.mem_powers _⟩

theorem algebraMap_mul_invX : algebraMap R (Localization.Away (x r)) (x r) * invX x r = 1 := by
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, one_mul]
  exact Localization.mk_self ⟨x r, Submonoid.mem_powers _⟩

theorem mk_eq_algebraMap_mul_invX (b : R) :
    Localization.mk b ⟨x r, Submonoid.mem_powers _⟩ =
      algebraMap R (Localization.Away (x r)) b * invX x r := by
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, one_mul]

theorem chartY_eq_mk_of_lt {k : Fin n} (hk : k < r) :
    chartY x r k = Localization.mk (x k) ⟨x r, Submonoid.mem_powers _⟩ :=
  chartYOf_of_lt _ _ _ hk

theorem chartY_eq_algebraMap_of_not_lt {k : Fin n} (hk : ¬ k < r) :
    chartY x r k = algebraMap R (Localization.Away (x r)) (x k) :=
  chartYOf_of_not_lt _ _ _ hk

theorem chartY_of_lt {k : Fin n} (hk : k < r) :
    chartY x r k = algebraMap R (Localization.Away (x r)) (x k) * invX x r := by
  rw [chartY_eq_mk_of_lt x r hk, mk_eq_algebraMap_mul_invX]

end Family

namespace RegularCoords

variable [IsRegularLocalRing R] [Algebra ℚ R] (c : RegularCoords R n) (r : Fin n)

theorem awayPderiv_algebraMap (j : Fin n) (a : R) :
    c.awayPderiv r j (algebraMap R (Localization.Away (c.x r)) a) =
      algebraMap R (Localization.Away (c.x r)) (c.pderiv j a) :=
  Derivation.localization_algebraMap _ _ a

theorem awayPderiv_algebraMap_x (j i : Fin n) :
    c.awayPderiv r j (algebraMap R (Localization.Away (c.x r)) (c.x i)) =
      if j = i then 1 else 0 := by
  rw [awayPderiv_algebraMap, c.pderiv_x]
  split_ifs <;> simp

theorem awayPderiv_invX (j : Fin n) :
    c.awayPderiv r j (invX c.x r) = -(invX c.x r ^ 2 * if j = r then 1 else 0) := by
  have hu : invX c.x r * algebraMap R (Localization.Away (c.x r)) (c.x r) = 1 := by
    rw [mul_comm]; exact algebraMap_mul_invX c.x r
  rw [(c.awayPderiv r j).leibniz_of_mul_eq_one hu, awayPderiv_algebraMap_x, smul_eq_mul]
  ring

/-- The table of derivatives of the chart coordinates (the proof of [Wlo05, Lemma 2.6.3]):
`∂ⱼ yₖ = δⱼₖ u − δⱼᵣ xₖ u²` for `k < r`. -/
theorem awayPderiv_chartY_of_lt (j : Fin n) {k : Fin n} (hk : k < r) :
    c.awayPderiv r j (chartY c.x r k) =
      (if j = k then 1 else 0) * invX c.x r -
        algebraMap R (Localization.Away (c.x r)) (c.x k) * invX c.x r ^ 2 *
          (if j = r then 1 else 0) := by
  rw [chartY_of_lt c.x r hk, Derivation.leibniz, awayPderiv_algebraMap_x, awayPderiv_invX,
    smul_eq_mul, smul_eq_mul]
  ring

theorem awayPderiv_chartY_of_not_lt (j : Fin n) {k : Fin n} (hk : ¬ k < r) :
    c.awayPderiv r j (chartY c.x r k) = if j = k then 1 else 0 := by
  rw [chartY_eq_algebraMap_of_not_lt c.x r hk, awayPderiv_algebraMap_x]

/-- `∂'ⱼ yₖ = δⱼₖ`: the transformed derivations are dual to the chart coordinates (the proof of
[Wlo05, Lemma 2.6.3]; [BM08, Lemma 3.1]). -/
theorem chartDeriv_chartY (j k : Fin n) :
    c.chartDeriv r j (chartY c.x r k) = if j = k then 1 else 0 := by
  classical
  have hu := algebraMap_mul_invX c.x r
  rcases lt_trichotomy j r with hj | hjr | hj
  · rw [c.chartDeriv_of_lt r hj, Derivation.smul_apply, smul_eq_mul]
    by_cases hk : k < r
    · rw [awayPderiv_chartY_of_lt c r j hk, ite_eq_right hj.ne]
      split_ifs
      · linear_combination hu
      · ring
    · rw [awayPderiv_chartY_of_not_lt c r j hk]
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      simp [hjk]
  · rw [hjr, c.chartDeriv_self r, Derivation.add_apply, Derivation.finset_sum_apply]
    simp only [Derivation.smul_apply, smul_eq_mul]
    by_cases hk : k < r
    · rw [awayPderiv_chartY_of_lt c r r hk, ite_eq_left (rfl : r = r), ite_eq_right hk.ne']
      rw [Finset.sum_eq_single k]
      · rw [awayPderiv_chartY_of_lt c r k hk, ite_eq_left (rfl : k = k), ite_eq_right hk.ne,
          chartY_of_lt c.x r hk]
        ring
      · intro i hi hik
        rw [awayPderiv_chartY_of_lt c r i hk, ite_eq_right hik,
          ite_eq_right (Finset.mem_filter.mp hi).2.ne]
        ring
      · intro hk'
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩ :
          k ∈ Finset.univ.filter (fun i : Fin n => i < r)) hk'
    · rw [awayPderiv_chartY_of_not_lt c r r hk]
      have : ∀ i ∈ Finset.univ.filter (fun i : Fin n => i < r),
          chartY c.x r i * c.awayPderiv r i (chartY c.x r k) = 0 := by
        intro i hi
        rw [awayPderiv_chartY_of_not_lt c r i hk,
          ite_eq_right (fun (h : i = k) => hk (h ▸ (Finset.mem_filter.mp hi).2)), mul_zero]
      rw [Finset.sum_eq_zero this, add_zero]
  · rw [c.chartDeriv_of_gt r hj]
    by_cases hk : k < r
    · rw [awayPderiv_chartY_of_lt c r j hk, ite_eq_right hj.ne', ite_eq_right (hk.trans hj).ne']
      ring
    · exact awayPderiv_chartY_of_not_lt c r j hk

/-- `∂'ⱼ` maps the image of `R` into the chart ring. -/
theorem chartDeriv_algebraMap_mem (j : Fin n) (a : R) :
    c.chartDeriv r j (algebraMap R (Localization.Away (c.x r)) a) ∈ chartRing c.x r := by
  rcases lt_trichotomy j r with hj | hjr | hj
  · rw [c.chartDeriv_of_lt r hj, Derivation.smul_apply, awayPderiv_algebraMap, smul_eq_mul,
      ← map_mul]
    exact Subalgebra.algebraMap_mem _ _
  · rw [hjr, c.chartDeriv_self r, Derivation.add_apply, Derivation.finset_sum_apply,
      awayPderiv_algebraMap]
    refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ ?_)
    intro i _
    rw [Derivation.smul_apply, awayPderiv_algebraMap, smul_eq_mul]
    exact Subalgebra.mul_mem _ (chartY_mem _ _ _) (Subalgebra.algebraMap_mem _ _)
  · rw [c.chartDeriv_of_gt r hj, awayPderiv_algebraMap]
    exact Subalgebra.algebraMap_mem _ _

/-- Each `∂'ⱼ` maps the chart ring `R'` into itself. -/
theorem chartDeriv_mem (j : Fin n) {z : Localization.Away (c.x r)} (hz : z ∈ chartRing c.x r) :
    c.chartDeriv r j z ∈ chartRing c.x r := by
  refine Algebra.adjoin_induction (p := fun z _ => c.chartDeriv r j z ∈ chartRing c.x r)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨i, hi, rfl⟩
    have hi' : i < r := hi
    change c.chartDeriv r j (Localization.mk (c.x i) ⟨c.x r, Submonoid.mem_powers _⟩) ∈
      chartRing c.x r
    rw [← chartY_eq_mk_of_lt c.x r hi', chartDeriv_chartY]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  · exact chartDeriv_algebraMap_mem c r j
  · intro z w _ _ hz' hw'
    rw [Derivation.map_add]
    exact Subalgebra.add_mem _ hz' hw'
  · intro z w hz hw hz' hw'
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hz hw') (Subalgebra.mul_mem _ hw hz')

end RegularCoords

section Origin

variable [IsRegularLocalRing R] (x : Fin n → R) (r : Fin n)

omit [IsRegularLocalRing R] in
/-- Every element of the chart ring is congruent modulo `𝔪'` to the image of an element of `R`
(the constant term of a polynomial in the `yᵢ`). -/
theorem exists_algebraMap_sub_mem_chartOriginOf (d : R) (z : chartRingOf x r d) :
    ∃ a : R, z - algebraMap R _ a ∈ chartOriginOf x r d := by
  obtain ⟨z, hz⟩ := z
  refine Algebra.adjoin_induction
    (p := fun z hz => ∃ a : R, (⟨z, hz⟩ : chartRingOf x r d) - algebraMap R _ a ∈
      chartOriginOf x r d) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨i, hi, rfl⟩
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero]
    have : (⟨Localization.mk (x i) ⟨d, Submonoid.mem_powers d⟩,
        Algebra.subset_adjoin ⟨i, hi, rfl⟩⟩ : chartRingOf x r d) = chartYROf x r d i :=
      Subtype.ext (chartYOf_of_lt x r d hi).symm
    rw [this]
    exact chartYROf_mem_chartOriginOf x r d i
  · intro a
    refine ⟨a, ?_⟩
    rw [show (⟨algebraMap R (Localization.Away d) a, Subalgebra.algebraMap_mem _ a⟩ :
      chartRingOf x r d) = algebraMap R _ a from rfl, sub_self]
    exact zero_mem _
  · rintro z w hz hw ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have : (⟨z + w, Subalgebra.add_mem _ hz hw⟩ : chartRingOf x r d) - algebraMap R _ (a + b) =
        (⟨z, hz⟩ - algebraMap R _ a) + (⟨w, hw⟩ - algebraMap R _ b) :=
      Subtype.ext (by simp; ring)
    rw [this]
    exact add_mem ha hb
  · rintro z w hz hw ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    have : (⟨z * w, Subalgebra.mul_mem _ hz hw⟩ : chartRingOf x r d) - algebraMap R _ (a * b) =
        ⟨z, hz⟩ * (⟨w, hw⟩ - algebraMap R _ b) +
          algebraMap R _ b * (⟨z, hz⟩ - algebraMap R _ a) :=
      Subtype.ext (by simp; ring)
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_left _ _ ha)

/-- The key point, `1 ∉ 𝔪'`: the origin of the chart in the proof of [Kol07, Lemma 61] is a
point.  Proof: `R/⟨xᵢ : i ≠ r⟩` is a regular local ring of dimension one
(`Hironaka/Algebra/Local/RegularSystem.lean`, after moving `x_r` to the last position) with maximal
ideal `⟨x̄_r⟩`, hence a domain in which `x̄_r ≠ 0`; the ring map from `R[1/x_r]` to its fraction
field sends `R'` into the quotient and every generator of `𝔪'` into its maximal ideal, so `1 ∈ 𝔪'`
would give `1 ∈ ⟨x̄_r⟩`. -/
theorem one_notMem_chartOriginOf (d : R) (hd : d = x r)
    (hx : maximalIdeal R = span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R) :
    (1 : chartRingOf x r d) ∉ chartOriginOf x r d := by
  subst hd
  intro h1
  classical
  have hpos : 0 < n := Fin.pos r
  set ℓ : Fin n := ⟨n - 1, by omega⟩ with hℓ
  set σ : Equiv.Perm (Fin n) := Equiv.swap r ℓ with hσ
  set x' : Fin n → R := x ∘ σ with hx'def
  have hx' : maximalIdeal R = span (Set.range x') := by
    rw [hx, hx'def, σ.surjective.range_comp]
  set Q : Ideal R := span (x' '' {j : Fin n | j.val < n - 1}) with hQ
  have hxℓ : x' ℓ = x r := by simp [x', σ]
  have hxrQ : x r ∉ Q := by
    have := notMem_span_image_lt x' hx' hn (i := n - 1) (by omega)
    rwa [show (⟨n - 1, by omega⟩ : Fin n) = ℓ from rfl, hxℓ] at this
  have hmemQ : ∀ i, i ≠ r → x i ∈ Q := by
    intro i hi
    refine Ideal.subset_span ⟨σ i, ?_, by simp [x', σ]⟩
    have hne : σ i ≠ ℓ := fun h => hi (by simpa [σ] using congrArg σ h)
    have : (σ i).val ≠ n - 1 := fun h => hne (Fin.ext h)
    have := (σ i).2
    change (σ i).val < n - 1
    omega
  have hS : IsRegularLocalRing (R ⧸ Q) :=
    isRegularLocalRing_quotient_span_image_lt x' hx' hn (n - 1)
  set S := R ⧸ Q with hSdef
  let F := FractionRing S
  let g : R →+* F := (algebraMap S F).comp (Ideal.Quotient.mk Q)
  have hinj : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
  have hg : IsUnit (g (x r)) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hxrQ
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hinj (by rw [map_zero]; exact h0)
  let ψ : Localization.Away (x r) →+* F := IsLocalization.Away.lift (x r) hg
  have hψ : ∀ a, ψ (algebraMap R _ a) = g a := fun a => IsLocalization.Away.lift_eq (x r) hg a
  have hmk : ∀ i, Ideal.Quotient.mk Q (x i) ∈ maximalIdeal S := fun i => by
    rw [maximalIdeal_quotient_eq_map]
    exact Ideal.mem_map_of_mem _ (x_mem_maximalIdeal_of_span_eq x hx i)
  have hy : ∀ i, ψ (chartY x r i) ∈ algebraMap S F '' (maximalIdeal S : Set S) := by
    intro i
    by_cases hi : i < r
    · rw [chartY_of_lt x r hi, map_mul, hψ]
      have : g (x i) = 0 := by
        change algebraMap S F (Ideal.Quotient.mk Q (x i)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hmemQ i hi.ne), map_zero]
      rw [this, zero_mul]
      exact ⟨0, zero_mem _, map_zero _⟩
    · rw [chartY_eq_algebraMap_of_not_lt x r hi, hψ]
      exact ⟨Ideal.Quotient.mk Q (x i), hmk i, rfl⟩
  have hR' : ∀ z ∈ chartRing x r, ψ z ∈ Set.range (algebraMap S F) := by
    intro z hz
    refine Algebra.adjoin_induction (p := fun z _ => ψ z ∈ Set.range (algebraMap S F))
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, hi, rfl⟩
      have hi' : i < r := hi
      obtain ⟨s, -, hs⟩ := hy i
      rw [chartY_eq_mk_of_lt x r hi'] at hs
      exact ⟨s, hs⟩
    · intro a
      exact ⟨Ideal.Quotient.mk Q a, (hψ a).symm⟩
    · rintro z w _ _ ⟨s, hs⟩ ⟨t, ht⟩
      exact ⟨s + t, by rw [map_add, map_add, hs, ht]⟩
    · rintro z w _ _ ⟨s, hs⟩ ⟨t, ht⟩
      exact ⟨s * t, by rw [map_mul, map_mul, hs, ht]⟩
  have hM : ∀ z ∈ chartOrigin x r,
      ψ (z : Localization.Away (x r)) ∈ algebraMap S F '' (maximalIdeal S : Set S) := by
    intro z hz
    refine Submodule.span_induction
      (p := fun (z : chartRing x r) _ =>
        ψ (z : Localization.Away (x r)) ∈ algebraMap S F '' (maximalIdeal S : Set S))
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      exact hy i
    · exact ⟨0, zero_mem _, by rw [Subalgebra.coe_zero, map_zero, map_zero]⟩
    · rintro z w _ _ ⟨s, hs, hs'⟩ ⟨t, ht, ht'⟩
      exact ⟨s + t, add_mem hs ht, by rw [map_add, Subalgebra.coe_add, map_add, hs', ht']⟩
    · rintro b z _ ⟨s, hs, hs'⟩
      obtain ⟨t, ht⟩ := hR' b b.2
      exact ⟨t * s, Ideal.mul_mem_left _ _ hs,
        by rw [map_mul, smul_eq_mul, Subalgebra.coe_mul, map_mul, ht, hs']⟩
  obtain ⟨s, hs, hs1⟩ := hM 1 h1
  rw [Subalgebra.coe_one, map_one] at hs1
  have : s = 1 := hinj (by rw [hs1, map_one])
  subst this
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr hs)

/-- `1 ∉ 𝔪'`. -/
theorem one_notMem_chartOrigin (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : (1 : chartRing x r) ∉ chartOrigin x r :=
  one_notMem_chartOriginOf x r (x r) rfl hx hn

/-- `𝔪'` is a proper ideal. -/
theorem chartOriginOf_ne_top (d : R) (hd : d = x r) (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : chartOriginOf x r d ≠ ⊤ :=
  fun h => one_notMem_chartOriginOf x r d hd hx hn (h ▸ Submodule.mem_top)

/-- `𝔪'` lies over `𝔪` (general denominator). -/
theorem comap_chartOriginOf (d : R) (hd : d = x r) (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) :
    (chartOriginOf x r d).comap (algebraMap R (chartRingOf x r d)) = maximalIdeal R := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) ?_
  · intro h
    apply chartOriginOf_ne_top x r d hd hx hn
    rw [Ideal.eq_top_iff_one] at h ⊢
    simpa using h
  · subst hd
    exact maximalIdeal_le_comap_chartOrigin x r hx

/-- `𝔪'` lies over `𝔪`. -/
theorem comap_chartOrigin (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) :
    (chartOrigin x r).comap (algebraMap R (chartRing x r)) = maximalIdeal R :=
  comap_chartOriginOf x r (x r) rfl hx hn

/-- `R'/𝔪' ≅ K`, as the bijectivity of the residue map `R/𝔪 → R'/𝔪'`. -/
theorem quotientMap_chartOrigin_bijective (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) :
    Function.Bijective (Ideal.quotientMap (chartOrigin x r) (algebraMap R (chartRing x r))
      (maximalIdeal_le_comap_chartOrigin x r hx)) := by
  refine ⟨Ideal.quotientMap_injective' (comap_chartOrigin x r hx hn).le, fun w => ?_⟩
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨a, ha⟩ := exists_algebraMap_sub_mem_chartOriginOf x r (x r) z
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  have := neg_mem_iff.mpr ha
  rwa [neg_sub] at this

/-- The origin of the chart is a maximal ideal of `R'` (the point `p'` of the proof of
[Kol07, Lemma 61]). -/
theorem chartOrigin_isMaximal (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : (chartOrigin x r).IsMaximal := by
  have hbij := quotientMap_chartOrigin_bijective x r hx hn
  exact Ideal.Quotient.maximal_of_isField _
    ((RingEquiv.ofBijective _ hbij).symm.isField (Field.toIsField (ResidueField R)))

end Origin

section Shift

variable (x : Fin n → R) (r : Fin n) (a : Fin n → R)

theorem shiftCoords_of_lt {i : Fin n} (hi : i < r) : shiftCoords x r a i = x i - a i * x r :=
  ite_eq_left hi

theorem shiftCoords_of_not_lt {i : Fin n} (hi : ¬ i < r) : shiftCoords x r a i = x i :=
  ite_eq_right hi

/-- `x'ᵢ/x_r = yᵢ − ãᵢ` for `i < r`. -/
theorem mk_shiftCoords_of_lt {i : Fin n} (hi : i < r) :
    Localization.mk (shiftCoords x r a i) ⟨x r, Submonoid.mem_powers _⟩ =
      Localization.mk (x i) ⟨x r, Submonoid.mem_powers _⟩ -
        algebraMap R (Localization.Away (x r)) (a i) := by
  rw [mk_eq_algebraMap_mul_invX, mk_eq_algebraMap_mul_invX, shiftCoords_of_lt x r a hi, map_sub,
    map_mul, sub_mul, mul_assoc, algebraMap_mul_invX, mul_one]

/-- The shifted coordinates generate `𝔪` (the linear change of coordinates in the proof of
[Kol07, Lemma 61]). -/
theorem span_range_shiftCoords [IsLocalRing R] (hx : maximalIdeal R = span (Set.range x)) :
    maximalIdeal R = span (Set.range (shiftCoords x r a)) := by
  have hxm : ∀ j, x j ∈ maximalIdeal R := fun j => hx ▸ Ideal.subset_span ⟨j, rfl⟩
  apply le_antisymm
  · rw [hx, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i < r
    · have : x i = shiftCoords x r a i + a i * shiftCoords x r a r := by
        rw [shiftCoords_of_lt x r a hi, shiftCoords_self]; ring
      rw [this]
      exact add_mem (Ideal.subset_span ⟨i, rfl⟩)
        (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨r, rfl⟩))
    · rw [← shiftCoords_of_not_lt x r a hi]
      exact Ideal.subset_span ⟨i, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    unfold shiftCoords
    split_ifs
    · exact sub_mem (hxm i) (Ideal.mul_mem_left _ _ (hxm r))
    · exact hxm i

/-- The shifted coordinates generate the same `P = ⟨xᵢ : i ≤ r⟩`. -/
theorem span_shiftCoords_le :
    span (shiftCoords x r a '' {i | i ≤ r}) = span (x '' {i | i ≤ r}) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i ≤ r := hi
    unfold shiftCoords
    split_ifs
    · exact sub_mem (Ideal.subset_span ⟨i, hi', rfl⟩)
        (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨r, le_refl r, rfl⟩))
    · exact Ideal.subset_span ⟨i, hi', rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i ≤ r := hi
    by_cases h : i < r
    · have : x i = shiftCoords x r a i + a i * shiftCoords x r a r := by
        rw [shiftCoords_of_lt x r a h, shiftCoords_self]; ring
      rw [this]
      exact add_mem (Ideal.subset_span ⟨i, hi', rfl⟩)
        (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨r, le_refl r, rfl⟩))
    · rw [← shiftCoords_of_not_lt x r a h]
      exact Ideal.subset_span ⟨i, hi', rfl⟩

/-- The shifted coordinates define the same chart ring (`x'ᵢ/x_r = yᵢ − ãᵢ`). -/
theorem chartRingOf_shiftCoords : chartRingOf (shiftCoords x r a) r (x r) = chartRing x r := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < r := hi
    dsimp only
    rw [mk_shiftCoords_of_lt x r a hi']
    exact Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨i, hi', rfl⟩)
      (Subalgebra.algebraMap_mem _ _)
  · apply Algebra.adjoin_le
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < r := hi
    have : Localization.mk (x i) ⟨x r, Submonoid.mem_powers _⟩ =
        Localization.mk (shiftCoords x r a i) ⟨x r, Submonoid.mem_powers _⟩ +
          algebraMap R (Localization.Away (x r)) (a i) := by
      rw [mk_shiftCoords_of_lt x r a hi', sub_add_cancel]
    dsimp only
    rw [this]
    exact Subalgebra.add_mem _ (Algebra.subset_adjoin ⟨i, hi', rfl⟩)
      (Subalgebra.algebraMap_mem _ _)

/-- The generators of `𝔪'_a` and of the origin of the shifted chart have the same images in
`R[1/x_r]`. -/
theorem coe_chartYROf_shiftCoords (i : Fin n) :
    ((chartYROf (shiftCoords x r a) r (x r) i : chartRingOf (shiftCoords x r a) r (x r)) :
        Localization.Away (x r)) =
      ((if i < r then chartYR x r i - algebraMap R _ (a i) else chartYR x r i : chartRing x r) :
        Localization.Away (x r)) := by
  rw [coe_chartYROf]
  by_cases hi : i < r
  · rw [ite_eq_left hi, chartYOf_of_lt _ _ _ hi, mk_shiftCoords_of_lt x r a hi, Subalgebra.coe_sub,
      Subalgebra.coe_algebraMap, coe_chartYROf, chartYOf_of_lt _ _ _ hi]
  · rw [ite_eq_right hi, chartYOf_of_not_lt _ _ _ hi, coe_chartYROf, chartYOf_of_not_lt _ _ _ hi,
      shiftCoords_of_not_lt x r a hi]

/-- `𝔪'_a` is the origin of the chart for the shifted coordinates (membership correspondence
through the ambient ring `R[1/x_r]`). -/
theorem mem_chartOriginAt_iff (z : chartRing x r) :
    z ∈ chartOriginAt x r a ↔
      ∃ w ∈ chartOriginOf (shiftCoords x r a) r (x r),
        (w : Localization.Away (x r)) = (z : Localization.Away (x r)) := by
  have hS := chartRingOf_shiftCoords x r a
  constructor
  · intro hz
    refine Submodule.span_induction
      (p := fun (z : chartRing x r) _ => ∃ w ∈ chartOriginOf (shiftCoords x r a) r (x r),
        (w : Localization.Away (x r)) = (z : Localization.Away (x r))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      exact ⟨chartYROf _ r (x r) i, chartYROf_mem_chartOriginOf _ r (x r) i,
        coe_chartYROf_shiftCoords x r a i⟩
    · exact ⟨0, zero_mem _, by rw [Subalgebra.coe_zero, Subalgebra.coe_zero]⟩
    · rintro z₁ z₂ _ _ ⟨w₁, hw₁, e₁⟩ ⟨w₂, hw₂, e₂⟩
      exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [Subalgebra.coe_add, Subalgebra.coe_add, e₁, e₂]⟩
    · rintro b z₁ _ ⟨w₁, hw₁, e₁⟩
      exact ⟨⟨b, hS.symm ▸ b.2⟩ * w₁, Ideal.mul_mem_left _ _ hw₁,
        by rw [smul_eq_mul, Subalgebra.coe_mul, Subalgebra.coe_mul, e₁]⟩
  · rintro ⟨w, hw, hwz⟩
    revert z
    refine Submodule.span_induction
      (p := fun (w : chartRingOf (shiftCoords x r a) r (x r)) _ => ∀ z : chartRing x r,
        (w : Localization.Away (x r)) = (z : Localization.Away (x r)) → z ∈ chartOriginAt x r a)
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, rfl⟩ z hz
      have : z = if i < r then chartYR x r i - algebraMap R _ (a i) else chartYR x r i :=
        Subtype.ext (hz.symm.trans (coe_chartYROf_shiftCoords x r a i))
      rw [this]
      exact Ideal.subset_span ⟨i, rfl⟩
    · intro z hz
      have : z = 0 := Subtype.ext (by rw [← hz, Subalgebra.coe_zero, Subalgebra.coe_zero])
      rw [this]
      exact zero_mem _
    · rintro w₁ w₂ _ _ ih₁ ih₂ z hz
      have h₁ := ih₁ ⟨w₁, hS ▸ w₁.2⟩ rfl
      have h₂ := ih₂ ⟨w₂, hS ▸ w₂.2⟩ rfl
      have : z = ⟨w₁, hS ▸ w₁.2⟩ + ⟨w₂, hS ▸ w₂.2⟩ :=
        Subtype.ext (by rw [← hz, Subalgebra.coe_add, Subalgebra.coe_add])
      rw [this]
      exact add_mem h₁ h₂
    · rintro b w₁ _ ih z hz
      have h₁ := ih ⟨w₁, hS ▸ w₁.2⟩ rfl
      have : z = ⟨b, hS ▸ b.2⟩ * ⟨w₁, hS ▸ w₁.2⟩ :=
        Subtype.ext (by rw [← hz, smul_eq_mul, Subalgebra.coe_mul, Subalgebra.coe_mul])
      rw [this]
      exact Ideal.mul_mem_left _ _ h₁

theorem shiftCoords_self_symm : x r = shiftCoords x r a r := (shiftCoords_self x r a).symm

variable [IsRegularLocalRing R]

/-- `1 ∉ 𝔪'_a`. -/
theorem one_notMem_chartOriginAt (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : (1 : chartRing x r) ∉ chartOriginAt x r a := by
  rw [mem_chartOriginAt_iff]
  rintro ⟨w, hw, hw1⟩
  have : w = 1 := Subtype.ext (by rw [hw1, Subalgebra.coe_one, Subalgebra.coe_one])
  subst this
  exact one_notMem_chartOriginOf (shiftCoords x r a) r (x r) (shiftCoords_self_symm x r a)
    (span_range_shiftCoords x r a hx) hn hw

/-- `𝔪'_a` lies over `𝔪`. -/
theorem comap_chartOriginAt (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) :
    (chartOriginAt x r a).comap (algebraMap R (chartRing x r)) = maximalIdeal R := by
  rw [← comap_chartOriginOf (shiftCoords x r a) r (x r) (shiftCoords_self_symm x r a)
    (span_range_shiftCoords x r a hx) hn]
  ext b
  rw [Ideal.mem_comap, Ideal.mem_comap, mem_chartOriginAt_iff]
  constructor
  · rintro ⟨w, hw, hwb⟩
    have : w = algebraMap R _ b :=
      Subtype.ext (by rw [hwb, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap])
    rwa [this] at hw
  · intro hb
    exact ⟨algebraMap R _ b, hb, by rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]⟩

/-- `𝔪'_a` has residue field `K`: `𝔪` maps into `𝔪'_a` and the residue map is bijective. -/
theorem quotientMap_chartOriginAt_bijective (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) :
    ∃ h : maximalIdeal R ≤ (chartOriginAt x r a).comap (algebraMap R (chartRing x r)),
      Function.Bijective
        (Ideal.quotientMap (chartOriginAt x r a) (algebraMap R (chartRing x r)) h) := by
  refine ⟨(comap_chartOriginAt x r a hx hn).ge, Ideal.quotientMap_injective'
    (comap_chartOriginAt x r a hx hn).le, fun w => ?_⟩
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨b, hb⟩ := exists_algebraMap_sub_mem_chartOriginOf (shiftCoords x r a) r (x r)
    ⟨z, (chartRingOf_shiftCoords x r a).symm ▸ z.2⟩
  refine ⟨Ideal.Quotient.mk _ b, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  have hmem : z - algebraMap R _ b ∈ chartOriginAt x r a :=
    (mem_chartOriginAt_iff x r a _).mpr ⟨_, hb, by
      rw [Subalgebra.coe_sub, Subalgebra.coe_sub, Subalgebra.coe_algebraMap,
        Subalgebra.coe_algebraMap]⟩
  have := neg_mem_iff.mpr hmem
  rwa [neg_sub] at this

/-- `𝔪'_a` is maximal. -/
theorem chartOriginAt_isMaximal (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : (chartOriginAt x r a).IsMaximal := by
  obtain ⟨h, hbij⟩ := quotientMap_chartOriginAt_bijective x r a hx hn
  exact Ideal.Quotient.maximal_of_isField _
    ((RingEquiv.ofBijective _ hbij).symm.isField (Field.toIsField (ResidueField R)))

end Shift

section Domain

variable [IsRegularLocalRing R] (x : Fin n → R) (r : Fin n)

/-- `R[1/x_r]` is a domain. -/
theorem isDomain_away (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : IsDomain (Localization.Away (x r)) :=
  IsLocalization.Away.isDomain (S := Localization.Away (x r)) (x_ne_zero_of_span_eq x hx hn r)

/-- The chart ring is a domain. -/
theorem isDomain_chartRing (hx : maximalIdeal R = span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) : IsDomain (chartRing x r) := by
  have := isDomain_away x r hx hn
  infer_instance

end Domain

namespace RegularCoords

variable [IsRegularLocalRing R] [Algebra ℚ R] (c : RegularCoords R n) (r : Fin n)

/-- `∂'ⱼ` as a derivation of the chart ring `R'` (it preserves `R'` by `chartDeriv_mem`): the
coordinate derivations of the chart, used in `Hironaka/Algebra/Local/ChartCoords.lean` and
`Hironaka/Algebra/Local/TransformDeriv.lean`. -/
noncomputable def chartDerivRing (j : Fin n) : Derivation ℚ (chartRing c.x r) (chartRing c.x r)
    where
  toFun z := ⟨c.chartDeriv r j z, c.chartDeriv_mem r j z.2⟩
  map_add' z w := Subtype.ext (by simp)
  map_smul' q z := Subtype.ext (by simp)
  map_one_eq_zero' := Subtype.ext (by simp)
  leibniz' z w := Subtype.ext (by simp [Derivation.leibniz])

@[simp]
theorem coe_chartDerivRing (j : Fin n) (z : chartRing c.x r) :
    (c.chartDerivRing r j z : Localization.Away (c.x r)) = c.chartDeriv r j z :=
  rfl

end RegularCoords

/-- A permutation of `Fin n` carrying the initial segment of length `s.card` onto `s`, with the last
element of the segment going to a prescribed `k ∈ s` (Kollár's convention `Z = (y_1 = ⋯ = y_r = 0)`
with the chart coordinate `y_r`); a combinatorial tool for the charts of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Chart.lean`. -/
theorem _root_.exists_equiv_image_eq {n : ℕ} (s : Finset (Fin n)) {kk : Fin n}
    (hk : kk ∈ s) :
    ∃ σ : Fin n ≃ Fin n, (∀ i : Fin n, σ i ∈ s ↔ i.val < s.card) ∧
      ∀ h : s.card - 1 < n, σ ⟨s.card - 1, h⟩ = kk := by
  classical
  set r := s.card with hr
  have hrpos : 0 < r := Finset.card_pos.mpr ⟨kk, hk⟩
  have hrn : r ≤ n := by
    have := Finset.card_le_univ s
    rwa [Fintype.card_fin] at this
  let g₀ : Fin r ↪o Fin n := s.orderEmbOfFin rfl
  have hg₀ : ∀ i, g₀ i ∈ s := fun i => Finset.orderEmbOfFin_mem s rfl i
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin r, g₀ i₀ = kk := by
    have : kk ∈ Set.range g₀ := by
      rw [Finset.range_orderEmbOfFin]
      exact hk
    exact this
  let ρ₀ : Fin r := ⟨r - 1, by omega⟩
  let τ : Fin r ≃ Fin r := Equiv.swap i₀ ρ₀
  let f₀ : Fin n → Fin n := fun i => if h : i.val < r then g₀ (τ ⟨i.val, h⟩) else i
  let s₀ : Finset (Fin n) := Finset.univ.filter fun i => i.val < r
  have hf₀ : ∀ i (h : i.val < r), f₀ i = g₀ (τ ⟨i.val, h⟩) := fun i h => dite_eq_left h
  have hinj : Set.InjOn f₀ ↑s₀ := by
    intro i hi j hj hij
    have hi' : i.val < r := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
    have hj' : j.val < r := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
    rw [hf₀ i hi', hf₀ j hj'] at hij
    have := τ.injective (g₀.injective hij)
    exact Fin.ext (Fin.mk.inj this)
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (t := (Finset.univ : Finset (Fin n)))
    (by rw [Finset.card_univ]) (s := s₀) (f := f₀) (Finset.subset_univ _) hinj
  refine ⟨g.trans (Equiv.subtypeUnivEquiv fun x => Finset.mem_univ x), ?_, ?_⟩
  · -- `σ` carries the initial segment onto `s`, and only it
    have hcard : s₀.card = r := by
      have : s₀ = Finset.univ.image (Fin.castLE hrn) := by
        ext i
        simp only [s₀, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hi
          exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
        · rintro ⟨j, rfl⟩
          exact j.2
      rw [this, Finset.card_image_of_injective _ (Fin.castLE_injective hrn), Finset.card_univ,
        Fintype.card_fin]
    have himg : s₀.image (fun i => (g i : Fin n)) = s := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        rw [hg i hi, hf₀ i (Finset.mem_filter.mp hi).2]
        exact hg₀ _
      · rw [Finset.card_image_of_injOn (fun i _ j _ hij => g.injective (Subtype.ext hij)), hcard]
    intro i
    constructor
    · intro hi
      by_contra hlt
      have hi' : (g i : Fin n) ∈ s₀.image (fun i => (g i : Fin n)) := himg ▸ hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi'
      have := g.injective (Subtype.ext hji)
      subst this
      exact hlt (Finset.mem_filter.mp hj).2
    · intro hi
      have hi' : i ∈ s₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [← himg]
      exact Finset.mem_image_of_mem _ hi'
  · intro h
    have hval : ((⟨r - 1, h⟩ : Fin n)).val = r - 1 := rfl
    have hlt : ((⟨r - 1, h⟩ : Fin n)).val < r := by rw [hval]; omega
    have hmem : (⟨r - 1, h⟩ : Fin n) ∈ s₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
    change (g ⟨r - 1, h⟩ : Fin n) = kk
    rw [hg _ hmem, hf₀ _ hlt]
    have : (⟨(⟨r - 1, h⟩ : Fin n).val, hlt⟩ : Fin r) = ρ₀ := rfl
    rw [this, Equiv.swap_apply_right]
    exact hi₀

end IsLocalRing
