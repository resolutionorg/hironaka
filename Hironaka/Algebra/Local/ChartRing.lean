/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.DerivationLocalization
public import Hironaka.Scheme.BlowUp.Presentation
public import Hironaka.Algebra.Local.Coords

/-!
# The chart ring of a blow-up along a coordinate subspace: definitions

Kollár computes with the blow-up of `Z = (x₁ = ⋯ = x_r = 0)` in the chart with coordinates
`y₁ = x₁/x_r, …, y_{r-1} = x_{r-1}/x_r, y_r = x_r, …, yₙ = xₙ` [Kol07, Definition 60, (60.2)].
This file fixes the ring-level form of that chart: for a family `x : Fin n → R` (a regular
system of parameters in use) and an index `r`, the elements `yᵢ` of `R[1/x_r]`, the chart ring
`R' = R[x_i/x_r : i < r] ⊆ R[1/x_r]`, the origin `𝔪' = ⟨y₁, …, yₙ⟩R'` of the chart, the
presentation `R[Y_i : i < r] → R'` with its Koszul relations `x_r Y_i − x_i`, the other
`K`-rational points `𝔪'_a` of the exceptional fibre and the shifted coordinates
`x'_i = x_i − ã_i x_r`, the extension of a derivation to `R[1/a]` and the transformed
derivations `∂'_j`.

## Conventions

Indices are `Fin n`; Kollár's `1 ≤ r ≤ n` (one-based) is `r : Fin n` (zero-based), the divided
coordinates are the `i < r`, and `x_r` itself is the denominator.  The denominator is a separate
argument `d` of `chartYOf`, `chartRingOf`, `chartOriginOf`, so that the chart of a second family
with the same `r`-th coordinate (the shifted coordinates: `x'_r = x_r` only propositionally)
lives in the same ring `R[1/x_r]`; `chartY x r`, `chartRing x r`, `chartOrigin x r` are the
specializations `d = x r`.  `Localization.Away d` is Mathlib's
`Localization (Submonoid.powers d)`, and `Localization.mk a ⟨d, _⟩` is `a / d`.  The transformed
derivations are `ℚ`-derivations of `R[1/x_r]`; that they preserve `R'` is proved in
`Hironaka/Algebra/Local/Chart.lean` (`chartDeriv_mem`), so here they are defined on `R[1/x_r]` only.

## Main declarations

* `IsLocalRing.chartY`, `chartRing`, `chartYR`, `chartY_mem`: the chart coordinates and the
  chart ring.
* `IsLocalRing.chartOrigin` and `maximalIdeal_le_comap_chartOrigin` (the map `R → R'` sends
  `𝔪` into `𝔪'`, so that the residue map `R/𝔪 → R'/𝔪'` is defined).
* `IsLocalRing.chartPresentation`, `chartRelations`: the polynomial presentation of `R'`.
* `IsLocalRing.shiftCoords`, `chartOriginAt`: the other rational points of the exceptional
  fibre and the coordinates centred at them.
* `Derivation.extendAway`: the extension of a derivation to `A[1/a]` (the specialization of
  `Derivation.localization` to `Submonoid.powers a`).
* `IsLocalRing.RegularCoords.awayPderiv`, `chartDeriv`: the transformed derivations
  `∂'_j = x_r ∂_j` for `j < r`, `∂'_r = ∂_r + ∑_{i<r} yᵢ ∂ᵢ`, `∂'_j = ∂_j` for `j > r`.

The properties of these constructions (beginning with `∂'ⱼ yₖ = δⱼₖ` and the stability of `R'`
under the `∂'ⱼ`) are proved in `Hironaka/Algebra/Local/Chart.lean`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

section Family

variable (x : Fin n → R) (r : Fin n) (d : R)

/-- The chart coordinates of [Kol07, Definition 60, (60.2)] with a general denominator `d`:
`yᵢ = xᵢ / d` for `i < r` and `yᵢ = xᵢ` for `i ≥ r`, in `R[1/d]`. -/
noncomputable def chartYOf (i : Fin n) : Localization.Away d :=
  if i < r then Localization.mk (x i) ⟨d, Submonoid.mem_powers d⟩ else algebraMap R _ (x i)

/-- The chart coordinates `yᵢ = xᵢ/x_r` for `i < r`, `y_r = x_r`, `yⱼ = xⱼ` for `j > r`, in
`R[1/x_r]` [Kol07, Definition 60, (60.2)]. -/
noncomputable abbrev chartY : Fin n → Localization.Away (x r) := chartYOf x r (x r)

theorem chartYOf_of_lt {i : Fin n} (h : i < r) :
    chartYOf x r d i = Localization.mk (x i) ⟨d, Submonoid.mem_powers d⟩ := ite_eq_left h

theorem chartYOf_of_not_lt {i : Fin n} (h : ¬ i < r) : chartYOf x r d i = algebraMap R _ (x i) :=
  ite_eq_right h

theorem chartYOf_self : chartYOf x r d r = algebraMap R _ (x r) := ite_eq_right (lt_irrefl r)

/-- With a general denominator `d`: the subalgebra `R[xᵢ/d : i < r]` of `R[1/d]`. -/
noncomputable def chartRingOf : Subalgebra R (Localization.Away d) :=
  Algebra.adjoin R
    ((fun i : Fin n => Localization.mk (x i) ⟨d, Submonoid.mem_powers d⟩) '' {i | i < r})

/-- The chart ring `R' = R[xᵢ/x_r : i < r] ⊆ R[1/x_r]` of the chart (60.2) of
[Kol07, Definition 60] and [Kol07, 75 (Birational transform of derivatives)], as
`Algebra.adjoin R {x_i / x_r : i < r}`. -/
noncomputable abbrev chartRing : Subalgebra R (Localization.Away (x r)) := chartRingOf x r (x r)

theorem chartYOf_mem (i : Fin n) : chartYOf x r d i ∈ chartRingOf x r d := by
  unfold chartYOf
  split_ifs with h
  · exact Algebra.subset_adjoin ⟨i, h, rfl⟩
  · exact Subalgebra.algebraMap_mem _ _

/-- Every `yᵢ` lies in the chart ring. -/
theorem chartY_mem (i : Fin n) : chartY x r i ∈ chartRing x r := chartYOf_mem x r (x r) i

/-- With a general denominator: `yᵢ` as an element of the chart ring. -/
noncomputable def chartYROf (i : Fin n) : chartRingOf x r d :=
  ⟨chartYOf x r d i, chartYOf_mem x r d i⟩

/-- `yᵢ` as an element of the chart ring `R'`. -/
noncomputable abbrev chartYR : Fin n → chartRing x r := chartYROf x r (x r)

@[simp]
theorem coe_chartYROf (i : Fin n) :
    (chartYROf x r d i : Localization.Away d) = chartYOf x r d i :=
  rfl

/-- With a general denominator: the ideal `⟨y₁, …, yₙ⟩` of the chart ring. -/
noncomputable def chartOriginOf : Ideal (chartRingOf x r d) :=
  Ideal.span (Set.range (chartYROf x r d))

/-- The origin `𝔪' = ⟨y₁, …, y_{r-1}, x_r, x_{r+1}, …, xₙ⟩ R'` of the chart: the point
"`p' ∈ B_Z X`, the origin of the chart we consider" of the proof of [Kol07, Lemma 61]. -/
noncomputable abbrev chartOrigin : Ideal (chartRing x r) := chartOriginOf x r (x r)

theorem chartYROf_mem_chartOriginOf (i : Fin n) : chartYROf x r d i ∈ chartOriginOf x r d :=
  Ideal.subset_span ⟨i, rfl⟩

/-- Every coordinate `xᵢ` of `R` maps into the origin of the chart: `xᵢ = yᵢ` for `i ≥ r` and
`xᵢ = yᵢ · x_r` for `i < r`. -/
theorem algebraMap_x_mem_chartOrigin (i : Fin n) :
    algebraMap R (chartRing x r) (x i) ∈ chartOrigin x r := by
  by_cases h : i < r
  · have hx : algebraMap R (chartRing x r) (x i) = chartYR x r i * chartYR x r r := by
      apply Subtype.ext
      simp only [Subalgebra.coe_algebraMap, Subalgebra.coe_mul, coe_chartYROf,
        chartYOf_of_lt _ _ _ h, chartYOf_self, ← Localization.mk_one_eq_algebraMap,
        Localization.mk_mul]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp; ring⟩
    rw [hx]
    exact Ideal.mul_mem_right _ _ (chartYROf_mem_chartOriginOf x r (x r) i)
  · have hx : algebraMap R (chartRing x r) (x i) = chartYR x r i :=
      Subtype.ext (by simp [chartYOf_of_not_lt _ _ _ h])
    rw [hx]
    exact chartYROf_mem_chartOriginOf x r (x r) i

/-- The algebra map `R → R'` sends `𝔪` into `𝔪'`, so the residue map `R/𝔪 → R'/𝔪'`
(`Ideal.quotientMap`) is defined. -/
theorem maximalIdeal_le_comap_chartOrigin [IsLocalRing R]
    (hx : maximalIdeal R = Ideal.span (Set.range x)) :
    maximalIdeal R ≤ (chartOrigin x r).comap (algebraMap R (chartRing x r)) := by
  rw [hx, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact algebraMap_x_mem_chartOrigin x r i

/-- The presentation `R[Y_i : i < r] → R'`, `Y_i ↦ yᵢ = xᵢ/x_r`, of the chart ring. -/
noncomputable def chartPresentation : MvPolynomial (Fin r) R →ₐ[R] chartRing x r :=
  MvPolynomial.aeval fun i : Fin r => chartYR x r (Fin.castLE r.2.le i)

/-- The Koszul relations `x_r Y_i − xᵢ` (`i < r`) of the presentation: the relation ideal
`presentationIdeal` of the affine blow-up algebra at `a = x_r`, `gᵢ = xᵢ`. -/
noncomputable abbrev chartRelations : Ideal (MvPolynomial (Fin r) R) :=
  AlgebraicGeometry.affineBlowUpAlgebra.presentationIdeal (x r) fun i : Fin r =>
    x (Fin.castLE r.2.le i)

/-- The coordinates after the linear change of the `(x₁, …, x_r)`-coordinates moving the origin
of the chart to the point `a` (the proof of [Kol07, Lemma 61]): `x'ᵢ = xᵢ − ãᵢ x_r` for `i < r`,
`x'ⱼ = xⱼ` for `j ≥ r` (`ã` the given lifts). -/
noncomputable def shiftCoords (a : Fin n → R) : Fin n → R :=
  fun i => if i < r then x i - a i * x r else x i

theorem shiftCoords_self (a : Fin n → R) : shiftCoords x r a r = x r := ite_eq_right (lt_irrefl r)

/-- The other `K`-rational points of the exceptional fibre,
`𝔪'_a = ⟨yᵢ − ãᵢ (i < r), x_r, x_{r+1}, …, xₙ⟩ R'`, the points the linear change of coordinates
in the proof of [Kol07, Lemma 61] moves to the origin. -/
noncomputable def chartOriginAt (a : Fin n → R) : Ideal (chartRing x r) :=
  Ideal.span (Set.range fun i : Fin n =>
    if i < r then chartYR x r i - algebraMap R _ (a i) else chartYR x r i)

end Family

end IsLocalRing

namespace Derivation

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The extension of a derivation `D` of `A` to `A[1/a]`,
`D(f / aᵏ) = (a · D f − k · f · D a) / aᵏ⁺¹` (the extension of the `∂/∂uᵢ` to the fraction field
in the proof of [Wlo05, Lemma 2.6.3]); the specialization of `Derivation.localization` to
`Submonoid.powers a`. -/
noncomputable def extendAway (D : Derivation k A A) (a : A) :
    Derivation k (Localization.Away a) (Localization.Away a) :=
  D.localization (Submonoid.powers a)

end Derivation

namespace IsLocalRing.RegularCoords

open IsLocalRing

universe u

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n) (r : Fin n)

/-- The coordinate derivation `∂ⱼ` extended to `R[1/x_r]`. -/
noncomputable def awayPderiv (j : Fin n) :
    Derivation ℚ (Localization.Away (c.x r)) (Localization.Away (c.x r)) :=
  (c.pderiv j).extendAway (c.x r)

/-- The transformed derivations on `R[1/x_r]`, `∂'ⱼ = x_r ∂ⱼ` for `j < r`,
`∂'_r = ∂_r + ∑_{i<r} yᵢ ∂ᵢ`, `∂'ⱼ = ∂ⱼ` for `j > r`: the derivations of the chart expressed
through those of the base, as in [Kol07, 75], the proof of [Wlo05, Lemma 2.6.3] and
[BM08, Lemma 3.1]. -/
noncomputable def chartDeriv (j : Fin n) :
    Derivation ℚ (Localization.Away (c.x r)) (Localization.Away (c.x r)) :=
  if j < r then algebraMap R (Localization.Away (c.x r)) (c.x r) • c.awayPderiv r j
  else if j = r then
    c.awayPderiv r r +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < r), chartY c.x r i • c.awayPderiv r i
  else c.awayPderiv r j

theorem chartDeriv_of_lt {j : Fin n} (h : j < r) :
    c.chartDeriv r j = algebraMap R (Localization.Away (c.x r)) (c.x r) • c.awayPderiv r j :=
  ite_eq_left h

theorem chartDeriv_self :
    c.chartDeriv r r = c.awayPderiv r r +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < r), chartY c.x r i • c.awayPderiv r i := by
  rw [chartDeriv, ite_eq_right (lt_irrefl r), ite_eq_left rfl]

theorem chartDeriv_of_gt {j : Fin n} (h : r < j) : c.chartDeriv r j = c.awayPderiv r j := by
  rw [chartDeriv, ite_eq_right (not_lt.mpr h.le), ite_eq_right h.ne']

end IsLocalRing.RegularCoords
