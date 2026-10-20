/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.Chart
import Hironaka.Algebra.Local.ChartLocal
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.LocalBlowUp
import Hironaka.Scheme.Smooth.LocalBlowUpStalk
import Hironaka.Scheme.Snc.TotalTransformOnCentre
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Points of the blow-up of a centre with simple normal crossings

The point-level facts behind the nerve transition of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Kernel.lean`, on a smooth `k`-scheme `X` with a
centre `Z` carrying Kollár's snc data `hZ` for a finite family `D` of ideal sheaves (the hypothesis
of `Hironaka/Scheme/Snc/TotalTransformSnc.lean`):

* `exists_stalkIdeal_comap_eq_span_of_mem_support`: at a point `x'` of the exceptional divisor
  over `x`, with `Z_x = (z_c : c ∈ s)`, some `z_c` (`c ∈ s`) generates the exceptional ideal
  `F_{x'} = π^*(Z_x)`. By the total-transform data of `Hironaka/Scheme/Snc/TotalTransformData.lean`,
  `F_{x'} = (z'_j)` and each `π^* z_c` generates an ideal of shape `(z'_a z'_j)`, `(z'_a)`,
  `(z'_j)` or `(1)`; the shapes `(z'_a)`, `(1)` are excluded since `(π^* z_c) ⊆ F_{x'}`, and if
  every `c ∈ s` had the shape `(z'_a z'_j)` then `F_{x'} ⊆ 𝔪_{x'} F_{x'}`, impossible by
  Nakayama for the regular parameter `z'_j`. This is the statement that `x'` lies in the chart
  of some `z_c`, as in the proof of [Hau14, Proposition 5.3].
* `exists_chartOrigin_point`, `exists_chartOrigin_point_of_mem`: the origin of the chart of a
  centre coordinate `y_ρ`, in the coordinates (60.2) of [Kol07, Definition 60], as a point of
  the blow-up over `x` at which `π^* y_ρ` generates the exceptional ideal and every other
  centre coordinate `π^* y_i = (y_i / y_ρ) · y_ρ` lies in `𝔪_{x'}²`.

Not in the sources as statements; they are the coordinate computations that Kollár's and
Hauser's descriptions of the blow-up in charts take for granted.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal
  Scheme.IdealSheafData

namespace Hironaka.Monomial

variable {X : Scheme.{u}}

/-! ### Nakayama for the exceptional ideal -/

section Chart

variable {k : Type u} [Field k] [PerfectField k] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
  {ι : Type*} [Finite ι] (D : ι → X.IdealSheafData) (Z : X.IdealSheafData)
  (hZ : ∀ x ∈ Z.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
    (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
    (∃ c : {i : ι // x ∈ (D i).support} → Fin n, Function.Injective c ∧
      ∀ i, (D i.1).stalkIdeal x = span {z (c i)}) ∧
    ∃ s : Finset (Fin n), Z.stalkIdeal x = span (z '' ↑s))

include f hZ in
/-- At a point `x'` of the exceptional divisor over `x`, with `Z_x = (z_c : c ∈ s)` and every
`z_c` (`c ∈ s`) the coordinate of a member `D_i` of the family, some `π^* z_c` generates the
exceptional ideal `F_{x'}`: `x'` lies in the chart of `z_c` (the proof of
[Hau14, Proposition 5.3]). -/
theorem exists_stalkIdeal_comap_eq_span_of_mem_support (x' : Scheme.IdealSheafData.blowUp Z)
    (hx' : x' ∈ (Z.comap (Scheme.IdealSheafData.blowUpπ Z)).support) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (Scheme.IdealSheafData.blowUpπ Z x')} {s : Finset (Fin n)}
    (hs : Z.stalkIdeal (Scheme.IdealSheafData.blowUpπ Z x') = span (z '' ↑s))
    (hD : ∀ c ∈ s, ∃ i, (D i).stalkIdeal (Scheme.IdealSheafData.blowUpπ Z x') = span {z c}) :
    ∃ c ∈ s, (Z.comap (Scheme.IdealSheafData.blowUpπ Z)).stalkIdeal x' = span
        {(Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (z c)} := by
  classical
  obtain ⟨hdata, -⟩ := exists_totalTransformData_of_mem_support f D Z hZ x' hx'
  obtain ⟨hreg, m, z', ⟨hspan', hdim'⟩, j, a, hF, -, hshape⟩ := hdata
  have := hreg
  set F := (Z.comap (Scheme.IdealSheafData.blowUpπ Z)).stalkIdeal x' with hFdef
  have hFle : F ≤ maximalIdeal ((Scheme.IdealSheafData.blowUp Z).presheaf.stalk x') :=
    (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ x').mp hx'
  have hFs : F = span ((Scheme.IdealSheafData.blowUpπ Z).stalkMap x' '' (z '' ↑s)) := by
    rw [hFdef, Scheme.IdealSheafData.stalkIdeal_comap, hs, Ideal.map_span]
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  -- every `π^* z_c`, `c ∈ s`, lies in `𝔪 F`
  have hmem : ∀ c ∈ s, (Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (z c) ∈
      maximalIdeal ((Scheme.IdealSheafData.blowUp Z).presheaf.stalk x') * F := by
    intro c hc
    obtain ⟨i, hi⟩ := hD c hc
    have hT : ((D i).comap (Scheme.IdealSheafData.blowUpπ Z)).stalkIdeal x' = span
        {(Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (z c)} :=
      stalkIdeal_comap_π_eq Z (D i) x' hi
    have hTle : ((D i).comap (Scheme.IdealSheafData.blowUpπ Z)).stalkIdeal x' ≤ F := by
      rw [hFdef, Scheme.IdealSheafData.stalkIdeal_comap, Scheme.IdealSheafData.stalkIdeal_comap]
      refine Ideal.map_mono ?_
      rw [hi, hs]
      exact Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨c, hc, rfl⟩)
    have hmemT : (Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (z c) ∈ ((D i).comap
        (Scheme.IdealSheafData.blowUpπ Z)).stalkIdeal x' := by
      rw [hT]
      exact Ideal.mem_span_singleton_self _
    have hshape' := hshape i
    simp only at hshape'
    rcases hshape' with ⟨hne, hTi | hTi⟩ | hTi | hTi
    · -- the shape `(z'_a z'_j) ⊆ 𝔪 (z'_j)`
      rw [hTi] at hmemT
      rw [hF]
      refine (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)) hmemT
      exact Ideal.mul_mem_mul (x_mem_maximalIdeal_of_span_eq z' hspan'.symm (a i))
        (Ideal.mem_span_singleton_self _)
    · -- the shape `(z'_a)`, `a ≠ j`, is not contained in `F = (z'_j)`
      exfalso
      rw [hTi, hF] at hTle
      exact notMem_span_singleton_of_ne hspan' hdim' hne.symm
        (hTle (Ideal.mem_span_singleton_self _))
    · -- the shape `(z'_j) = F`: `F` is generated by `π^* z_c`
      exfalso
      exact hcon c hc (hF.trans (hTi.symm.trans hT))
    · -- the unit ideal is not contained in `F ⊆ 𝔪`
      exfalso
      rw [hTi] at hTle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (hTle.trans hFle))
  -- hence `F ⊆ 𝔪 F`, so the regular parameter `z'_j` is zero
  have hFle' : F ≤ maximalIdeal ((Scheme.IdealSheafData.blowUp Z).presheaf.stalk x') * F := by
    refine hFs.le.trans (Ideal.span_le.mpr ?_)
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact hmem c hc
  have hj : z' j ∈ span {z' j} * maximalIdeal ((Scheme.IdealSheafData.blowUp Z).presheaf.stalk x')
      := by
    rw [mul_comm, ← hF]
    exact hFle' (hF ▸ Ideal.mem_span_singleton_self _)
  obtain ⟨u, hu, huj⟩ := Ideal.mem_span_singleton_mul.mp hj
  have hunit : IsUnit (1 - u) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits u ((IsLocalRing.mem_maximalIdeal _).mp hu)
  have hzero : z' j * (1 - u) = 0 := by rw [mul_sub, mul_one, huj, sub_self]
  have hzj : z' j = 0 := (hunit.mul_left_eq_zero).mp hzero
  exact notMem_sq_of_span_eq z' hspan'.symm hdim' j
    (by rw [hzj]; exact Ideal.zero_mem _)

end Chart

/-! ### The origin of a chart as a point of the blow-up -/

section Origin

open IsLocalRing

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]

/-- Transport of a stalk ideal's description along an equality of points. -/
theorem stalkIdeal_eq_span_image_eqRec {I : X.IdealSheafData} {p q : X} (h : q = p) {n : ℕ}
    (z : Fin n → X.presheaf.stalk p) (s : Set (Fin n)) (hI : I.stalkIdeal p = span (z '' s)) :
    I.stalkIdeal q = span ((fun i => (h ▸ z i : X.presheaf.stalk q)) '' s) := by
  subst h
  exact hI

/-- Transport of a germ along an equality of points. -/
theorem germ_eqRec {V : X.Opens} {p q : X} (h : q = p) (hp : p ∈ V) (s : Γ(X, V)) :
    (h ▸ X.presheaf.germ V p hp s : X.presheaf.stalk q) = X.presheaf.germ V q (h ▸ hp) s := by
  subst h
  rfl

include f in
/-- The chart of [Kol07, Definition 60], formula (60.2): with a regular system of parameters `y`
at `x` whose first `r` members generate `Z_x`, the origin of the chart of `y_ρ` (`ρ = r - 1`) is
a point `x'` of the blow-up over `x` at which `π^* y_ρ` generates the exceptional ideal and every
other `π^* y_i` (`i < r`) lies in `𝔪_{x'}²`, since `π^* y_i = (y_i / y_ρ) · y_ρ` with both
factors in the maximal ideal of the chart ring's localisation at the origin. -/
theorem exists_chartOrigin_point (Z : X.IdealSheafData) (x : X) {n r : ℕ}
    (y : Fin n → X.presheaf.stalk x) (hn : (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (hy : maximalIdeal (X.presheaf.stalk x) = span (Set.range y))
    (hZ : Z.stalkIdeal x = span (y '' {i | i.val < r})) (ρ : Fin n) (hρ : ρ.val + 1 = r) :
    ∃ (x' : Scheme.IdealSheafData.blowUp Z) (hx' : Scheme.IdealSheafData.blowUpπ Z x' = x),
      (Z.comap (Scheme.IdealSheafData.blowUpπ Z)).stalkIdeal x' =
        span
          {(Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ y ρ : X.presheaf.stalk
              (Scheme.IdealSheafData.blowUpπ Z x'))} ∧
      ∀ i : Fin n, i.val < r → i ≠ ρ →
        (Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ y i : X.presheaf.stalk
            (Scheme.IdealSheafData.blowUpπ Z x')) ∈
          maximalIdeal ((Scheme.IdealSheafData.blowUp Z).presheaf.stalk x') ^ 2 := by
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f x
  have hprime : (chartOrigin y ρ).IsPrime := (chartOrigin_isMaximal y ρ hy hn).isPrime
  obtain ⟨x', hx', e, he⟩ :=
    @exists_stalk_equiv_localization_chartOrigin_of_isIso X Z x hreg n r y hn hy hZ
      ρ hρ hprime (fun H p => isIso_stalkMap_of_isPullback_fromSpecStalk H p)
  -- `e` on the transports of arbitrary elements of `𝒪_{X,x}`
  have key : ∀ c : X.presheaf.stalk x,
      e ((Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ c : X.presheaf.stalk
          (Scheme.IdealSheafData.blowUpπ Z x'))) =
        algebraMap (chartRing y ρ) (Localization.AtPrime (chartOrigin y ρ))
          (algebraMap _ (chartRing y ρ) c) := by
    intro c
    obtain ⟨V, hxV, s, rfl⟩ := X.presheaf.exists_germ_eq c
    exact (congrArg (fun t => e ((Scheme.IdealSheafData.blowUpπ Z).stalkMap x' t))
        (germ_eqRec hx' hxV s)).trans
      (he V hxV s)
  -- the divided coordinates: `y_i = (y_i / y_ρ) · y_ρ` in the chart ring
  have hcoord : ∀ i : Fin n, i < ρ →
      algebraMap _ (chartRing y ρ) (y i) = chartYR y ρ i * chartYR y ρ ρ := by
    intro i hi
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, coe_chartYROf, coe_chartYROf,
      chartYOf_of_lt y ρ (y ρ) hi, chartYOf_self, mk_eq_algebraMap_mul_invX, mul_assoc,
      mul_comm (invX y ρ), algebraMap_mul_invX, mul_one]
  have hcoordρ : algebraMap _ (chartRing y ρ) (y ρ) = chartYR y ρ ρ := by
    apply Subtype.ext
    rw [Subalgebra.coe_algebraMap, coe_chartYROf, chartYOf_self]
  -- the chart coordinates lie in the maximal ideal of the localization at the origin
  have hmemY : ∀ i : Fin n, algebraMap (chartRing y ρ) (Localization.AtPrime (chartOrigin y ρ))
      (chartYR y ρ i) ∈ maximalIdeal (Localization.AtPrime (chartOrigin y ρ)) := by
    intro i
    rw [maximalIdeal_localization_chartOrigin]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hmemR : ∀ w, w ∈ maximalIdeal (Localization.AtPrime (chartOrigin y ρ)) →
      e.symm w ∈ maximalIdeal ((Scheme.IdealSheafData.blowUp Z).presheaf.stalk x') := by
    intro w hw
    rw [← map_maximalIdeal_ringEquiv e]
    exact Ideal.mem_map_of_mem _ hw
  have hyρ : e.symm (algebraMap (chartRing y ρ) (Localization.AtPrime (chartOrigin y ρ))
      (chartYR y ρ ρ)) = (Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ y ρ) := by
    rw [← hcoordρ, ← key, e.symm_apply_apply]
  have hyi : ∀ i : Fin n, i < ρ → (Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ y i) =
      e.symm (algebraMap (chartRing y ρ) (Localization.AtPrime (chartOrigin y ρ))
        (chartYR y ρ i)) * (Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ y ρ) := by
    intro i hi
    rw [← hyρ, ← map_mul, ← map_mul, ← hcoord i hi, ← key, e.symm_apply_apply]
  have hlt : ∀ i : Fin n, i.val < r → i ≠ ρ → i < ρ := by
    intro i hi hiρ
    rw [Fin.lt_def]
    have := Fin.val_ne_of_ne hiρ
    omega
  -- the exceptional ideal at `x'` is `π^*(Z_x) = (π^* y_i : i < r)`
  have hFs : (Z.comap (Scheme.IdealSheafData.blowUpπ Z)).stalkIdeal x' =
      span ((fun i : Fin n => (Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ y i)) ''
          {i | i.val < r}) := by
    rw [Scheme.IdealSheafData.stalkIdeal_comap, stalkIdeal_eq_span_image_eqRec hx' y _ hZ,
        Ideal.map_span,
      Set.image_image]
  refine ⟨x', hx', ?_, ?_⟩
  · -- the exceptional ideal is generated by `π^* y_ρ`
    rw [hFs]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      change (Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ y i) ∈
        span {(Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ y ρ)}
      by_cases hiρ : i = ρ
      · subst hiρ
        exact Ideal.mem_span_singleton_self _
      · rw [hyi i (hlt i hi hiρ)]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
      have hρr : ρ ∈ {i : Fin n | i.val < r} := show ρ.val < r by omega
      exact Ideal.subset_span (Set.mem_image_of_mem _ hρr)
  · -- the other divided coordinates lie in `𝔪_{x'}²`
    intro i hi hiρ
    rw [hyi i (hlt i hi hiρ), pow_two]
    exact Ideal.mul_mem_mul (hmemR _ (hmemY i)) (hyρ ▸ hmemR _ (hmemY ρ))

include f in
/-- The chart-origin point for an unordered set of centre coordinates: with snc coordinates `z`
at `x`, `Z_x = (z_c : c ∈ s)` and `k ∈ s`, there is a point `x'` over `x` at which `π^* z_k`
generates the exceptional ideal and `π^* z_c ∈ 𝔪_{x'}²` for every other `c ∈ s` (the origin of
the chart of `z_k`, after reordering the coordinates). -/
theorem exists_chartOrigin_point_of_mem (Z : X.IdealSheafData) (x : X) {n : ℕ}
    (z : Fin n → X.presheaf.stalk x) (hn : (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (hz : maximalIdeal (X.presheaf.stalk x) = span (Set.range z)) {s : Finset (Fin n)}
    (hs : Z.stalkIdeal x = span (z '' ↑s)) {kk : Fin n} (hk : kk ∈ s) :
    ∃ (x' : Scheme.IdealSheafData.blowUp Z) (hx' : Scheme.IdealSheafData.blowUpπ Z x' = x),
      (Z.comap (Scheme.IdealSheafData.blowUpπ Z)).stalkIdeal x' =
        span
          {(Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ z kk : X.presheaf.stalk
              (Scheme.IdealSheafData.blowUpπ Z x'))} ∧
      ∀ c ∈ s, c ≠ kk →
        (Scheme.IdealSheafData.blowUpπ Z).stalkMap x' (hx' ▸ z c : X.presheaf.stalk
            (Scheme.IdealSheafData.blowUpπ Z x')) ∈
          maximalIdeal ((Scheme.IdealSheafData.blowUp Z).presheaf.stalk x') ^ 2 := by
  obtain ⟨σ, hσ, hσρ⟩ := exists_equiv_image_eq s hk
  have hrpos : 0 < s.card := Finset.card_pos.mpr ⟨kk, hk⟩
  have hrn : s.card ≤ n := by
    have := Finset.card_le_univ s
    rwa [Fintype.card_fin] at this
  let ρ : Fin n := ⟨s.card - 1, by omega⟩
  have hρ : ρ.val + 1 = s.card := by
    change s.card - 1 + 1 = s.card
    omega
  have hy : maximalIdeal (X.presheaf.stalk x) = span (Set.range (z ∘ σ)) := by
    rw [σ.surjective.range_comp z]
    exact hz
  have himg : σ '' {i : Fin n | i.val < s.card} = ↑s := by
    ext j
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (hσ i).mpr hi
    · intro hj
      exact ⟨σ.symm j, (hσ _).mp (by simpa using hj), σ.apply_symm_apply j⟩
  have hZ : Z.stalkIdeal x = span ((z ∘ σ) '' {i : Fin n | i.val < s.card}) := by
    rw [Set.image_comp, himg]
    exact hs
  obtain ⟨x', hx', hF, hsq⟩ := exists_chartOrigin_point f Z x (z ∘ σ) hn hy hZ ρ hρ
  have hσρ' : σ ρ = kk := hσρ _
  refine ⟨x', hx', ?_, ?_⟩
  · have hzρ : (z ∘ σ) ρ = z kk := by rw [Function.comp_apply, hσρ']
    rw [hzρ] at hF
    exact hF
  · intro c hc hck
    have hi : (σ.symm c).val < s.card := (hσ _).mp (by simpa using hc)
    have hiρ : σ.symm c ≠ ρ := by
      intro h
      apply hck
      rw [← σ.apply_symm_apply c, h, hσρ']
    have := hsq (σ.symm c) hi hiρ
    have hzc : (z ∘ σ) (σ.symm c) = z c := by rw [Function.comp_apply, σ.apply_symm_apply]
    rw [hzc] at this
    exact this

end Origin

end Hironaka.Monomial
