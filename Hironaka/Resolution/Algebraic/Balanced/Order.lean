/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.Derivative.Cosupport
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# D-balanced ideal sheaves: order `m` or `0`, cosupport, restriction, going up

The remarks following [Kol07, Definition 83]: a D-balanced `I` has, at every point, "order either
`m` or `0`" — if `ord_p I < m` then `(D^{m−1} I)_p = 𝒪_{p,X}`, so `I^{m−1}` and `I` contain a unit
at `p` — hence `cosupp(I, m) = cosupp I` and the maximal order commutes with restrictions; and a
smooth blow-up of order `≥ m` for `I|_S` "corresponds to a smooth blow-up of order `≥ m` for `I`".

* The order dichotomy (`IsDBalanced.ord_eq_zero_or_le`, `ord_eq_zero_or_eq`) is Kollár's argument:
  [Kol07, Lemma 74 (3)] at the stalk (`le_ord_iff_le_ord_derivativeIter`) turns `ord_x I < m` into
  `(D^{m−1} I)_x = 𝒪_x`, and the D-balanced inclusion `(D^{m−1} I)^m ≤ I` makes `I_x` the unit
  ideal.
* `cosupp(I, m) = cosupp I` (`cosupp_eq_support`) follows, and so does the restriction statement
  (`cosupp_restrict`): the order never drops under the local homomorphism of stalks
  `𝒪_{X, ι s} → 𝒪_{S, s}` (`ord_le_ord_map`, `stalkIdeal_comap`), and where `ord_{ι s} I = 0` the
  stalk is the unit ideal on both sides.
* The going-up reformulation (`isOrderBlowUp_of_restrict`): a generic point `η` of the centre
  `Z ⊆ S` lies in `S`; the order of `I|_S` along `Z` is at least `m` at every point of `Z`
  (`leOrdAlong_iff_forall_mem` on the smooth `S`), so `ord_η I ≥ m` by `cosupp_restrict`, and
  `ord_η I ≤ max-ord I = m`.
-/

public section

universe u

open CategoryTheory TopologicalSpace IsLocalRing

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- A stalk of order `0` is the unit ideal (`ord_eq_zero_iff` at the stalk). -/
theorem stalkIdeal_eq_top_of_ord_eq_zero {I : X.IdealSheafData} {x : X} (h : I.ord x = 0) :
    I.stalkIdeal x = ⊤ := by
  rwa [ord_eq_ord_stalkIdeal, IsLocalRing.ord_eq_zero_iff] at h

/-- The order of `I` at `g y` is at most the order of the pull-back `g⁻¹ I` at `y`: the stalk map is
a local homomorphism (`ord_le_ord_map`; the inequality `ord_p I ≤ ord_p (I|_S)` noted before
[Kol07, Definition 83]). -/
theorem ord_le_ord_comap (I : X.IdealSheafData) {Y : Scheme.{u}} (g : Y ⟶ X) (y : Y) :
    I.ord (g y) ≤ (I.comap g).ord y := by
  rw [ord_eq_ord_stalkIdeal, ord_eq_ord_stalkIdeal, stalkIdeal_comap]
  exact ord_le_ord_map (g.stalkMap y).hom _

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [CharZero k] (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n in
/-- A D-balanced ideal sheaf has order `0` or at least `m` at every point (the remark after
[Kol07, Definition 83]). -/
theorem IsDBalanced.ord_eq_zero_or_le {I : X.IdealSheafData} {m : ℕ} (h : I.IsDBalanced f m)
    (x : X) : I.ord x = 0 ∨ (m : ℕ∞) ≤ I.ord x := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inr (by simp [hm])
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, hlt⟩ := hcon
  -- Lemma 74 (3) with `r = m - 1`: `m ≤ ord_x I ↔ 1 ≤ ord_x (D^{m-1} I)`.
  have h74 := le_ord_iff_le_ord_derivativeIter f n I x (Nat.sub_lt hm one_pos)
  rw [show m - (m - 1) = 1 by omega, Nat.cast_one, one_le_ord_iff] at h74
  have hx : x ∉ (I.derivativeIter f (m - 1)).support := fun hx => hlt (h74.mpr hx)
  have htop : (I.derivativeIter f (m - 1)).stalkIdeal x = ⊤ := by
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal] at hx
    exact not_not.mp fun hne => hx (IsLocalRing.le_maximalIdeal hne)
  -- the D-balanced inclusion at `i = m - 1`: `(D^{m-1} I)^m ≤ I`.
  have hle := h (m - 1) (Nat.sub_lt hm one_pos)
  rw [show m - (m - 1) = 1 by omega, pow_one] at hle
  have hst := stalkIdeal_mono hle x
  rw [stalkIdeal_pow, htop, Ideal.top_pow] at hst
  apply h0
  rw [ord_eq_zero_iff, mem_support_iff_stalkIdeal_le_maximalIdeal]
  intro hle'
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (hst.trans hle'))

include n in
/-- With `m = max-ord I`, a D-balanced ideal sheaf has order `0` or `m` at every point (the remark
after [Kol07, Definition 83]). -/
theorem IsDBalanced.ord_eq_zero_or_eq {I : X.IdealSheafData} {m : ℕ} (h : I.IsDBalanced f m)
    (hmax : I.maxOrd = m) (x : X) : I.ord x = 0 ∨ I.ord x = m := by
  rcases h.ord_eq_zero_or_le f n x with h0 | hm
  · exact Or.inl h0
  · exact Or.inr (le_antisymm (hmax ▸ le_maxOrd I x) hm)

include n in
/-- "`cosupp(I, m) = cosupp I`" for a D-balanced ideal sheaf (the remark after
[Kol07, Definition 83]). -/
theorem IsDBalanced.cosupp_eq_support {I : X.IdealSheafData} {m : ℕ} (h : I.IsDBalanced f m)
    (hm : 1 ≤ m) : {x | (m : ℕ∞) ≤ I.ord x} = (I.support : Set X) := by
  ext x
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · intro hx
    rw [← one_le_ord_iff]
    exact le_trans (by exact_mod_cast hm) hx
  · intro hx
    rcases h.ord_eq_zero_or_le f n x with h0 | hle
    · exact absurd hx ((ord_eq_zero_iff I x).mp h0)
    · exact hle

include n in
/-- "The maximal order commutes with restrictions" (the remark after [Kol07, Definition 83]):
`cosupp(I|_S, m) = cosupp(I, m) ∩ S`, pointwise on `S`. -/
theorem IsDBalanced.cosupp_restrict {I : X.IdealSheafData} {m : ℕ} (h : I.IsDBalanced f m)
    (S : X.IdealSheafData) (s : S.subscheme) :
    (m : ℕ∞) ≤ (I.comap S.subschemeι).ord s ↔ (m : ℕ∞) ≤ I.ord (S.subschemeι s) := by
  refine ⟨fun hs => ?_, fun hx => hx.trans (ord_le_ord_comap I S.subschemeι s)⟩
  rcases h.ord_eq_zero_or_le f n (S.subschemeι s) with h0 | hm'
  · have hcomap : (I.comap S.subschemeι).ord s = 0 := by
      rw [ord_eq_ord_stalkIdeal, stalkIdeal_comap, stalkIdeal_eq_top_of_ord_eq_zero h0,
        Ideal.map_top, IsLocalRing.ord_top]
    rw [hcomap] at hs
    have hm0 : m = 0 := by exact_mod_cast le_zero_iff.mp hs
    simp [hm0]
  · exact hm'

include n in
/-- The going-up remark after [Kol07, Definition 83]: for `I` D-balanced with `m = max-ord I`, `S` a
smooth hypersurface and `Z ⊆ S` a centre with `ord_Z (I|_S) ≥ m`, `ord_Z I = m`. -/
theorem IsDBalanced.isOrderBlowUp_of_restrict {I : X.IdealSheafData} {m : ℕ}
    (h : I.IsDBalanced f m) (hmax : I.maxOrd = m) (S : X.IdealSheafData)
    [SmoothOfRelativeDimension (n - 1) (S.subschemeι ≫ f)]
    (Z : X.IdealSheafData) (hZS : S ≤ Z)
    (hZ : (I.comap S.subschemeι).LeOrdAlong (Z.comap S.subschemeι).support (m : ℕ∞)) :
    I.OrdAlongEq Z.support (m : ℕ∞) := by
  intro η hη
  have hηZ : η ∈ Z.support := hη.1
  have hηS : η ∈ S.support := support_antitone hZS hηZ
  obtain ⟨s, rfl⟩ : η ∈ Set.range S.subschemeι := by rwa [range_subschemeι]
  refine le_antisymm (hmax ▸ le_maxOrd I _) ?_
  rw [← h.cosupp_restrict f n S s]
  have hall := (leOrdAlong_iff_forall_mem (I.comap S.subschemeι) (S.subschemeι ≫ f) (n - 1)
    (Z.comap S.subschemeι).support (m : ℕ∞)).mp hZ
  refine hall s ?_
  rw [support_comap]
  exact hηZ

end AlgebraicGeometry.Scheme.IdealSheafData
