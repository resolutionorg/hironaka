/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.ChartSubst
public import Hironaka.Algebra.Local.CompletionMap
public import Hironaka.Algebra.Local.SymbolicPower
import Hironaka.Algebra.Local.CompletionCoords
import Hironaka.Algebra.Local.PowerSeries
import Hironaka.Algebra.Local.PowerSeriesRegular
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.Transform
import Mathlib.Combinatorics.Matroid.Init

/-!
# The order of a transform, through the completion

The proof of [Kol07, Lemma 61] bounds the order of the birational transform `π⁻¹_*(f, m)` of an
element `f` of order `m` by `m`: written as a power series, `f` has a monomial of degree `m`;
after the chart substitution `xᵢ ↦ yᵢ y_r` (`i < r`), `xⱼ ↦ yⱼ` (`j ≥ r`) that monomial has degree
`≤ 2m`, so after division by `y_rᵐ` the transform has a monomial of degree `≤ m`.

This module proves the transfer step of that argument in the abstract form needed later
(`ordElem_le_of_completionMap_eq_subst`). Let `R` be a regular local ring containing `ℚ` with a
regular system of parameters `x`, so that `R̂ ≅ K⟦x⟧` by the Cohen isomorphism `cohenEquiv`
(`Hironaka/Algebra/Local/CohenIso.lean`); let `φ : R → B` be a local homomorphism into a Noetherian
local ring, `Ψ : K⟦y⟧ ≃ B̂` an isomorphism under which the map `R̂ → B̂` induced by `φ`
(`completionMap`, `Hironaka/Algebra/Local/CompletionMap.lean`) is the chart substitution `chartSubst
r` (`Hironaka/Algebra/Local/ChartSubst.lean`), and `g ∈ B` with `φ(x_r)ᵐ g = φ(f)`, where
`f ∈ Pᵐ = (x₀, …, x_r)ᵐ` has order `m`. Then `ord_B g ≤ m`: the series of `f` has all its monomials
of `x₀, …, x_r`-degree `≥ m` (`mem_chartCenter_pow_iff_le_weightedOrder'`,
`Hironaka/Algebra/Local/SymbolicPower.lean`), its substitution is `y_rᵐ G'` with `ord G' ≤ m`
(`exists_X_pow_mul_eq_subst_chartSubst`), `Ψ(G')` is the image of `g` in `B̂` after cancelling
`φ(x_r)ᵐ` in the domain `B̂`, and orders are preserved by `Ψ` and by `B → B̂`
(`ordElem_algebraMap_adicCompletion`, `Hironaka/Algebra/Local/CompletionCoords.lean`).

`Hironaka/Algebra/Local/ChartCompletion.lean` supplies the hypothesis on `Ψ` for the local ring of
the chart ring at its origin, and `Hironaka/Algebra/Local/Lemma61.lean` derives Kollár's bound at
every `K`-rational point of the chart from it.

Also here: an ideal of order `m` of a Noetherian local ring contains an element of order `m`
(`exists_mem_ordElem_eq_of_ord_eq`); the order of the transformed ideal `π⁻¹_*(I, m)` in a local
ring of the chart is bounded by the order of the transform of an element of `I` of order `m`
(`ord_map_transformIdeal_le_of_forall`, Kollár's "This shows that `ord_{p'} π⁻¹_* I ≤ m`"); and
the order of an ideal is invariant under isomorphisms of local rings (`ord_map_ringEquiv`, used
throughout `Hironaka/Order` and `Hironaka/Sequence`).
-/

public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

section Transport

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (x : Fin n → R) (hx : maximalIdeal R = Ideal.span (Set.range x))
  (hn : (n : WithBot ℕ∞) = ringKrullDim R)

local notation "R̂" => AdicCompletion (maximalIdeal R) R

/-- The weight of an exponent `d` for the indicator weight of `x₀, …, x_r` is `∑_{i ≤ r} dᵢ`, the
`x₀, …, x_r`-degree of the monomial `x^d`. -/
theorem weight_indicator_filter_le (r : Fin n) (d : Fin n →₀ ℕ) :
    Finsupp.weight (indicatorWeight (Finset.univ.filter (· ≤ r))) d =
      ∑ i ∈ Finset.univ.filter (· ≤ r), d i := by
  rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset d (Finset.subset_univ _) _
    (fun i _ => by simp), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [indicatorWeight]

end Transport

section Core

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (x : Fin n → R) (hx : maximalIdeal R = Ideal.span (Set.range x))
  (hn : (n : WithBot ℕ∞) = ringKrullDim R) (r : Fin n)
  {B : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (φ : R →+* B) [IsLocalHom φ]

/-- **The order of a transform through the completion** (the proof of [Kol07, Lemma 61]): if the
map induced on completions by `φ : R → B` is the chart substitution under the Cohen isomorphisms
(`hΨ`), `f ∈ Pᵐ` has order `m`, and `φ(x_r)ᵐ g = φ(f)` (so `g` is the transform `π⁻¹_*(f, m)`),
then `ord_B g ≤ m`: the series of `f` has all its monomials of `x₀, …, x_r`-degree `≥ m`, its
substitution is `y_rᵐ G'` with `ord G' ≤ m`, and `Ψ(G') = ι'(g)` by cancelling `ι'(φ(x_r))ᵐ` in the
domain `B̂ ≅ K⟦y⟧`; orders are preserved by `Ψ` and by `ι' : B → B̂`. -/
theorem ordElem_le_of_completionMap_eq_subst
    (Ψ : MvPowerSeries (Fin n) (ResidueField R) ≃+* AdicCompletion (maximalIdeal B) B)
    (hΨ : ∀ F, completionMap φ (cohenEquiv R x hx hn F) = Ψ (subst (chartSubst r) F))
    {m : ℕ} {f : R} (hf : f ∈ chartCenter x r ^ m) (hord : ordElem f = m)
    {g : B} (hg : φ (x r) ^ m * g = φ f) : ordElem g ≤ m := by
  have : IsDomain (AdicCompletion (maximalIdeal B) B) :=
    MulEquiv.isDomain (MvPowerSeries (Fin n) (ResidueField R)) Ψ.symm.toMulEquiv
  -- the series of `f`: order `m`, all monomials of `x₀..x_r`-degree `≥ m`
  have hFord : ((cohenEquiv R x hx hn).symm
      (algebraMap R (AdicCompletion (maximalIdeal R) R) f)).order = m := by
    rw [← ordElem_eq_order, ← ordElem_ringEquiv (cohenEquiv R x hx hn), RingEquiv.apply_symm_apply,
      ordElem_algebraMap_adicCompletion (R := R), hord]
  have hFP : ∀ d, coeff d ((cohenEquiv R x hx hn).symm
      (algebraMap R (AdicCompletion (maximalIdeal R) R) f)) ≠ 0 →
      m ≤ ∑ i ∈ Finset.univ.filter (· ≤ r), d i := by
    intro d hd
    have h1 := (mem_chartCenter_pow_iff_le_weightedOrder' x hx hn r f m).mp hf
    have h2 := weightedOrder_le (indicatorWeight (Finset.univ.filter (· ≤ r))) hd
    rw [← weight_indicator_filter_le]
    exact_mod_cast le_trans h1 h2
  -- the substitution is `y_r ^ m * G'` with `ord G' ≤ m`
  obtain ⟨G', hG', hordG'⟩ := exists_X_pow_mul_eq_subst_chartSubst r hFord hFP
  -- `Ψ (X r) = ι' (φ (x r))`
  have hΨr : Ψ (X r) = algebraMap B (AdicCompletion (maximalIdeal B) B) (φ (x r)) := by
    have h := hΨ (X r)
    rw [cohenEquiv_X, completionMap_algebraMap, subst_X (hasSubst_chartSubst r),
      chartSubst, ite_eq_right (lt_irrefl r)] at h
    exact h.symm
  -- `Ψ G' = ι' g`, cancelling `ι' (φ (x r)) ^ m` in the domain `B̂`
  have hcancel : algebraMap B (AdicCompletion (maximalIdeal B) B) (φ (x r)) ^ m * Ψ G' =
      algebraMap B (AdicCompletion (maximalIdeal B) B) (φ (x r)) ^ m *
        algebraMap B (AdicCompletion (maximalIdeal B) B) g := by
    have h := hΨ ((cohenEquiv R x hx hn).symm (algebraMap R (AdicCompletion (maximalIdeal R) R) f))
    rw [RingEquiv.apply_symm_apply, completionMap_algebraMap, ← hg, map_mul, map_pow, ← hG',
      map_mul, map_pow, hΨr] at h
    exact h.symm
  have hne : algebraMap B (AdicCompletion (maximalIdeal B) B) (φ (x r)) ≠ 0 := by
    classical
    rw [← hΨr]
    refine (map_ne_zero_iff Ψ Ψ.injective).mpr fun hX => ?_
    have h := congrArg (coeff (Finsupp.single r 1)) hX
    rw [coeff_X, ite_eq_left rfl, map_zero] at h
    exact one_ne_zero h
  have hΨG : Ψ G' = algebraMap B (AdicCompletion (maximalIdeal B) B) g :=
    mul_left_cancel₀ (pow_ne_zero m hne) hcancel
  calc ordElem g = ordElem (algebraMap B (AdicCompletion (maximalIdeal B) B) g) :=
        (ordElem_algebraMap_adicCompletion (R := B) g).symm
    _ = ordElem (Ψ G') := by rw [hΨG]
    _ = ordElem G' := ordElem_ringEquiv Ψ G'
    _ = G'.order := ordElem_eq_order G'
    _ ≤ m := hordG'

end Core

section Ideal

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (x : Fin n → R) (r : Fin n) {B : Type*} [CommRing B] [IsLocalRing B]

omit [Algebra ℚ R] in
/-- An ideal of order `m` contains an element of order `m`: `R` is Noetherian, so `I` is finitely
generated, and the order of an ideal is attained on a generator. -/
theorem exists_mem_ordElem_eq_of_ord_eq {I : Ideal R} {m : ℕ} (hord : ord I = m) :
    ∃ f ∈ I, ordElem f = m := by
  obtain ⟨S, hS⟩ := I.fg_of_isNoetherianRing
  have hne : (S : Set R).Nonempty := by
    rw [Finset.coe_nonempty, Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [← hS, Finset.coe_empty, Ideal.span_empty, ord_eq_top_iff.mpr rfl] at hord
    exact ENat.top_ne_natCast m hord
  obtain ⟨f, hf, hfeq⟩ := exists_ord_span_eq_ordElem S.finite_toSet hne
  refine ⟨f, hS ▸ Ideal.subset_span hf, ?_⟩
  rw [← hfeq, hS, hord]

omit [Algebra ℚ R] in
/-- Kollár's "This shows that `ord_{p'} π⁻¹_* I ≤ m`" (the proof of [Kol07, Lemma 61]): the order
of the transformed ideal `π⁻¹_*(I, m)` in a local ring `B` of the chart is bounded by the order of
the transform of an element of `I` of order `m`. -/
theorem ord_map_transformIdeal_le_of_forall {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m)
    (hord : ord I = m) (ψ : chartRing x r →+* B)
    (h : ∀ f (hf : f ∈ I), ordElem f = m → ordElem (ψ (transformElem x r f (hI hf))) ≤ m) :
    ord ((transformIdeal x r I m).map ψ) ≤ m := by
  obtain ⟨f, hf, hfm⟩ := exists_mem_ordElem_eq_of_ord_eq hord
  have hmem : ψ (transformElem x r f (hI hf)) ∈ (transformIdeal x r I m).map ψ := by
    refine Ideal.mem_map_of_mem _ ?_
    rw [transformIdeal_eq_span_range_transformElem _ _ hI]
    exact Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩
  refine le_trans ?_ (h f hf hfm)
  rw [ord_eq_iInf]
  exact iInf₂_le _ hmem

end Ideal

section Equiv

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

/-- The order of an ideal is invariant under isomorphisms of local rings. -/
theorem ord_map_ringEquiv (e : A ≃+* B) (K : Ideal A) : ord (K.map (e : A →+* B)) = ord K := by
  rw [ord_eq_iInf, ord_eq_iInf]
  apply le_antisymm
  · refine le_iInf₂ fun f hf => ?_
    have : e f ∈ K.map (e : A →+* B) := Ideal.mem_map_of_mem _ hf
    exact (iInf₂_le (e f) this).trans (le_of_eq (ordElem_ringEquiv e f))
  · refine le_iInf₂ fun g hg => ?_
    obtain ⟨f, hf, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp hg
    exact (iInf₂_le f hf).trans (le_of_eq (ordElem_ringEquiv e f).symm)

end Equiv

end IsLocalRing
