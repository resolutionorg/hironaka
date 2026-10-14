/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CoordsOver
public import Hironaka.Manifold.Germ.CoordDeriv
import Hironaka.Algebra.Local.Completion
import Hironaka.Manifold.Germ.CoordDerivChart
import Hironaka.Manifold.Germ.TaylorCompletion
import Hironaka.Manifold.Germ.TaylorIdeal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The analytic stalk as an instance of the regular coordinates of the `Hironaka` library

Kollár's local coordinates `x_1, …, x_n` at a point of a smooth scheme come with the derivations
`∂/∂x_1, …, ∂/∂x_n`, "local generators of `Der_X`" [Kol07, Definition 73]; the `Hironaka` library
packages this structure on a local ring as `IsLocalRing.RegularCoords R n` — coordinates
generating the maximal ideal, as many as the Krull dimension, with commuting derivations `∂_i`
and `∂_i x_j = δ_ij` — together with the two conditions `IsLinearOver 𝕜` (the derivations kill the
constants) and `SpansDerivations 𝕜` (every `𝕜`-derivation is `∑_i δ(x_i) ∂_i`). This module shows
that the stalk `𝒪_{M,a}` of an analytic manifold with the centred coordinate germs `x_i − x_i(a)`
and the partial derivatives `∂_i` of a chart (`coordDerivStalk`,
`Hironaka/Manifold/Germ/CoordDeriv.lean`) is such an instance (`exists_regularCoords_stalk`),
so that the `Hironaka` library's local theory of regular coordinates applies to analytic stalks:

* `∂_i (x_j − x_j(a)) = δ_ij` (`Hironaka/Manifold/Germ/CoordDerivChart.lean`) and
  `𝔪_a = (x_i − x_i(a))_i` (`maximalIdeal_eq_span_coord'`);
* the `∂_i` commute (`coordDerivStalk_comm`): through the injective Taylor homomorphism
  (`T_a ∘ ∂_i = ∂_{X_i} ∘ T_a`) this is the commutation of the formal partial derivatives
  `∂_{X_i}`, a computation on coefficients (`pderiv_comm`);
* every `𝕜`-derivation `δ` of the stalk is `δ = ∑_i δ(x_i − x_i(a)) ∂_i`
  (`derivation_eq_sum_coordDerivStalk`), by the uniqueness of Taylor coefficients:
  `δ' := δ − ∑_i δ(x_i − x_i(a)) ∂_i` is a `𝕜`-derivation killing the coordinates, hence the
  polynomials in them; every germ is a polynomial plus an element of `𝔪_a^{k+1}` for each `k`
  (`𝔪_a^k` is spanned by the monomials of degree `k`), a derivation lowers the order by one
  (`Derivation.mem_pow_of_mem_pow_succ`), so `δ' f` lies in every `𝔪_a^k`, and `⋂_k 𝔪_a^k = 0` in
  the analytic stalk (`T_a` is injective and `𝕜[[X]]` is `(X)`-adically separated,
  `eq_zero_of_forall_mem_maximalIdeal_pow`);
* `𝕜`-linearity is the derivation property `∂_i (algebraMap c) = 0`.

Given that `𝒪_{M,a}` is a regular local ring of dimension `n`
(`Hironaka/Manifold/Germ/StalkNoetherian.lean`; taken here as the hypotheses
`[IsRegularLocalRing 𝒪_{M,a}]`, `n = ringKrullDim 𝒪_{M,a}`), `exists_regularCoords_stalk` packages
the instance as an existence statement. It is used for the derivative ideal sheaves
(`Hironaka/Manifold/IdealSheaf/Deriv.lean`) and for the transport of derivations along germ
maps in the maximal-contact construction (`Hironaka/Manifold/MaximalContact/`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Series

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- The formal partial derivatives `∂_{X_i}` commute: on coefficients,
`(ν_i + 1)(ν_j + δ_ij + 1) = (ν_j + 1)(ν_i + δ_ji + 1)`. -/
theorem pderiv_comm (i j : Fin n) (F : MvPowerSeries (Fin n) 𝕜) :
    MvPowerSeries.pderiv (R := 𝕜) i (MvPowerSeries.pderiv (R := 𝕜) j F) =
      MvPowerSeries.pderiv (R := 𝕜) j (MvPowerSeries.pderiv (R := 𝕜) i F) := by
  ext ν
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
    MvPowerSeries.coeff_pderiv, add_right_comm ν (Finsupp.single i 1) (Finsupp.single j 1),
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    push_cast
    ring

end Series

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M} (ha : a ∈ φ.source)

/-- The centred coordinate germs `x_i − x_i(a)`, abbreviated. -/
abbrev centredCoord (i : Fin n) : (structureSheaf 𝕜 E M).presheaf.stalk a :=
  coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))

theorem coordDerivStalk_centredCoord (i j : Fin n) :
    coordDerivStalk E ψ φ hφ ha i (centredCoord E ψ φ hφ ha j) = if i = j then 1 else 0 :=
  coordDerivStalk_coord_sub_const E ψ φ hφ ha i j

/-- The partial derivatives on `𝒪_{M,a}` commute (the axiom `pderiv_comm` of `RegularCoords`):
through the injective Taylor homomorphism, the formal ones do. -/
theorem coordDerivStalk_comm (i j : Fin n) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    coordDerivStalk E ψ φ hφ ha i (coordDerivStalk E ψ φ hφ ha j s) =
      coordDerivStalk E ψ φ hφ ha j (coordDerivStalk E ψ φ hφ ha i s) := by
  have hT := isTaylorHom_taylorHom E ψ φ ha hφ
  apply IsTaylorHom.injective' E ψ φ ha hT
  rw [IsTaylorHom.pderiv E ψ φ hφ ha hT, IsTaylorHom.pderiv E ψ φ hφ ha hT,
    IsTaylorHom.pderiv E ψ φ hφ ha hT, IsTaylorHom.pderiv E ψ φ hφ ha hT, pderiv_comm]

include ψ hφ ha in
/-- `⋂_k 𝔪_a^k = 0` in the analytic stalk: the Taylor homomorphism is injective and sends `𝔪_a^k`
into `(X)^k`, and `𝕜[[X]]` is `(X)`-adically separated. -/
theorem eq_zero_of_forall_mem_maximalIdeal_pow (s : (structureSheaf 𝕜 E M).presheaf.stalk a)
    (h : ∀ k, s ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k) : s = 0 := by
  apply IsTaylorHom.injective' E ψ φ ha (isTaylorHom_taylorHom E ψ φ ha hφ)
  rw [map_zero]
  refine eq_of_forall_mk_eq fun k => ?_
  rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact (taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ s k).mpr (h k)

/-- Every germ is a polynomial in the centred coordinates plus an element of `𝔪_a^k`: `𝔪_a^k` is
spanned by the monomials of degree `k`, and a coefficient `g` of such a monomial is its value
`g(a)` plus an element of `𝔪_a`. -/
theorem exists_mem_adjoin_sub_mem_maximalIdeal_pow (k : ℕ)
    (f : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    ∃ p ∈ Algebra.adjoin 𝕜 (Set.range (centredCoord E ψ φ hφ ha)),
      f - p ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k := by
  induction k generalizing f with
  | zero => exact ⟨0, Subalgebra.zero_mem _, by simp⟩
  | succ k ih =>
    obtain ⟨p, hp, hfp⟩ := ih f
    rw [maximalIdeal_pow_eq_span_monomials' E ψ φ ha hφ k] at hfp
    obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hfp
    have hsum' : f - p = ∑ l, c l * (g l : (structureSheaf 𝕜 E M).presheaf.stalk a) := by
      rw [← hsum]
      rfl
    refine ⟨p + ∑ l, const 𝕜 E M a (eval 𝕜 E M a (c l)) *
      (g l : (structureSheaf 𝕜 E M).presheaf.stalk a), ?_, ?_⟩
    · refine Subalgebra.add_mem _ hp (Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ ?_ ?_)
      · exact Subalgebra.algebraMap_mem _ (eval 𝕜 E M a (c l))
      · obtain ⟨ν, hν⟩ := (g l).2
        rw [← hν]
        exact Subalgebra.prod_mem _ fun i _ =>
          Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _
    · have h1 : f - (p + ∑ l, const 𝕜 E M a (eval 𝕜 E M a (c l)) *
          (g l : (structureSheaf 𝕜 E M).presheaf.stalk a)) =
          ∑ l, (c l - const 𝕜 E M a (eval 𝕜 E M a (c l))) *
            (g l : (structureSheaf 𝕜 E M).presheaf.stalk a) := by
        simp only [sub_mul, Finset.sum_sub_distrib, ← hsum']
        ring
      rw [h1, pow_succ']
      refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_mul ?_ ?_
      · exact (mem_maximalIdeal_iff_eval E _).mpr (by rw [map_sub, eval_const, sub_self])
      · rw [maximalIdeal_pow_eq_span_monomials' E ψ φ ha hφ k]
        exact Ideal.subset_span (g l).2

/-- Every `𝕜`-derivation `δ` of the stalk is `δ = ∑_i δ(x_i − x_i(a)) ∂_i` (the condition
`SpansDerivations 𝕜`; Kollár's "`∂/∂x_1, …, ∂/∂x_n` are local generators of `Der_X`"
[Kol07, Definition 73]), by the uniqueness of Taylor coefficients:
`δ' = δ − ∑_i δ(x_i − x_i(a)) ∂_i` kills the polynomials in the coordinates and lowers the order,
so `δ' f ∈ ⋂_k 𝔪_a^k = 0`. -/
theorem derivation_eq_sum_coordDerivStalk
    (δ : Derivation 𝕜 ((structureSheaf 𝕜 E M).presheaf.stalk a)
      ((structureSheaf 𝕜 E M).presheaf.stalk a))
    (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    δ s = ∑ i, δ (centredCoord E ψ φ hφ ha i) * coordDerivStalk E ψ φ hφ ha i s := by
  set δ' : Derivation 𝕜 ((structureSheaf 𝕜 E M).presheaf.stalk a)
      ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
    δ - ∑ i, δ (centredCoord E ψ φ hφ ha i) • coordDerivStalk E ψ φ hφ ha i with hδ'
  have hδ'x : ∀ j, δ' (centredCoord E ψ φ hφ ha j) = 0 := by
    intro j
    rw [hδ', Derivation.sub_apply, derivation_sum_apply, sub_eq_zero]
    simp only [Derivation.smul_apply, smul_eq_mul, coordDerivStalk_centredCoord, mul_boole,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hδ'poly : ∀ p ∈ Algebra.adjoin 𝕜 (Set.range (centredCoord E ψ φ hφ ha)), δ' p = 0 := by
    intro p hp
    induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨j, rfl⟩ := hp
      exact hδ'x j
    | algebraMap r => exact Derivation.map_algebraMap δ' r
    | add p q _ _ hp hq => rw [map_add, hp, hq, add_zero]
    | mul p q _ _ hp hq => rw [Derivation.leibniz, hp, hq, smul_zero, smul_zero, add_zero]
  have hδ'zero : ∀ f, δ' f = 0 := by
    intro f
    refine eq_zero_of_forall_mem_maximalIdeal_pow E ψ φ hφ ha _ fun k => ?_
    obtain ⟨p, hp, hfp⟩ := exists_mem_adjoin_sub_mem_maximalIdeal_pow E ψ φ hφ ha (k + 1) f
    have h1 := Derivation.mem_pow_of_mem_pow_succ _ δ' k hfp
    rwa [map_sub, hδ'poly p hp, sub_zero] at h1
  have h2 := hδ'zero s
  rw [hδ', Derivation.sub_apply, sub_eq_zero, derivation_sum_apply] at h2
  simpa only [Derivation.smul_apply, smul_eq_mul] using h2

/-- Given that `𝒪_{M,a}` is a regular local ring of dimension `n`, the stalk carries the regular
coordinates `RegularCoords` of the `Hironaka` library, with `x_i` the centred coordinate germs and
`∂_i` the partial derivatives of the chart, `𝕜`-linear (`IsLinearOver 𝕜`) and spanning the
`𝕜`-derivations (`SpansDerivations 𝕜`). -/
theorem exists_regularCoords_stalk [IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk a)]
    (hdim : (n : WithBot ℕ∞) = ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk a)) :
    ∃ c : RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk a) n,
      (∀ i, c.x i = centredCoord E ψ φ hφ ha i) ∧
        (∀ i, c.pderiv i = (coordDerivStalk E ψ φ hφ ha i).restrictScalars ℚ) ∧
          c.IsLinearOver 𝕜 ∧ c.SpansDerivations 𝕜 :=
  ⟨{ x := centredCoord E ψ φ hφ ha
     pderiv := fun i => (coordDerivStalk E ψ φ hφ ha i).restrictScalars ℚ
     span_x := maximalIdeal_eq_span_coord' E ψ φ ha hφ
     card := hdim
     pderiv_x := fun i j => by
       rw [Derivation.restrictScalars_apply, coordDerivStalk_centredCoord]
     pderiv_comm := fun i j f => by
       simp only [Derivation.restrictScalars_apply]
       exact coordDerivStalk_comm E ψ φ hφ ha i j f },
    fun _ => rfl, fun _ => rfl,
    fun i c => by simp only [Derivation.restrictScalars_apply, Derivation.map_algebraMap],
    fun δ f => derivation_eq_sum_coordDerivStalk E ψ φ hφ ha δ f⟩

end Manifold

end
