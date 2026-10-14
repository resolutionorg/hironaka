/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.ChartLocal
public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Algebra.Local.Chart
public import Hironaka.Algebra.Local.ChartSubst
public import Hironaka.Algebra.Local.CohenIso
public import Hironaka.Algebra.Local.CompletionMap
import Hironaka.Algebra.Local.ChartShift
import Hironaka.Algebra.Local.Transform
import Hironaka.Algebra.Local.TransformOrder
import Mathlib.Combinatorics.Matroid.Init

/-!
# Lemma 61 in local form: the order bounds at the rational points of the chart

[Kol07, Lemma 61]: for `I ≤ Pᵐ` with `ord_R I = m`, the transform `π⁻¹_*(I, m)` has order `≤ m` at
every point of the chart over `𝔪` rational over the residue field `K`. Kollár's proof computes at
the origin of the chart and moves the origin by a linear change of coordinates. Here the
computation at the origin is done through the completion: the map `R̂ → B̂` induced by
`φ : R → B = R'_{𝔪'}`, the local ring of the chart ring `R'` at the chart origin `𝔪' = (y)`, is the
chart substitution `xᵢ ↦ yᵢ y_r` (`i < r`), `xⱼ ↦ yⱼ` (`j ≥ r`) under the Cohen isomorphisms of `R̂`
and `B̂` (the predicate `HasCohenChart`, proved in `Hironaka/Algebra/Local/ChartCompletion.lean`),
and the order bound then follows from `ordElem_le_of_completionMap_eq_subst` of
`Hironaka/Algebra/Local/TransformOrder.lean`. At the other `K`-rational points `𝔪'_a` of the chart
(`chartOriginAt`), the same statement holds for the shifted coordinates `x' = shiftCoords x r a`
of `Hironaka/Algebra/Local/ChartRing.lean`, transported along the isomorphism `R'_{𝔪'(x')} ≃
R'_{𝔪'_a}` of `Hironaka/Algebra/Local/ChartShift.lean`.

Main results, all under the hypothesis `HasCohenChart` (for `x`, or for the shifted coordinates):

* `ord_{R'_{𝔪'}} π⁻¹_*(f, m) ≤ m` for `f ∈ I` of order `m`
  (`ordElem_transformElem_le_of_hasCohenChart`);
* `ord_{R'_{𝔪'}} π⁻¹_*(I, m) ≤ m` (`ord_map_transformIdeal_le_of_hasCohenChart`);
* the same bound at `𝔪'_a` (`ord_map_transformIdeal_le_at_of_hasCohenChart`) and hence at every
  `K`-rational point of the chart over `𝔪`
  (`ord_map_transformIdeal_le_of_rational_of_hasCohenChart`).

Also here: `R → R'_{𝔪'}` and `R → R'_{𝔪'_a}` are local homomorphisms
(`isLocalHom_algebraMap_atPrime_chartOrigin`, `isLocalHom_algebraMap_atPrime_chartOriginAt`); the
residue field of `R'_{𝔪'}` is `K` (`residueField_map_bijective_chartOrigin`); and the coefficient
field of `R̂` is transported to a coefficient field of `(R'_{𝔪'})^` along the induced map
(`chartCoefficientField`, `residue_chartCoefficientField`), the datum on which the Cohen
isomorphism of `(R'_{𝔪'})^` is built in `Hironaka/Algebra/Local/ChartCompletion.lean`.

The bound at every prime of the fibre, rational or not, is obtained by a different argument in
`Hironaka/Algebra/Local/ChartFibre.lean`. Used in
`Hironaka/Resolution/Analytic/GoingUp/MaxOrder.lean`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

section Local

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (x : Fin n → R) (r : Fin n)

omit [Algebra ℚ R] in
/-- `R → R'_{𝔪'}` is a local homomorphism: `𝔪'` lies over `𝔪`. -/
theorem isLocalHom_algebraMap_atPrime_chartOrigin (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) [(chartOrigin x r).IsPrime] :
    IsLocalHom (algebraMap R (Localization.AtPrime (chartOrigin x r))) := by
  refine ((local_hom_TFAE _).out 5 1).mp ?_
  have h1 : (maximalIdeal (Localization.AtPrime (chartOrigin x r))).comap
      (algebraMap (chartRing x r) (Localization.AtPrime (chartOrigin x r))) = chartOrigin x r := by
    rw [← Ideal.under_def]
    exact IsLocalization.AtPrime.under_maximalIdeal
      (S := Localization.AtPrime (chartOrigin x r)) (I := chartOrigin x r) inferInstance
  rw [IsScalarTower.algebraMap_eq R (chartRing x r), ← Ideal.comap_comap, h1,
    comap_chartOrigin x r hx hn]

omit [Algebra ℚ R] in
/-- `R → R'_{𝔪'_a}` is a local homomorphism: `𝔪'_a` lies over `𝔪`. -/
theorem isLocalHom_algebraMap_atPrime_chartOriginAt (a : Fin n → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
    [(chartOriginAt x r a).IsPrime] :
    IsLocalHom (algebraMap R (Localization.AtPrime (chartOriginAt x r a))) := by
  refine ((local_hom_TFAE _).out 5 1).mp ?_
  have h1 : (maximalIdeal (Localization.AtPrime (chartOriginAt x r a))).comap
      (algebraMap (chartRing x r) (Localization.AtPrime (chartOriginAt x r a))) =
        chartOriginAt x r a := by
    rw [← Ideal.under_def]
    exact IsLocalization.AtPrime.under_maximalIdeal
      (S := Localization.AtPrime (chartOriginAt x r a)) (I := chartOriginAt x r a) inferInstance
  rw [IsScalarTower.algebraMap_eq R (chartRing x r), ← Ideal.comap_comap, h1,
    comap_chartOriginAt x r a hx hn]

omit [Algebra ℚ R] in
/-- The residue field of the chart's local ring `R'_{𝔪'}` is `K = R/𝔪`: `R'/𝔪' ≅ R/𝔪`
(`quotientMap_chartOrigin_bijective`), and the residue field of a localization at a maximal ideal
is the quotient; so `ResidueField.map (R → R'_{𝔪'})` is bijective. -/
theorem residueField_map_bijective_chartOrigin (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) [(chartOrigin x r).IsPrime] :
    haveI := isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn
    Function.Bijective
      (ResidueField.map (algebraMap R (Localization.AtPrime (chartOrigin x r)))) := by
  have := isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn
  have hmax := chartOrigin_isMaximal x r hx hn
  have h1 := quotientMap_chartOrigin_bijective x r hx hn
  have h2 := Ideal.bijective_algebraMap_quotient_residueField (chartOrigin x r)
  have hfun : ⇑(ResidueField.map (algebraMap R (Localization.AtPrime (chartOrigin x r)))) =
      ⇑(algebraMap (chartRing x r ⧸ chartOrigin x r) (chartOrigin x r).ResidueField) ∘
        ⇑(Ideal.quotientMap (chartOrigin x r) (algebraMap R (chartRing x r))
          (maximalIdeal_le_comap_chartOrigin x r hx)) := by
    funext k
    obtain ⟨a, rfl⟩ := residue_surjective k
    rw [ResidueField.map_residue]
    change _ = algebraMap (chartRing x r ⧸ chartOrigin x r) (chartOrigin x r).ResidueField
      (Ideal.quotientMap (chartOrigin x r) (algebraMap R (chartRing x r))
        (maximalIdeal_le_comap_chartOrigin x r hx) (Ideal.Quotient.mk (maximalIdeal R) a))
    rw [Ideal.quotientMap_mk, Ideal.algebraMap_quotient_residueField_mk,
      IsScalarTower.algebraMap_apply R (chartRing x r) (Localization.AtPrime (chartOrigin x r)) a]
    rfl
  rw [hfun]
  exact h2.comp h1

/-- The coefficient field on the completion of `B = R'_{𝔪'}` transported from `R̂` along the
induced map: `ι_B := φ̂ ∘ σ_R ∘ e⁻¹`, with `σ_R` the coefficient field of `R̂` and `e : K ≃ K_B` the
isomorphism of residue fields. -/
noncomputable def chartCoefficientField (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) [(chartOrigin x r).IsPrime] :
    ResidueField (Localization.AtPrime (chartOrigin x r)) →+*
      AdicCompletion (maximalIdeal (Localization.AtPrime (chartOrigin x r)))
        (Localization.AtPrime (chartOrigin x r)) :=
  have := isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn
  ((completionMap (algebraMap R (Localization.AtPrime (chartOrigin x r)))).comp
    (coefficientField R)).comp
    (RingEquiv.ofBijective _ (residueField_map_bijective_chartOrigin x r hx hn)).symm

/-- The transported datum is a coefficient field: it is a section of the residue map of
`(R'_{𝔪'})^`, as the Cohen isomorphism `cohenEquivOfResidue` requires. -/
theorem residue_chartCoefficientField (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) [(chartOrigin x r).IsPrime]
    (k : ResidueField (Localization.AtPrime (chartOrigin x r))) :
    haveI : IsNoetherianRing (chartRing x r) := isNoetherianRing_chartRing x r
    residue _ (chartCoefficientField x r hx hn k) =
      residueFieldEquiv (Localization.AtPrime (chartOrigin x r)) k := by
  have := isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn
  have : IsNoetherianRing (chartRing x r) := isNoetherianRing_chartRing x r
  exact residue_completionMap_coefficientField _
    (residueField_map_bijective_chartOrigin x r hx hn) k

/-- There is a Cohen isomorphism `Ψ : K⟦y⟧ ≃ B̂` of the completion of `B = R'_{𝔪'}` under which
the map induced by `R → B` is the chart substitution `xᵢ ↦ yᵢ y_r` (`i < r`), `xⱼ ↦ yⱼ` (`j ≥ r`) of
[Kol07, (60.3)]. Proved in `Hironaka/Algebra/Local/ChartCompletion.lean` (`hasCohenChart`). -/
def HasCohenChart (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) [(chartOrigin x r).IsPrime] : Prop :=
  have := isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn
  ∃ Ψ : MvPowerSeries (Fin n) (ResidueField R) ≃+*
      AdicCompletion (maximalIdeal (Localization.AtPrime (chartOrigin x r)))
        (Localization.AtPrime (chartOrigin x r)),
    ∀ F, completionMap (algebraMap R (Localization.AtPrime (chartOrigin x r)))
      (cohenEquiv R x hx hn F) = Ψ (subst (chartSubst r) F)

/-- (The proof of [Kol07, Lemma 61].) Given `HasCohenChart`, for `I ≤ Pᵐ` and `f ∈ I` of order
`m`, `ord_{R'_{𝔪'}} π⁻¹_*(f, m) ≤ m`. -/
theorem ordElem_transformElem_le_of_hasCohenChart (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) [(chartOrigin x r).IsPrime]
    (hΨ : HasCohenChart x r hx hn) {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m) {f : R}
    (hf : f ∈ I) (hord : ordElem f = m) :
    ordElem (algebraMap (chartRing x r) (Localization.AtPrime (chartOrigin x r))
      (transformElem x r f (hI hf))) ≤ m := by
  have := isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn
  have : IsNoetherianRing (chartRing x r) := isNoetherianRing_chartRing x r
  obtain ⟨Ψ, hΨ⟩ := hΨ
  refine ordElem_le_of_completionMap_eq_subst x hx hn r _ Ψ hΨ (hI hf) hord ?_
  rw [IsScalarTower.algebraMap_apply R (chartRing x r) (Localization.AtPrime (chartOrigin x r))
    (x r), ← map_pow, ← map_mul, algebraMap_pow_mul_transformElem]
  exact (IsScalarTower.algebraMap_apply R (chartRing x r) _ f).symm

/-- Kollár's "This shows that `ord_{p'} π⁻¹_* I ≤ m`" (the proof of [Kol07, Lemma 61]), given
`HasCohenChart`: for `I ≤ Pᵐ` with `ord I = m`, `ord_{R'_{𝔪'}} π⁻¹_*(I, m) ≤ m`. -/
theorem ord_map_transformIdeal_le_of_hasCohenChart (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) [(chartOrigin x r).IsPrime]
    (hΨ : HasCohenChart x r hx hn) {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m)
    (hord : ord I = m) :
    ord ((transformIdeal x r I m).map
      (algebraMap (chartRing x r) (Localization.AtPrime (chartOrigin x r)))) ≤ m :=
  ord_map_transformIdeal_le_of_forall x r hI hord _ fun _ hf hfm =>
    ordElem_transformElem_le_of_hasCohenChart x r hx hn hΨ hI hf hfm

set_option maxHeartbeats 400000 in
-- Since Mathlib v4.34.0, unifying `Ψ.trans (completionEquiv _)` with the expected completion map
-- takes slightly over the default 200000 heartbeats.
/-- The same bound at the `K`-rational point `𝔪'_a` of the chart (Kollár's linear change of
coordinates moving the origin, in the proof of [Kol07, Lemma 61]), given `HasCohenChart` for the
shifted coordinates `x'`: through the isomorphism `R'_{𝔪'(x')} ≃ R'_{𝔪'_a}` of
`Hironaka/Algebra/Local/ChartShift.lean`; the transform `π⁻¹_*(f, m)` satisfies the same equation
`x_rᵐ g = f` in both. -/
theorem ord_map_transformIdeal_le_at_of_hasCohenChart (a : Fin n → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
    [(chartOriginAt x r a).IsPrime] [(chartOrigin (shiftCoords x r a) r).IsPrime]
    (hΨ : HasCohenChart (shiftCoords x r a) r (span_range_shiftCoords x r a hx) hn)
    {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m) (hord : ord I = m) :
    ord ((transformIdeal x r I m).map
      (algebraMap (chartRing x r) (Localization.AtPrime (chartOriginAt x r a)))) ≤ m := by
  have := isLocalHom_algebraMap_atPrime_chartOriginAt x r a hx hn
  have := isLocalHom_algebraMap_atPrime_chartOrigin (shiftCoords x r a) r
    (span_range_shiftCoords x r a hx) hn
  have : IsNoetherianRing (chartRing x r) := isNoetherianRing_chartRing x r
  have : IsNoetherianRing (chartRing (shiftCoords x r a) r) :=
    isNoetherianRing_chartRing (shiftCoords x r a) r
  obtain ⟨Ψ, hΨ⟩ := hΨ
  refine ord_map_transformIdeal_le_of_forall x r hI hord _ fun f hf hfm => ?_
  have hI' : I ≤ chartCenter (shiftCoords x r a) r ^ m := by rwa [chartCenter_shiftCoords]
  have hcomp : (localizationEquivShift x r a :
      Localization.AtPrime (chartOrigin (shiftCoords x r a) r) →+*
        Localization.AtPrime (chartOriginAt x r a)).comp
      (algebraMap R (Localization.AtPrime (chartOrigin (shiftCoords x r a) r))) =
      algebraMap R (Localization.AtPrime (chartOriginAt x r a)) :=
    RingHom.ext (localizationEquivShift_algebraMap_R x r a)
  have hcm : (completionMap (localizationEquivShift x r a :
        Localization.AtPrime (chartOrigin (shiftCoords x r a) r) →+*
          Localization.AtPrime (chartOriginAt x r a))).comp
        (completionMap
          (algebraMap R (Localization.AtPrime (chartOrigin (shiftCoords x r a) r)))) =
      completionMap (algebraMap R (Localization.AtPrime (chartOriginAt x r a))) := by
    refine completionMap_unique _ _ fun k z => ?_
    rw [RingHom.comp_apply, evalₐ_completionMap, evalₐ_completionMap]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) k z)
    rw [← hy, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    exact congrArg (Ideal.Quotient.mk _) (congrArg (fun g => g y) hcomp)
  refine ordElem_le_of_completionMap_eq_subst (shiftCoords x r a) (span_range_shiftCoords x r a hx)
    hn r (algebraMap R (Localization.AtPrime (chartOriginAt x r a)))
    (Ψ.trans (completionEquiv (localizationEquivShift x r a))) (fun F => ?_) (hI' hf) hfm ?_
  · rw [← hcm, RingHom.comp_apply, hΨ]
    rfl
  · rw [shiftCoords_self, IsScalarTower.algebraMap_apply R (chartRing x r)
      (Localization.AtPrime (chartOriginAt x r a)) (x r), ← map_pow, ← map_mul,
      algebraMap_pow_mul_transformElem]
    exact (IsScalarTower.algebraMap_apply R (chartRing x r) _ f).symm

/-- [Kol07, Lemma 61] in local form: the bound at every `K`-rational point `q = 𝔪'_a` of the
chart over `𝔪`, given `HasCohenChart` for the shifted coordinates. -/
theorem ord_map_transformIdeal_le_of_rational_of_hasCohenChart
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
    (hΨ : ∀ a : Fin n → R,
      haveI := (chartOrigin_isMaximal _ r (span_range_shiftCoords x r a hx) hn).isPrime
      HasCohenChart (shiftCoords x r a) r (span_range_shiftCoords x r a hx) hn)
    (q : Ideal (chartRing x r)) [q.IsPrime] (hq : ∃ a : Fin n → R, q = chartOriginAt x r a)
    {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ m) (hord : ord I = m) :
    ord ((transformIdeal x r I m).map
      (algebraMap (chartRing x r) (Localization.AtPrime q))) ≤ m := by
  obtain ⟨a, rfl⟩ := hq
  have := (chartOrigin_isMaximal _ r (span_range_shiftCoords x r a hx) hn).isPrime
  exact ord_map_transformIdeal_le_at_of_hasCohenChart x r a hx hn (hΨ a) hI hord

end Local

end IsLocalRing
