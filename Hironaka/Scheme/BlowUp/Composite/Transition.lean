/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
public import Hironaka.Scheme.BlowUp.Transition
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.InverseImage
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Chart transitions of the ideals of `J'` and the exponent of Hironaka's `J(m)`

The cross-chart step in the proof that `K_m.comap b = J' · E^m` for `m` large
(`Hironaka.Scheme.BlowUp.Composite.Main`).  A generator `g = y/a^n` (`y ∈ I^n`) of the ideal `J'_a`
of `J'` on the chart of `a` is, on the chart of `c`, the fraction `y/c^n` times the unit
`(a/c)^{-n}` of the overlap `D(a/c)`; since `J'_a` and `J'_c` cut out the same ideal sheaf on the
overlap, `y/c^n` lies in `J'_c` after multiplication by a power of `a/c`: there is `N` with
`(a/c)^N · (y/c^n) ∈ J'_c`.

* Ring level (`R` any commutative ring, `a, c ∈ I`): `fracPow I n hy = y/a^n ∈ R[I/a]`;
  `transitionHom_fracPow`: the transition `R[I/a] → R[I/a]_{c/a} ≃ R[I/c]_{a/c}` of
  `Hironaka.Scheme.BlowUp.Transition` sends `y/a^n` to `(y/c^n)·(a/c)^{-n}` — proved through the
  common embedding into `R_{ca}`;
  `exists_pow_frac_mul_mem`: from an identity `P·R[I/c]_{a/c} = Q·R[I/c]_{a/c}` of the transported
  ideals, the exponent for the elements `y/a^n ∈ P`.
* Scheme level: the two inclusions of the overlap `Spec R[I/c]_{a/c}` into the blow-up — through
  the chart of `c` and, via the transition, through the chart of `a` — are equal (`blowUp.hom_ext`:
  both are admissible morphisms over `X`), so the inverse images of `J'` agree:
  `chartIdeal_map_transition`, the identity `J'_a·R[I/c]_{a/c} = J'_c·R[I/c]_{a/c}`.

The charts of an affine blow-up glue along the localizations `R_{g_j}, R_{g_l} ⊆ R_{g_j g_l}`
[Hau14, Definition 4.13].  The overlap computations are also used for the stalks along the
exceptional divisor (`Hironaka.Scheme.IdealSheaf.Order.ExceptionalOrder`,
`Hironaka.Scheme.Snc.ChartStalk`).
-/

@[expose] public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

namespace affineBlowUpAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R) {a c : R}

/-- The fraction `y/aⁿ ∈ R[I/a]` for `y ∈ Iⁿ`. -/
noncomputable def fracPow (n : ℕ) {y : R} (hy : y ∈ I ^ n) : affineBlowUpAlgebra I a :=
  ⟨awayFrac a n y, awayFrac_mem_affineBlowUpAlgebra n hy⟩

theorem coe_fracPow (n : ℕ) {y : R} (hy : y ∈ I ^ n) :
    ((fracPow I n hy : affineBlowUpAlgebra I a) : Localization.Away a) = awayFrac a n y := rfl

theorem awayFrac_mul_algebraMap_pow (n : ℕ) (y : R) :
    awayFrac a n y * algebraMap R (Localization.Away a) (a ^ n) =
      algebraMap R (Localization.Away a) y := by
  unfold awayFrac
  rw [Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec _ _ _

/-- The image of `y/aⁿ` in `R_{c'}` (`a ∣ c'`) times `aⁿ` is `y`. -/
theorem toAway_fracPow_mul {c' : R} (hac : a ∣ c') (n : ℕ) {y : R} (hy : y ∈ I ^ n) :
    toAway I hac (fracPow I n hy) * algebraMap R (Localization.Away c') a ^ n =
      algebraMap R (Localization.Away c') y := by
  rw [toAway, AlgHom.comp_apply, Subalgebra.coe_val]
  change awayToAwayₐ a c' hac (awayFrac a n y) * _ = _
  rw [← map_pow, ← awayToAwayₐ_algebraMap a c' hac, ← map_mul, awayFrac_mul_algebraMap_pow,
    awayToAwayₐ_algebraMap]

variable (ha : a ∈ I) (hc : c ∈ I)

/-- The transition `R[I/a] → R[I/a]_{c/a} ≃ R[I/c]_{a/c}` (`Hironaka.Scheme.BlowUp.Transition`) as
an `R`-algebra map into the overlap ring of the charts of `a` and `c`, in the coordinates of the
chart of `c`. -/
noncomputable def transitionHom :
    affineBlowUpAlgebra I a →ₐ[R] Localization.Away (frac (a := c) ha) :=
  ((transitionEquiv I hc ha).symm : Localization.Away (frac (a := a) hc) →ₐ[R]
      Localization.Away (frac (a := c) ha)).comp
    (IsScalarTower.toAlgHom R (affineBlowUpAlgebra I a) (Localization.Away (frac (a := a) hc)))

theorem transitionHom_apply (z : affineBlowUpAlgebra I a) :
    transitionHom I ha hc z = (transitionEquiv I hc ha).symm
      (algebraMap (affineBlowUpAlgebra I a) (Localization.Away (frac (a := a) hc)) z) := rfl

/-- The transition on the fraction `y/aⁿ`: it is `(y/cⁿ) · (a/c)⁻ⁿ`, i.e.
`τ(y/aⁿ) · (a/c)ⁿ = y/cⁿ`.  Checked after the injective embedding into `R_{ca}`, where both sides
are `y · c⁻ⁿ`. -/
theorem transitionHom_fracPow (n : ℕ) {y : R} (hy : y ∈ I ^ n) :
    transitionHom I ha hc (fracPow I n hy) *
      algebraMap (affineBlowUpAlgebra I c) (Localization.Away (frac (a := c) ha))
        (frac (a := c) ha) ^ n =
    algebraMap (affineBlowUpAlgebra I c) (Localization.Away (frac (a := c) ha))
      (fracPow I n hy) := by
  apply embedAB_injective I ha
  have hu : IsUnit (algebraMap R (Localization.Away (c * a)) c ^ n) :=
    (isUnit_algebraMap_of_dvd (dvd_mul_right c a)).pow n
  apply hu.mul_left_injective
  have h1 : embedAB I ha c (transitionHom I ha hc (fracPow I n hy)) =
      embedBA I hc a (algebraMap (affineBlowUpAlgebra I a) (Localization.Away (frac (a := a) hc))
        (fracPow I n hy)) := by
    rw [transitionHom_apply, ← embedBA_transitionEquiv I hc ha, AlgEquiv.apply_symm_apply]
  change embedAB I ha c (_ * _) * _ = embedAB I ha c _ * _
  rw [map_mul, map_pow, h1, embedBA_algebraMap, embedAB_algebraMap, embedAB_algebraMap,
    mul_assoc, ← mul_pow, toAway_frac_mul I (dvd_mul_right c a) ha,
    toAway_fracPow_mul I (dvd_mul_left a c), toAway_fracPow_mul I (dvd_mul_right c a)]

/-- The exponent at the ring level: if the ideals `P ⊆ R[I/a]` and `Q ⊆ R[I/c]`
generate the same ideal of the overlap ring `R[I/c]_{a/c}` (`P` transported by the transition), then
every `y/aⁿ ∈ P` satisfies `(a/c)^N · (y/cⁿ) ∈ Q` for some `N`. -/
theorem exists_pow_frac_mul_mem {P : Ideal (affineBlowUpAlgebra I a)}
    {Q : Ideal (affineBlowUpAlgebra I c)}
    (hPQ : P.map (transitionHom I ha hc) =
      Q.map (algebraMap (affineBlowUpAlgebra I c) (Localization.Away (frac (a := c) ha))))
    (n : ℕ) {y : R} (hy : y ∈ I ^ n) (hz : fracPow I n hy ∈ P) :
    ∃ N : ℕ, frac (a := c) ha ^ N * fracPow I n hy ∈ Q := by
  set r := frac (a := c) ha with hr
  have h1 := Ideal.mem_map_of_mem (transitionHom I ha hc) hz
  rw [hPQ] at h1
  have h2 : algebraMap (affineBlowUpAlgebra I c) (Localization.Away r) (fracPow I n hy) ∈
      Q.map (algebraMap (affineBlowUpAlgebra I c) (Localization.Away r)) := by
    rw [← transitionHom_fracPow I ha hc n hy]
    exact Ideal.mul_mem_right _ _ h1
  obtain ⟨⟨j, s⟩, hjk⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers r) (Localization.Away r)).mp h2
  have h3 : algebraMap (affineBlowUpAlgebra I c) (Localization.Away r)
      (fracPow I n hy * (s : affineBlowUpAlgebra I c) - (j : affineBlowUpAlgebra I c)) = 0 := by
    rw [map_sub, map_mul, sub_eq_zero]
    exact hjk
  obtain ⟨m, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers r) (Localization.Away r) _).mp h3
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff _ _).mp m.2
  refine ⟨l + k, ?_⟩
  have h4 : r ^ (l + k) * fracPow I n hy = r ^ l * (j : affineBlowUpAlgebra I c) := by
    rw [← hl, ← hk] at hm
    linear_combination hm
  rw [h4]
  exact Ideal.mul_mem_left _ _ j.2

include hc in
/-- `I` extends to the principal ideal `(c)` of the overlap ring `R[I/c]_{a/c}` (as on the chart
of `c`, then localized). -/
theorem map_algebraMap_away_frac :
    I.map (algebraMap R (Localization.Away (frac (a := c) ha))) =
      Ideal.span
        {algebraMap (affineBlowUpAlgebra I c) (Localization.Away (frac (a := c) ha))
          (algebraMap R (affineBlowUpAlgebra I c) c)} := by
  rw [IsScalarTower.algebraMap_eq R (affineBlowUpAlgebra I c)
    (Localization.Away (frac (a := c) ha)), ← Ideal.map_map, map_algebraMap_eq_span_singleton hc,
    Ideal.map_span, Set.image_singleton]

/-- `c` stays a nonzerodivisor in the overlap ring `R[I/c]_{a/c}` (as in `R[I/c]`, then
localization). -/
theorem algebraMap_mem_nonZeroDivisors_away_frac :
    algebraMap (affineBlowUpAlgebra I c) (Localization.Away (frac (a := c) ha))
        (algebraMap R (affineBlowUpAlgebra I c) c) ∈
      nonZeroDivisors (Localization.Away (frac (a := c) ha)) :=
  IsLocalization.map_nonZeroDivisors_le (M := Submonoid.powers (frac (a := c) ha))
    (S := Localization.Away (frac (a := c) ha))
    (Submonoid.mem_map_of_mem _ algebraMap_mem_nonZeroDivisors)

end affineBlowUpAlgebra

section SchemeLevel

variable {X : Scheme.{u}} (I : X.IdealSheafData) (J' : (blowUp I).IdealSheafData)
  (U : X.affineOpens) (a c : I.ideal U)

/-- The inverse image along `Spec ψ ≫ fromSpec_U` of an ideal sheaf `K` on `X` is the ideal sheaf
of `K(U)·S` (through `comap_fromSpec` and `comap_ofIdealTop_Spec_map`). -/
theorem comap_specMap_fromSpec (K : X.IdealSheafData) {S : Type u} [CommRing S]
    (ψ : Γ(X, U) →+* S) :
    K.comap (Spec.map (CommRingCat.ofHom ψ) ≫ U.2.fromSpec) = specIdealSheaf ((K.ideal U).map ψ) :=
  (comap_comp K _ _).trans
    ((congrArg (fun L : (Spec Γ(X, U)).IdealSheafData => L.comap (Spec.map (CommRingCat.ofHom ψ)))
      (comap_fromSpec K U)).trans (comap_ofIdealTop_Spec_map _ _))

theorem comap_specIdealSheaf_Spec_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : Ideal R) :
    (specIdealSheaf P).comap (Spec.map (CommRingCat.ofHom f)) = specIdealSheaf (P.map f) :=
  comap_ofIdealTop_Spec_map (CommRingCat.ofHom f) P

/-- The overlap `D(a/c)` of the charts of `a` and `c`, as the localization of the chart ring of
`c` at `a/c`. -/
noncomputable abbrev overlapRing : Type u :=
  Localization.Away (affineBlowUpAlgebra.frac (a := (c : Γ(X, U))) a.2)

/-- A morphism `Spec T ⟶ blowUp I` through the chart of `b` composed with the blow-up map is the
morphism `Spec T ⟶ Spec Γ(X, U) ⟶ X` of the composite ring map. -/
theorem specMap_chart_π {T : Type u} [CommRing T] (χ : Γ(X, U) →+* T) (b : I.ideal U)
    (ψ : affineBlowUpAlgebra (I.ideal U) b →+* T)
    (hψ : ψ.comp (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) b)) = χ) :
    (Spec.map (CommRingCat.ofHom ψ) ≫ blowUp.chart I U b) ≫ blowUpπ I =
      Spec.map (CommRingCat.ofHom χ) ≫ U.2.fromSpec := by
  rw [Category.assoc, blowUp.chart_π, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    hψ]
  rfl

/-- The overlap `Spec R[I/c]_{a/c} ⟶ X` is admissible for `I`: `I` extends to the principal ideal
generated by the nonzerodivisor `c`. -/
theorem isInvertible_comap_overlap :
    (I.comap (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (overlapRing I U a c))) ≫
      U.2.fromSpec)).IsInvertible := by
  rw [comap_specMap_fromSpec, affineBlowUpAlgebra.map_algebraMap_away_frac (I.ideal U) a.2 c.2]
  exact isInvertible_specIdealSheaf_span_singleton
    (affineBlowUpAlgebra.algebraMap_mem_nonZeroDivisors_away_frac (I.ideal U) a.2)

/-- The two inclusions of the overlap `Spec R[I/c]_{a/c}` into the blow-up — through the chart of
`c`, and through the chart of `a` via the transition — agree: both are admissible morphisms over
`X` (`blowUp.hom_ext`). -/
theorem specMap_algebraMap_chart_eq :
    Spec.map (CommRingCat.ofHom
        (algebraMap (affineBlowUpAlgebra (I.ideal U) c) (overlapRing I U a c))) ≫
      blowUp.chart I U c =
    Spec.map (CommRingCat.ofHom
        (affineBlowUpAlgebra.transitionHom (I.ideal U) a.2 c.2).toRingHom) ≫
      blowUp.chart I U a :=
  blowUp.hom_ext I _ (isInvertible_comap_overlap I U a c) _ _
    (specMap_chart_π I U _ c _
      (IsScalarTower.algebraMap_eq Γ(X, U) _ (overlapRing I U a c)).symm)
    (specMap_chart_π I U _ a _ (AlgHom.comp_algebraMap _))

/-- The chart ideals of `J'` on the charts of `a` and `c` generate the same ideal of the overlap
ring `R[I/c]_{a/c}`, the ideal of `a` transported by the transition: each localizes to the ideal
of `J'` on the overlap `D(a/c)`. -/
theorem chartIdeal_map_transition :
    (chartIdeal I J' U a).map (affineBlowUpAlgebra.transitionHom (I.ideal U) a.2 c.2) =
      (chartIdeal I J' U c).map
        (algebraMap (affineBlowUpAlgebra (I.ideal U) c) (overlapRing I U a c)) := by
  have h := congrArg (fun φ => J'.comap φ) (specMap_algebraMap_chart_eq I U a c)
  have h1 : J'.comap (Spec.map (CommRingCat.ofHom
      (algebraMap (affineBlowUpAlgebra (I.ideal U) c) (overlapRing I U a c))) ≫
        blowUp.chart I U c) =
      specIdealSheaf ((chartIdeal I J' U c).map
        (algebraMap (affineBlowUpAlgebra (I.ideal U) c) (overlapRing I U a c))) :=
    (comap_comp J' _ _).trans
      ((congrArg (fun L : (Spec (.of (affineBlowUpAlgebra (I.ideal U) c))).IdealSheafData =>
        L.comap _) (comap_chart_eq_specIdealSheaf I J' U c)).trans
          (comap_specIdealSheaf_Spec_map _ _))
  have h2 : J'.comap (Spec.map (CommRingCat.ofHom
      (affineBlowUpAlgebra.transitionHom (I.ideal U) a.2 c.2).toRingHom) ≫
        blowUp.chart I U a) =
      specIdealSheaf ((chartIdeal I J' U a).map
        (affineBlowUpAlgebra.transitionHom (I.ideal U) a.2 c.2).toRingHom) :=
    (comap_comp J' _ _).trans
      ((congrArg (fun L : (Spec (.of (affineBlowUpAlgebra (I.ideal U) a))).IdealSheafData =>
        L.comap _) (comap_chart_eq_specIdealSheaf I J' U a)).trans
          (comap_specIdealSheaf_Spec_map _ _))
  exact (specIdealSheaf_inj (h2.symm.trans (h.symm.trans h1)))

end SchemeLevel

end AlgebraicGeometry
