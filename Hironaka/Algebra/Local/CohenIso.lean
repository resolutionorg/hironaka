/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Cohen
public import Hironaka.Algebra.Local.Order
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.Local.CompletionCoords
import Hironaka.Algebra.Local.PowerSeries
import Hironaka.Algebra.Local.PowerSeriesRegular
import Hironaka.Algebra.Local.RegularSystem
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# `R̂ ≅ K⟦X₁, …, X_d⟧` for a regular local ring containing `ℚ`

The Cohen structure theorem in the form Kollár uses, `Ô_{p,X} ≅ k(p)⟦x₁, …, xₙ⟧`
[Kol07, Definition 55].  With the coefficient field
(`Hironaka/Algebra/Local/CoefficientField.lean`), the map `Φ`
(`Hironaka/Algebra/Local/CohenMap.lean`) and its surjectivity (`Hironaka/Algebra/Local/Cohen.lean`),
what remains is the injectivity of `Φ`, which is where the regularity of `R` enters:

1. `R̂` is Noetherian, as a quotient of `K⟦X⟧` (`isNoetherianRing_adicCompletion`).
2. `dim R̂ = dim R` (`ringKrullDim_adicCompletion_eq`; [Sta, Tag 07NV]): `R → R̂` is flat
   (`AdicCompletion.flat_of_isNoetherian`), hence satisfies going down
   (`Algebra.HasGoingDown.of_flat`); Krull's height formula for a prime lying over a prime
   (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, [Sta, Tag 00ON])
   applied to `𝔪̂` over `𝔪` gives `height 𝔪̂ = height 𝔪 + height (𝔪̂/𝔪R̂)`, and the fibre
   `R̂/𝔪R̂ = K` is a field, so the last term is zero; heights of the maximal ideals are the
   Krull dimensions (`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`).
3. If `Φ(F) = 0` with `F ≠ 0`, then `R̂` is a quotient of `K⟦X⟧/(F)`, whose dimension is at most
   `d − 1` because `F` is a nonzerodivisor of the domain `K⟦X⟧`
   (`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`); but `dim R̂ = dim R = d` by 2 and the
   hypothesis that `x₁, …, x_d` is a regular system of parameters.  So `Φ` is injective.

Consequences: `Φ` is a ring isomorphism (`cohenEquiv`), `R̂` is a regular local ring (from the
regularity of `K⟦X⟧`, `Hironaka/Algebra/Local/PowerSeriesRegular.lean`, by
`IsRegularLocalRing.of_ringEquiv`), and the order is multiplicative on `R` (for `[Algebra ℚ R]`):
`ord_R f = ord_{R̂} (ι f)` (`Hironaka/Algebra/Local/CompletionCoords.lean`) is transported along
`Φ⁻¹` to `K⟦X⟧`, where it is `MvPowerSeries.order` (`MvPowerSeries.ordElem_eq_order`) and
`order (f g) = order f + order g` (`MvPowerSeries.order_mul`).  Neither the general Cohen
structure theorem nor the associated graded ring is used.

Everything is proved for an arbitrary coefficient field `[Algebra (ResidueField R) R̂]` with
`hι : IsCoefficientAlgebra R` (the `…_of_residue` declarations and `cohenEquivOfResidue`; the only
use of `hι` is the surjectivity), then specialized to the chosen coefficient field (`ℚ ⊆ R`).
The completed chart map (`Hironaka/Algebra/Local/ChartCompletion.lean`) applies the general form to
the chart's local ring `R'_{𝔪'}` with the coefficient field transported from `R̂`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

/-! ### Transport of the order along a ring isomorphism of local rings -/

section Transport

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

omit [IsLocalRing A] [IsLocalRing B] in
theorem isLocalHom_ringEquiv (e : A ≃+* B) : IsLocalHom (e : A →+* B) :=
  ⟨fun a ha => by
    have := ha.map (e.symm : B →+* A)
    simpa using this⟩

/-- The order of an element is invariant under a ring isomorphism of local rings
(`ord_le_ord_map` in both directions). -/
theorem ordElem_ringEquiv (e : A ≃+* B) (a : A) : ordElem (e a) = ordElem a := by
  have h1 := isLocalHom_ringEquiv e
  have h2 := isLocalHom_ringEquiv e.symm
  have hmap : ∀ (φ : A →+* B) (a : A), (Ideal.span {a}).map φ = Ideal.span {φ a} := fun φ a => by
    rw [Ideal.map_span, Set.image_singleton]
  have hmap' : ∀ (φ : B →+* A) (b : B), (Ideal.span {b}).map φ = Ideal.span {φ b} := fun φ b => by
    rw [Ideal.map_span, Set.image_singleton]
  refine le_antisymm ?_ ?_
  · have := ord_le_ord_map (e.symm : B →+* A) (Ideal.span {e a})
    rwa [hmap', RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this
  · have := ord_le_ord_map (e : A →+* B) (Ideal.span {a})
    rwa [hmap] at this

end Transport

section Iso

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {d : ℕ}

local notation "R̂" => AdicCompletion (maximalIdeal R) R

/-- `dim R̂ = dim R` [Sta, Tag 07NV], by going down along the flat map `R → R̂` and the
zero-dimensional fibre `R̂/𝔪R̂ = K`. -/
theorem ringKrullDim_adicCompletion_eq [IsNoetherianRing R̂] :
    ringKrullDim R̂ = ringKrullDim R := by
  have : Algebra.HasGoingDown R R̂ := Algebra.HasGoingDown.of_flat
  have : (maximalIdeal R̂).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R R̂)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
    (maximalIdeal R̂)
  have hbot : (maximalIdeal R̂).map
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R R̂))) = ⊥ := by
    rw [← AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.map_quotient_self _
  have hmax : ((maximalIdeal R).map (algebraMap R R̂)).IsMaximal := by
    rw [← AdicCompletion.maximalIdeal_eq_map]
    exact maximalIdeal.isMaximal R̂
  have : Nontrivial (R̂ ⧸ (maximalIdeal R).map (algebraMap R R̂)) := inferInstance
  rw [hbot, Ideal.height_bot, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]

variable [Algebra (ResidueField R) (AdicCompletion (maximalIdeal R) R)]

/-- `R̂` is Noetherian, being a quotient of `K⟦X₁, …, X_d⟧`; for any coefficient field. -/
theorem isNoetherianRing_adicCompletion_of_residue (x : Fin d → R) (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) : IsNoetherianRing R̂ :=
  isNoetherianRing_of_surjective (MvPowerSeries (Fin d) (ResidueField R)) R̂
    (cohenMap' R x hx).toRingHom (cohenMap_surjective_of_residue R x hι hx)

/-- `Φ` is injective when `x₁, …, x_d` is a regular system of parameters: a nonzero kernel would
drop the dimension of the quotient below `d = dim R = dim R̂`.  For any coefficient field.  (The
injectivity half of [Kol07, Definition 55], for which Kollár refers to Shafarevich's textbook.) -/
theorem cohenMap_injective_of_residue (x : Fin d → R) (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R) :
    Function.Injective (cohenMap' R x hx) := by
  have := isNoetherianRing_adicCompletion_of_residue R x hι hx
  have hdim : ringKrullDim R̂ = d := by rw [ringKrullDim_adicCompletion_eq R, hd]
  rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hne
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  rw [ringKrullDim_mvPowerSeries] at h1
  have hker : ∀ a ∈ Ideal.span {F}, (cohenMap' R x hx).toRingHom a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, hF, mul_zero]
  have h2 : ringKrullDim R̂ ≤
      ringKrullDim (MvPowerSeries (Fin d) (ResidueField R) ⧸ Ideal.span {F}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ _ hker)
      (Ideal.Quotient.lift_surjective_of_surjective _ hker
        (cohenMap_surjective_of_residue R x hι hx))
  rw [hdim] at h2
  have h3 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : ℕ) := by
    push_cast
    exact le_trans (add_le_add h2 (le_refl 1)) h1
  have := Nat.cast_le.mp h3
  omega

/-- `Φ : K⟦X₁, …, X_d⟧ ≃ R̂` [Kol07, Definition 55], for any coefficient field (the form used on
the chart's local ring in `Hironaka/Algebra/Local/ChartCompletion.lean`). -/
noncomputable def cohenEquivOfResidue (x : Fin d → R) (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R) :
    MvPowerSeries (Fin d) (ResidueField R) ≃+* R̂ :=
  RingEquiv.ofBijective (cohenMap' R x hx).toRingHom
    ⟨cohenMap_injective_of_residue R x hι hx hd, cohenMap_surjective_of_residue R x hι hx⟩

theorem cohenEquivOfResidue_apply (x : Fin d → R) (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R)
    (F : MvPowerSeries (Fin d) (ResidueField R)) :
    cohenEquivOfResidue R x hι hx hd F = cohenMap' R x hx F := rfl

/-- The completion of a regular local ring with a regular system of parameters `x₁, …, x_d` and a
coefficient field is a regular local ring. -/
theorem isRegularLocalRing_adicCompletion_of_residue (x : Fin d → R) (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R) :
    IsRegularLocalRing R̂ := by
  have := isRegularLocalRing_mvPowerSeries (ResidueField R) d
  exact IsRegularLocalRing.of_ringEquiv (cohenEquivOfResidue R x hι hx hd)

/-- The order of a product is the sum of the orders, for `R` a regular local ring with a regular
system of parameters `x₁, …, x_d` and a coefficient field (used silently by Kollár in property (3)
of [Kol07, Definition 59] and in [Kol07, Theorem 54.2]; a regular local ring is a domain whose
associated graded ring is a polynomial ring, [AM69, 11.22–11.23]). -/
theorem ordElem_mul_of_residue (x : Fin d → R) (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R)
    (f g : R) : ordElem (f * g) = ordElem f + ordElem g := by
  have e := cohenEquivOfResidue R x hι hx hd
  rw [← ordElem_algebraMap_adicCompletion (f * g), ← ordElem_algebraMap_adicCompletion f,
    ← ordElem_algebraMap_adicCompletion g, map_mul,
    ← ordElem_ringEquiv e.symm (algebraMap R R̂ f * algebraMap R R̂ g),
    ← ordElem_ringEquiv e.symm (algebraMap R R̂ f), ← ordElem_ringEquiv e.symm (algebraMap R R̂ g),
    map_mul, MvPowerSeries.ordElem_eq_order, MvPowerSeries.ordElem_eq_order,
    MvPowerSeries.ordElem_eq_order, MvPowerSeries.order_mul]

end Iso

section IsoRat

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra ℚ R] {d : ℕ}

local notation "R̂" => AdicCompletion (maximalIdeal R) R

/-! The specializations at the chosen coefficient field (`ℚ ⊆ R`). -/

/-- `R̂` is Noetherian, being a quotient of `K⟦X₁, …, X_d⟧`. -/
theorem isNoetherianRing_adicCompletion (x : Fin d → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) : IsNoetherianRing R̂ :=
  isNoetherianRing_adicCompletion_of_residue R x (isCoefficientAlgebra_coefficientAlgebra R) hx

/-- `Φ` is injective when `x₁, …, x_d` is a regular system of parameters. -/
theorem cohenMap_injective (x : Fin d → R) (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hd : (d : WithBot ℕ∞) = ringKrullDim R) : Function.Injective (cohenMap' R x hx) :=
  cohenMap_injective_of_residue R x (isCoefficientAlgebra_coefficientAlgebra R) hx hd

/-- `Φ : K⟦X₁, …, X_d⟧ ≃ R̂`, the identification of [Kol07, Definition 55]. -/
noncomputable def cohenEquiv (x : Fin d → R) (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hd : (d : WithBot ℕ∞) = ringKrullDim R) : MvPowerSeries (Fin d) (ResidueField R) ≃+* R̂ :=
  cohenEquivOfResidue R x (isCoefficientAlgebra_coefficientAlgebra R) hx hd

theorem cohenEquiv_apply (x : Fin d → R) (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hd : (d : WithBot ℕ∞) = ringKrullDim R) (F : MvPowerSeries (Fin d) (ResidueField R)) :
    cohenEquiv R x hx hd F = cohenMap' R x hx F := rfl

/-- The completion of a regular local ring containing `ℚ` with a regular system of parameters
`x₁, …, x_d` is a regular local ring. -/
theorem isRegularLocalRing_adicCompletion_of_span (x : Fin d → R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (hd : (d : WithBot ℕ∞) = ringKrullDim R) :
    IsRegularLocalRing R̂ :=
  isRegularLocalRing_adicCompletion_of_residue R x (isCoefficientAlgebra_coefficientAlgebra R) hx
    hd

/-- For `R` a regular local ring containing `ℚ` with a regular system of parameters `x₁, …, x_d`,
the order of a product is the sum of the orders. -/
theorem ordElem_mul_of_span (x : Fin d → R) (hx : maximalIdeal R = Ideal.span (Set.range x))
    (hd : (d : WithBot ℕ∞) = ringKrullDim R) (f g : R) :
    ordElem (f * g) = ordElem f + ordElem g :=
  ordElem_mul_of_residue R x (isCoefficientAlgebra_coefficientAlgebra R) hx hd f g

end IsoRat

section Regular

variable (R : Type*) [CommRing R] [IsRegularLocalRing R]

local notation "R̂" => AdicCompletion (maximalIdeal R) R

variable [Algebra ℚ R]

/-- The completion of a regular local ring containing `ℚ` is a regular local ring, as an
instance: the instance argument of `RegularCoords.adicCompletion`
(`Hironaka/Algebra/Local/CompletionCoords.lean`). -/
instance isRegularLocalRing_adicCompletion : IsRegularLocalRing R̂ := by
  obtain ⟨d, x, hx, hd⟩ := exists_regularSystem R
  exact isRegularLocalRing_adicCompletion_of_span R x hx hd

/-- The order is multiplicative on a regular local ring containing `ℚ`: the hypothesis `hmul` of
the order calculus of `Hironaka/Algebra/Local/Order.lean`, discharged. -/
theorem ordElem_mul_of_algebraRat (f g : R) : ordElem (f * g) = ordElem f + ordElem g := by
  obtain ⟨d, x, hx, hd⟩ := exists_regularSystem R
  exact ordElem_mul_of_span R x hx hd f g

end Regular

end IsLocalRing
