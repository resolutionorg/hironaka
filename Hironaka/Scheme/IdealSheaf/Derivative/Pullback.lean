/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Algebra.Derivative.Extension
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# `D(f^*I) = f^*D(I)` for a smooth morphism `f`

[Kol07, Lemma 74 (4)]: "if `f : Y → X` is smooth, then `D(f^*I) = f^*(D(I))`", for `X` smooth over
the field `k`. For `fX : X ⟶ Spec k` smooth, `f : Y ⟶ X` smooth and an ideal sheaf `I` on `X`, the
derivative of the pullback ideal sheaf `I.comap f` on the `k`-scheme `Y` (structure morphism
`f ≫ fX`) is the pullback of the derivative (`Scheme.IdealSheafData.derivative_comap_of_smooth`),
and likewise for the iterates (`derivativeIter_comap_of_smooth`).

The proof is stalkwise: two ideal sheaves with the same stalks agree (`ext_stalkIdeal`,
`Hironaka/Scheme/BlowUp/Descent.lean`). At `y ∈ Y` with `x = f y`, `A = 𝒪_{X,x} → B = 𝒪_{Y,y}` the
stalk map: `D(I)_x = D(I_x)` (`stalkIdeal_derivative`,
`Hironaka/Scheme/IdealSheaf/Derivative/Sheaf.lean`), `(I.comap f)_y = I_x B` (`stalkIdeal_comap`,
`Hironaka/Scheme/IdealSheaf/StalkIdeal.lean`), so both sides are `D(I_x B)` and `D(I_x) B`, equal by
the affine-local theorem `Ideal.derivative_map_of_formallySmooth` of
`Hironaka/Algebra/Derivative/Extension.lean`: `B` is formally smooth over `A` because the stalk maps
of a smooth morphism are formally smooth (Mathlib's smooth locus, `formallySmooth_stalkMap`), and
`Ω_{A/k}` is finite projective because `A` is a localization of a standard smooth `k`-algebra of
finite type, hence formally smooth over `k` (`formallySmooth_stalk`, so `Ω` is projective) and
essentially of finite type over `k` (`essFiniteType_stalk`, so `Ω` is finite). The `k`-algebra
structures are those induced by `fX` and `f ≫ fX` (`stalkAlgebra`,
`Hironaka/Algebra/RegularSmooth/Stalk.lean`), and `k → 𝒪_{X,x} → 𝒪_{Y,y}` is a scalar tower
(`isScalarTower_stalkAlgebra_stalkMap`).

Used for the étale equivalence and the restriction of hypersurfaces of maximal contact
(`Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquiv.lean`,
`Hironaka/Resolution/Algebraic/MaximalContact/Restrict.lean`,
`Hironaka/Resolution/Algebraic/Kol07/MaximalContactGlobalization.lean`), for the tuning ideal under
pull-back (`Hironaka/Resolution/Algebraic/Tuning/Pullback.lean`), for functoriality
(`Hironaka/Resolution/Algebraic/BoundaryClearing/FunctorialityPullback.lean`) and for the change of
the base field (`Hironaka/Scheme/IdealSheaf/Derivative/BaseChange.lean`).
-/

public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The `k`-algebra structure of `𝒪_{Y,y}` induced by `f ≫ fX` is the one of `𝒪_{X, f y}` induced
by `fX` followed by the stalk map of `f`. -/
theorem Scheme.Hom.stalkMap_comp_algebraMap_stalkAlgebra (fX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    (y : Y) :
    letI := fX.stalkAlgebra (f y)
    letI := (f ≫ fX).stalkAlgebra y
    (f.stalkMap y).hom.comp (algebraMap k (X.presheaf.stalk (f y))) =
      algebraMap k (Y.presheaf.stalk y) := by
  refine RingHom.ext fun c => ?_
  exact Scheme.Hom.germ_stalkMap_apply f (fX ⁻¹ᵁ ⊤) y (show f y ∈ fX ⁻¹ᵁ ⊤ from trivial)
    (fX.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c))

/-- The scalar tower `k → 𝒪_{X, f y} → 𝒪_{Y, y}` for the structures induced by `fX`, `f ≫ fX` and
the stalk map of `f`. -/
theorem Scheme.Hom.isScalarTower_stalkAlgebra_stalkMap (fX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    (y : Y) :
    letI := fX.stalkAlgebra (f y)
    letI := (f ≫ fX).stalkAlgebra y
    letI := (f.stalkMap y).hom.toAlgebra
    IsScalarTower k (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
  letI := fX.stalkAlgebra (f y)
  letI := (f ≫ fX).stalkAlgebra y
  letI := (f.stalkMap y).hom.toAlgebra
  IsScalarTower.of_algebraMap_eq' (Scheme.Hom.stalkMap_comp_algebraMap_stalkAlgebra fX f y).symm

/-- The stalk maps of a smooth morphism are formally smooth (every point lies in the smooth
locus, Mathlib's `Scheme.Hom.smoothLocus_eq_top`), as algebras through the stalk map. -/
theorem Scheme.Hom.formallySmooth_stalkMap (f : Y ⟶ X) [Smooth f] (y : Y) :
    letI := (f.stalkMap y).hom.toAlgebra
    Algebra.FormallySmooth (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) := by
  let _ := (f.stalkMap y).hom.toAlgebra
  have hy : y ∈ f.smoothLocus := by rw [f.smoothLocus_eq_top]; trivial
  exact RingHom.formallySmooth_algebraMap.mp (Scheme.Hom.mem_smoothLocus.mp hy)

/-- The stalk of a scheme smooth over `k` is formally smooth over `k`: it is a localization of a
standard smooth `k`-algebra (`AlgebraicGeometry.exists_affineOpen_isStandardSmooth`). This is the
`[Smooth fX]` form of `AlgebraicGeometry.formallySmooth_stalk` of
`Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean`, which assumes `SmoothOfRelativeDimension n
fX`; the hypothesis here is `Smooth`, so the weaker form is needed. -/
theorem Scheme.Hom.formallySmooth_stalk (fX : X ⟶ Spec (.of k)) [Smooth fX] (x : X) :
    letI := fX.stalkAlgebra x
    Algebra.FormallySmooth k (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, hstd⟩ := exists_affineOpen_isStandardSmooth fX x
  let _ := fX.sectionsAlgebra U
  let _ := fX.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := fX.isScalarTower_sectionsAlgebra_stalk U hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have h1 : Algebra.FormallySmooth k Γ(X, U) :=
    (inferInstance : Algebra.Smooth k Γ(X, U)).formallySmooth
  have h2 : Algebra.FormallySmooth Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallySmooth.of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Algebra.FormallySmooth.comp k Γ(X, U) (X.presheaf.stalk x)

/-- The stalk of a `k`-scheme locally of finite type is essentially of finite type over `k`: a
localization of the finite type `k`-algebra `Γ(X, U)` at the prime of `x`. The
`[LocallyOfFiniteType fX]` form of `AlgebraicGeometry.essFiniteType_stalk` of
`Hironaka/Scheme/Smooth/DifferentialBasis.lean`, which assumes `SmoothOfRelativeDimension n fX`. -/
theorem Scheme.Hom.essFiniteType_stalk (fX : X ⟶ Spec (.of k)) [LocallyOfFiniteType fX] (x : X) :
    letI := fX.stalkAlgebra x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  obtain ⟨U, hxU⟩ := Scheme.IdealSheafData.exists_affineOpens_mem x
  let _ := fX.sectionsAlgebra U.1
  let _ := fX.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := fX.isScalarTower_sectionsAlgebra_stalk U.1 hxU
  have := U.2.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.FiniteType k Γ(X, U.1) := fX.finiteType_sectionsAlgebra U.2
  have : Algebra.EssFiniteType Γ(X, U.1) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp k Γ(X, U.1) (X.presheaf.stalk x)

namespace Scheme.IdealSheafData

variable (fX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [Smooth fX] [Smooth f]

/-- [Kol07, Lemma 74 (4)] ("if `f : Y → X` is smooth, then `D(f^*I) = f^*(D(I))`"): for `X` smooth
over `k` and `f : Y ⟶ X` smooth, the derivative of the pullback ideal sheaf on the `k`-scheme `Y`
(structure morphism `f ≫ fX`) is the pullback of the derivative; stalkwise, `D(I_x B) = D(I_x) B`
for the stalk map `A → B`. -/
theorem derivative_comap_of_smooth (I : X.IdealSheafData) :
    (I.comap f).derivative (f ≫ fX) = (I.derivative fX).comap f := by
  refine ext_stalkIdeal fun y => ?_
  let _ := fX.stalkAlgebra (f y)
  let _ := (f ≫ fX).stalkAlgebra y
  let _ := (f.stalkMap y).hom.toAlgebra
  have := Scheme.Hom.isScalarTower_stalkAlgebra_stalkMap fX f y
  have := f.formallySmooth_stalkMap y
  have := fX.formallySmooth_stalk (f y)
  have := fX.essFiniteType_stalk (f y)
  rw [stalkIdeal_derivative (f ≫ fX) (I.comap f) y, stalkIdeal_comap, stalkIdeal_comap,
    stalkIdeal_derivative fX I (f y)]
  exact Ideal.derivative_map_of_formallySmooth (k := k) (I.stalkIdeal (f y))

/-- The iterates: `Dʳ(f^*I) = f^*(Dʳ(I))`. -/
theorem derivativeIter_comap_of_smooth (r : ℕ) (I : X.IdealSheafData) :
    (I.comap f).derivativeIter (f ≫ fX) r = (I.derivativeIter fX r).comap f := by
  induction r with
  | zero => rfl
  | succ r ih => rw [derivativeIter_succ, derivativeIter_succ, ih, derivative_comap_of_smooth]

end Scheme.IdealSheafData

end AlgebraicGeometry
