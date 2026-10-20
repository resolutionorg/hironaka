/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.RegularSmooth.Regular
import Hironaka.Algebra.RegularSmooth.RegularImpliesSmooth
import Hironaka.Algebra.RegularSmooth.SchemeForms

/-!
# Regular equals smooth over a perfect field

The scheme form of [Sta, Tag 00TV] with [Sta, Tag 00TT] (see also [Sta, Tag 038X]): for `X`
locally of finite type over a perfect field `k`, the smooth locus of `X → Spec k` is exactly the set
of regular points, and `X → Spec k` is smooth iff `X` is regular. Smooth implies regular is
`Scheme.isRegularAt_of_mem_smoothLocus` (`SchemeForms.lean`); regular implies smooth reduces,
through an affine open neighbourhood `U` of the point and the affine forms of `Regular.lean` and
`SmoothAt.lean` (`x ∈ f.smoothLocus` iff `Γ(X, U)` is smooth at the prime of `x`; `X` regular at
`x` iff that localization is a regular local ring), to the affine statement
`Algebra.IsSmoothAt.of_isRegularLocalRing_of_perfectField`.
The global statement is the pointwise one with Mathlib's `Scheme.Hom.smoothLocus_eq_top_iff`
(finite type over the Noetherian `Spec k` is finite presentation); see also `SingularLocus.lean`.
-/

public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- For `X` locally of finite type over a perfect field `k`, a point lies in the smooth locus of
`X → Spec k` iff it is a regular point ([Sta, Tag 00TV] with [Sta, Tag 00TT]; see also
[Sta, Tag 038X]). -/
theorem Scheme.mem_smoothLocus_iff_isRegularAt [PerfectField k] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) : x ∈ f.smoothLocus ↔ X.IsRegularAt x := by
  refine ⟨Scheme.isRegularAt_of_mem_smoothLocus f, fun hx => ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := f.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_sectionsAlgebra hU
  rw [Scheme.isRegularAt_iff_isRegularLocalRing_localization hU hxU] at hx
  rw [f.mem_smoothLocus_iff_isSmoothAt hU hxU]
  exact Algebra.IsSmoothAt.of_isRegularLocalRing_of_perfectField (k := k)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal

/-- Over a perfect field `k`, `X → Spec k` locally of finite type is smooth iff `X` is regular. -/
theorem Scheme.smooth_iff_isRegular [PerfectField k] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] : Smooth f ↔ IsRegular X := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, isRegular_iff, eq_top_iff]
  constructor
  · intro h x
    exact (Scheme.mem_smoothLocus_iff_isRegularAt f x).mp
      (IsConcreteLE.le_iff.mp h (TopologicalSpace.Opens.mem_top x))
  · intro h
    exact IsConcreteLE.le_iff.mpr fun x _ => (Scheme.mem_smoothLocus_iff_isRegularAt f x).mpr (h x)

end AlgebraicGeometry
