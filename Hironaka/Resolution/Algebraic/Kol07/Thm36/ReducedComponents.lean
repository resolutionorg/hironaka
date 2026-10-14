/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Resolution.Algebraic.Smooth.GeometricallyReduced
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.IdealSheaf.Order.Exceptional
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The irreducible components of a reduced Noetherian scheme

Facts about an irreducible component `C` of a reduced Noetherian scheme `X`, used by the resolution
functor of [Kol07, Theorem 36] on reduced equidimensional schemes, where the components may meet.
Mathlib's open neighbourhood `X.irreducibleComponentOpen C`, the complement of the other
components, is a nonempty open subscheme contained in `C` with closure `C`, hence integral
(`isIntegral_irreducibleComponentOpen_of_isReduced`); its generic point is a generic point of `C`
and lies in the smooth locus of `X` over a perfect field (`exists_isGenericPoint_mem_smoothLocus`);
the reduced closed subscheme `X.irreducibleComponentIdeal C` of `C` is integral
(`isIntegral_irreducibleComponent_of_isReduced`), and so is its push-forward along a closed
immersion (`isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced`); the
generic point of `C` pushed along a closed immersion is a generic point of the pushed subscheme
(`isGenericPoint_map_irreducibleComponentIdeal`); and a flat morphism sends the generic point of a
component to the generic point of the component containing its image (`map_genericPoint_eq_of_flat`,
`comap_irreducibleComponentIdeal_le`). No disjointness of the components is assumed.

Mathlib's `irreducibleComponentIdeal C` is the kernel of the inclusion of the open neighbourhood,
so its reducedness is that of a scheme-theoretic image: the kernel of a morphism from a reduced
scheme is radical (`radical_ker_eq_self`), so the image is reduced (`isReduced_image`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme

namespace Hironaka.Resolution

/-! ### The scheme-theoretic image of a reduced scheme is reduced -/

/-- The kernel of a morphism from a reduced scheme is radical: its radical has, on every affine
open `U`, an ideal contained in the radical of `ker (f.app U)`, which is `ker (f.app U)` itself
since the sections of the reduced source form a reduced ring, and the kernel is the largest ideal
sheaf below these kernels (`Scheme.IdealSheafData.le_ofIdeals_iff`). -/
theorem radical_ker_eq_self {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] :
    f.ker.radical = f.ker := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)
  change f.ker.radical ≤ Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (f.app U).hom
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U => ?_
  rw [Scheme.IdealSheafData.radical_ideal]
  intro s hs
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hs
  have h1 : s ^ n ∈ RingHom.ker (f.app U).hom := f.ideal_ker_le U hn
  rw [RingHom.mem_ker, map_pow] at h1
  exact RingHom.mem_ker.mpr (IsNilpotent.eq_zero ⟨n, h1⟩)

/-- The scheme-theoretic image of a morphism from a reduced scheme is reduced
(`radical_ker_eq_self`, `isReduced_subscheme_of_radical_eq_self`). -/
theorem isReduced_image {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] : IsReduced f.image :=
  Hironaka.Smooth.isReduced_subscheme_of_radical_eq_self f.ker (radical_ker_eq_self f)

/-! ### The open neighbourhood of a component -/

variable {X : Scheme.{u}} [IsNoetherian X]

/-- The open neighbourhood of a component is contained in the component: a point outside the other
components lies on its own component, which is `C`. -/
theorem mem_of_mem_irreducibleComponentOpen {C : Set X} {x : X}
    (hx : x ∈ X.irreducibleComponentOpen C) : x ∈ C := by
  by_contra hxC
  refine hx (Set.mem_sUnion.mpr ⟨_root_.irreducibleComponent x,
    ⟨irreducibleComponent_mem_irreducibleComponents x, fun h => ?_⟩, mem_irreducibleComponent⟩)
  exact hxC (Set.mem_singleton_iff.mp h ▸ mem_irreducibleComponent)

/-- The closure of the open neighbourhood of a component is the component (Mathlib's
`closure_sUnion_irreducibleComponents_sdiff_singleton`). -/
theorem closure_irreducibleComponentOpen (C : Set X) (hC : C ∈ irreducibleComponents X) :
    closure ((X.irreducibleComponentOpen C : X.Opens) : Set X) = C :=
  closure_sUnion_irreducibleComponents_sdiff_singleton
    NoetherianSpace.finite_irreducibleComponents C hC

/-- On a reduced Noetherian scheme the open neighbourhood of a component is an integral scheme:
reduced as an open of `X`, irreducible since its closure is the irreducible `C`. -/
theorem isIntegral_irreducibleComponentOpen_of_isReduced [IsReduced X] (C : Set X)
    (hC : C ∈ irreducibleComponents X) : IsIntegral (X.irreducibleComponentOpen C) :=
  have : IrreducibleSpace (X.irreducibleComponentOpen C) :=
    isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_iff_closure.mp ((closure_irreducibleComponentOpen C hC).symm ▸ hC.1))
  isIntegral_of_irreducibleSpace_of_isReduced _

section Field

variable {k : Type u} [Field k] [PerfectField k] [X.Over (Spec (CommRingCat.of k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]

/-- Every component of a reduced scheme of finite type over a perfect field has a generic point in
the smooth locus: the generic point of the integral open neighbourhood of the component is a generic
point of the component (its closure is the component) and a smooth point
(`Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField`). -/
theorem exists_isGenericPoint_mem_smoothLocus [IsReduced X] (C : Set X)
    (hC : C ∈ irreducibleComponents X) :
    ∃ η : X, IsGenericPoint η C ∧ η ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus := by
  have hint := isIntegral_irreducibleComponentOpen_of_isReduced C hC
  refine ⟨(X.irreducibleComponentOpen C).ι (genericPoint (X.irreducibleComponentOpen C)), ?_, ?_⟩
  · have h := (genericPoint_spec (X.irreducibleComponentOpen C)).image
      (X.irreducibleComponentOpen C).ι.continuous
    rwa [Set.image_univ, Scheme.Opens.range_ι, closure_irreducibleComponentOpen C hC] at h
  · have h := ((X.irreducibleComponentOpen C).ι ≫
      (X ↘ Spec (CommRingCat.of k))).genericPoint_mem_smoothLocus_of_perfectField
    rwa [← Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at h

end Field

/-! ### The reduced closed subscheme of a component -/

/-- On a reduced Noetherian scheme the reduced closed subscheme of a component is integral:
irreducible, its support being the irreducible `C`, and reduced as the scheme-theoretic image of
the open neighbourhood of the component (`isReduced_image`). -/
theorem isIntegral_irreducibleComponent_of_isReduced [IsReduced X] (C : Set X)
    (hC : C ∈ irreducibleComponents X) :
    IsIntegral (X.irreducibleComponentIdeal C hC).subscheme := by
  have hred : IsReduced (X.irreducibleComponentIdeal C hC).subscheme := by
    rw [Scheme.irreducibleComponentIdeal_def]
    exact isReduced_image _
  have hirr : IrreducibleSpace (X.irreducibleComponentIdeal C hC).subscheme :=
    irreducibleSpace_subscheme_of_isGenericPoint _
      (hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC))
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The reduced ideal of a component of a reduced Noetherian scheme pushed along a closed immersion
`emb` has an integral subscheme: `V(I_C) → X → A` is a closed immersion from an integral scheme with
kernel `I_C.map emb`. -/
theorem isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced [IsReduced X] (C : Set X)
    (hC : C ∈ irreducibleComponents X) {A : Scheme.{u}} (emb : X ⟶ A) [IsClosedImmersion emb] :
    IsIntegral ((X.irreducibleComponentIdeal C hC).map emb).subscheme := by
  have : IsIntegral (X.irreducibleComponentIdeal C hC).subscheme :=
    isIntegral_irreducibleComponent_of_isReduced C hC
  have h := IsIntegral.of_isIso ((X.irreducibleComponentIdeal C hC).subschemeι ≫ emb).toImage
  exact h

/-- The support of the reduced ideal of a component is the component. -/
theorem support_irreducibleComponentIdeal' (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    ((X.irreducibleComponentIdeal Z hZ).support : Set X) = Z :=
  rfl

/-- The generic point of a component `C` of `X`, pushed along a closed immersion `emb`, is the
generic point of the support of the reduced ideal of `C` pushed to the ambient. -/
theorem isGenericPoint_map_irreducibleComponentIdeal (C : Set X) (hC : C ∈ irreducibleComponents X)
    {A : Scheme.{u}} (emb : X ⟶ A) {ηC : X} (hηC : IsGenericPoint ηC C) :
    IsGenericPoint (emb ηC) (((X.irreducibleComponentIdeal C hC).map emb).support : Set A) := by
  rw [Scheme.IdealSheafData.support_map]
  have h := hηC.image emb.continuous
  rwa [← support_irreducibleComponentIdeal' C hC] at h

/-! ### Components along a flat morphism -/

omit [AlgebraicGeometry.IsNoetherian X] in
/-- A flat map sends the generic point of a component `D` of `Z` to the generic point of the
component `C ⊇ f(D)` of `X`: generalisations lift along flat maps, and the generic point of a
component has no proper generalisation. -/
theorem map_genericPoint_eq_of_flat {Z : Scheme.{u}} (f : Z ⟶ X) [Flat f] {C : Set X}
    {D : Set Z} (hD : D ∈ irreducibleComponents Z)
    (hfD : f '' D ⊆ C) {ηC : X} (hηC : IsGenericPoint ηC C) {ηD : Z}
    (hηD : IsGenericPoint ηD D) : f ηD = ηC := by
  have hspec : ηC ⤳ f ηD := hηC.specializes (hfD ⟨ηD, hηD.mem, rfl⟩)
  obtain ⟨ξ, hξ, hfξ⟩ := Flat.generalizingMap f hspec
  rw [← hfξ, eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents hD hηD hξ]

/-- If the component `D` of the reduced Noetherian `Z` maps into the component `C` of `X` under
`f`, the pullback of the reduced ideal of `C` lies in that of `D` (the Galois connection
`le_support_iff_le_vanishingIdeal`; the reduced ideal of `D` is radical). -/
theorem comap_irreducibleComponentIdeal_le {Z : Scheme.{u}} [IsNoetherian Z] [IsReduced Z]
    (f : Z ⟶ X) (C : Set X) (hC : C ∈ irreducibleComponents X) (D : Set Z)
    (hD : D ∈ irreducibleComponents Z) (hfD : f '' D ⊆ C) :
    (X.irreducibleComponentIdeal C hC).comap f ≤ Z.irreducibleComponentIdeal D hD := by
  have hint := isIntegral_irreducibleComponent_of_isReduced D hD
  have h1 : (Z.irreducibleComponentIdeal D hD).support ≤
      ((X.irreducibleComponentIdeal C hC).comap f).support := by
    rw [Scheme.IdealSheafData.support_comap]
    intro z hz
    have hz' : z ∈ D := hz
    exact hfD ⟨z, hz', rfl⟩
  have h2 := Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h1
  rwa [Scheme.IdealSheafData.vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme] at h2

end Hironaka.Resolution
