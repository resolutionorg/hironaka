/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Hironaka.Algebra.Local.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Algebra.Local.CompletionCoords
import Hironaka.Algebra.Local.TransformOrder
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Invariance of the order under open immersions, isomorphisms and completion

[Hau03, Appendix A]: the order "is invariant with respect to field extensions, passage to the
completion and local isomorphisms". This module: `ord` is invariant under isomorphisms, under
restriction to opens, and under completion; smooth morphisms are
`Hironaka/Scheme/IdealSheaf/Order/Smooth.lean`.

* Open immersions and isomorphisms (`ord_comap_of_isOpenImmersion`, `ord_comap_of_isIso`,
  `ord_comap_ι`): the stalk of the inverse image `f⁻¹ I` at `y` is the image of the stalk `I_{f y}`
  under the stalk map (`stalkIdeal_comap`, `Hironaka/Scheme/IdealSheaf/StalkIdeal.lean`), which is
  an isomorphism of local rings for an open immersion, and the order of an ideal is transported
  along ring isomorphisms (`IsLocalRing.ord_map_ringEquiv`,
  `Hironaka/Algebra/Local/TransformOrder.lean`).
* Completion (`ord_eq_ord_map_adicCompletion`): `ord_x I = ord (I_x Ô_{X,x})` in the maximal-adic
  completion of the Noetherian local ring `𝒪_{X,x}` (`ord_map_adicCompletion` of
  `Hironaka/Algebra/Local/CompletionCoords.lean`: `𝔪̂ʳ ∩ 𝒪 = 𝔪ʳ` by Krull's intersection theorem,
  which [Kol07, 55] recalls from [AM69, 10.17]).

The maximal order is invariant under isomorphisms as well (`maxOrd_comap_of_isIso`, in the
namespace of its user `Hironaka/Resolution/Algebraic/Hir64/OrderReductionRound.lean`).

Used for the transport of orders along open covers and isomorphisms
(`Hironaka/Scheme/BlowUpSequence/OpenTransport.lean`,
`Hironaka/Resolution/Algebraic/Kol07/CosuppTransport.lean`,
`Hironaka/Scheme/BlowUpSequence/DisjointUnion.lean`,
`Hironaka/Resolution/Algebraic/Kol07/MaximalContactGlobalization.lean`,
`Hironaka/Resolution/Algebraic/MaximalContact/Existence.lean`,
`Hironaka/Resolution/Algebraic/MaximalContact/Restrict.lean`,
`Hironaka/Resolution/Algebraic/BoundaryClearing/Transform.lean`).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The order is invariant under open immersions, `ord_y (f⁻¹ I) = ord_{f y} I` ("local
isomorphisms", [Hau03, Appendix A]). -/
theorem ord_comap_of_isOpenImmersion {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    (I.comap f).ord y = I.ord (f y) := by
  rw [ord_eq_ord_stalkIdeal, ord_eq_ord_stalkIdeal, stalkIdeal_comap]
  exact ord_map_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv _

/-- The order is invariant under isomorphisms. -/
theorem ord_comap_of_isIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (y : Y) :
    (I.comap f).ord y = I.ord (f y) :=
  ord_comap_of_isOpenImmersion I f y

/-- The order is invariant under restriction to an open `U ⊆ X`. -/
theorem ord_comap_ι (U : X.Opens) (u : U) : (I.comap U.ι).ord u = I.ord (U.ι u) :=
  ord_comap_of_isOpenImmersion I U.ι u

/-- "Passage to the completion" ([Hau03, Appendix A]): `ord_x I = ord (I_x Ô_{X,x})` in the
maximal-adic completion of `𝒪_{X,x}`, since `𝔪̂ʳ ∩ 𝒪 = 𝔪ʳ` by Krull's intersection theorem
(`ord_map_adicCompletion`). -/
theorem ord_eq_ord_map_adicCompletion [IsLocallyNoetherian X] (x : X) :
    I.ord x = IsLocalRing.ord ((I.stalkIdeal x).map
      (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))) := by
  rw [ord_eq_ord_stalkIdeal, ord_map_adicCompletion]

end AlgebraicGeometry.Scheme.IdealSheafData

/-! ### `max-ord` under an isomorphism -/

universe u

namespace AlgebraicGeometry

open CategoryTheory AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- `max-ord` is invariant under the inverse image along an isomorphism (`ord_comap_of_isIso`
pointwise); in the namespace of its user
`Hironaka/Resolution/Algebraic/Hir64/OrderReductionRound.lean`. -/
theorem maxOrd_comap_of_isIso (I : X.IdealSheafData) (f : Y ⟶ X) [IsIso f] :
    (I.comap f).maxOrd = I.maxOrd := by
  refine le_antisymm ((I.comap f).maxOrd_le_iff.mpr fun y => ?_)
    (I.maxOrd_le_iff.mpr fun x => ?_)
  · rw [I.ord_comap_of_isIso f y]
    exact I.le_maxOrd _
  · have hI : I = (I.comap f).comap (inv f) := by
      rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
    calc I.ord x = ((I.comap f).comap (inv f)).ord x := by rw [← hI]
      _ = (I.comap f).ord (inv f x) := (I.comap f).ord_comap_of_isIso (inv f) x
      _ ≤ (I.comap f).maxOrd := (I.comap f).le_maxOrd _

end AlgebraicGeometry
