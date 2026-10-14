/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUpSequence.Pushforward
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Deleting empty blow-ups commutes with pull-back and push-forward

The second clause of functoriality for smooth morphisms [Kol07, 34.1] compares two blow-up
sequences after "deleting every blow-up whose center is empty" (`eraseEmpty`), and the proof of
[Kol07, Lemma 102] says that for an arbitrary smooth `h` "the same blow-ups end up with empty
centers". To turn that sentence into equations one moves `eraseEmpty` past the three operations
that build the boundary-clearing sequence: the pull-back along a flat surjection, the pull-back
followed by a second deletion, and the push-forward along a closed immersion. This module proves
the three identities, all by induction on the sequence.

*The center test.* `eraseEmpty (cons X D rest)` tests `D = ⊤` and, when it holds, carries the
deleted tail back to `X` along the inverse of the isomorphism `D.blowUpπ`
(`isIso_blowUpπ_of_eq_top`: the blow-up of the unit ideal). The lemma `eraseEmpty_cons_of_eq_top`
states this branch for any center `D` with a proof of `D = ⊤`, so that pulled-back and
pushed-forward centers (`D.comap h`, `Z.map j`), which are only propositionally equal to `⊤`, need
no transport of types.

*The identities.* A flat surjection `h` preserves emptiness of centers both ways
(`eq_top_of_comap_eq_top_of_surjective`), and the inverse isomorphisms of the trivial blow-ups
intertwine with `blowUpMap` (`inv_blowUpπ_comp_blowUpMap`: both compose to the same map to `X`),
so `eraseEmpty (S.pullback h) = (eraseEmpty S).pullback h`
(`eraseEmpty_pullback_of_flat_surjective`). For an arbitrary `h` a nonempty center may pull back
to `⊤`; deleting before or after the pull-back gives the same deleted sequence
(`eraseEmpty_pullback_eraseEmpty'`), the isomorphism case reducing to the surjective lemma. A
closed immersion preserves emptiness both ways (`map_top`, `comap_map_of_isClosedImmersion`), and
the square of a trivial blow-up is cartesian because its vertical maps are isomorphisms
(`IsPullback.of_vert_isIso`), so `pullback_pushforward_of_isPullback_of_flat` of
`Hironaka/Scheme/BlowUpSequence/Pushforward.lean` gives
`eraseEmpty (S.pushforward j) = (eraseEmpty S).pushforward j` (`eraseEmpty_pushforward`).
-/

public section
universe u

open CategoryTheory AlgebraicGeometry Scheme Scheme.Hom BlowUpSequence
  Scheme.IdealSheafData IdealSheafData

namespace AlgebraicGeometry

open Hironaka

variable {X Y : Scheme.{u}}

/-- The blow-up of a center equal to the unit ideal is an isomorphism [Kol07, Warning 20]. -/
theorem isIso_blowUpπ_of_eq_top {D : X.IdealSheafData} (hD : D = ⊤) : IsIso
    D.blowUpπ := by
  subst hD
  exact blowUp.isIso_π_of_isInvertible _ isInvertible_top

/-- The deletion of an empty first blow-up, for a center only propositionally equal to `⊤`
(`eraseEmpty_cons_top` without a transport of the tail's type). -/
theorem eraseEmpty_cons_of_eq_top {D : X.IdealSheafData}
    (rest : BlowUpSequence D.blowUp)
    (hD : D = ⊤) [IsIso D.blowUpπ] :
    (cons X D rest).eraseEmpty = rest.eraseEmpty.pullback (inv D.blowUpπ) := by
  rw [eraseEmpty, dite_eq_left hD]

/-- The inverses of two trivial blow-ups intertwine `h` with `blowUpMap` (both composites are the
same map to `X`, by `blowUpMap_π`). -/
theorem inv_blowUpπ_comp_blowUpMap (h : Y ⟶ X) (D : X.IdealSheafData) [IsIso D.blowUpπ]
    [IsIso (D.comap h).blowUpπ] :
    inv (D.comap h).blowUpπ ≫ Scheme.Hom.blowUpMap h D =
      h ≫ inv D.blowUpπ := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  exact blowUpMap_π h D

/-- The map of blow-ups over a flat `h` is flat (base change). -/
theorem flat_blowUpMap (h : Y ⟶ X) [Flat h] (D : X.IdealSheafData) :
    Flat (Scheme.Hom.blowUpMap h D) :=
  property_of_isPullback @Flat (isPullback_blowUpMap h D) inferInstance

/-- The map of blow-ups over a flat surjection is surjective (base change). -/
theorem surjective_blowUpMap (h : Y ⟶ X) [Flat h] (hs : Function.Surjective h)
    (D : X.IdealSheafData) :
    Function.Surjective (Scheme.Hom.blowUpMap h D) := by
  have : Surjective h := ⟨hs⟩
  have : Surjective (Scheme.Hom.blowUpMap h D) :=
    property_of_isPullback @Surjective (isPullback_blowUpMap h D) inferInstance
  exact (Scheme.Hom.blowUpMap h D).surjective

/-- Deleting empty blow-ups commutes with pull-back along a flat surjection: a center is `⊤` iff
its inverse image is (the first clause of [Kol07, 34.1] is a statement without deletions). -/
theorem eraseEmpty_pullback_of_flat_surjective (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (hs : Function.Surjective h) : (S.pullback h).eraseEmpty = S.eraseEmpty.pullback h := by
  induction S generalizing Y with
  | nil X => rfl
  | cons X D rest ih =>
    rw [pullback_cons]
    have := flat_blowUpMap h D
    have hsurj := surjective_blowUpMap h hs D
    by_cases hD : D = ⊤
    · have := isIso_blowUpπ_of_eq_top hD
      have hD' : D.comap h = ⊤ := by rw [hD, comap_top]
      have := isIso_blowUpπ_of_eq_top hD'
      rw [eraseEmpty_cons_of_eq_top _ hD', eraseEmpty_cons_of_eq_top rest hD, ih _ hsurj,
        ← pullback_comp, ← pullback_comp, inv_blowUpπ_comp_blowUpMap]
    · have hD' : D.comap h ≠ ⊤ := fun e => hD (eq_top_of_comap_eq_top_of_surjective D h hs e)
      rw [eraseEmpty_cons_of_ne_top _ hD', eraseEmpty_cons_of_ne_top rest hD, pullback_cons,
        ih _ hsurj]

-- `surjective_of_isIso` (an isomorphism of schemes is surjective on points) is in
-- `Hironaka/Scheme/BlowUpSequence/Pullback.lean`.

/-- Deleting the empty blow-ups before pulling back along any `h` does not change the deleted
pull-back (the second clause of [Kol07, 34.1]; "the same blow-ups end up with empty centers" in
the proof of [Kol07, Lemma 102]): the pulled-back center of a deleted step is `⊤.comap h = ⊤`,
and the deletion commutes with the isomorphisms `inv (blowUpπ _ ⊤)`
(`eraseEmpty_pullback_of_flat_surjective` on an isomorphism); the statement assumes no flatness
of `h`. -/
theorem eraseEmpty_pullback_eraseEmpty' (S : BlowUpSequence X) (h : Y ⟶ X) :
    (S.eraseEmpty.pullback h).eraseEmpty = (S.pullback h).eraseEmpty := by
  induction S generalizing Y with
  | nil X => rfl
  | cons X D rest ih =>
    by_cases hD : D = ⊤
    · have := isIso_blowUpπ_of_eq_top hD
      have hD' : D.comap h = ⊤ := by rw [hD, comap_top]
      have := isIso_blowUpπ_of_eq_top hD'
      rw [eraseEmpty_cons_of_eq_top rest hD, ← pullback_comp, ih, pullback_cons,
        eraseEmpty_cons_of_eq_top _ hD',
        ← eraseEmpty_pullback_of_flat_surjective _ _ (surjective_of_isIso _), ← pullback_comp,
        inv_blowUpπ_comp_blowUpMap]
    · rw [eraseEmpty_cons_of_ne_top rest hD, pullback_cons, pullback_cons]
      by_cases hD' : D.comap h = ⊤
      · have := isIso_blowUpπ_of_eq_top hD'
        rw [eraseEmpty_cons_of_eq_top _ hD', eraseEmpty_cons_of_eq_top _ hD', ih]
      · rw [eraseEmpty_cons_of_ne_top _ hD', eraseEmpty_cons_of_ne_top _ hD', ih]

/-- Deleting empty blow-ups commutes with the push-forward along a closed immersion
([Kol07, 30.3] with the convention of [Kol07, 32]): a center is `⊤` iff its image is, and the
square of a trivial blow-up is cartesian (`pullback_pushforward_of_isPullback_of_flat`). -/
theorem eraseEmpty_pushforward (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j] :
    (S.pushforward j).eraseEmpty = S.eraseEmpty.pushforward j := by
  induction S generalizing X with
  | nil Y => rfl
  | cons Y Z rest ih =>
    rw [pushforward_cons]
    by_cases hZ : Z = ⊤
    · have hZ' : Z.map j = ⊤ := by rw [hZ, map_top]
      have := isIso_blowUpπ_of_eq_top hZ
      have := isIso_blowUpπ_of_eq_top hZ'
      have : Flat (inv (Z.map j).blowUpπ) := inferInstance
      rw [eraseEmpty_cons_of_eq_top _ hZ', eraseEmpty_cons_of_eq_top rest hZ, ih]
      refine pullback_pushforward_of_isPullback_of_flat _ (pushforwardBlowUp j Z) _ j
        (inv Z.blowUpπ) (IsPullback.of_vert_isIso ⟨?_⟩)
      rw [IsIso.comp_inv_eq, Category.assoc, pushforwardBlowUp_π, IsIso.inv_hom_id_assoc]
    · have hZ' : Z.map j ≠ ⊤ := fun e => hZ (by
        have := comap_map_of_isClosedImmersion j Z
        rw [e, comap_top] at this
        exact this.symm)
      rw [eraseEmpty_cons_of_ne_top _ hZ', eraseEmpty_cons_of_ne_top rest hZ, pushforward_cons, ih]

/-- Deleting the empty blow-ups of the tail first does not change the deleted sequence
(`eraseEmpty_eraseEmpty`). -/
theorem eraseEmpty_cons_eraseEmpty (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) :
    (cons X D rest.eraseEmpty).eraseEmpty = (cons X D rest).eraseEmpty := by
  by_cases hD : D = ⊤
  · have := isIso_blowUpπ_of_eq_top hD
    rw [eraseEmpty_cons_of_eq_top _ hD, eraseEmpty_cons_of_eq_top rest hD, eraseEmpty_eraseEmpty]
  · rw [eraseEmpty_cons_of_ne_top _ hD, eraseEmpty_cons_of_ne_top rest hD, eraseEmpty_eraseEmpty]

end AlgebraicGeometry
