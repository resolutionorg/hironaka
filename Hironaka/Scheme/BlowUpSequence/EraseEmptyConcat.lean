/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
public import Hironaka.Scheme.BlowUpSequence.ConcatPullback
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Deleting empty blow-ups through a concatenation

The empty blow-up convention [Kol07, 32] deletes the empty blow-ups of a sequence, and the second
clause of functoriality for smooth morphisms [Kol07, 34.1] compares two sequences up to that
deletion. Here `eraseEmpty` deletes an empty blow-up by pulling the tail back along the inverse of
its blow-up map (an isomorphism), so the last stage of the erased sequence is only isomorphic to
the last stage of the sequence: `eraseEmptyLastHom S : S.eraseEmpty.last ⟶ S.last` is that
isomorphism (the composite of the last-stage lifts of the inverses), defined by recursion. With
it:

* `eraseEmpty_concat`: deleting the empty blow-ups of `S.concat T` is deleting them in `S`, then in
  `T` transported along `eraseEmptyLastHom S`; this is what the functoriality of a sequence
  assembled from rounds by concatenation needs;
* `eraseEmpty_eq_nil`: a sequence all of whose centers are empty erases to the empty sequence (the
  case of a pulled-back sequence whose ideal has order below the mark everywhere);
* `eraseEmpty_concat_eraseEmpty`: deleting the empty blow-ups of a concatenation whose second
  piece has already been cleaned is deleting them from the concatenation itself.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The isomorphism between the last stage of the erased sequence and the last stage of the
sequence: on a trivial blow-up (`D = ⊤`) the last-stage lift of `inv (D.blowUpπ)`, composed with
the isomorphism for the tail; on a nontrivial one the isomorphism for the tail. -/
noncomputable def Scheme.BlowUpSequence.eraseEmptyLastHom :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X), S.eraseEmpty.last ⟶ S.last
  | _, nil X => 𝟙 X
  | _, cons X D rest =>
    open scoped Classical in
    if h : D = ⊤ then
      haveI := isIso_blowUpπ_of_eq_top h
      eqToHom (congrArg BlowUpSequence.last (eraseEmpty_cons_of_eq_top rest h)) ≫
        rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom
    else
      eqToHom (congrArg BlowUpSequence.last (eraseEmpty_cons_of_ne_top rest h)) ≫
        rest.eraseEmptyLastHom

theorem eraseEmptyLastHom_nil : (nil X).eraseEmptyLastHom = 𝟙 X := rfl

theorem eraseEmptyLastHom_cons_of_eq_top (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp)
    (h : D = ⊤) [IsIso D.blowUpπ] :
    (cons X D rest).eraseEmptyLastHom =
      eqToHom (congrArg BlowUpSequence.last (eraseEmpty_cons_of_eq_top rest h)) ≫
        rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom := by
  rw [BlowUpSequence.eraseEmptyLastHom, dite_eq_left h]
  rfl

theorem eraseEmptyLastHom_cons_of_ne_top (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (h : ¬ D = ⊤) :
    (cons X D rest).eraseEmptyLastHom =
      eqToHom (congrArg BlowUpSequence.last (eraseEmpty_cons_of_ne_top rest h)) ≫
        rest.eraseEmptyLastHom := by
  rw [BlowUpSequence.eraseEmptyLastHom, dite_eq_right h]
  rfl

/-- Transport of the second argument of a concatenation along an equality of first arguments: the
`eqToHom` of the last-stage identification is absorbed. -/
theorem concat_pullback_eqToHom {S S' : BlowUpSequence X} (e : S = S')
    (R : BlowUpSequence S'.last) :
    S.concat (R.pullback (eqToHom (congrArg BlowUpSequence.last e))) = S'.concat R := by
  subst e
  change S.concat (R.pullback (𝟙 _)) = S.concat R
  simp

/-- Deleting the empty blow-ups of a concatenation is deleting them in the first sequence, then in
the second transported along the last-stage isomorphism of the first [Kol07, 32]. -/
theorem eraseEmpty_concat : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (T : BlowUpSequence S.last),
    (S.concat T).eraseEmpty = S.eraseEmpty.concat (T.eraseEmpty.pullback S.eraseEmptyLastHom)
  | _, nil X, T => (pullback_id T.eraseEmpty).symm
  | _, cons X D rest, T => by
    classical
    by_cases h : D = ⊤
    · have := isIso_blowUpπ_of_eq_top h
      have ih := eraseEmpty_concat rest T
      have e := eraseEmpty_cons_of_eq_top rest h
      have s1 : (cons X D (rest.concat T)).eraseEmpty =
          (rest.eraseEmpty.concat (T.eraseEmpty.pullback rest.eraseEmptyLastHom)).pullback
            (inv D.blowUpπ) :=
        (eraseEmpty_cons_of_eq_top _ h).trans
          (congrArg (fun R : BlowUpSequence D.blowUp => R.pullback (inv D.blowUpπ)) ih)
      have s2 : (rest.eraseEmpty.concat (T.eraseEmpty.pullback rest.eraseEmptyLastHom)).pullback
            (inv D.blowUpπ) =
          (rest.eraseEmpty.pullback (inv D.blowUpπ)).concat
            (T.eraseEmpty.pullback
              (rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom)) :=
        (pullback_concat _ _ _).trans
          (congrArg (rest.eraseEmpty.pullback (inv D.blowUpπ)).concat
            (pullback_comp T.eraseEmpty _ _).symm)
      have s3 : (rest.eraseEmpty.pullback (inv D.blowUpπ)).concat
            (T.eraseEmpty.pullback
              (rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom)) =
          (cons X D rest).eraseEmpty.concat (T.eraseEmpty.pullback
            (eqToHom (congrArg BlowUpSequence.last e) ≫
              rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom)) :=
        (concat_pullback_eqToHom e _).symm.trans
          (congrArg ((cons X D rest).eraseEmpty.concat) (pullback_comp T.eraseEmpty _ _).symm)
      have s4 : (cons X D rest).eraseEmpty.concat (T.eraseEmpty.pullback
            (eqToHom (congrArg BlowUpSequence.last e) ≫
              rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom)) =
          (cons X D rest).eraseEmpty.concat
            (T.eraseEmpty.pullback (cons X D rest).eraseEmptyLastHom) :=
        congrArg (fun q => (cons X D rest).eraseEmpty.concat (T.eraseEmpty.pullback q))
          (eraseEmptyLastHom_cons_of_eq_top D rest h).symm
      exact s1.trans (s2.trans (s3.trans s4))
    · have ih := eraseEmpty_concat rest T
      have e := eraseEmpty_cons_of_ne_top rest h
      have s1 : (cons X D (rest.concat T)).eraseEmpty =
          (cons X D rest.eraseEmpty).concat (T.eraseEmpty.pullback rest.eraseEmptyLastHom) :=
        (eraseEmpty_cons_of_ne_top _ h).trans (congrArg (cons X D) ih)
      have s3 : (cons X D rest.eraseEmpty).concat (T.eraseEmpty.pullback rest.eraseEmptyLastHom) =
          (cons X D rest).eraseEmpty.concat (T.eraseEmpty.pullback
            (eqToHom (congrArg BlowUpSequence.last e) ≫ rest.eraseEmptyLastHom)) :=
        (concat_pullback_eqToHom e _).symm.trans
          (congrArg ((cons X D rest).eraseEmpty.concat) (pullback_comp T.eraseEmpty _ _).symm)
      have s4 : (cons X D rest).eraseEmpty.concat (T.eraseEmpty.pullback
            (eqToHom (congrArg BlowUpSequence.last e) ≫ rest.eraseEmptyLastHom)) =
          (cons X D rest).eraseEmpty.concat
            (T.eraseEmpty.pullback (cons X D rest).eraseEmptyLastHom) :=
        congrArg (fun q => (cons X D rest).eraseEmpty.concat (T.eraseEmpty.pullback q))
          (eraseEmptyLastHom_cons_of_ne_top D rest h).symm
      exact s1.trans (s3.trans s4)

/-- A sequence all of whose centers are empty erases to the empty sequence [Kol07, 32]. -/
theorem eraseEmpty_eq_nil : ∀ {X : Scheme.{u}} (S : BlowUpSequence X),
    (∀ i, S.center i = ⊤) → S.eraseEmpty = nil X
  | _, nil X, _ => rfl
  | _, cons X D rest, hS => by
    have hD : D = ⊤ := hS ⟨0, Nat.succ_pos _⟩
    have := isIso_blowUpπ_of_eq_top hD
    rw [eraseEmpty_cons_of_eq_top rest hD, eraseEmpty_eq_nil rest (fun i => hS i.succ)]
    exact pullback_nil _

/-- Deleting the empty blow-ups of a concatenation whose second piece has already been cleaned is
deleting them from the concatenation itself (`eraseEmpty_concat` twice and
`eraseEmpty_eraseEmpty`). -/
theorem eraseEmpty_concat_eraseEmpty (S : BlowUpSequence X) (T : BlowUpSequence S.last) :
    (S.concat T.eraseEmpty).eraseEmpty = (S.concat T).eraseEmpty := by
  rw [eraseEmpty_concat, eraseEmpty_concat, eraseEmpty_eraseEmpty]

end AlgebraicGeometry
