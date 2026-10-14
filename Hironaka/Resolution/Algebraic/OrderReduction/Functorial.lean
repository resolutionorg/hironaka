/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Basic
import Hironaka.Resolution.Algebraic.Balanced.Order
import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Derivative.BaseChange
import Hironaka.Scheme.IdealSheaf.Derivative.Cosupport
import Hironaka.Scheme.IdealSheaf.Derivative.Properties
import Hironaka.Scheme.IdealSheaf.Order.Smooth
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Resolution.Algebraic.Kol07.GoingUp

/-!
# Step 1 of order reduction: the reduced functor inherits clauses (1) and (2)

`OrderSeqAssignment.ofTuned B hDom` is
Step 1 of the proof of [Kol07, Theorem 103] read as a construction: from a smooth blow-up sequence
functor `B` of order `s(m)` on tuned triples, the functor of order `m` on `BOClass n m` whose value
on `(X, I, E)` is `B(X, W_{s(m)}(I), E)` when `max-ord I = m` and the empty sequence when `max-ord I
< m`. This module shows that the clauses of Theorem 103 pass from `B` to the reduced functor.

*The two values* (`ofTuned_seq_of_maxOrd_eq`, `ofTuned_seq_of_maxOrd_lt`) are the two branches of
the definition.

*Clause (1)* (`ofTuned_maxOrd_lt`). Above the mark the value is `B` on the tuned triple, a
sequence of order `m` for `(X, I, E)` by [Kol07, Corollary 101] (`isOrderSeq_tuned_iff`), along
which `max-ord W_r < s(m)`, clause (1) for `B`, gives `max-ord I_r < m`
(`maxOrd_weakTransformSeq_lt_iff_tuned`). Below the mark the value is empty, `I_r = I`, and
`max-ord I < m` is the case hypothesis.

*Clause (2), smooth morphisms* (`ofTuned_commutesWithSmooth`, [Kol07, 34.1]). The case splits of
the two triples must align, and they do: the maximal order does not increase under a smooth
pull-back (`maxOrd_comap_le_of_smooth`, the order being preserved pointwise) and does not decrease
under a surjection (`maxOrd_le_maxOrd_comap_of_surjective`, every point having a preimage). For a
smooth surjection both triples are above the mark or both below; above, the tuned triples are
again a pull-back pair (`isPullbackOf_tuned`) and `B` commutes; below, both values are empty. For
an arbitrary smooth morphism the same holds except in one case, `T` above the mark and its
pull-back `T'` below. There the value on `T'` is empty, and the pulled-back sequence with its empty
blow-ups deleted is a smooth blow-up sequence of order `m` for `T'` without empty centres
(`isOrderSeq_eraseEmpty_pullback_of_equidim`), which must itself be empty: its first centre would
carry a generic point of a component where `I'` has order `m`, above `max-ord I' < m`
(`eq_nil_of_isOrderSeq_of_maxOrd_lt`).

*Clause (2), change of fields* (`ofTuned_commutesWithBaseChange`, [Kol07, 34.2]). The maximal
order is preserved under a change of fields in characteristic zero
(`maxOrd_comap_of_isPullback_specMap`): it does not decrease because the projection is surjective
and the order can only grow under pull-back, and it does not increase because `max-ord I ≤ μ` iff
the iterated derivative `D^μ I` is the unit ideal (`derivativeIter_eq_top_iff_maxOrd_le`) and the
derivative commutes with the base-change square (`derivativeIter_comap_of_isPullback_specMap`). No
pointwise comparison of orders under a transcendental extension is needed. The case splits
therefore align, and the tuned triples are again a base-change pair (`isBaseChangeOf_tuned`).

*The general form.* The construction and the three transfers depend on the class `BOClass n m`
only through `1 ≤ m` and `max-ord I ≤ m`, so they are stated first for
`OrderSeqAssignment.ofTunedClass` on an arbitrary class `C` with hypotheses `hmC : ∀ T, C T → 1 ≤ m`
and `hmax : ∀ T, C T → max-ord I ≤ m` (`ofTunedClass_seq_of_maxOrd_eq`,
`ofTunedClass_seq_of_maxOrd_lt`, `ofTunedClass_seq_isOrderSeq`, `ofTunedClass_seq_noEmptyCenters`,
`ofTunedClass_maxOrd_lt`, `ofTunedClass_commutesWithSmooth`, `ofTunedClass_commutesWithBaseChange`);
the `ofTuned_*` lemmas are their instances at `C := BOClass n m`, and the boundary-clearing
functor `Hironaka.BD.tunedFunctor` takes its instances at `C := BDClass n m j`.

The last section shows that a change of fields preserves the order of an ideal at every point
(`Hironaka.BMO.ord_comap_of_isPullback_specMap`), the pointwise form of
`maxOrd_comap_of_isPullback_specMap`; it serves the change-of-fields clause of the marked functor
of [Kol07, Theorem 107]
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/BaseChangeParameters.lean`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData IsLocalRing

namespace Hironaka.BO

open Hironaka Scheme AlgebraicGeometry BlowUpSequence

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-! ### The maximal order under pull-back -/

/-- A smooth pull-back does not raise the maximal order: the order is preserved pointwise
(`ord_comap_of_smooth`). Not in the sources; an auxiliary lemma for [Kol07, 34.1]. -/
theorem maxOrd_comap_le_of_smooth {Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h] (I : X.IdealSheafData) :
    (I.comap h).maxOrd ≤ I.maxOrd := by
  rw [IdealSheafData.maxOrd_le_iff]
  intro y
  rw [IdealSheafData.ord_comap_of_smooth I h y]
  exact IdealSheafData.le_maxOrd I (h y)

/-- A surjective morphism does not lower the maximal order: the order can only grow under
pull-back (`ord_le_ord_comap`) and every point has a preimage. Not in the sources. -/
theorem maxOrd_le_maxOrd_comap_of_surjective {Y : Scheme.{u}} (h : Y ⟶ X)
    (hs : Function.Surjective h) (I : X.IdealSheafData) : I.maxOrd ≤ (I.comap h).maxOrd := by
  rw [IdealSheafData.maxOrd_le_iff]
  intro x
  obtain ⟨y, rfl⟩ := hs x
  exact (IdealSheafData.ord_le_ord_comap I h y).trans (IdealSheafData.le_maxOrd _ y)

/-- A change of fields preserves the maximal order in characteristic zero: `max-ord I ≤ μ` iff the
iterated derivative `D^μ I` is the unit ideal, the derivative commutes with the base-change square
(`derivativeIter_comap_of_isPullback_specMap`), and the projection is surjective. Not in the
sources; an auxiliary lemma for [Kol07, 34.2]. -/
theorem maxOrd_comap_of_isPullback_specMap [CharZero k] {L : Type u} [Field L] {Y : Scheme.{u}}
    {p : Y ⟶ X} {g' : Y ⟶ Spec (.of L)} {f : X ⟶ Spec (.of k)} {σ : k →+* L}
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) (n : ℕ)
    [SmoothOfRelativeDimension n f] (n' : ℕ) [SmoothOfRelativeDimension n' g']
    (I : X.IdealSheafData) : (I.comap p).maxOrd = I.maxOrd := by
  have : CharZero L := charZero_of_ringHom σ
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  refine le_antisymm ?_ ?_
  · rcases h : I.maxOrd with _ | μ
    · exact le_top
    · have h1 : IdealSheafData.derivativeIter f μ I = ⊤ :=
        (IdealSheafData.derivativeIter_eq_top_iff_maxOrd_le f n I μ).mpr h.le
      have h2 : IdealSheafData.derivativeIter g' μ (I.comap p) = ⊤ := by
        rw [IdealSheafData.derivativeIter_comap_of_isPullback_specMap sq μ I, h1,
            IdealSheafData.comap_top]
      exact (IdealSheafData.derivativeIter_eq_top_iff_maxOrd_le g' n' (I.comap p) μ).mp h2
  · have : Surjective p :=
      property_of_isPullback @Surjective sq (flat_and_surjective_specMap σ).2
    exact maxOrd_le_maxOrd_comap_of_surjective p p.surjective I

/-- A smooth blow-up sequence of order `m` without empty blow-ups ([Kol07, Definition 66 and 32])
for an ideal of maximal order `< m` is the empty sequence: its first centre, being nonempty, has a
generic point of a component (`Closeds.exists_mem_genericPoints_specializes`) at which the order
is `m`, above the maximal order. Not in the sources. -/
theorem eq_nil_of_isOrderSeq_of_maxOrd_lt (f : X ⟶ Spec (.of k))
    {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}
    (hS : S.IsOrderSeq f I E m) (hne : S.NoEmptyCenters) (hI : I.maxOrd < m) : S = nil X := by
  cases S with
  | nil => rfl
  | cons _ D rest =>
    exfalso
    rw [isOrderSeq_cons_iff] at hS
    rw [noEmptyCenters_cons_iff] at hne
    have hsup : (D.support : Set X) ≠ ∅ := fun h =>
      hne.1 ((IdealSheafData.support_eq_bot_iff D).mp (SetLike.coe_injective (by rw [h]; rfl)))
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hsup
    obtain ⟨η, hη, -⟩ := Closeds.exists_mem_genericPoints_specializes D.support hz
    have h1 : I.ord η = m := hS.1.2.2 η hη
    have h2 : I.ord η ≤ I.maxOrd := IdealSheafData.le_maxOrd I η
    rw [h1] at h2
    exact absurd (lt_of_le_of_lt h2 hI) (lt_irrefl _)

/-- Congruence of the final maximal order along an equality of sequences (the index `Fin.last _`
depends on the sequence, so this is stated once and used in place of `rw`). -/
theorem maxOrd_weakTransformSeq_last_congr {S S' : BlowUpSequence X} (e : S = S')
    (I : X.IdealSheafData) :
    (S.weakTransformSeq I (Fin.last _)).maxOrd = (S'.weakTransformSeq I (Fin.last _)).maxOrd := by
  subst e; rfl

/-! ### The reduced functor on an arbitrary class -/

section Generic

variable [CharZero k] {m : ℕ} {C Dom' : Triple k → Prop}
  (B : OrderSeqAssignment k (tuningParam m) Dom') (hmC : ∀ T : Triple k, C T → 1 ≤ m)
  (hDom : ∀ (T : Triple k) (hT : C T), T.I.maxOrd = m → Dom' (T.tuned m (hmC T hT)))

/-- Above the mark, the reduced functor on `C` returns `B` on the tuned triple (Step 1 of the
proof of [Kol07, Theorem 103]). -/
theorem ofTunedClass_seq_of_maxOrd_eq (T : Triple k) (hT : C T) (h : T.I.maxOrd = m) :
    (OrderSeqAssignment.ofTunedClass B hmC hDom).seq T hT =
      B.seq (T.tuned m (hmC T hT)) (hDom T hT h) :=
  dite_eq_left h

/-- Below the mark, the reduced functor on `C` returns the empty sequence (the remark after
[Kol07, Theorem 68]: the case `max-ord I < m` is trivial). -/
theorem ofTunedClass_seq_of_maxOrd_lt (T : Triple k) (hT : C T) (h : T.I.maxOrd < m) :
    (OrderSeqAssignment.ofTunedClass B hmC hDom).seq T hT = BlowUpSequence.nil T.X.left :=
  dite_eq_right h.ne

/-- The value of the reduced functor on `C` is a smooth blow-up sequence of order `m` starting
with `(X, I, E)`: the first proof field of `ofTunedClass`. -/
theorem ofTunedClass_seq_isOrderSeq (T : Triple k) (hT : C T) :
    ((OrderSeqAssignment.ofTunedClass B hmC hDom).seq T hT).IsOrderSeq (T.X.left ↘ Spec (.of k))
      T.I T.E m :=
  (OrderSeqAssignment.ofTunedClass B hmC hDom).isOrderSeq T hT

/-- The value of the reduced functor on `C` contains no empty blow-up ([Kol07, 32]): the second
proof field of `ofTunedClass`. -/
theorem ofTunedClass_seq_noEmptyCenters (T : Triple k) (hT : C T) :
    ((OrderSeqAssignment.ofTunedClass B hmC hDom).seq T hT).NoEmptyCenters :=
  (OrderSeqAssignment.ofTunedClass B hmC hDom).noEmptyCenters T hT

/-- Clause (1) of [Kol07, Theorem 103] for the reduced functor on a class `C` of triples with
`max-ord I ≤ m` (`hmax`), from clause (1) for `B` on the tuned triples. -/
theorem ofTunedClass_maxOrd_lt (hmax : ∀ T : Triple k, C T → T.I.maxOrd ≤ (m : ℕ∞))
    (hB : ∀ (T' : Triple k) (hT' : Dom' T'),
      ((B.seq T' hT').weakTransformSeq T'.I (Fin.last _)).maxOrd < (tuningParam m : ℕ∞))
    (T : Triple k) (hT : C T) :
    (((OrderSeqAssignment.ofTunedClass B hmC hDom).seq T hT).weakTransformSeq T.I
      (Fin.last _)).maxOrd < (m : ℕ∞) := by
  by_cases h : T.I.maxOrd = m
  · refine (maxOrd_weakTransformSeq_last_congr
      (ofTunedClass_seq_of_maxOrd_eq B hmC hDom T hT h) T.I).trans_lt ?_
    obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
    have hord : (B.seq (T.tuned m (hmC T hT)) (hDom T hT h)).IsOrderSeq (T.X.left ↘ Spec (.of k))
        T.I T.E m :=
      (isOrderSeq_tuned_iff _ h (hmC T hT)).mpr (B.isOrderSeq _ _)
    exact (maxOrd_weakTransformSeq_lt_iff_tuned (T.X.left ↘ Spec (.of k)) d _ T.I T.E m h (hmC T hT)
      hord).mp (hB _ _)
  · have hl : T.I.maxOrd < m := lt_of_le_of_ne (hmax T hT) h
    refine (maxOrd_weakTransformSeq_last_congr
      (ofTunedClass_seq_of_maxOrd_lt B hmC hDom T hT hl) T.I).trans_lt ?_
    rw [weakTransformSeq_nil]
    exact hl

/-- Clause (2) of [Kol07, Theorem 103] for smooth morphisms ([Kol07, 34.1]): the reduced functor
on a class `C` of triples with `max-ord I ≤ m` commutes with smooth morphisms when `B` does. The
case splits align because the maximal order does not rise under a smooth pull-back and is
preserved by a surjection; in the one mixed case the pulled-back sequence, an order-`m` sequence
without empty centres for a triple below the mark, is empty. -/
theorem ofTunedClass_commutesWithSmooth (hmax : ∀ T : Triple k, C T → T.I.maxOrd ≤ (m : ℕ∞))
    (hB : B.CommutesWithSmooth) : (OrderSeqAssignment.ofTunedClass B hmC hDom).CommutesWithSmooth
        := by
  refine ⟨?_, ?_⟩
  · intro T T' g _ hs hpb hT hT'
    have hle : T'.I.maxOrd = T.I.maxOrd := by
      rw [hpb.2.1]
      exact le_antisymm (maxOrd_comap_le_of_smooth g T.I)
        (maxOrd_le_maxOrd_comap_of_surjective g hs T.I)
    by_cases h : T.I.maxOrd = m
    · have h' : T'.I.maxOrd = m := hle.trans h
      rw [ofTunedClass_seq_of_maxOrd_eq B hmC hDom T' hT' h',
        ofTunedClass_seq_of_maxOrd_eq B hmC hDom T hT h]
      exact hB.1 (T.tuned m (hmC T hT)) (T'.tuned m (hmC T' hT')) g hs
        (isPullbackOf_tuned hpb m (hmC T hT)) (hDom T hT h) (hDom T' hT' h')
    · have hl : T.I.maxOrd < m := lt_of_le_of_ne (hmax T hT) h
      rw [ofTunedClass_seq_of_maxOrd_lt B hmC hDom T' hT' (by rw [hle]; exact hl),
        ofTunedClass_seq_of_maxOrd_lt B hmC hDom T hT hl, pullback_nil]
  · intro T T' g _ hpb hT hT'
    have hle : T'.I.maxOrd ≤ T.I.maxOrd := by
      rw [hpb.2.1]
      exact maxOrd_comap_le_of_smooth g T.I
    by_cases h : T.I.maxOrd = m
    · by_cases h' : T'.I.maxOrd = m
      · rw [ofTunedClass_seq_of_maxOrd_eq B hmC hDom T' hT' h',
          ofTunedClass_seq_of_maxOrd_eq B hmC hDom T hT h]
        exact hB.2 (T.tuned m (hmC T hT)) (T'.tuned m (hmC T' hT')) g
          (isPullbackOf_tuned hpb m (hmC T hT)) (hDom T hT h) (hDom T' hT' h')
      · have hl' : T'.I.maxOrd < m := lt_of_le_of_ne (hmax T' hT') h'
        rw [ofTunedClass_seq_of_maxOrd_lt B hmC hDom T' hT' hl',
          ofTunedClass_seq_of_maxOrd_eq B hmC hDom T hT h]
        obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
        obtain ⟨d', hd'⟩ := T'.smoothOfRelativeDimension
        have hcomp : g ≫ (T.X.left ↘ Spec (.of k)) = T'.X.left ↘ Spec (.of k) := hpb.1
        have : SmoothOfRelativeDimension d' (g ≫ (T.X.left ↘ Spec (.of k))) := hcomp.symm ▸ hd'
        have hord : (B.seq (T.tuned m (hmC T hT)) (hDom T hT h)).IsOrderSeq
            (T.X.left ↘ Spec (.of k)) T.I T.E m :=
          (isOrderSeq_tuned_iff _ h (hmC T hT)).mpr (B.isOrderSeq _ _)
        have hR := isOrderSeq_eraseEmpty_pullback_of_equidim (T.X.left ↘ Spec (.of k)) d g d' hord
        rw [hcomp, ← hpb.2.1, ← hpb.2.2] at hR
        exact (eq_nil_of_isOrderSeq_of_maxOrd_lt _ hR (noEmptyCenters_eraseEmpty _) hl').symm
    · have hl : T.I.maxOrd < m := lt_of_le_of_ne (hmax T hT) h
      rw [ofTunedClass_seq_of_maxOrd_lt B hmC hDom T' hT' (lt_of_le_of_lt hle hl),
        ofTunedClass_seq_of_maxOrd_lt B hmC hDom T hT hl, pullback_nil, eraseEmpty_nil]

/-- Clause (2) of [Kol07, Theorem 103] for change of fields ([Kol07, 34.2]): the reduced functors
on a class `C` of triples over `k` with `max-ord I ≤ m` and on a class `C'` over `L` commute with a
change of fields when `B` and `B'` do. The maximal order is preserved under a change of fields in
characteristic zero, so the case splits align. -/
theorem ofTunedClass_commutesWithBaseChange (hmax : ∀ T : Triple k, C T → T.I.maxOrd ≤ (m : ℕ∞))
    {L : Type u} [Field L] [CharZero L] {C' Dom'' : Triple L → Prop}
    (B' : OrderSeqAssignment L (tuningParam m) Dom'') (hmC' : ∀ T : Triple L, C' T → 1 ≤ m)
    (hDom' : ∀ (T : Triple L) (hT : C' T), T.I.maxOrd = m → Dom'' (T.tuned m (hmC' T hT)))
    (σ : k →+* L) (hB : B.CommutesWithBaseChange B' σ) :
    (OrderSeqAssignment.ofTunedClass B hmC hDom).CommutesWithBaseChange
      (OrderSeqAssignment.ofTunedClass B' hmC' hDom') σ := by
  intro T T' p hbc hT hT'
  have hmax' : T'.I.maxOrd = T.I.maxOrd := by
    rw [hbc.2.1]
    obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
    obtain ⟨d', hd'⟩ := T'.smoothOfRelativeDimension
    exact maxOrd_comap_of_isPullback_specMap hbc.1 d d' T.I
  by_cases h : T.I.maxOrd = m
  · have h' : T'.I.maxOrd = m := hmax'.trans h
    rw [ofTunedClass_seq_of_maxOrd_eq B' hmC' hDom' T' hT' h',
      ofTunedClass_seq_of_maxOrd_eq B hmC hDom T hT h]
    exact hB (T.tuned m (hmC T hT)) (T'.tuned m (hmC' T' hT')) p
      (isBaseChangeOf_tuned hbc m (hmC T hT)) (hDom T hT h) (hDom' T' hT' h')
  · have hl : T.I.maxOrd < m := lt_of_le_of_ne (hmax T hT) h
    rw [ofTunedClass_seq_of_maxOrd_lt B' hmC' hDom' T' hT' (by rw [hmax']; exact hl),
      ofTunedClass_seq_of_maxOrd_lt B hmC hDom T hT hl, pullback_nil]

end Generic

/-! ### The reduced functor on `BOClass n m` -/

variable [CharZero k] {n m : ℕ} {Dom' : Triple k → Prop}
  (B : OrderSeqAssignment k (tuningParam m) Dom')
  (hDom : ∀ (T : Triple k) (hT : Triple.BOClass n m T), T.I.maxOrd = m → Dom' (T.tuned m hT.1))

/-- Above the mark, the reduced functor returns `B` on the tuned triple. -/
theorem ofTuned_seq_of_maxOrd_eq (T : Triple k) (hT : Triple.BOClass n m T)
    (h : T.I.maxOrd = m) :
    (OrderSeqAssignment.ofTuned B hDom).seq T hT = B.seq (T.tuned m hT.1) (hDom T hT h) :=
  dite_eq_left h

/-- Below the mark, the reduced functor returns the empty sequence. -/
theorem ofTuned_seq_of_maxOrd_lt (T : Triple k) (hT : Triple.BOClass n m T)
    (h : T.I.maxOrd < m) : (OrderSeqAssignment.ofTuned B hDom).seq T hT =
      BlowUpSequence.nil T.X.left :=
  dite_eq_right h.ne

/-- The value of the reduced functor is a smooth blow-up sequence of order `m` starting with
`(X, I, E)`: the first proof field of `ofTuned`. -/
theorem ofTuned_seq_isOrderSeq (T : Triple k) (hT : Triple.BOClass n m T) :
    ((OrderSeqAssignment.ofTuned B hDom).seq T hT).IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m :=
  (OrderSeqAssignment.ofTuned B hDom).isOrderSeq T hT

/-- The value of the reduced functor contains no empty blow-up ([Kol07, 32]): the second proof
field of `ofTuned`. -/
theorem ofTuned_seq_noEmptyCenters (T : Triple k) (hT : Triple.BOClass n m T) :
    ((OrderSeqAssignment.ofTuned B hDom).seq T hT).NoEmptyCenters :=
  (OrderSeqAssignment.ofTuned B hDom).noEmptyCenters T hT

/-- Clause (1) of [Kol07, Theorem 103] for the reduced functor, from clause (1) for `B` on the
tuned triples. -/
theorem ofTuned_maxOrd_lt (hB : ∀ (T' : Triple k) (hT' : Dom' T'),
      ((B.seq T' hT').weakTransformSeq T'.I (Fin.last _)).maxOrd < (tuningParam m : ℕ∞))
    (T : Triple k) (hT : Triple.BOClass n m T) :
    (((OrderSeqAssignment.ofTuned B hDom).seq T hT).weakTransformSeq T.I (Fin.last _)).maxOrd <
      (m : ℕ∞) :=
  ofTunedClass_maxOrd_lt B (fun _ hT => hT.1) hDom (fun _ hT => hT.2.2) hB T hT

/-- Clause (2) of [Kol07, Theorem 103] for smooth morphisms ([Kol07, 34.1]): the reduced functor
commutes with smooth morphisms when `B` does. -/
theorem ofTuned_commutesWithSmooth (hB : B.CommutesWithSmooth) :
    (OrderSeqAssignment.ofTuned B hDom).CommutesWithSmooth :=
  ofTunedClass_commutesWithSmooth B (fun _ hT => hT.1) hDom (fun _ hT => hT.2.2) hB

/-- Clause (2) of [Kol07, Theorem 103] for change of fields ([Kol07, 34.2]): the reduced functors
over `k` and over `L` commute with a change of fields when `B` and `B'` do. -/
theorem ofTuned_commutesWithBaseChange {L : Type u} [Field L] [CharZero L]
    {Dom'' : Triple L → Prop} (B' : OrderSeqAssignment L (tuningParam m) Dom'')
    (hDom' : ∀ (T : Triple L) (hT : Triple.BOClass n m T), T.I.maxOrd = m →
      Dom'' (T.tuned m hT.1))
    (σ : k →+* L) (hB : B.CommutesWithBaseChange B' σ) :
    (OrderSeqAssignment.ofTuned B hDom).CommutesWithBaseChange
      (OrderSeqAssignment.ofTuned B' hDom') σ :=
  ofTunedClass_commutesWithBaseChange B (fun _ hT => hT.1) hDom (fun _ hT => hT.2.2) B'
    (fun _ hT => hT.1) hDom' σ hB

end Hironaka.BO

namespace Hironaka.BMO

open Hironaka.Sequence

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L] {X Y : Scheme.{u}}

/-- Along the projection `p` of a base-change square over a field extension `σ : k → L`, the order
of the inverse image of `I` at a point is the order of `I` at its image: for every `μ ≥ 1`,
`ord_y (p^* I) ≥ μ` iff `y` lies in the support of `D^{μ-1}(p^* I) = p^*(D^{μ-1} I)`, iff
`ord_{p y} I ≥ μ` (the support of a marked ideal through iterated derivatives,
[Wlo05, Lemma 2.6.2]). The pointwise form of `maxOrd_comap_of_isPullback_specMap`. -/
theorem ord_comap_of_isPullback_specMap {p : Y ⟶ X} {g' : Y ⟶ Spec (.of L)}
    {f : X ⟶ Spec (.of k)} {σ : k →+* L}
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) (n : ℕ)
    [SmoothOfRelativeDimension n f] (n' : ℕ) [SmoothOfRelativeDimension n' g']
    (I : X.IdealSheafData) (y : Y) : (I.comap p).ord y = I.ord (p y) := by
  have hL : CharZero L := charZero_of_ringHom σ
  have hf : Smooth f := SmoothOfRelativeDimension.smooth n f
  refine _root_.ENat.eq_of_forall_natCast_le_iff fun a => ?_
  rcases a with _ | a
  · simp
  · rw [Scheme.IdealSheafData.le_ord_iff_mem_support_derivativeIter g' n' (I.comap p) y
      (Nat.succ_pos a),
      Scheme.IdealSheafData.le_ord_iff_mem_support_derivativeIter f n I (p y) (Nat.succ_pos a),
      Scheme.IdealSheafData.derivativeIter_comap_of_isPullback_specMap sq,
          mem_support_comap_iff_apply]

end Hironaka.BMO
