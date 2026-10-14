/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.AssemblyZero
import Hironaka.Resolution.Algebraic.BoundaryClearing.FunctorialityBaseChange
import Hironaka.Resolution.Algebraic.BoundaryClearing.Tuned
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Scheme.BlowUpSequence.TrivialCenter
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lemma 102 (1)–(2) for `m ≥ 1`, and the assembly over every field

`BD.tunedFunctor hm F hDom'` (`Assembly.lean`) is the tuning device of Step 1 of the proof of
[Kol07, Theorem 103] on the class of Lemma 102: `F(X, W_{s(m)}(I), E)` above the mark, the empty
sequence below it. This module shows that the clauses of [Kol07, Lemma 102] pass through it, as
the `ofTunedClass_*` transfers of `Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean` do
for the class-generic `OrderSeqAssignment.ofTunedClass`, here at `C := BDClass n m j` with the
global `hm : 1 ≤ m` and `max-ord I ≤ m` read off `BDClass` (`hT.2.1`):

* the two values (`tunedFunctor_seq_of_maxOrd_eq`, `tunedFunctor_seq_of_maxOrd_lt`);
* clause (2) (`tunedFunctor_commutesWithSmooth`, `tunedFunctor_commutesWithBaseChange`): the case
  splits of two triples align because `max-ord` does not rise under a smooth pull-back
  (`maxOrd_comap_le_of_smooth`), is preserved by a surjection
  (`maxOrd_le_maxOrd_comap_of_surjective`) and by a change of fields
  (`maxOrd_comap_of_isPullback_specMap`); in the one mixed case, `T` above the mark, its smooth
  pull-back `T'` below, the pulled-back sequence with its empty blow-ups deleted is an order-`m`
  sequence without empty centers for `T'` (`isOrderSeq_eraseEmpty_pullback_of_equidim`), hence
  empty (`eq_nil_of_isOrderSeq_of_maxOrd_lt`).

For `BD.dataFunctor n m j hm B hDom`, the tuned functor applied to the functor of `Output.lean` at
order `s(m)`:

* clause (1) (`disjoint_cosupp_dataFunctor`): above the mark the value is the output of
  `Output.lean` for `(W_{s(m)}(I), s(m))`, whose final cosupport is disjoint from the birational
  transform of `E^j` (`disjoint_cosupp_eraseEmpty_rawSeq`); the same sequence is of order `m` for
  `(I, E)` (`isOrderSeq_tuned_iff`), and `cosupp(I_r, m) = cosupp(W_r, s(m))` at the last stage
  (`le_ord_weakTransformSeq_iff_tuned`, `Tuned.lean`), so the disjointness transfers; below the
  mark the value is empty and `cosupp(I, m) = ∅`.
* clause (2) from `functor_commutesWithSmooth`/`functor_commutesWithBaseChange` of the two
  functoriality modules, through the tuning layer.
* `totalFunctor_zero`/`totalFunctor_succ`: the case split on the mark.
* `bdData`, `exists_bdData`: the assembled `BDData n m j` from the induction hypothesis
  `BMO_{≤ n−1, s(m)}` over every field (given as a Π-bundle over the fields, in the order of
  `BDData`'s fields), with `bdDataZero` at the mark `0`.

Used by `ClauseThree.lean`, `Indifference.lean` and `NilAtUnit.lean`, and outside this directory by
`Hironaka/Resolution/Algebraic/Stage/Congr.lean`, `HironakaExamples/Dimension1.lean` and the
embedded-resolution modules `Hironaka/Resolution/Algebraic/Wlo05/EmbeddedCP1Step21.lean`,
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedCP3Step21.lean`,
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedCP3Tower.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData IsLocalRing Hironaka.BO

namespace Hironaka.BD

variable {k : Type u} [Field k]

section Tuned

variable [CharZero k] {n m j : ℕ} (hm : 1 ≤ m) {Dom' : Triple k → Prop}
  (F : OrderSeqAssignment k (tuningParam m) Dom')
  (hDom' : ∀ T : Triple k, Triple.BDClass n m j T → T.I.maxOrd = m → Dom' (T.tuned m hm))

/-- Above the mark the tuned functor returns `F` on the tuned triple (Step 1 of the proof of
[Kol07, Theorem 103], on the class of Lemma 102). -/
theorem tunedFunctor_seq_of_maxOrd_eq (T : Triple k) (hT : Triple.BDClass n m j T)
    (h : T.I.maxOrd = m) :
    (tunedFunctor hm F hDom').seq T hT = F.seq (T.tuned m hm) (hDom' T hT h) :=
  dite_eq_left h

/-- Below the mark the tuned functor returns the empty sequence (the convention of
[Kol07, Theorem 68]). -/
theorem tunedFunctor_seq_of_maxOrd_lt (T : Triple k) (hT : Triple.BDClass n m j T)
    (h : T.I.maxOrd < m) : (tunedFunctor hm F hDom').seq T hT = BlowUpSequence.nil T.X.left :=
  dite_eq_right h.ne

/-- The tuned functor commutes with smooth morphisms when `F` does ([Kol07, 34.1]): the argument of
`Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean` on `BDClass n m j`. -/
theorem tunedFunctor_commutesWithSmooth (hF : F.CommutesWithSmooth) :
    (tunedFunctor hm F hDom').CommutesWithSmooth :=
  ofTunedClass_commutesWithSmooth F (fun _ _ => hm) hDom' (fun _ hT => hT.2.1) hF

/-- The tuned functors commute with a change of fields when `F` and `F'` do ([Kol07, 34.2]): the
argument of `Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean` on `BDClass n m j`. -/
theorem tunedFunctor_commutesWithBaseChange {L : Type u} [Field L] [CharZero L]
    {Dom'' : Triple L → Prop} (F' : OrderSeqAssignment L (tuningParam m) Dom'')
    (hDom'' : ∀ T : Triple L, Triple.BDClass n m j T → T.I.maxOrd = m → Dom'' (T.tuned m hm))
    (σ : k →+* L) (hF : F.CommutesWithBaseChange F' σ) :
    (tunedFunctor hm F hDom').CommutesWithBaseChange (tunedFunctor hm F' hDom'') σ :=
  ofTunedClass_commutesWithBaseChange F (fun _ _ => hm) hDom' (fun _ hT => hT.2.1) F'
    (fun _ _ => hm) hDom'' σ hF

end Tuned

section Data

variable [CharZero k] (n m j : ℕ) (hm : 1 ≤ m) {Dom : MarkedTriple k → Prop}
  (B : OrderGeSeqAssignment k Dom)
  (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom T')

/-- Above the mark `BD_{n,m,j}` is the functor of `Output.lean` at order `s(m)` on the tuned triple
(the proof of [Kol07, Lemma 102]). -/
theorem dataFunctor_seq_of_maxOrd_eq (T : Triple k) (hT : Triple.BDClass n m j T)
    (h : T.I.maxOrd = m) :
    (dataFunctor n m j hm B hDom).seq T hT =
      (functor n (tuningParam m) j B hDom).seq (T.tuned m hm) (domain_tuned hm hT h) :=
  dite_eq_left h

/-- Below the mark `BD_{n,m,j}` is the empty sequence (the convention of [Kol07, Theorem 68]). -/
theorem dataFunctor_seq_of_maxOrd_lt (T : Triple k) (hT : Triple.BDClass n m j T)
    (h : T.I.maxOrd < m) : (dataFunctor n m j hm B hDom).seq T hT = BlowUpSequence.nil T.X.left :=
  dite_eq_right h.ne

/-- Clause (1) of [Kol07, Lemma 102] for `BD_{n,m,j}` from clause (1) of [Kol07, Theorem 69] for
`B`: clause (1) of `Output.lean` for `(W_{s(m)}(I), s(m))` transported to `(I, m)` at the last stage
by `le_ord_weakTransformSeq_iff_tuned`; below the mark the cosupport is empty. -/
theorem disjoint_cosupp_dataFunctor
    (hB : ∀ (T' : MarkedTriple k) (hT' : Dom T'), (B.endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (T : Triple k) (hT : Triple.BDClass n m j T) :
    Disjoint
      {x | (m : ℕ∞) ≤
        (((dataFunctor n m j hm B hDom).seq T hT).weakTransformSeq T.I (Fin.last _)).ord x}
      ((((dataFunctor n m j hm B hDom).seq T hT).strictTransformSeq (T.E.nth ⟨j, hT.2.2⟩)
        (Fin.last _)).support : Set _) := by
  by_cases h : T.I.maxOrd = m
  · refine (disjoint_cosupp_congr (dataFunctor_seq_of_maxOrd_eq n m j hm B hDom T hT h)
      T.I _ m).mpr ?_
    refine (disjoint_cosupp_congr (functor_seq n (tuningParam m) j B hDom (T.tuned m hm)
      (domain_tuned hm hT h)) T.I _ m).mpr ?_
    obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
    have hord : ((rawSeq (T.tuned m hm) (tuningParam m)
        (monoEquivOfFin (T.tuned m hm).E.ι rfl ⟨j, (domain_tuned hm hT h).2.2.2⟩)
        (domain_tuned hm hT h).2.1 (domain_tuned hm hT h).2.2.1 (domain_tuned hm hT h).1 B
        hDom).eraseEmpty).IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m :=
      (isOrderSeq_tuned_iff _ h hm).mpr
        ((functor n (tuningParam m) j B hDom).isOrderSeq (T.tuned m hm) (domain_tuned hm hT h))
    have hland := disjoint_cosupp_eraseEmpty_rawSeq (T.tuned m hm) (tuningParam m)
      (monoEquivOfFin (T.tuned m hm).E.ι rfl ⟨j, (domain_tuned hm hT h).2.2.2⟩)
      (domain_tuned hm hT h).2.1 (domain_tuned hm hT h).2.2.1 (domain_tuned hm hT h).1 B hDom hB
    rw [Set.disjoint_left] at hland ⊢
    intro x hx hx'
    have hx2 := (le_ord_weakTransformSeq_iff_tuned (T.X.left ↘ Spec (.of k)) d _ T.I T.E m h hm hord
      (Fin.last _) x).mp hx
    exact hland hx2 hx'
  · have hl : T.I.maxOrd < m := lt_of_le_of_ne hT.2.1 h
    refine (disjoint_cosupp_congr (dataFunctor_seq_of_maxOrd_lt n m j hm B hDom T hT hl)
      T.I _ m).mpr ?_
    rw [Set.disjoint_left]
    intro x hx _
    have hx' : (m : ℕ∞) ≤ T.I.ord x := hx
    exact absurd hx' (not_le.mpr ((maxOrd_lt_iff_forall_ord_lt T.I hm).mp hl x))

/-- `BD_{n,m,j}` commutes with smooth morphisms when `B` does ([Kol07, 34.1]):
`functor_commutesWithSmooth` through the tuning layer. -/
theorem dataFunctor_commutesWithSmooth (hB : B.CommutesWithSmooth) :
    (dataFunctor n m j hm B hDom).CommutesWithSmooth :=
  tunedFunctor_commutesWithSmooth hm _ _ (functor_commutesWithSmooth n (tuningParam m) j B hDom hB)

/-- `BD_{n,m,j}` over `k` and over `L` commute with a change of fields when `B` and `B'` do
([Kol07, 34.2]): `functor_commutesWithBaseChange` through the tuning layer. -/
theorem dataFunctor_commutesWithBaseChange {L : Type u} [Field L] [CharZero L]
    {Dom' : MarkedTriple L → Prop} (B' : OrderGeSeqAssignment L Dom')
    (hDom' : ∀ T' : MarkedTriple L, T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom' T')
    (σ : k →+* L) (hB : B.CommutesWithBaseChange B' σ) :
    (dataFunctor n m j hm B hDom).CommutesWithBaseChange (dataFunctor n m j hm B' hDom') σ :=
  tunedFunctor_commutesWithBaseChange hm _ _ _ _ σ
    (functor_commutesWithBaseChange n (tuningParam m) j B hDom B' hDom' σ hB)

end Data

section Total

variable [CharZero k] (n j : ℕ) {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)

/-- The case split at the mark `0`. -/
theorem totalFunctor_zero
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam 0 → Dom T') :
    totalFunctor n 0 j B hDom = zeroFunctor n j :=
  rfl

/-- The case split at a mark `m + 1`. -/
theorem totalFunctor_succ (m : ℕ)
    (hDom : ∀ T' : MarkedTriple k,
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam (m + 1) → Dom T') :
    totalFunctor n (m + 1) j B hDom = dataFunctor n (m + 1) j (Nat.le_add_left 1 m) B hDom :=
  rfl

end Total

/-- **`BD_{n,m,j}` over every field of characteristic zero** (clauses (1)–(2) of
[Kol07, Lemma 102]), from the induction hypothesis `BMO_{≤ n−1, s(m)}` given as a Π-bundle over the
fields (the functors, clause (1) of [Kol07, Theorem 69], commutation with smooth morphisms,
commutation with change of fields, in the order of `BDData`'s fields), by a case split on the mark:
`bdDataZero` at `0`, the tuned assembly at `m + 1`. -/
noncomputable def bdData (n : ℕ) : (m j : ℕ) →
    (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop) →
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k)) →
    (∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T') →
    (∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞)) →
    (∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth) →
    (∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ) →
    BDData.{u} n m j
  | 0, j, _, _, _, _, _, _ => bdDataZero n j
  | m + 1, j, _, B, hDom, hB, hsm, hbc =>
    { functor := fun k _ _ => dataFunctor n (m + 1) j (Nat.le_add_left 1 m) (B k) (hDom k)
      disjoint_cosupp := fun k _ _ T hT =>
        disjoint_cosupp_dataFunctor n (m + 1) j (Nat.le_add_left 1 m) (B k) (hDom k) (hB k) T hT
      commutesWithSmooth := fun k _ _ =>
        dataFunctor_commutesWithSmooth n (m + 1) j (Nat.le_add_left 1 m) (B k) (hDom k) (hsm k)
      commutesWithBaseChange := fun k L _ _ _ _ σ =>
        dataFunctor_commutesWithBaseChange n (m + 1) j (Nat.le_add_left 1 m) (B k) (hDom k) (B L)
          (hDom L) σ (hbc k L σ) }

/-- Clauses (1)–(2) of [Kol07, Lemma 102]: a `BDData n m j` whose functor over `k` is
`totalFunctor n m j (B k) (hDom k)` (existential form of `bdData`). -/
theorem exists_bdData (n m j : ℕ)
    (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ) :
    ∃ D : BDData n m j, ∀ (k : Type u) [Field k] [CharZero k] (T : Triple k)
      (hT : Triple.BDClass n m j T),
      (D.functor k).seq T hT = (totalFunctor n m j (B k) (hDom k)).seq T hT :=
  ⟨bdData n m j Dom B hDom hB hsm hbc, fun k _ _ T hT => by cases m <;> rfl⟩

end Hironaka.BD
