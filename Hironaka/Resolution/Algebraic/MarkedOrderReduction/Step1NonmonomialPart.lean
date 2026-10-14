/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Basic
public import Hironaka.Resolution.Algebraic.OrderReduction.Basic
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Scheme.BlowUpSequence.Concat
public import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Transform
public import Hironaka.Scheme.BlowUpSequence.ConcatMarked
public import Hironaka.Scheme.BlowUpSequence.ConcatTransforms
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.MarkedLeWeak
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.IdealSheaf.Order.MaxOrdAnti
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 1 of marked order reduction: reducing the order of the nonmonomial part below the mark

Step 1 of the proof of [Kol07, Theorem 107] ([Kol07, 111, Step 1]) reduces the order of the
nonmonomial part: if `ord N(I) ≥ m`, order reduction for ideals ([Kol07, Theorem 68]) is applied to
`N(I)` until its order drops below `m`, reaching some `Π_1 : X^1 → X`; the birational transforms
`(Π_1)^{-1}_* N(I)` and `(Π_1)^{-1}_*(I, m)` differ only by an ideal sheaf of exceptional divisors,
hence only in their monomial part, so `N((Π_1)^{-1}_*(I, m)) = (Π_1)^{-1}_* N(I)` and the maximal
order of the nonmonomial part is now `< m`.

## Conventions

"Until its order drops below `m`" is read as a loop. The functor `BO_d` of [Kol07, Theorem 68] is
defined only on triples with `max-ord ≤ d`, so a round applies `BO_{n,d}(X, N(I), E)` at the
current `d := max-ord N(I) ≥ m`; the round is a smooth blow-up sequence of order `d ≥ m` for
`N(I)`, hence of order `≥ m` for `(I, m)`; after it the nonmonomial part of the induced marked
ideal has maximal order `< d`; and the loop repeats, terminating on the strictly decreasing natural
number `d`. The input is order reduction for ideals in dimension `n` at every mark,
`bo : ∀ d, BOData n d`, since the orders `d` that occur are not bounded in terms of `m`. Kollár's
equation `N((Π_1)^{-1}_*(I, m)) = (Π_1)^{-1}_* N(I)` without the outer `N` on the right is not
asserted; what Step 1 uses is the equality of the nonmonomial parts and
`max-ord N(J) ≤ max-ord J`.

* `nonmonomialTriple T`: the unmarked triple `(X, N(I), E)` of a marked triple `(X, I, m, E)`.
* `roundOrder T`: the loop variable `d = max-ord N(I)`, a natural number (the maximal order is
  finite on a triple's Noetherian scheme for an ideal sheaf nonzero on every component;
  `coe_roundOrder`).
* `step1Round bo T hT hd`: one round, `BO_{n,d}(X, N(I), E)` for `m ≤ d`
  (`boClass_nonmonomialTriple`: `(X, N(I), E)` lies in `BOClass n d`); it is a smooth blow-up
  sequence of order `≥ m` for `(X, I, m, E)` (`step1Round_isOrderGeSeq`, since `I ⊆ N(I)` gives
  `ord_Z I ≥ ord_Z N(I)` at every centre) without empty blow-ups.
* `roundTriple bo T hT hd`: the marked triple `(X^1, (Π_1)^{-1}_*(I, m), m, (Π_1)^{-1}_{tot} E)`
  induced at the end of the round (`MarkedTriple.induced`), again of `BMOClass n m`
  (`bmoClass_roundTriple`), with `max-ord N((Π_1)^{-1}_*(I, m)) < d`
  (`maxOrd_nonmonomialPart_roundTriple_lt`, `roundOrder_roundTriple_lt`): along the round,
  `N(Π^{-1}_{i *}(I, m)) = N(Π^{-1}_{i *} N(I))` at every stage
  (`nonmonomialPart_markedTransformSeq_last_eq`, iterating `nonmonomialPart_markedTransform` for
  the marked triples `(X_i, I_i, m, E_i)` and `(X_i, J_i, d, E_i)`), and
  `max-ord N(J_r) ≤ max-ord J_r < d` by `maxOrd_anti` and clause (1) of [Kol07, Theorem 103].
* `step1 bo T hT`: **Step 1**, by well-founded recursion on `roundOrder T`: the empty sequence once
  `d < m`, and otherwise the round followed by Step 1 of the induced marked triple (`concat`);
  carried with it, it is a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)`
  (`isOrderGeSeq_concat`) without empty blow-ups (`noEmptyCenters_concat`). The unfolding
  equations are `step1_of_lt` and `step1_of_le`, and the result of Step 1 is
  `maxOrd_nonmonomialPart_step1_lt`: `max-ord N((Π_1)^{-1}_*(I, m)) < m` at the end.

Step 1 is followed by Step 2
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step2Separation.lean`) and Step 3
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Input.lean`) in the assembly of the
functor (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Assembly.lean`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka
  Scheme.IdealSheafData Scheme BlowUpSequence

namespace Hironaka.BMO

section Idempotent

variable {k : Type u} [Field k] [CharZero k] (T : Triple k)

/-- The nonmonomial part is idempotent, `N(N(I)) = N(I)`: `N(I)` is `I` with the monomial `M(I)`
divided out, and the nonmonomial part ignores monomials (`nonmonomialPart_monomial_mul`). Not in
the sources. -/
theorem nonmonomialPart_nonmonomialPart :
    nonmonomialPart (nonmonomialPart T.I T.E) T.E = nonmonomialPart T.I T.E := by
  have h := nonmonomialPart_monomial_mul T (fun η => (T.I.ord η).toNat) (nonmonomialPart T.I T.E)
    (isNonzeroEverywhere_nonmonomialPart T)
  rw [← monomialPart_eq_monomial T.I T.E, monomialPart_mul_nonmonomialPart] at h
  exact h.symm

end Idempotent

section Invariant

variable {k : Type u} [Field k] [CharZero k]

/-- The recursion behind `nonmonomialPart_markedTransformSeq_last_eq`, by induction on the length
of the sequence (the marked triple advances to `blowUpTriple` at each step, so the induction is on
the length, not structural on a sequence over a fixed scheme). -/
theorem nonmonomialPart_markedTransformSeq_last_eq_aux (l : ℕ) :
    ∀ (T : MarkedTriple k) (S : BlowUpSequence T.X.left), S.length = l →
      ∀ {J : T.X.left.IdealSheafData}, IsNonzeroEverywhere J → ∀ {d : ℕ},
        S.IsOrderSeq (T.X.left ↘ Spec (.of k)) J T.E d →
        S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E →
        nonmonomialPart T.I T.E = nonmonomialPart J T.E →
        nonmonomialPart (S.markedTransformSeq T.I T.m (Fin.last _))
            (S.totalTransformSeq T.E (Fin.last _)) =
          nonmonomialPart (S.weakTransformSeq J (Fin.last _))
            (S.totalTransformSeq T.E (Fin.last _)) := by
  induction l with
  | zero =>
    intro T S hl J hJ d hS hge hN
    cases S with
    | nil => exact hN
    | cons _ D rest => exact absurd hl (Nat.succ_ne_zero _)
  | succ l ih =>
    intro T S hl J hJ d hS hge hN
    cases S with
    | nil => exact absurd hl (Nat.zero_ne_add_one _)
    | cons _ D rest =>
      obtain ⟨⟨hD, hsnc, hord⟩, ht⟩ := (isOrderSeq_cons_iff _ J T.E d D rest).1 hS
      obtain ⟨⟨-, -, hle⟩, hget⟩ := (isOrderGeSeq_cons_iff _ T.I T.E T.m D rest).1 hge
      have hZ : T.IsOrderGeBlowUp D := ⟨hD, hsnc, hle⟩
      obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
      let Tj : MarkedTriple k := { T with I := J, isNonzeroEverywhere := hJ, m := d }
      have hZj : Tj.IsOrderGeBlowUp D := ⟨hD, hsnc, fun η hη => (hord η hη).ge⟩
      have hJ' : IsNonzeroEverywhere (J.weakTransform D) :=
        isNonzeroEverywhere_weakTransform (T.X.left ↘ Spec (.of k)) D hD J hJ
      have e : ((blowUpTriple T D hZ).X.left ↘ Spec (.of k)) =
          D.blowUpπ ≫ (T.X.left ↘ Spec (.of k)) := by
        change (𝟙 _ ≫ D.blowUpπ) ≫ _ = _
        rw [Category.id_comp]
      have hS' : rest.IsOrderSeq ((blowUpTriple T D hZ).X.left ↘ Spec (.of k)) (J.weakTransform D)
          (blowUpTriple T D hZ).E d := by
        rw [e]
        exact ht
      have hge' : rest.IsOrderGeSeq ((blowUpTriple T D hZ).X.left ↘ Spec (.of k))
          (blowUpTriple T D hZ).I (blowUpTriple T D hZ).m (blowUpTriple T D hZ).E := by
        rw [e]
        exact hget
      have hN' : nonmonomialPart (blowUpTriple T D hZ).I (blowUpTriple T D hZ).E =
          nonmonomialPart (J.weakTransform D) (blowUpTriple T D hZ).E := by
        have h1 := nonmonomialPart_markedTransform T D hZ
        have h2 := nonmonomialPart_markedTransform Tj D hZj
        have h3 := weakTransform_eq_markedTransform_of_smooth (T.X.left ↘ Spec (.of k)) n D J hord
        change nonmonomialPart (T.I.markedTransform D T.m) (T.E.totalTransform D) =
          nonmonomialPart (J.weakTransform D) (T.E.totalTransform D)
        rw [h1, hN, h3]
        exact h2.symm
      exact ih (blowUpTriple T D hZ) rest (Nat.succ.inj hl) hJ' hS' hge' hN'

/-- Along a smooth blow-up sequence `S` of order `d` for `(X, J, E)` which is also of order `≥ m`
for the marked triple `T = (X, I, m, E)`, if `N(I) = N(J)` then the nonmonomial parts of the
induced marked ideal `Π^{-1}_*(I, m)` and of the induced birational transform `Π^{-1}_* J` agree at
the end of `S`, with respect to the induced boundary ([Kol07, 111, Step 1]:
"`N((Π_1)^{-1}_*(I, m)) = (Π_1)^{-1}_* N(I)`", read modulo `N` at every stage and iterated). One
stage applies `nonmonomialPart_markedTransform` twice: to `(X_i, I_i, m, E_i)`, giving
`N(I_{i+1}) = N(π^* N(I_i))`, and to `(X_i, J_i, d, E_i)`, whose marked transform at the exact
order `d` is the birational transform (`weakTransform_eq_markedTransform_of_smooth`), giving
`N(J_{i+1}) = N(π^* N(J_i))`. By recursion on `S`, the marked triple advancing to `blowUpTriple`. -/
theorem nonmonomialPart_markedTransformSeq_last_eq (T : MarkedTriple k)
    (S : BlowUpSequence T.X.left) {J : T.X.left.IdealSheafData} (hJ : IsNonzeroEverywhere J) {d : ℕ}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) J T.E d)
    (hge : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (hN : nonmonomialPart T.I T.E = nonmonomialPart J T.E) :
    nonmonomialPart (S.markedTransformSeq T.I T.m (Fin.last _))
        (S.totalTransformSeq T.E (Fin.last _)) =
      nonmonomialPart (S.weakTransformSeq J (Fin.last _))
        (S.totalTransformSeq T.E (Fin.last _)) :=
  nonmonomialPart_markedTransformSeq_last_eq_aux S.length T S rfl hJ hS hge hN

end Invariant

section Round

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)
  (T : MarkedTriple k)

/-- The unmarked triple `(X, N(I), E)` of the marked triple `(X, I, m, E)` ([Kol07, 111]: "we write
`I = M(I) · N(I)` and try to deal with the two parts separately"; Step 1 applies (68) "to `N(I)`"):
the ambient scheme and the boundary of `T`, the ideal its nonmonomial part, nonzero on every
component by `isNonzeroEverywhere_nonmonomialPart`. -/
noncomputable def nonmonomialTriple : Triple k :=
  { T.toTriple with
    I := nonmonomialPart T.I T.E
    isNonzeroEverywhere := isNonzeroEverywhere_nonmonomialPart T.toTriple }

omit [CharZero k] in
theorem nonmonomialTriple_X : (nonmonomialTriple T).X.left = T.X.left := rfl

omit [CharZero k] in
theorem nonmonomialTriple_I : (nonmonomialTriple T).I = nonmonomialPart T.I T.E := rfl

omit [CharZero k] in
theorem nonmonomialTriple_E : (nonmonomialTriple T).E = T.E := rfl

/-- The loop variable of Step 1, `d = max-ord N(I)`, as a natural number (`coe_roundOrder`: the
maximal order is finite). -/
noncomputable def roundOrder : ℕ := (nonmonomialPart T.I T.E).maxOrd.toNat

/-- `(roundOrder T : ℕ∞) = max-ord N(I)`: the maximal order of an ideal sheaf nonzero on every
component is finite on the Noetherian scheme of a triple (`maxOrd_ne_top`). -/
theorem coe_roundOrder : (roundOrder T : ℕ∞) = (nonmonomialPart T.I T.E).maxOrd := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have := Hironaka.BD.noetherianSpace_triple T.toTriple
  exact ENat.natCast_toNat (maxOrd_ne_top _ (T.X.left ↘ Spec (.of k)) n'
    (isNonzeroEverywhere_nonmonomialPart T.toTriple))

/-- For `m ≤ d = max-ord N(I)`, the triple `(X, N(I), E)` lies in the domain `BOClass n d` of
`BO_{n,d}` ([Kol07, Theorem 68]: "defined on triples `(X, I, E)` with `max-ord I ≤ m`"): the mark
`d ≥ m ≥ 1`, the dimension bound of `T`, and `max-ord N(I) ≤ d` by definition of `d`. -/
theorem boClass_nonmonomialTriple (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    Triple.BOClass n (roundOrder T) (nonmonomialTriple T) :=
  ⟨hT.1.trans hd, hT.2.1, (coe_roundOrder T).ge⟩

/-- **One round of Step 1** ([Kol07, 111, Step 1]: "apply order reduction (68) to `N(I)`"): the
value of `BO_{n,d}` at the current order `d = max-ord N(I) ≥ m` on the triple `(X, N(I), E)`. -/
noncomputable def step1Round (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    BlowUpSequence T.X.left :=
  ((bo (roundOrder T)).functor k).seq (nonmonomialTriple T) (boClass_nonmonomialTriple T hT hd)

theorem step1Round_eq (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    step1Round bo T hT hd =
      ((bo (roundOrder T)).functor k).seq (nonmonomialTriple T)
        (boClass_nonmonomialTriple T hT hd) :=
  rfl

/-- The round is a smooth blow-up sequence of order `d` for `(X, N(I), E)` (the functor's field;
[Kol07, Theorem 68]). -/
theorem step1Round_isOrderSeq (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    (step1Round bo T hT hd).IsOrderSeq (T.X.left ↘ Spec (.of k)) (nonmonomialPart T.I T.E) T.E
      (roundOrder T) :=
  ((bo (roundOrder T)).functor k).isOrderSeq _ _

/-- The round contains no empty blow-up (the functor's field; [Kol07, 32]). -/
theorem step1Round_noEmptyCenters (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    (step1Round bo T hT hd).NoEmptyCenters :=
  ((bo (roundOrder T)).functor k).noEmptyCenters _ _

/-- The birational transform of `N(I)` at the end of the round has maximal order `< d` (clause (1)
of [Kol07, Theorem 103] for the round at order `d`; `BOData.maxOrd_lt`). -/
theorem maxOrd_weakTransformSeq_step1Round_lt (hT : MarkedTriple.BMOClass n m T)
    (hd : m ≤ roundOrder T) :
    ((step1Round bo T hT hd).weakTransformSeq (nonmonomialPart T.I T.E) (Fin.last _)).maxOrd <
      (roundOrder T : ℕ∞) :=
  (bo (roundOrder T)).maxOrd_lt k _ _

/-- **The round is a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`**
([Kol07, 111, Step 1]): the same centres, smooth and with normal crossings with the same boundaries
`E_i`, and `ord_{Z_i} I_i ≥ ord_{Z_i} J_i = d ≥ m` at every stage since `I_i ⊆ J_i`
(`isOrderGeSeq_of_isOrderSeq_of_le` with `I ⊆ N(I) = (I : M(I))`). -/
theorem step1Round_isOrderGeSeq (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    (step1Round bo T hT hd).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hmd : T.m ≤ roundOrder T := by
    rw [hT.2.2]
    exact hd
  exact isOrderGeSeq_of_isOrderSeq_of_le (T.X.left ↘ Spec (.of k)) n' hmd
    (step1Round_isOrderSeq bo T hT hd) (le_colon_self _ _)

/-- The marked triple `(X^1, (Π_1)^{-1}_*(I, m), m, (Π_1)^{-1}_{tot} E)` induced at the end of one
round ([Kol07, 111, Step 1]: "this happens at some `Π_1 : X^1 → X`"; `MarkedTriple.induced` through
`step1Round_isOrderGeSeq`). -/
noncomputable def roundTriple (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    MarkedTriple k :=
  T.induced (step1Round bo T hT hd) (step1Round_isOrderGeSeq bo T hT hd) (Fin.last _)

theorem roundTriple_X (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    (roundTriple bo T hT hd).X.left = (step1Round bo T hT hd).last :=
  rfl

theorem roundTriple_I (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    (roundTriple bo T hT hd).I =
      (step1Round bo T hT hd).markedTransformSeq T.I T.m (Fin.last _) :=
  rfl

theorem roundTriple_E (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    (roundTriple bo T hT hd).E = (step1Round bo T hT hd).totalTransformSeq T.E (Fin.last _) :=
  rfl

theorem roundTriple_m (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    (roundTriple bo T hT hd).m = T.m :=
  rfl

/-- The induced marked triple after a round is again of `BMOClass n m`: the stages of a smooth
blow-up sequence are smooth of the same relative dimension
(`IsSmooth.stageMap_smoothOfRelativeDimension`), and the mark is unchanged. -/
theorem bmoClass_roundTriple (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    MarkedTriple.BMOClass n m (roundTriple bo T hT hd) := by
  obtain ⟨n', hn'n, hn'⟩ := hT.2.1
  have : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  exact ⟨hT.1, ⟨n', hn'n,
    IsSmooth.stageMap_smoothOfRelativeDimension (step1Round_isOrderGeSeq bo T hT hd).1
      (Fin.last _)⟩, hT.2.2⟩

/-- **After a round at order `d`, the nonmonomial part of the induced marked ideal has maximal
order `< d`** ([Kol07, 111, Step 1]: the nonmonomial part of the marked transform after `Π_1` is
the marked transform of `N(I)`, which reduces the proof to the case `max-ord N(I) < m`; here the
drop of one round): `N(Π_1^{-1}_*(I, m)) = N(Π_1^{-1}_* N(I))` along the round
(`nonmonomialPart_markedTransformSeq_last_eq` at `J = N(I)`, with `N(N(I)) = N(I)`), `N(J) ⊇ J`
gives `max-ord N(J) ≤ max-ord J` (`maxOrd_anti`), and clause (1) of [Kol07, Theorem 103] gives
`max-ord Π_1^{-1}_* N(I) < d`. -/
theorem maxOrd_nonmonomialPart_roundTriple_lt (hT : MarkedTriple.BMOClass n m T)
    (hd : m ≤ roundOrder T) :
    (nonmonomialPart (roundTriple bo T hT hd).I (roundTriple bo T hT hd).E).maxOrd <
      (roundOrder T : ℕ∞) := by
  have h1 := nonmonomialPart_markedTransformSeq_last_eq T (step1Round bo T hT hd)
    (isNonzeroEverywhere_nonmonomialPart T.toTriple) (step1Round_isOrderSeq bo T hT hd)
    (step1Round_isOrderGeSeq bo T hT hd) (nonmonomialPart_nonmonomialPart T.toTriple).symm
  change (nonmonomialPart ((step1Round bo T hT hd).markedTransformSeq T.I T.m (Fin.last _))
    ((step1Round bo T hT hd).totalTransformSeq T.E (Fin.last _))).maxOrd < _
  rw [h1]
  exact lt_of_le_of_lt (maxOrd_anti (le_colon_self _ _))
    (maxOrd_weakTransformSeq_step1Round_lt bo T hT hd)

/-- The loop variable strictly decreases along a round: the termination measure of Step 1. -/
theorem roundOrder_roundTriple_lt (hT : MarkedTriple.BMOClass n m T) (hd : m ≤ roundOrder T) :
    roundOrder (roundTriple bo T hT hd) < roundOrder T := by
  have h : (roundOrder (roundTriple bo T hT hd) : ℕ∞) < (roundOrder T : ℕ∞) := by
    rw [coe_roundOrder (roundTriple bo T hT hd)]
    exact maxOrd_nonmonomialPart_roundTriple_lt bo T hT hd
  exact_mod_cast h

end Round

section Step1

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)

/-- **Step 1 of the proof of [Kol07, Theorem 107]**, `Π_1 : X^1 → X` ([Kol07, 111, Step 1]: order
reduction for ideals, [Kol07, Theorem 68], is applied to `N(I)` until its order drops below `m`,
which happens at some `Π_1 : X^1 → X`), by well-founded recursion on the loop variable
`d = max-ord N(I)`: the empty
sequence once `d < m`, and otherwise one round `BO_{n,d}(X, N(I), E)` followed by Step 1 of the
induced marked triple `(X^1, (Π_1)^{-1}_*(I, m), m, (Π_1)^{-1}_{tot} E)`, whose loop variable is
smaller (`roundOrder_roundTriple_lt`). Carried with the sequence: it is a smooth blow-up sequence
of order `≥ m` starting with `(X, I, m, E)` (`isOrderGeSeq_concat` with `step1Round_isOrderGeSeq`)
without empty blow-ups (`noEmptyCenters_concat`). `BO_{n,d}` is called only for `d ≥ m ≥ 1`. -/
noncomputable def step1 (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    {S : BlowUpSequence T.X.left // S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧
      S.NoEmptyCenters} :=
  if hd : m ≤ roundOrder T then
    let R := step1 (roundTriple bo T hT hd) (bmoClass_roundTriple bo T hT hd)
    ⟨(step1Round bo T hT hd).concat R.1,
      isOrderGeSeq_concat _ _ _ (step1Round_isOrderGeSeq bo T hT hd) R.2.1,
      noEmptyCenters_concat _ _ (step1Round_noEmptyCenters bo T hT hd) R.2.2⟩
  else ⟨BlowUpSequence.nil T.X.left, isOrderGeSeq_nil _ _ _ _, fun i => i.elim0⟩
termination_by roundOrder T
decreasing_by exact roundOrder_roundTriple_lt bo T hT hd

/-- Below the mark, Step 1 is the empty sequence ([Kol07, 111, Step 1]: "if `ord N(I) ≥ m`";
otherwise nothing is done). -/
theorem step1_of_lt (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T)
    (h : roundOrder T < m) : (step1 bo T hT).1 = BlowUpSequence.nil T.X.left := by
  rw [step1, dite_eq_right (not_le.mpr h)]

/-- At or above the mark, Step 1 is one round followed by Step 1 of the induced marked triple (the
loop unrolled once). -/
theorem step1_of_le (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T)
    (hd : m ≤ roundOrder T) :
    (step1 bo T hT).1 =
      (step1Round bo T hT hd).concat
        (step1 bo (roundTriple bo T hT hd) (bmoClass_roundTriple bo T hT hd)).1 := by
  rw [step1, dite_eq_left hd]

/-- Step 1 is a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`
([Kol07, Definition 66] for `Π_1`). -/
theorem step1_isOrderGeSeq (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    (step1 bo T hT).1.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
  (step1 bo T hT).2.1

/-- Step 1 contains no empty blow-up ([Kol07, 32]). -/
theorem step1_noEmptyCenters (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    (step1 bo T hT).1.NoEmptyCenters :=
  (step1 bo T hT).2.2

/-- The induction behind `maxOrd_nonmonomialPart_step1_lt`, on a bound `l` for the loop variable,
following the recursion of `step1`. -/
theorem maxOrd_nonmonomialPart_step1_lt_aux (l : ℕ) :
    ∀ (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T), roundOrder T ≤ l →
      (nonmonomialPart ((step1 bo T hT).1.markedTransformSeq T.I T.m (Fin.last _))
        ((step1 bo T hT).1.totalTransformSeq T.E (Fin.last _))).maxOrd < (m : ℕ∞) := by
  induction l with
  | zero =>
    intro T hT hl
    have hlt : roundOrder T < m := lt_of_le_of_lt hl hT.1
    rw [step1_of_lt bo T hT hlt]
    change (nonmonomialPart T.I T.E).maxOrd < (m : ℕ∞)
    rw [← coe_roundOrder]
    exact_mod_cast hlt
  | succ l ih =>
    intro T hT hl
    by_cases hd : m ≤ roundOrder T
    · rw [step1_of_le bo T hT hd]
      exact (markedEnd_concat_iff (fun {Y} I' E' => (nonmonomialPart I' E').maxOrd < (m : ℕ∞))
        _ _ _ _ _).mpr
        (ih (roundTriple bo T hT hd) (bmoClass_roundTriple bo T hT hd)
          (Nat.lt_succ_iff.mp (lt_of_lt_of_le (roundOrder_roundTriple_lt bo T hT hd) hl)))
    · have hlt : roundOrder T < m := not_le.mp hd
      rw [step1_of_lt bo T hT hlt]
      change (nonmonomialPart T.I T.E).maxOrd < (m : ℕ∞)
      rw [← coe_roundOrder]
      exact_mod_cast hlt

/-- **At the end of Step 1, `max-ord N((Π_1)^{-1}_*(I, m)) < m`** with respect to the induced
boundary `(Π_1)^{-1}_{tot} E` ([Kol07, 111, Step 1]: "we have reduced to the case where the maximal
order of the nonmonomial part is `< m`"). By induction along the loop: below the mark the sequence
is empty and `max-ord N(I) < m` is the exit condition; otherwise the end data of `round ++ rest`
are the end data of `rest` for the induced marked triple (`markedEnd_concat_iff`), where the
statement holds by induction. -/
theorem maxOrd_nonmonomialPart_step1_lt (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    (nonmonomialPart ((step1 bo T hT).1.markedTransformSeq T.I T.m (Fin.last _))
      ((step1 bo T hT).1.totalTransformSeq T.E (Fin.last _))).maxOrd < (m : ℕ∞) :=
  maxOrd_nonmonomialPart_step1_lt_aux bo (roundOrder T) T hT le_rfl

/-- The loop variable of the marked triple induced at the end of Step 1 is below the mark: the form
in which Step 2 receives the result ([Kol07, 111]: "from now on we may assume that
`max-ord N(I) < m`"). -/
theorem roundOrder_induced_step1_lt (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    roundOrder (T.induced (step1 bo T hT).1 (step1_isOrderGeSeq bo T hT) (Fin.last _)) < m := by
  have h : (roundOrder (T.induced (step1 bo T hT).1 (step1_isOrderGeSeq bo T hT) (Fin.last _)) :
      ℕ∞) < (m : ℕ∞) := by
    rw [coe_roundOrder]
    exact maxOrd_nonmonomialPart_step1_lt bo T hT
  exact_mod_cast h

end Step1

end Hironaka.BMO
