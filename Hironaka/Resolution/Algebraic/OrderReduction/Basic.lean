/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
public import Hironaka.Algebra.Local.TuningParam
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.BoundaryClearing.Tuned
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.Functor
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The order-reduction functor `BO_{n,m}`: its class, its data and the tuned triple

Kollár's order reduction for ideals in dimension `n`, [Kol07, Theorem 103]: assuming order
reduction for marked ideals in dimensions `< n`, for every `m` there is a smooth blow-up sequence
functor `BO_{n,m}` of order `m`, defined on triples `(X, I, E)` with `dim X = n` and
`max-ord I ≤ m`, such that (1) the final birational transform `I_r` has `max-ord I_r < m`, and
(2) `BO_{n,m}` commutes with smooth morphisms and with change of fields ([Kol07, 34.1–34.2]).
This module fixes the vocabulary in which the theorem is stated and proved in
`Hironaka/Resolution/Algebraic/OrderReduction/` and formalises Step 1 of Kollár's proof.

* `Triple.BOClass n m` is the domain of `BO_{n,m}`: the triples with `dim X ≤ n` and
  `max-ord I ≤ m`, for a mark `m ≥ 1`. Kollár's `dim X = n` is read as `dim X ≤ n`, the convention
  of every functoriality class of this development, so that the inductive hypothesis is invoked at
  the triple's own dimension; at `m = 0` clause (1) has no solution on a nonempty scheme, so the
  class is empty there.
* `BOData n m` packages clauses (1)–(2) of Theorem 103: a smooth blow-up sequence functor of order
  `m` on `BOClass n m` for every field of characteristic zero at once, whose final ideal has
  maximal order `< m` and which commutes with smooth morphisms and with change of fields. The
  existence of such data under the inductive hypothesis is Theorem 103 itself
  (`Hironaka.BO.data` in `Hironaka/Resolution/Algebraic/OrderReduction/Step3Data.lean`); clause (3)
  of the theorem is `Hironaka/Resolution/Algebraic/OrderReduction/ClosedEmbedding.lean`.
* `Triple.tuned T m hm` is Step 1 of the proof ("Tuning I"): the triple `(X, W(I), E)` in which
  `W(I) = W_{s(m)}(I)` is the maximal coefficient ideal of [Kol07, Definition 98] at the exponent
  `s(m) = tuningParam m`. Since `W_s(I)` contains `I^s`, it is nonzero on every component
  (`isNonzeroEverywhere_W`).
* `OrderSeqAssignment.ofTunedClass` and `OrderSeqAssignment.ofTuned` are Step 1 as a construction:
  from a smooth blow-up sequence functor `B` of order `s(m)` defined on the tuned triples, the
  functor of order `m` that assigns to `(X, I, E)` the sequence `B(X, W(I), E)` when `max-ord I = m`
  and the empty sequence otherwise (the case `max-ord I < m` is trivial, `X_r = X`, as remarked
  after [Kol07, Theorem 68]). It is of order `m` by [Kol07, Corollary 101]: a smooth blow-up
  sequence is of order `m` for `(X, I, E)` iff it is of order `s(m)` for `(X, W_{s(m)}(I), E)`.
* `BOData.ext`: two `BOData n m` with the same values are equal.

## Conventions

The tuning exponent is `tuningParam m = max (m − 1) 1 · lcm(2, …, m)`, an admissible choice in
[Kol07, Corollary 101] (`s = r · lcm(2, …, m)` with `r ≥ m − 1`); Kollár's text takes `s = m!`.
The tuning ideal `W f I m s` takes the mark `m` as a parameter, so `T.tuned m hm` is Kollár's
`W(I)` exactly when `max-ord I = m`, the only case in which `ofTuned` evaluates its argument on it.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData IsLocalRing

namespace Hironaka

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

/-- The domain of the order-reduction functor `BO_{n,m}` of [Kol07, Theorem 103]: the triples
`(X, I, E)` with `dim X ≤ n` and `max-ord I ≤ m`, for a mark `m ≥ 1`. Kollár states the theorem
for `dim X = n`; the weaker bound is the convention of every functoriality class of this
development, so that the inductive hypothesis is invoked at the triple's own dimension. Clause (1)
of the theorem, `max-ord I_r < m`, has no solution on a nonempty scheme when `m = 0`, so `1 ≤ m`
is part of the class. Reducible, so that its three clauses are projections of the hypothesis `hT`
under instance transparency. -/
abbrev BOClass (n m : ℕ) (T : Triple k) : Prop :=
  1 ≤ m ∧ T.HasDimLE n ∧ T.I.maxOrd ≤ (m : ℕ∞)

end AlgebraicGeometry.Triple

namespace Hironaka

/-- **Clauses (1)–(2) of [Kol07, Theorem 103] as data.** For every field `k` of characteristic
zero, a smooth blow-up sequence functor of order `m` on the triples of `BOClass n m`
(`OrderSeqFunctor`: [Kol07, Definition 31] with the order condition of [Kol07, Definition 66] and
the convention of [Kol07, 32] that the output contains no empty blow-up), such that (1) for every
triple `(X, I, E)` of the class with `BO_{n,m}(X, I, E) = Π : X_r → ⋯ → X_0 = X` the final
birational transform `I_r = Π^{-1}_* I` has `max-ord I_r < m`, and (2) the functor commutes with
smooth morphisms ([Kol07, 34.1], `CommutesWithSmooth`) and with change of fields ([Kol07, 34.2],
`CommutesWithBaseChange`, relating the functors over `k` and over `L`). Theorem 103 asserts the
existence of such data under the inductive hypothesis; it is constructed as `Hironaka.BO.data` in
`Hironaka/Resolution/Algebraic/OrderReduction/Step3Data.lean`. Clause (3) of the theorem is proved
in `Hironaka/Resolution/Algebraic/OrderReduction/ClosedEmbedding.lean`. -/
structure BOData (n m : ℕ) where
  /-- The functor `BO_{n,m}` over each field `k` of characteristic zero. -/
  functor : ∀ (k : Type u) [Field k] [CharZero k], OrderSeqAssignment k m (Triple.BOClass n m)
  /-- Clause (1) of [Kol07, Theorem 103]: `max-ord I_r < m`. -/
  maxOrd_lt : ∀ (k : Type u) [Field k] [CharZero k] (T : Triple k) (hT : Triple.BOClass n m T),
    (((functor k).seq T hT).weakTransformSeq T.I (Fin.last _)).maxOrd < (m : ℕ∞)
  /-- Clause (2) of [Kol07, Theorem 103], first half: `BO_{n,m}` commutes with smooth morphisms
  ([Kol07, 34.1]). -/
  commutesWithSmooth : ∀ (k : Type u) [Field k] [CharZero k], (functor k).CommutesWithSmooth
  /-- Clause (2) of [Kol07, Theorem 103], second half: `BO_{n,m}` commutes with change of fields
  ([Kol07, 34.2]). -/
  commutesWithBaseChange : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L]
    (σ : k →+* L), (functor k).CommutesWithBaseChange (functor L) σ

end Hironaka

namespace Hironaka.BO

open Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- For `m ≥ 1` the maximal coefficient ideal `W_s(I)` of [Kol07, Definition 98] contains `I^s`
(the exponent vector `(s, 0, …, 0)` has weight `m s ≥ s`), so it is nonzero on every irreducible
component when `I` is, the stalks of a smooth scheme being domains. Not in the sources; this is
what makes `(X, W_s(I), E)` a triple. -/
theorem isNonzeroEverywhere_W (f : X ⟶ Spec (.of k)) [Smooth f] {I : X.IdealSheafData}
    (hI : IsNonzeroEverywhere I) {m : ℕ} (hm : 1 ≤ m) (s : ℕ) :
    IsNonzeroEverywhere (W f I m s) := by
  intro x hW
  have hW' : (W f I m s).stalkIdeal x = ⊥ := hW
  have hI' : I.stalkIdeal x ≠ ⊥ := hI x
  have hle : I ^ s ≤ W f I m s := pow_le_W f (Nat.le_mul_of_pos_left s hm)
  have := isRegularLocalRing_stalk f x
  have h1 : (I ^ s).stalkIdeal x ≤ (W f I m s).stalkIdeal x := stalkIdeal_mono hle x
  rw [hW', le_bot_iff, stalkIdeal_pow] at h1
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI'
  have hmem : a ^ s ∈ I.stalkIdeal x ^ s := Ideal.pow_mem_pow haI s
  rw [h1] at hmem
  exact pow_ne_zero s ha0 ((Submodule.mem_bot _).mp hmem)

end Hironaka.BO

namespace Hironaka

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

/-- **The tuned triple** `(X, W_{s(m)}(I), E)` of `(X, I, E)`, Step 1 of the proof of
[Kol07, Theorem 103], which replaces `I` by an ideal `W(I) = W_s(I)`, for a suitable `s`, that is
D-balanced and MC-invariant and whose order reduction is equivalent to that of `I`. The scheme and
the divisor are those of `T`; the ideal is the maximal coefficient
ideal `W` at the exponent `s(m) = tuningParam m`, nonzero on every component by
`isNonzeroEverywhere_W` (whence `m ≥ 1`). The ideal `W f I m s` takes the mark `m` as a
parameter, so `T.tuned m hm` is Kollár's `W(I)` exactly when `max-ord I = m`, the only case in
which `ofTuned` evaluates its argument on it. Reducible, so that `(T.tuned m hm).X.left` is
`T.X.left` under instance transparency, as the case split of `ofTuned` needs. -/
noncomputable abbrev tuned (T : Triple k) (m : ℕ) (hm : 1 ≤ m) : Triple k :=
  { T with
    I := Scheme.IdealSheafData.W (T.X.left ↘ Spec (.of k)) T.I m (tuningParam m)
    isNonzeroEverywhere :=
      Hironaka.BO.isNonzeroEverywhere_W (T.X.left ↘ Spec (.of k)) T.isNonzeroEverywhere hm _ }

end AlgebraicGeometry.Triple

namespace Hironaka

namespace OrderSeqAssignment

variable {k : Type u} [Field k] [CharZero k]

/-- **The reduction to the tuned ideal on an arbitrary class** `C` of triples whose mark is at
least `1` (`hmC`): from a smooth blow-up sequence functor `B` of order `s(m)` on a class `Dom'`
containing the tuned triples of `C`, the functor of order `m` on `C` whose value on `(X, I, E)` is
`B(X, W_{s(m)}(I), E)` when `max-ord I = m` and the empty sequence otherwise (the case
`max-ord I < m` is trivial, `X_r = X`: the remark after [Kol07, Theorem 68]). Its value is a smooth
blow-up sequence of order `m` starting with `(X, I, E)` by [Kol07, Corollary 101]
(`Hironaka.BD.isOrderSeq_iff_tuned`), and contains no empty blow-up because the values of `B` do
not. `ofTuned` is its instance at `C := BOClass n m`, and the boundary-clearing functor
`Hironaka.BD.tunedFunctor` its instance at `C := BDClass n m j`. -/
noncomputable def ofTunedClass {m : ℕ} {C Dom' : Triple k → Prop}
    (B : OrderSeqAssignment k (tuningParam m) Dom') (hmC : ∀ T : Triple k, C T → 1 ≤ m)
    (hDom : ∀ (T : Triple k) (hT : C T), T.I.maxOrd = m → Dom' (T.tuned m (hmC T hT))) :
    OrderSeqAssignment k m C where
  seq T hT :=
    if h : T.I.maxOrd = m then B.seq (T.tuned m (hmC T hT)) (hDom T hT h)
    else Scheme.BlowUpSequence.nil T.X.left
  isOrderSeq T hT := by
    by_cases h : T.I.maxOrd = m
    · rw [dite_eq_left h]
      obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
      exact (Hironaka.BD.isOrderSeq_iff_tuned (T.X.left ↘ Spec (.of k)) d _ T.I T.E m h
        (hmC T hT)).mpr (B.isOrderSeq (T.tuned m (hmC T hT)) (hDom T hT h))
    · rw [dite_eq_right h]
      exact ⟨isSmooth_nil _, fun i => i.elim0⟩
  noEmptyCenters T hT := by
    by_cases h : T.I.maxOrd = m
    · rw [dite_eq_left h]
      exact B.noEmptyCenters _ _
    · rw [dite_eq_right h]
      exact fun i => i.elim0

/-- **The reduction to the tuned ideal**, Step 1 of the proof of [Kol07, Theorem 103] ("thus from
now on we assume that `I` is D-balanced and MC-invariant"): from a smooth blow-up sequence functor
`B` of order `s(m)` on a class `Dom'` containing the tuned triples of `BOClass n m`, the functor of
order `m` on `BOClass n m` whose value on `(X, I, E)` is `B(X, W_{s(m)}(I), E)` when
`max-ord I = m` and the empty sequence when `max-ord I < m`. The instance of `ofTunedClass` at
`C := BOClass n m`. -/
noncomputable def ofTuned {n m : ℕ} {Dom' : Triple k → Prop}
    (B : OrderSeqAssignment k (tuningParam m) Dom')
    (hDom : ∀ (T : Triple k) (hT : Triple.BOClass n m T), T.I.maxOrd = m →
      Dom' (T.tuned m hT.1)) :
    OrderSeqAssignment k m (Triple.BOClass n m) :=
  ofTunedClass B (fun _ hT => hT.1) hDom

end OrderSeqAssignment

end Hironaka

/-! ### Extensionality of `BOData` -/

namespace Hironaka

/-- Two `BOData n m` with the same values are equal: the functor is determined by its `seq`
(`OrderSeqAssignment.ext`) and the remaining fields are propositions. Used to show that the
stage-`0` package of the dimension tower is unique (`HironakaExamples/Stage/BaseCases.lean`). -/
theorem BOData.ext {n m : ℕ} {D D' : BOData.{u} n m}
    (h : ∀ (k : Type u) [Field k] [CharZero k] (T : Triple k) (hT : T.BOClass n m),
      (D.functor k).seq T hT = (D'.functor k).seq T hT) : D = D' := by
  cases D with
  | mk f _ _ _ =>
    cases D' with
    | mk f' _ _ _ =>
      obtain rfl : f = f' := by
        funext k _ _
        exact OrderSeqAssignment.ext fun T hT => h k T hT
      rfl

end Hironaka
