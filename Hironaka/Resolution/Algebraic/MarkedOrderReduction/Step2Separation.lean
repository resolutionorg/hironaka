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
import Hironaka.Resolution.Algebraic.Balanced.Order
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.MarkedSupPow
import Hironaka.Resolution.Algebraic.Kol07.Tuning
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.NonmonomialInvariant
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart
import Hironaka.Resolution.Algebraic.Order.SupPow
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUp.Descent
public import Hironaka.Scheme.BlowUpSequence.ConcatMarked
public import Hironaka.Scheme.BlowUpSequence.ConcatTransforms
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.MarkedTripleBlowUp
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2 of marked order reduction: separating the cosupport from the nonmonomial part

Step 2 of the proof of [Kol07, Theorem 107] ([Kol07, 111, Step 2]) makes the cosupports of `(I, m)`
and of `N(I)` disjoint. With `s` the maximal order of `N(I)` along `cosupp(I, m)`, the order is
reduced step by step until `s = 0`, which is the disjointness. Kollár's device is the observation
that `ord_Z J₁ ≥ s` and `ord_Z J₂ ≥ m` together are equivalent to `ord_Z (J₁^m + J₂^s) ≥ ms`: order
reduction is applied to the single ideal `N(I)^m + I^s`, of order `≥ ms`, and every smooth blow-up
sequence of order `ms` for it is at once one of order `s` for `N(I)` and one of order `m` for `I`;
after `r = r(m, s)` blow-ups `cosupp(I_r, m) ∩ cosupp(N(I_r), s) = ∅`, and the process continues
with `s − 1`. At the end the two cosupports are disjoint; since every further centre lies in
`cosupp(I, m)`, `X` may be replaced by `X ∖ cosupp N(I)`, where `I = M(I)`.

The construction follows the pattern of Step 1
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step1NonmonomialPart.lean`), with the input `bo
: ∀ d, BOData n d`, order reduction for ideals in dimension `n` at every mark.

* `sepOrder T`: Kollár's `s`, the maximal order of `N(I)` along `cosupp(I, m) = {x | m ≤ ord_x I}`
  (`maxOrdAlong`), as a natural number (`coe_sepOrder`); `sepOrder_eq_zero_iff`: `s = 0` iff the
  two cosupports are disjoint, the exit of the loop.
* `sepIdeal T = N(I)^m + I^s` and `sepTriple T = (X, N(I)^m + I^s, E)`, with `max-ord ≤ ms`
  (`maxOrd_sepIdeal_le`) and the admission `boClass_sepTriple` to `BOClass n (m·s)` for `s ≥ 1`.
* `step2Round bo T hT hs`: one round, `BO_{n,ms}(X, N(I)^m + I^s, E)`; `weakTransformSeq_step2Round`
  (the induced birational transform of `N(I)^m + I^s` is `Π^{-1}_*(N(I), s)^m + Π^{-1}_*(I, m)^s`
  at every stage), `step2Round_isOrderGeSeq` (of order `≥ m` for `(I, m)`) and
  `step2Round_isOrderGeSeq_nonmonomial` (of order `≥ s` for `(N(I), s)`).
* `step2Triple bo T hT hs`: the marked triple `(X_r, Π^{-1}_*(I, m), m, Π^{-1}_{tot} E)` induced at
  the end of the round, again of `BMOClass n m` (`bmoClass_step2Triple`);
  `sepOrder_step2Triple_lt`: its `s` is smaller, since clause (1) of [Kol07, Theorem 103] for the
  round and Kollár's observation leave no point with `ord N_r ≥ s` and `ord I_r ≥ m`, while
  `N(I_r) = N(N_r)` (`nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq`) with `N_r ⊆ N(N_r)`
  gives `ord N(I_r) ≤ ord N_r < s` on `cosupp(I_r, m)`.
* `step2 bo T hT`: **Step 2**, by well-founded recursion on `sepOrder T`: the empty sequence once
  `s = 0`, otherwise the round followed by Step 2 of the induced marked triple (`concat`), carried
  with the proofs that it is a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)` without
  empty blow-ups; the unfolding equations `step2_of_eq_zero`, `step2_of_pos` and the result
  `sepOrder_induced_step2_eq_zero`, `disjoint_cosupp_induced_step2`: at the end,
  `cosupp(I_r, m) ∩ cosupp N(I_r) = ∅`.
* The reduction to the monomial part, in the form the assembly uses: at the exit, `cosupp(I, m)`
  lies in the open `U = X ∖ cosupp N(I)` (`setOf_le_ord_subset_compl_support_of_sepOrder_eq_zero`),
  `I = M(I)` on `U` (`stalkIdeal_eq_monomialPart_of_notMem_support`, `comap_ι_eq_monomialPart` for
  an open inside `U`); with the remarks `cosupp(M(I), m) ⊆ cosupp(I, m)` and `ord_x I = ord_x M(I)`
  off `cosupp N(I)`.

The result of Step 1, `max-ord N(I) < m`, is not a hypothesis here: the construction, its admission
and its termination do not use it (the bound `max-ord (N(I)^m + I^s) ≤ ms` holds for every marked
triple of the class); the assembly
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Assembly.lean`) applies Step 2 after Step 1.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.BMO

section Sep

variable {k : Type u} [Field k] [CharZero k] (T : MarkedTriple k)

/-- The separation order `s` ([Kol07, 111, Step 2]: "let `s` be the maximum order of `N(I)` along
`cosupp(I, m)`"), as a natural number (`coe_sepOrder`). -/
noncomputable def sepOrder : ℕ :=
  ((nonmonomialPart T.I T.E).maxOrdAlong {x | (T.m : ℕ∞) ≤ T.I.ord x}).toNat

/-- `(sepOrder T : ℕ∞) = max-ord_{cosupp(I, m)} N(I)`: the maximal order along a set of an ideal
sheaf nonzero on every component is finite (`maxOrdAlong_ne_top`). -/
theorem coe_sepOrder :
    (sepOrder T : ℕ∞) = (nonmonomialPart T.I T.E).maxOrdAlong {x | (T.m : ℕ∞) ≤ T.I.ord x} := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have := Hironaka.BD.noetherianSpace_triple T.toTriple
  exact ENat.natCast_toNat (maxOrdAlong_ne_top _ (T.X.left ↘ Spec (.of k)) n'
    fun x _ => isNonzeroEverywhere_nonmonomialPart T.toTriple x)

/-- The exit of the loop ([Kol07, 111, Step 2]: "`s = 0`, which is the same as
`cosupp(I, m) ∩ cosupp N(I) = ∅`"). -/
theorem sepOrder_eq_zero_iff :
    sepOrder T = 0 ↔
      Disjoint {x | (T.m : ℕ∞) ≤ T.I.ord x} ((nonmonomialPart T.I T.E).support : Set T.X.left) := by
  rw [Set.disjoint_left]
  constructor
  · intro h0 x hx
    have hle : (nonmonomialPart T.I T.E).maxOrdAlong {x | (T.m : ℕ∞) ≤ T.I.ord x} ≤ 0 := by
      rw [← coe_sepOrder T, h0, Nat.cast_zero]
    have hx0 : (nonmonomialPart T.I T.E).ord x = 0 :=
      le_antisymm ((maxOrdAlong_le_iff _).mp hle x hx) bot_le
    exact (ord_eq_zero_iff (I := nonmonomialPart T.I T.E) (x := x)).mp hx0
  · intro h
    have hle : (nonmonomialPart T.I T.E).maxOrdAlong {x | (T.m : ℕ∞) ≤ T.I.ord x} ≤ 0 :=
      (maxOrdAlong_le_iff _).mpr fun x hx =>
        ((ord_eq_zero_iff (I := nonmonomialPart T.I T.E) (x := x)).mpr (h hx)).le
    have h1 : ((sepOrder T : ℕ) : ℕ∞) = 0 := by
      rw [coe_sepOrder T]
      exact le_antisymm hle bot_le
    exact_mod_cast h1

/-- The separating ideal `N(I)^m + I^s` of [Kol07, 111, Step 2] (the sum of ideal sheaves is
`⊔`). -/
noncomputable def sepIdeal : T.X.left.IdealSheafData :=
  nonmonomialPart T.I T.E ^ T.m ⊔ T.I ^ sepOrder T

omit [CharZero k] in
/-- Powers of an ideal sheaf nonzero on every component of a triple's scheme are nonzero on every
component, the stalks being domains (`isNonzeroEverywhere_mul`); no characteristic hypothesis. -/
theorem isNonzeroEverywhere_pow (T' : Triple k) {I : T'.X.left.IdealSheafData}
    (hI : IsNonzeroEverywhere I) (c : ℕ) : IsNonzeroEverywhere (I ^ c) := by
  induction c with
  | zero =>
    intro x h
    rw [pow_zero, one_eq_top] at h
    change (⊤ : T'.X.left.IdealSheafData).stalkIdeal x = ⊥ at h
    rw [stalkIdeal_top] at h
    exact top_ne_bot h
  | succ c ih =>
    rw [pow_succ]
    exact isNonzeroEverywhere_mul T' ih hI

omit [CharZero k] in
/-- `N(I)^m + I^s` is nonzero on every component: it contains `N(I)^m`. -/
theorem isNonzeroEverywhere_sepIdeal : IsNonzeroEverywhere (sepIdeal T) :=
  isNonzeroEverywhere_of_le le_sup_left
    (isNonzeroEverywhere_pow T.toTriple (isNonzeroEverywhere_nonmonomialPart T.toTriple) T.m)

/-- The unmarked triple `(X, N(I)^m + I^s, E)` to which the round's order reduction is applied
([Kol07, 111, Step 2]). -/
noncomputable def sepTriple : Triple k :=
  { T.toTriple with
    I := sepIdeal T
    isNonzeroEverywhere := isNonzeroEverywhere_sepIdeal T }

omit [CharZero k] in
/-- The scheme of `(X, N(I)^m + I^s, E)` is `X`. -/
theorem sepTriple_X : (sepTriple T).X.left = T.X.left := rfl

omit [CharZero k] in
/-- The ideal of `(X, N(I)^m + I^s, E)` is the separating ideal. -/
theorem sepTriple_I : (sepTriple T).I = sepIdeal T := rfl

omit [CharZero k] in
/-- The boundary of `(X, N(I)^m + I^s, E)` is `E`. -/
theorem sepTriple_E : (sepTriple T).E = T.E := rfl

variable {n m : ℕ}

/-- `max-ord (N(I)^m + I^s) ≤ ms` ([Kol07, 111, Step 2]: "which has order `≥ ms`"; here the upper
bound needed for the domain of `BO_{n,ms}`): off `cosupp(I, m)`, `ord_x I ≤ m` so
`s · ord_x I ≤ ms`; on it, `ord_x N(I) ≤ s` by the definition of `s`, so `m · ord_x N(I) ≤ ms`;
the order of the sum is the minimum. No hypothesis on the outcome of Step 1 is needed. -/
theorem maxOrd_sepIdeal_le (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    (sepIdeal T).maxOrd ≤ ((T.m * sepOrder T : ℕ) : ℕ∞) := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hm1 : 1 ≤ T.m := by
    rw [hT.2.2]
    exact hT.1
  refine (maxOrd_le_iff _).mpr fun x => ?_
  rw [sepIdeal, ord_sup_eq_min, Hironaka.Sequence.ord_pow (T.X.left ↘ Spec (.of k)) n' _ _ hm1 x,
    Hironaka.Sequence.ord_pow (T.X.left ↘ Spec (.of k)) n' _ _ hs x, Nat.cast_mul]
  by_cases hx : (T.m : ℕ∞) ≤ T.I.ord x
  · refine (min_le_left _ _).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
    rw [coe_sepOrder T]
    exact le_maxOrdAlong _ hx
  · refine (min_le_right _ _).trans ?_
    calc (sepOrder T : ℕ∞) * T.I.ord x ≤ (sepOrder T : ℕ∞) * (T.m : ℕ∞) :=
          mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp hx)) zero_le
      _ = (T.m : ℕ∞) * (sepOrder T : ℕ∞) := mul_comm _ _

/-- For `s ≥ 1` the triple `(X, N(I)^m + I^s, E)` lies in `BOClass n (m·s)` ([Kol07, Theorem 68],
the domain of `BO_{ms}`): the mark `m·s ≥ 1`, the dimension bound of `T`, and `max-ord ≤ m·s`. -/
theorem boClass_sepTriple (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    Triple.BOClass n (T.m * sepOrder T) (sepTriple T) := by
  have hm1 : 1 ≤ T.m := by
    rw [hT.2.2]
    exact hT.1
  exact ⟨Nat.mul_pos hm1 hs, hT.2.1, maxOrd_sepIdeal_le T hT hs⟩

end Sep

section Round

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)
  (T : MarkedTriple k)

/-- **One round of Step 2** ([Kol07, 111, Step 2]: "we apply order reduction to the ideal
`N(I)^m + I^s`"): the value of `BO_{n,ms}` at the order `m·s` on the triple `(X, N(I)^m + I^s, E)`,
for `s ≥ 1`. -/
noncomputable def step2Round (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    BlowUpSequence T.X.left :=
  ((bo (T.m * sepOrder T)).functor k).seq (sepTriple T) (boClass_sepTriple T hT hs)

/-- One round of Step 2 is the value of `BO_{n,ms}` on `(X, N(I)^m + I^s, E)`. -/
theorem step2Round_eq (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    step2Round bo T hT hs =
      ((bo (T.m * sepOrder T)).functor k).seq (sepTriple T) (boClass_sepTriple T hT hs) :=
  rfl

/-- The round is a smooth blow-up sequence of order `m·s` for `(X, N(I)^m + I^s, E)` (the
functor's field; [Kol07, Theorem 68]). -/
theorem step2Round_isOrderSeq (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    (step2Round bo T hT hs).IsOrderSeq (T.X.left ↘ Spec (.of k)) (sepIdeal T) T.E
      (T.m * sepOrder T) :=
  ((bo (T.m * sepOrder T)).functor k).isOrderSeq _ _

/-- The round contains no empty blow-up (the functor's field; [Kol07, 32]). -/
theorem step2Round_noEmptyCenters (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    (step2Round bo T hT hs).NoEmptyCenters :=
  ((bo (T.m * sepOrder T)).functor k).noEmptyCenters _ _

/-- The birational transform of `N(I)^m + I^s` at the end of the round has maximal order `< m·s`
(clause (1) of [Kol07, Theorem 103] for the round at order `m·s`). -/
theorem maxOrd_weakTransformSeq_step2Round_lt (hT : MarkedTriple.BMOClass n m T)
    (hs : 0 < sepOrder T) :
    ((step2Round bo T hT hs).weakTransformSeq (sepIdeal T) (Fin.last _)).maxOrd <
      ((T.m * sepOrder T : ℕ) : ℕ∞) :=
  (bo (T.m * sepOrder T)).maxOrd_lt k _ _

/-- At every stage of the round, the induced birational transform of `N(I)^m + I^s` is
`Π^{-1}_*(N(I), s)^m + Π^{-1}_*(I, m)^s` ([Kol07, 111, Step 2]: a sequence of order `ms` for the
sum is one of order `s` for `N(I)` and of order `m` for `I`, and the transforms match). -/
theorem weakTransformSeq_step2Round (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T)
    (i : Fin ((step2Round bo T hT hs).length + 1)) :
    (step2Round bo T hT hs).weakTransformSeq (sepIdeal T) i =
      (step2Round bo T hT hs).markedTransformSeq (nonmonomialPart T.I T.E) (sepOrder T) i ^ T.m ⊔
        (step2Round bo T hT hs).markedTransformSeq T.I T.m i ^ sepOrder T := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hm1 : 1 ≤ T.m := by
    rw [hT.2.2]
    exact hT.1
  exact weakTransformSeq_pow_sup_pow (T.X.left ↘ Spec (.of k)) n' hm1 hs
    (step2Round_isOrderSeq bo T hT hs) i

/-- **The round is a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`**
([Kol07, 111, Step 2]: "also … a smooth blow-up sequence of order `m` starting with `I`"): the same
centres and boundaries, the order clause by Kollár's observation
`ord_Z (J₁^m + J₂^s) ≥ ms ⇔ ord_Z J₁ ≥ s ∧ ord_Z J₂ ≥ m`. -/
theorem step2Round_isOrderGeSeq (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    (step2Round bo T hT hs).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hm1 : 1 ≤ T.m := by
    rw [hT.2.2]
    exact hT.1
  exact isOrderGeSeq_of_isOrderSeq_pow_sup_pow_right (T.X.left ↘ Spec (.of k)) n' hm1 hs
    (step2Round_isOrderSeq bo T hT hs)

/-- The round is a smooth blow-up sequence of order `≥ s` starting with `(X, N(I), s, E)`
([Kol07, 111, Step 2]: "also a smooth blow-up sequence of order `s` starting with `N(I)`"). -/
theorem step2Round_isOrderGeSeq_nonmonomial (hT : MarkedTriple.BMOClass n m T)
    (hs : 0 < sepOrder T) :
    (step2Round bo T hT hs).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) (nonmonomialPart T.I T.E)
      (sepOrder T) T.E := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hm1 : 1 ≤ T.m := by
    rw [hT.2.2]
    exact hT.1
  exact isOrderGeSeq_of_isOrderSeq_pow_sup_pow_left (T.X.left ↘ Spec (.of k)) n' hm1 hs
    (step2Round_isOrderSeq bo T hT hs)

/-- The marked triple `(X_r, Π^{-1}_*(I, m), m, Π^{-1}_{tot} E)` induced at the end of one round
([Kol07, 111, Step 2]: "we stop after `r = r(m, s)` steps"; `MarkedTriple.induced` through
`step2Round_isOrderGeSeq`). -/
noncomputable def step2Triple (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    MarkedTriple k :=
  T.induced (step2Round bo T hT hs) (step2Round_isOrderGeSeq bo T hT hs) (Fin.last _)

/-- The scheme of the induced marked triple after a round is the end result of the round. -/
theorem step2Triple_X (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    (step2Triple bo T hT hs).X.left = (step2Round bo T hT hs).last :=
  rfl

/-- The ideal of the induced marked triple after a round is `Π^{-1}_*(I, m)`. -/
theorem step2Triple_I (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    (step2Triple bo T hT hs).I =
      (step2Round bo T hT hs).markedTransformSeq T.I T.m (Fin.last _) :=
  rfl

/-- The boundary of the induced marked triple after a round is `Π^{-1}_{tot} E`. -/
theorem step2Triple_E (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    (step2Triple bo T hT hs).E = (step2Round bo T hT hs).totalTransformSeq T.E (Fin.last _) :=
  rfl

/-- The mark of the induced marked triple after a round is unchanged. -/
theorem step2Triple_m (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    (step2Triple bo T hT hs).m = T.m :=
  rfl

/-- The induced marked triple after a round is again of `BMOClass n m`: the stages of a smooth
blow-up sequence are smooth of the same relative dimension, and the mark is unchanged. -/
theorem bmoClass_step2Triple (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    MarkedTriple.BMOClass n m (step2Triple bo T hT hs) := by
  obtain ⟨n', hn'n, hn'⟩ := hT.2.1
  have : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  exact ⟨hT.1, ⟨n', hn'n,
    IsSmooth.stageMap_smoothOfRelativeDimension (step2Round_isOrderGeSeq bo T hT hs).1
      (Fin.last _)⟩, hT.2.2⟩

/-- **After a round at order `m·s`, the separation order drops** ([Kol07, 111, Step 2]: the rounds
at the separation order `s` stop once `cosupp(I_r, m)` and `cosupp(N(I_r), s)` are disjoint, and
Kollár continues with `s − 1`): clause (1) of [Kol07, Theorem 103] gives
`max-ord (N_r^m + I_r^s) < ms`, so by Kollár's
observation no point has `ord N_r ≥ s` and `ord I_r ≥ m`; and `N(I_r) = N(N_r)`
(`nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq`) with `N_r ⊆ N(N_r)` gives
`ord_x N(I_r) ≤ ord_x N_r < s` on `cosupp(I_r, m)`. -/
theorem sepOrder_step2Triple_lt (hT : MarkedTriple.BMOClass n m T) (hs : 0 < sepOrder T) :
    sepOrder (step2Triple bo T hT hs) < sepOrder T := by
  obtain ⟨n', hn'⟩ := (step2Triple bo T hT hs).smoothOfRelativeDimension
  have hm1 : 1 ≤ T.m := by
    rw [hT.2.2]
    exact hT.1
  have hN : nonmonomialPart (step2Triple bo T hT hs).I (step2Triple bo T hT hs).E =
      nonmonomialPart ((step2Round bo T hT hs).markedTransformSeq (nonmonomialPart T.I T.E)
        (sepOrder T) (Fin.last _)) (step2Triple bo T hT hs).E :=
    nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq T (step2Round bo T hT hs)
      (isNonzeroEverywhere_nonmonomialPart T.toTriple)
      (step2Round_isOrderGeSeq_nonmonomial bo T hT hs) (step2Round_isOrderGeSeq bo T hT hs)
      (nonmonomialPart_nonmonomialPart T.toTriple).symm
  have hlt := maxOrd_weakTransformSeq_step2Round_lt bo T hT hs
  rw [weakTransformSeq_step2Round bo T hT hs (Fin.last _)] at hlt
  have key : ∀ x, (T.m : ℕ∞) ≤ (step2Triple bo T hT hs).I.ord x →
      (nonmonomialPart (step2Triple bo T hT hs).I (step2Triple bo T hT hs).E).ord x <
        (sepOrder T : ℕ∞) := by
    intro x hx
    by_contra hge
    rw [not_lt] at hge
    have h1 : (nonmonomialPart (step2Triple bo T hT hs).I (step2Triple bo T hT hs).E).ord x ≤
        ((step2Round bo T hT hs).markedTransformSeq (nonmonomialPart T.I T.E) (sepOrder T)
          (Fin.last _)).ord x := by
      rw [hN]
      exact ord_anti (le_colon_self _ _) x
    have h2 := (le_ord_pow_sup_pow_iff ((step2Triple bo T hT hs).X.left ↘ Spec (.of k))
      n' _ _ hm1 hs x).mpr ⟨hge.trans h1, hx⟩
    exact absurd (h2.trans (le_maxOrd _ x)) (not_le.mpr hlt)
  have h2 : ((sepOrder (step2Triple bo T hT hs) : ℕ) : ℕ∞) < (sepOrder T : ℕ∞) := by
    rw [coe_sepOrder]
    change (nonmonomialPart (step2Triple bo T hT hs).I (step2Triple bo T hT hs).E).maxOrdAlong
      {x | (T.m : ℕ∞) ≤ (step2Triple bo T hT hs).I.ord x} < (sepOrder T : ℕ∞)
    have := Hironaka.BD.noetherianSpace_triple (step2Triple bo T hT hs).toTriple
    by_cases hne : ({x | (T.m : ℕ∞) ≤ (step2Triple bo T hT hs).I.ord x} :
        Set (step2Triple bo T hT hs).X.left).Nonempty
    · obtain ⟨z, hz, hzeq⟩ := exists_ord_eq_maxOrdAlong
        (nonmonomialPart (step2Triple bo T hT hs).I (step2Triple bo T hT hs).E)
        ((step2Triple bo T hT hs).X.left ↘ Spec (.of k)) n' hne
        fun x _ => isNonzeroEverywhere_nonmonomialPart (step2Triple bo T hT hs).toTriple x
      rw [← hzeq]
      exact key z hz
    · have hle : (nonmonomialPart (step2Triple bo T hT hs).I (step2Triple bo T hT hs).E).maxOrdAlong
          {x | (T.m : ℕ∞) ≤ (step2Triple bo T hT hs).I.ord x} ≤ 0 :=
        (maxOrdAlong_le_iff _).mpr fun x hx => absurd ⟨x, hx⟩ hne
      exact lt_of_le_of_lt hle (by exact_mod_cast hs)
  exact_mod_cast h2

end Round

section Step2

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)

/-- **Step 2 of the proof of [Kol07, Theorem 107]** ([Kol07, 111, Step 2]: "we reduce this order
step-by-step, eventually ending up with `s = 0`"), by well-founded recursion on the separation
order `s = sepOrder T`: the empty sequence once `s = 0`, and otherwise one round
`BO_{n,ms}(X, N(I)^m + I^s, E)` followed by Step 2 of the induced marked triple, whose separation
order is smaller (`sepOrder_step2Triple_lt`). Carried with the sequence: it is a smooth blow-up
sequence of order `≥ m` starting with `(X, I, m, E)` (`isOrderGeSeq_concat` with
`step2Round_isOrderGeSeq`) without empty blow-ups (`noEmptyCenters_concat`). `BO_{n,ms}` is called
only for `s ≥ 1`. -/
noncomputable def step2 (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    {S : BlowUpSequence T.X.left // S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧
      S.NoEmptyCenters} :=
  if hs : 0 < sepOrder T then
    let R := step2 (step2Triple bo T hT hs) (bmoClass_step2Triple bo T hT hs)
    ⟨(step2Round bo T hT hs).concat R.1,
      isOrderGeSeq_concat _ _ _ (step2Round_isOrderGeSeq bo T hT hs) R.2.1,
      noEmptyCenters_concat _ _ (step2Round_noEmptyCenters bo T hT hs) R.2.2⟩
  else ⟨BlowUpSequence.nil T.X.left, isOrderGeSeq_nil _ _ _ _, fun i => i.elim0⟩
termination_by sepOrder T
decreasing_by exact sepOrder_step2Triple_lt bo T hT hs

/-- At the exit (`s = 0`), Step 2 is the empty sequence. -/
theorem step2_of_eq_zero (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T)
    (h : sepOrder T = 0) : (step2 bo T hT).1 = BlowUpSequence.nil T.X.left := by
  rw [step2, dite_eq_right (not_lt.mpr h.le)]

/-- For `s ≥ 1`, Step 2 is one round followed by Step 2 of the induced marked triple (the loop
unrolled once). -/
theorem step2_of_pos (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T)
    (hs : 0 < sepOrder T) :
    (step2 bo T hT).1 =
      (step2Round bo T hT hs).concat
        (step2 bo (step2Triple bo T hT hs) (bmoClass_step2Triple bo T hT hs)).1 := by
  rw [step2, dite_eq_left hs]

/-- Step 2 is a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`
([Kol07, Definition 66] for `Π_2`). -/
theorem step2_isOrderGeSeq (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    (step2 bo T hT).1.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
  (step2 bo T hT).2.1

/-- Step 2 contains no empty blow-up ([Kol07, 32]). -/
theorem step2_noEmptyCenters (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    (step2 bo T hT).1.NoEmptyCenters :=
  (step2 bo T hT).2.2

/-- The induction behind the result of Step 2, on a bound `l` for the separation order, following
the recursion of `step2`; stated on the induced data of the sequence (no dependence on the order
proof), so that the unfolding equations rewrite. -/
theorem maxOrdAlong_nonmonomialPart_step2_eq_zero_aux (l : ℕ) :
    ∀ (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T), sepOrder T ≤ l →
      (nonmonomialPart ((step2 bo T hT).1.markedTransformSeq T.I T.m (Fin.last _))
          ((step2 bo T hT).1.totalTransformSeq T.E (Fin.last _))).maxOrdAlong
        {x | (T.m : ℕ∞) ≤ ((step2 bo T hT).1.markedTransformSeq T.I T.m (Fin.last _)).ord x} =
          0 := by
  induction l with
  | zero =>
    intro T hT hl
    have h0 : sepOrder T = 0 := Nat.le_zero.mp hl
    rw [step2_of_eq_zero bo T hT h0]
    change (nonmonomialPart T.I T.E).maxOrdAlong {x | (T.m : ℕ∞) ≤ T.I.ord x} = 0
    rw [← coe_sepOrder T, h0, Nat.cast_zero]
  | succ l ih =>
    intro T hT hl
    by_cases hs : 0 < sepOrder T
    · rw [step2_of_pos bo T hT hs]
      exact (markedEnd_concat_iff
        (fun {Y} I' E' => (nonmonomialPart I' E').maxOrdAlong {x | (T.m : ℕ∞) ≤ I'.ord x} = 0)
        _ _ _ _ _).mpr
        (ih (step2Triple bo T hT hs) (bmoClass_step2Triple bo T hT hs)
          (Nat.lt_succ_iff.mp (lt_of_lt_of_le (sepOrder_step2Triple_lt bo T hT hs) hl)))
    · have h0 : sepOrder T = 0 := Nat.eq_zero_of_not_pos hs
      rw [step2_of_eq_zero bo T hT h0]
      change (nonmonomialPart T.I T.E).maxOrdAlong {x | (T.m : ℕ∞) ≤ T.I.ord x} = 0
      rw [← coe_sepOrder T, h0, Nat.cast_zero]

/-- **At the end of Step 2 the separation order is `0`**, for the marked triple induced at the end
([Kol07, 111, Step 2]: "eventually we achieve a situation where the cosupports of `N(I)` and of
`(I, m)` are disjoint"). -/
theorem sepOrder_induced_step2_eq_zero (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    sepOrder (T.induced (step2 bo T hT).1 (step2_isOrderGeSeq bo T hT) (Fin.last _)) = 0 := by
  change ((nonmonomialPart ((step2 bo T hT).1.markedTransformSeq T.I T.m (Fin.last _))
      ((step2 bo T hT).1.totalTransformSeq T.E (Fin.last _))).maxOrdAlong
    {x | (T.m : ℕ∞) ≤ ((step2 bo T hT).1.markedTransformSeq T.I T.m (Fin.last _)).ord x}).toNat = 0
  rw [maxOrdAlong_nonmonomialPart_step2_eq_zero_aux bo (sepOrder T) T hT le_rfl]
  rfl

/-- At the end of Step 2, `cosupp(I_r, m) ∩ cosupp N(I_r) = ∅` ([Kol07, 111, Step 2]), the set
form of `sepOrder_induced_step2_eq_zero`. -/
theorem disjoint_cosupp_induced_step2 (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    Disjoint
      {x | ((T.induced (step2 bo T hT).1 (step2_isOrderGeSeq bo T hT) (Fin.last _)).m : ℕ∞) ≤
        (T.induced (step2 bo T hT).1 (step2_isOrderGeSeq bo T hT) (Fin.last _)).I.ord x}
      ((nonmonomialPart (T.induced (step2 bo T hT).1 (step2_isOrderGeSeq bo T hT) (Fin.last _)).I
        (T.induced (step2 bo T hT).1 (step2_isOrderGeSeq bo T hT) (Fin.last _)).E).support :
        Set (T.induced (step2 bo T hT).1 (step2_isOrderGeSeq bo T hT) (Fin.last _)).X.left) :=
  (sepOrder_eq_zero_iff _).mp (sepOrder_induced_step2_eq_zero bo T hT)

end Step2

section Reduction

variable {k : Type u} [Field k] [CharZero k] (T : MarkedTriple k)

/-- When the separation order is `0`, `cosupp(I, m)` is contained in the complement of
`cosupp N(I)` ([Kol07, 111, Step 2]: "the center of any further blow-up is contained in
`cosupp(I, m)`", which at the exit lies in `X ∖ cosupp N(I)`). -/
theorem setOf_le_ord_subset_compl_support_of_sepOrder_eq_zero (h : sepOrder T = 0) :
    {x | (T.m : ℕ∞) ≤ T.I.ord x} ⊆ ((nonmonomialPart T.I T.E).support : Set T.X.left)ᶜ :=
  Set.subset_compl_iff_disjoint_right.mpr ((sepOrder_eq_zero_iff T).mp h)

omit [CharZero k] in
/-- Off `cosupp N(I)` the stalk of `I` is the stalk of its monomial part ([Kol07, 111, Step 2]:
"replace `X` by `X ∖ cosupp N(I)` and thus assume that `I = M(I)`", at a point): `I = M(I) · N(I)`
and `N(I)_x = 𝒪_x`. -/
theorem stalkIdeal_eq_monomialPart_of_notMem_support {x : T.X.left}
    (hx : x ∉ (nonmonomialPart T.I T.E).support) :
    T.I.stalkIdeal x = (monomialPart T.I T.E).stalkIdeal x := by
  have hN : (nonmonomialPart T.I T.E).stalkIdeal x = ⊤ :=
    stalkIdeal_eq_top_of_ord_eq_zero
      ((ord_eq_zero_iff (I := nonmonomialPart T.I T.E) (x := x)).mpr hx)
  conv_lhs => rw [← monomialPart_mul_nonmonomialPart T.toTriple]
  rw [stalkIdeal_mul, hN, Ideal.mul_top]

omit [CharZero k] in
/-- Off `cosupp N(I)`, the order of `I` is the order of `M(I)`. -/
theorem ord_eq_ord_monomialPart_of_notMem_support {x : T.X.left}
    (hx : x ∉ (nonmonomialPart T.I T.E).support) :
    T.I.ord x = (monomialPart T.I T.E).ord x := by
  rw [ord_eq_ord_stalkIdeal, ord_eq_ord_stalkIdeal,
    stalkIdeal_eq_monomialPart_of_notMem_support T hx]

omit [CharZero k] in
/-- On an open `U` inside the complement of `cosupp N(I)`, the restrictions of `I` and of `M(I)`
agree ([Kol07, 111, Step 2]: "`I = M(I)`" on `X ∖ cosupp N(I)`); extensionality by stalks, through
the stalk map of an open immersion. -/
theorem comap_ι_eq_monomialPart (U : T.X.left.Opens)
    (hU : Set.range U.ι ⊆ ((nonmonomialPart T.I T.E).support : Set T.X.left)ᶜ) :
    T.I.comap U.ι = (monomialPart T.I T.E).comap U.ι :=
  ext_stalkIdeal fun u => by
    rw [stalkIdeal_comap, stalkIdeal_comap,
      stalkIdeal_eq_monomialPart_of_notMem_support T (hU ⟨u, rfl⟩)]

omit [CharZero k] in
/-- `cosupp(M(I), m) ⊆ cosupp(I, m)`, since `I ⊆ M(I)`: a centre of order `≥ m` for the monomial
part is of order `≥ m` for `I`. -/
theorem setOf_le_ord_monomialPart_subset :
    {x | (T.m : ℕ∞) ≤ (monomialPart T.I T.E).ord x} ⊆ {x | (T.m : ℕ∞) ≤ T.I.ord x} := by
  intro x hx
  have hle : T.I ≤ monomialPart T.I T.E := by
    conv_lhs => rw [← monomialPart_mul_nonmonomialPart T.toTriple]
    exact mul_le_self_left _ _
  exact le_trans hx (ord_anti hle x)

end Reduction

end Hironaka.BMO
