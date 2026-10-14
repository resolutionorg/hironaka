/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bStep
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial phase at the mark `1`, by recursion

The monomial phase of the modified algorithm [Wlo09, Theorem 7.4.1] resolves `(M(𝓘), 1)` by the
sequence of blow-ups of [Wlo09, §6, Step 2b] at `µ = 1`: while some member carries a component of
positive exponent, blow up the positive locus of the latest-born such member (`Step2bCenter.lean`)
and carry the triple along (`Step2bStep.lean`). This module defines the sequence **by recursion on a
fuel `k`**: `step2bPhase k T hT` is the list of the first `k` steps, stopping early (the empty list)
once no member is active, and proves the properties which hold for every fuel: no empty centre
([Kol07, 32]; the centre is nonempty by construction), the order clause of [Kol07, Definition 66]
at the mark `1`, the length bound and the recursion equations. The fuel is a device of the
definition: the termination of the phase, i.e. that the fuel `Σ_D a_D` over the components exhausts
the active members (the invariant of [Wlo09, §6, Step 2b] decreases), is the theorem
`step2bPhase_eq_of_step2bMeasure_le` of `Step2bMeasure.lean`, and the value on a relatively compact
open is read at that fuel (`Step2bFamily.lean`).

The rule is intrinsic (the latest-born active member, in the order of birth along the total
transforms), so the phase is canonical.
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

open scoped Classical in
/-- **The first `k` steps of the monomial phase at the mark `1`** ("blow-ups at exceptional divisors
for which `ρ(x)` is maximal", [Wlo09, Theorem 7.4.1]): while a member is active, blow up the centre
of `Step2bCenter.lean` and continue on the triple after the step; the empty list when no member is
active or the fuel is spent. -/
def step2bPhase : ℕ → ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M),
    AnalyticTriple.BMOClass 1 T → BlowUpSequence ψ₀ M
  | 0, M, _, _ => BlowUpSequence.nil M
  | k + 1, M, T, hT =>
    if hne : (activeMembers T).Nonempty then
      BlowUpSequence.cons (stepCenter T (activeMembers_finite T hT) hne)
        (step2bPhase k (stepTriple T (activeMembers_finite T hT) hne)
          (bmoClass_stepTriple T (activeMembers_finite T hT) hne hT))
    else BlowUpSequence.nil M

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BMOClass 1 T)

/-! ### The recursion equations -/

theorem step2bPhase_zero : step2bPhase 0 T hT = BlowUpSequence.nil M := rfl

theorem step2bPhase_succ_of_nonempty (k : ℕ) (hne : (activeMembers T).Nonempty) :
    step2bPhase (k + 1) T hT =
      BlowUpSequence.cons (stepCenter T (activeMembers_finite T hT) hne)
        (step2bPhase k (stepTriple T (activeMembers_finite T hT) hne)
          (bmoClass_stepTriple T (activeMembers_finite T hT) hne hT)) := by
  rw [step2bPhase, dite_eq_left hne]

theorem step2bPhase_succ_of_not_nonempty (k : ℕ) (hne : ¬ (activeMembers T).Nonempty) :
    step2bPhase (k + 1) T hT = BlowUpSequence.nil M := by
  rw [step2bPhase, dite_eq_right hne]

/-- With no active member the phase is empty at every fuel (the purely nonmonomial case
`I′ = N(I′)` of [Wlo09, Theorem 7.4.1] has been reached). -/
theorem step2bPhase_of_not_nonempty (hne : ¬ (activeMembers T).Nonempty) (k : ℕ) :
    step2bPhase k T hT = BlowUpSequence.nil M := by
  cases k with
  | zero => rfl
  | succ k => exact step2bPhase_succ_of_not_nonempty T hT k hne

/-! ### The clauses at every fuel -/

/-- The phase has no empty centre [Kol07, 32]: every centre is the positive locus of an active
member (`step2bCenter_nonempty`). -/
theorem noEmptyCenters_step2bPhase :
    ∀ (k : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (hT : AnalyticTriple.BMOClass 1 T), (step2bPhase k T hT).NoEmptyCenters
  | 0, _, _, _ => BlowUpSequence.noEmptyCenters_nil
  | k + 1, M, T, hT => by
    by_cases hne : (activeMembers T).Nonempty
    · rw [step2bPhase_succ_of_nonempty T hT k hne, noEmptyCenters_cons_step_iff]
      exact noEmptyCenters_step2bPhase k _ _
    · rw [step2bPhase_succ_of_not_nonempty T hT k hne]
      exact BlowUpSequence.noEmptyCenters_nil

/-- The order clause of [Kol07, Definition 66] at the mark `1`: the phase is of order `≥ 1` for
`(M, 𝓘, E)`. The two head clauses of each step hold at its centre (`isOfOrderGe_cons_step_iff`). -/
theorem isOfOrderGe_step2bPhase :
    ∀ (k : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (hT : AnalyticTriple.BMOClass 1 T),
      (step2bPhase k T hT).toSuccession.IsOfOrderGe T.I 1 (T.F.idealSheaf (𝕜 := 𝕜) (E := E))
  | 0, _, T, _ => FiniteSuccession.isOfOrderGe_nil T.I _ 1
  | k + 1, M, T, hT => by
    by_cases hne : (activeMembers T).Nonempty
    · rw [step2bPhase_succ_of_nonempty T hT k hne, isOfOrderGe_cons_step_iff]
      exact isOfOrderGe_step2bPhase k _ _
    · rw [step2bPhase_succ_of_not_nonempty T hT k hne]
      exact FiniteSuccession.isOfOrderGe_nil T.I _ 1

/-- The phase at fuel `k` has at most `k` steps. -/
theorem length_step2bPhase_le :
    ∀ (k : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (hT : AnalyticTriple.BMOClass 1 T), (step2bPhase k T hT).length ≤ k
  | 0, _, _, _ => le_rfl
  | k + 1, M, T, hT => by
    by_cases hne : (activeMembers T).Nonempty
    · rw [step2bPhase_succ_of_nonempty T hT k hne, BlowUpSequence.length_cons]
      exact Nat.succ_le_succ (length_step2bPhase_le k _ _)
    · rw [step2bPhase_succ_of_not_nonempty T hT k hne, BlowUpSequence.length_nil]
      exact Nat.zero_le _

end Hironaka.Manifold.BMOmod

end
