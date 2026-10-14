/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Measure

/-!
# Kollár's Step 3 on the monomial state, and its termination

The phases `3.1, …, 3.n` of [Kol07, 111, Step 3] on the combinatorial state of
`Hironaka/Resolution/Algebraic/Monomial/State.lean`. `phase r st hs` runs phase `r` (Kollár's Step
3.r): while Kollár's choice at phase `r` is nonempty, blow up its centre. The recursion is well
founded on `measure r`, which decreases at every blow-up (`measure_blowUp_lt` of
`Hironaka/Resolution/Algebraic/Monomial/Measure.lean`), and the hypothesis `hs`, `(∗_s)` for `s <
r`, is carried along by `star_blowUp`. `step3 st` runs the phases `1, …, n` in order (structural
recursion on the number of phases; `(∗_1)`, …, `(∗_r)` hold when phase `r + 1` starts). The result
is the final state and the list of centres, in order.

Postconditions, Kollár's "eventually we reach the stage where the property `(∗_r)` also holds"
and the end of Step 3.n: `step3_star` gives `(∗_s)` for every `s`, hence every face of the
final nerve has sum `< m` (`step3_maxOrd_lt`, the combinatorial form of
`max-ord (M(I), m) < m`). The run is recorded by `IsRun`: each centre of the list is Kollár's
nonempty choice at some phase `r ∈ [1, n]` of the state reached before it, and the final state
is the fold of the centres (`step3_isRun`, `IsRun.fold`).

`phaseFuel`/`step3Fuel` are executable copies with a fuel parameter (structural recursion) that
agree with `phase`/`step3` whenever the fuel suffices (`phase_eq_of_phaseFuel`,
`step3_eq_of_step3Fuel`); the example computations of `HironakaExamples/Monomial/Example112.lean`
and `HironakaExamples/MonomialState.lean` run them by `decide`, since a definition by well-founded
recursion does not reduce in the kernel.

Kollár's text is the source of the phases and of the measure; the run as a list of centres, the
predicate `IsRun` and the fuelled copies are bookkeeping not in the sources. The geometric
realisation of a run, blow-up by blow-up, is `Hironaka.Monomial.PieceFamily.realize`
(`Hironaka/Resolution/Algebraic/Monomial/Geometric/Pieces.lean`); functoriality of `step3` under
restriction and refinement of the state is `Hironaka/Resolution/Algebraic/Monomial/Restrict.lean`
and its submodules.
-/

@[expose] public section

namespace Hironaka.Monomial.MonomialState

open Finset

/-! ### One phase -/

/-- Phase `r` of Step 3 ([Kol07, 111, Step 3.r]): while Kollár's choice at phase `r` is
nonempty, blow up its centre; well-founded recursion on `measure r`, with `(∗_s)` for `s < r`
preserved along the run (`star_blowUp`). Returns the final state of the phase and its list of
centres. -/
def phase (r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    MonomialState × List (Finset (Finset ℕ)) :=
  if (st.choice r).Nonempty then
    let res := phase r (st.blowUp (st.choice r)) fun _ hsr => st.star_blowUp hs hsr
    (res.1, st.choice r :: res.2)
  else (st, [])
termination_by st.measure r
decreasing_by exact st.measure_blowUp_lt hs ‹_›

variable {r : ℕ}

theorem phase_of_nonempty (st : MonomialState) (hs : ∀ s < r, st.Star s)
    (h : (st.choice r).Nonempty) :
    phase r st hs = ((phase r (st.blowUp (st.choice r)) fun _ hsr => st.star_blowUp hs hsr).1,
      st.choice r :: (phase r (st.blowUp (st.choice r)) fun _ hsr => st.star_blowUp hs hsr).2) := by
  rw [phase, ite_eq_left h]

theorem phase_of_not_nonempty (st : MonomialState) (hs : ∀ s < r, st.Star s)
    (h : ¬ (st.choice r).Nonempty) : phase r st hs = (st, []) := by
  rw [phase, ite_eq_right h]

/-- A run of Step 3: each centre is Kollár's nonempty choice at some phase `r`, `1 ≤ r ≤ n`, of
the state reached before it. -/
inductive IsRun : MonomialState → List (Finset (Finset ℕ)) → MonomialState → Prop
  | nil (st : MonomialState) : IsRun st [] st
  | cons {st st' : MonomialState} {L : List (Finset (Finset ℕ))} (r : ℕ) (hr : 1 ≤ r)
      (hrn : r ≤ st.n) (h : (st.choice r).Nonempty)
      (hL : IsRun (st.blowUp (st.choice r)) L st') : IsRun st (st.choice r :: L) st'

/-- Every centre of a run is Kollár's choice at some size `r` on the state reached so far (the
fold of the preceding centres), nonempty and within the dimension bound. -/
theorem IsRun.exists_get_eq_choice {st st' : MonomialState}
    {L : List (Finset (Finset ℕ))} (h : MonomialState.IsRun st L st') (i : Fin L.length) :
    ∃ r, 1 ≤ r ∧ r ≤ ((L.take i).foldl MonomialState.blowUp st).n ∧
      (((L.take i).foldl MonomialState.blowUp st).choice r).Nonempty ∧
      L.get i = ((L.take i).foldl MonomialState.blowUp st).choice r := by
  induction h with
  | nil st => exact i.elim0
  | cons r hr hrn hne _ ih =>
    rcases i with ⟨_ | j, hj⟩
    · exact ⟨r, hr, hrn, hne, rfl⟩
    · obtain ⟨r', hr', hrn', hne', hget⟩ := ih ⟨j, Nat.lt_of_succ_lt_succ hj⟩
      exact ⟨r', hr', hrn', hne', hget⟩

theorem IsRun.append {st st₁ st₂ : MonomialState} {L₁ L₂ : List (Finset (Finset ℕ))}
    (h₁ : IsRun st L₁ st₁) (h₂ : IsRun st₁ L₂ st₂) : IsRun st (L₁ ++ L₂) st₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons r hr hrn h _ ih => exact IsRun.cons r hr hrn h (ih h₂)

/-- The final state of a run is the fold of its centres. -/
theorem IsRun.fold {st st' : MonomialState} {L : List (Finset (Finset ℕ))} (h : IsRun st L st') :
    st' = L.foldl blowUp st := by
  induction h with
  | nil => rfl
  | cons r _ _ _ _ ih => exact ih

theorem IsRun.n_eq {st st' : MonomialState} {L : List (Finset (Finset ℕ))} (h : IsRun st L st') :
    st'.n = st.n := by
  induction h with
  | nil => rfl
  | cons r _ _ _ _ ih => exact ih

theorem IsRun.m_eq {st st' : MonomialState} {L : List (Finset (Finset ℕ))} (h : IsRun st L st') :
    st'.m = st.m := by
  induction h with
  | nil => rfl
  | cons r _ _ _ _ ih => exact ih

/-- The run of one phase, when the phase is within the dimension bound. -/
theorem phase_isRun (hr : 1 ≤ r) (st : MonomialState) (hs : ∀ s < r, st.Star s) (hrn : r ≤ st.n) :
    IsRun st (phase r st hs).2 (phase r st hs).1 := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih =>
    rw [phase_of_nonempty st hs h]
    exact IsRun.cons r hr hrn h (ih hrn)
  | case2 st hs h =>
    rw [phase_of_not_nonempty st hs h]
    exact IsRun.nil st

/-- At the end of phase `r`, `(∗_r)` holds: Kollár's "eventually we reach the stage where the
property `(∗_r)` also holds" of [Kol07, 111, Step 3.r]. -/
theorem phase_star (st : MonomialState) (hs : ∀ s < r, st.Star s) : (phase r st hs).1.Star r := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih => rw [phase_of_nonempty st hs h]; exact ih
  | case2 st hs h =>
    rw [phase_of_not_nonempty st hs h]
    exact st.choice_eq_empty_iff.mp (Finset.not_nonempty_iff_eq_empty.mp h)

/-- `(∗_s)`, `s < r`, still holds at the end of phase `r` (`star_blowUp` along the run). -/
theorem phase_star_of_lt (st : MonomialState) (hs : ∀ s < r, st.Star s) {s : ℕ} (hsr : s < r) :
    (phase r st hs).1.Star s := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih => rw [phase_of_nonempty st hs h]; exact ih
  | case2 st hs h => rw [phase_of_not_nonempty st hs h]; exact hs s hsr

theorem phase_n (st : MonomialState) (hs : ∀ s < r, st.Star s) : (phase r st hs).1.n = st.n := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih => rw [phase_of_nonempty st hs h]; exact ih
  | case2 st hs h => rw [phase_of_not_nonempty st hs h]

theorem phase_m (st : MonomialState) (hs : ∀ s < r, st.Star s) : (phase r st hs).1.m = st.m := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih => rw [phase_of_nonempty st hs h]; exact ih
  | case2 st hs h => rw [phase_of_not_nonempty st hs h]

/-! ### The phases `r, r + 1, …` and Step 3 -/

/-- `(∗_s)` for `s < r + 1` from `(∗_s)` for `s < r` at the end of phase `r`. -/
theorem phase_star_succ (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    ∀ s < r + 1, (phase r st hs).1.Star s := fun s hsr => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hsr with h | rfl
  · exact phase_star_of_lt st hs h
  · exact phase_star st hs

/-- `k` consecutive phases starting at phase `r`. -/
def phases : (k r : ℕ) → (st : MonomialState) → (∀ s < r, st.Star s) →
    MonomialState × List (Finset (Finset ℕ))
  | 0, _, st, _ => (st, [])
  | k + 1, r, st, hs =>
    let p := phase r st hs
    let q := phases k (r + 1) p.1 (phase_star_succ st hs)
    (q.1, p.2 ++ q.2)

theorem phases_zero (r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    phases 0 r st hs = (st, []) := rfl

theorem phases_succ (k r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    phases (k + 1) r st hs =
      ((phases k (r + 1) (phase r st hs).1 (phase_star_succ st hs)).1,
        (phase r st hs).2 ++ (phases k (r + 1) (phase r st hs).1 (phase_star_succ st hs)).2) := rfl

theorem phases_n (k r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    (phases k r st hs).1.n = st.n := by
  induction k generalizing r st with
  | zero => rfl
  | succ k ih => rw [phases_succ, ih, phase_n]

theorem phases_m (k r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    (phases k r st hs).1.m = st.m := by
  induction k generalizing r st with
  | zero => rfl
  | succ k ih => rw [phases_succ, ih, phase_m]

/-- After the phases `r, …, r + k - 1`, `(∗_s)` holds for every `s < r + k`. -/
theorem phases_star (k r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    ∀ s < r + k, (phases k r st hs).1.Star s := by
  induction k generalizing r st with
  | zero => intro s hsr; exact hs s (by simpa using hsr)
  | succ k ih =>
    intro s hsr
    rw [phases_succ]
    exact ih (r + 1) _ (phase_star_succ st hs) s (by omega)

theorem phases_isRun (k r : ℕ) (hr : 1 ≤ r) (st : MonomialState) (hs : ∀ s < r, st.Star s)
    (hk : r + k ≤ st.n + 1) : IsRun st (phases k r st hs).2 (phases k r st hs).1 := by
  induction k generalizing r st with
  | zero => exact IsRun.nil st
  | succ k ih =>
    rw [phases_succ]
    have hp := phase_isRun hr st hs (by omega)
    refine hp.append (ih (r + 1) (by omega) _ (phase_star_succ st hs) ?_)
    rw [phase_n]; omega

/-- `(∗_0)` holds since faces are nonempty (`star_zero`). -/
theorem star_of_lt_one (st : MonomialState) : ∀ s < 1, st.Star s := fun s hs => by
  obtain rfl : s = 0 := by omega
  exact st.star_zero

/-- Step 3 of [Kol07, 111]: the phases `1, …, n` in order, each by well-founded recursion on
`(m_r, n_r)`; the final state and the list of centres. -/
def step3 (st : MonomialState) : MonomialState × List (Finset (Finset ℕ)) :=
  phases st.n 1 st (star_of_lt_one st)

theorem step3_n (st : MonomialState) : (step3 st).1.n = st.n := phases_n _ _ _ _

theorem step3_m (st : MonomialState) : (step3 st).1.m = st.m := phases_m _ _ _ _

/-- At the end of Step 3, `(∗_s)` holds for every `s`. -/
theorem step3_star (st : MonomialState) (s : ℕ) : (step3 st).1.Star s := by
  by_cases hs : s < 1 + st.n
  · exact phases_star st.n 1 st (star_of_lt_one st) s hs
  · exact star_of_lt _ (by rw [step3_n]; omega)

/-- The postcondition of [Kol07, 111, Step 3] ("at the end of Step 3.n we are done"): every face
of the final nerve has sum `< m`. On the geometric side this is `max-ord (M(I), m) < m`. -/
theorem step3_maxOrd_lt (st : MonomialState) {T : Finset ℕ} (hT : T ∈ (step3 st).1.nerve) :
    (step3 st).1.total T < st.m := by
  rw [← step3_m st]
  exact step3_star st T.card T ((step3 st).1.mem_faces.mpr ⟨hT, rfl⟩)

/-- The list of centres of Step 3 is a run: each centre is Kollár's nonempty choice at a phase
`r ∈ [1, n]` of the state before it, and the final state is their fold. -/
theorem step3_isRun (st : MonomialState) : IsRun st (step3 st).2 (step3 st).1 :=
  phases_isRun st.n 1 le_rfl st (star_of_lt_one st) (by omega)

/-! ### Executable copies with fuel -/

/-- `phase` with fuel: `none` when the fuel runs out. -/
def phaseFuel : ℕ → ℕ → MonomialState → Option (MonomialState × List (Finset (Finset ℕ)))
  | 0, _, _ => none
  | fuel + 1, r, st =>
    if (st.choice r).Nonempty then
      (phaseFuel fuel r (st.blowUp (st.choice r))).map fun res => (res.1, st.choice r :: res.2)
    else some (st, [])

theorem phase_eq_of_phaseFuel {fuel : ℕ} {st : MonomialState} (hs : ∀ s < r, st.Star s)
    {res : MonomialState × List (Finset (Finset ℕ))} (h : phaseFuel fuel r st = some res) :
    phase r st hs = res := by
  induction fuel generalizing st res with
  | zero => exact absurd h (by simp [phaseFuel])
  | succ fuel ih =>
    by_cases hne : (st.choice r).Nonempty
    · rw [phaseFuel, ite_eq_left hne, Option.map_eq_some_iff] at h
      obtain ⟨res', hres', rfl⟩ := h
      rw [phase_of_nonempty st hs hne, ih (fun _ hsr => st.star_blowUp hs hsr) hres']
    · rw [phaseFuel, ite_eq_right hne, Option.some.injEq] at h
      rw [phase_of_not_nonempty st hs hne, h]

/-- `phases` with fuel per phase. -/
def phasesFuel (fuel : ℕ) : ℕ → ℕ → MonomialState →
    Option (MonomialState × List (Finset (Finset ℕ)))
  | 0, _, st => some (st, [])
  | k + 1, r, st =>
    match phaseFuel fuel r st with
    | none => none
    | some p =>
      match phasesFuel fuel k (r + 1) p.1 with
      | none => none
      | some q => some (q.1, p.2 ++ q.2)

theorem phases_eq_of_phasesFuel {fuel k r : ℕ} {st : MonomialState} (hs : ∀ s < r, st.Star s)
    {res : MonomialState × List (Finset (Finset ℕ))} (h : phasesFuel fuel k r st = some res) :
    phases k r st hs = res := by
  induction k generalizing r st res with
  | zero =>
    simp only [phasesFuel, Option.some.injEq] at h
    rw [phases_zero, h]
  | succ k ih =>
    rcases hp : phaseFuel fuel r st with _ | p
    · simp [phasesFuel, hp] at h
    · rcases hq : phasesFuel fuel k (r + 1) p.1 with _ | q
      · simp [phasesFuel, hp, hq] at h
      · simp only [phasesFuel, hp, hq, Option.some.injEq] at h
        have hpe : phase r st hs = p := phase_eq_of_phaseFuel hs hp
        have hq' : phasesFuel fuel k (r + 1) (phase r st hs).1 = some q := by rw [hpe]; exact hq
        rw [phases_succ, ih (phase_star_succ st hs) hq', hpe, ← h]

/-- `step3` with fuel per phase. -/
def step3Fuel (fuel : ℕ) (st : MonomialState) : Option (MonomialState × List (Finset (Finset ℕ))) :=
  phasesFuel fuel st.n 1 st

theorem step3_eq_of_step3Fuel {fuel : ℕ} {st : MonomialState}
    {res : MonomialState × List (Finset (Finset ℕ))} (h : step3Fuel fuel st = some res) :
    step3 st = res :=
  phases_eq_of_phasesFuel (star_of_lt_one st) h

/-- Any function `f` of the run read off the fuelled copy (for `decide`: the final state has
function fields, so it is compared through `f`). -/
theorem step3_map_eq_of_step3Fuel {fuel : ℕ} {st : MonomialState} {α : Type*}
    (f : MonomialState × List (Finset (Finset ℕ)) → α) {x : α}
    (h : (step3Fuel fuel st).map f = some x) : f (step3 st) = x := by
  obtain ⟨res, hres, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [step3_eq_of_step3Fuel hres]

end Hironaka.Monomial.MonomialState
