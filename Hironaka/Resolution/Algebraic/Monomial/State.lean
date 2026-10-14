/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Prod.Lex
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max

/-!
# The monomial state: Kollár's Step 3 as a combinatorial object

Step 3 of the proof of [Kol07, Theorem 107] ([Kol07, 111, Step 3]) reduces the order of a
monomial ideal `𝒪_X(-∑ a_j E^j)`, `E = ∑ E^j` a simple normal crossing divisor with an ordered
index set, below the mark `m` by blowing up intersections of the `E^j` in a prescribed order. The
procedure only looks at which intersections are nonempty and at the exponents, so this module
runs it on a purely combinatorial state, with no scheme in sight. The state records the
irreducible *components* of the divisors as natural numbers below `nextComp`, each with the
*label* of its divisor `E^j` (a natural number below `nextLabel`; the exceptional divisor of a
blow-up gets the label `nextLabel`, [Kol07, Definition 65]: the new divisor is put last) and an
*exponent*, and the *nerve*: the finite family of nonempty sets of components with nonempty
common intersection. The nerve is down-closed, its faces have size at most the dimension bound
`n` and carry at most one component per label; dead components (empty divisors) lie in no face.

Deviation from the source. Kollár's state has one exponent per divisor `E^j` and blows up the
whole intersection `E^{j₁} ∩ ⋯ ∩ E^{j_r}`. Here every irreducible component of `E^j` has its own
exponent (the order of the ideal along that component, the fine monomial split of
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/MonomialPart.lean`), and the centre at a phase
is a set of faces with a common label tuple, each of which contributes its own exceptional component
with its own exponent. With one component per label the two procedures coincide. The refinement is
forced by functoriality under open immersions: with one exponent per possibly reducible member the
procedure is not even compatible with restriction to an open subscheme
(`HironakaExamples/Monomial/Examples.lean`, `coarseX` and `coarseU`, and the computation
`split_coarse_runs` of `HironakaExamples/Monomial/Example112.lean`). Not in the sources in this
form.

* `MonomialState`; `total` (the sum `a(T)` of the exponents of a face), `labels`, `labelTuple`
  (the sorted list of the labels of a face, Kollár's `(j₁ < ⋯ < j_r)`).
* `blowUp st S`: the transition for a centre `S` (a finset of faces with a common label tuple):
  new label `nextLabel`; one new component `newComp S P` per face `P ∈ S` with that label and
  exponent `a(P) - m`; the nerve transformed by the rule
  `N ↦ {T ∈ N : P ⊄ T} ∪ {T₁ ∪ {c_P} : T₁ ∪ P ∈ N, P ⊄ T₁}` for the faces `P` of the centre.
  The definition applies the rule to all faces of `S` at once and asks, for the new faces of `P`,
  that no face of the centre be contained in `T₁`; for a centre this is the condition `P ⊄ T₁` of
  the rule (`mem_blowUp_nerve`), and it makes the transition a total function of the state and
  an arbitrary finset of faces, preserving every invariant of the state. That this rule is what
  the total transform of the boundary does under the blow-up of the centre is proved on schemes
  in `Hironaka/Resolution/Algebraic/Monomial/Geometric/Kernel.lean` (`nerve_blowUpPieces`).
* `faces st r`, `maxTotal`, `numMax`, `measure st r = toLex (m_r, n_r)` and `Star st s`:
  Kollár's `(m_r(E), n_r(E))` and `(∗_s)` of [Kol07, 111, Step 3.r], counting faces of
  components.
* `choice st r`: Kollár's choice at phase `r`, the faces of size `r` of maximal sum among those
  of sum `≥ m`, whose label tuple is lexicographically smallest among the maximizers; empty when
  no `r`-face has sum `≥ m` (`mem_choice`, `choice_eq_empty_iff`).
* `Valid`, `ofValid`, `valid_self`: the invariants as a decidable predicate on the raw data, so
  that concrete states can be built by `decide`.

The measure decreases under a blow-up along `choice st r`
(`Hironaka/Resolution/Algebraic/Monomial/Measure.lean`); the phases and their termination are
`Hironaka/Resolution/Algebraic/Monomial/Step3Phases.lean`. The geometric realisation of the state on
a scheme is `Hironaka.Monomial.PieceFamily`
(`Hironaka/Resolution/Algebraic/Monomial/Geometric/Pieces.lean`), and the real-analytic strand
(`Hironaka/Resolution/Analytic/OrderReduction/BMO/Step3Monomial/`) runs the same combinatorial
procedure on its own piece families.
-/

@[expose] public section

namespace Hironaka.Monomial

open Finset

/-- The combinatorial state of the monomial procedure of [Kol07, 111, Step 3]. Components and
labels are natural numbers below `nextComp` and `nextLabel`; `label c` is the divisor `E^j` the
component `c` belongs to, `a c` its exponent; `nerve` is the family of faces (nonempty sets of
components with nonempty common intersection): down-closed, every face of size at most the
dimension bound `n`, with injective labels. Dead components lie in no face. -/
@[ext]
structure MonomialState where
  /-- The dimension bound `n = dim X` (the last phase of Step 3 is Step `3.n`). -/
  n : ℕ
  /-- The marking `m ≥ 1` of the marked monomial ideal. -/
  m : ℕ
  one_le_m : 1 ≤ m
  /-- Components are `0, …, nextComp - 1`; a blow-up allocates from `nextComp`. -/
  nextComp : ℕ
  /-- Labels are `0, …, nextLabel - 1`; a blow-up creates the label `nextLabel`. -/
  nextLabel : ℕ
  /-- The label (index of the divisor `E^j`) of a component. -/
  label : ℕ → ℕ
  /-- The exponent of a component. -/
  a : ℕ → ℕ
  /-- The nerve: the faces. -/
  nerve : Finset (Finset ℕ)
  nerve_nonempty : ∀ T ∈ nerve, T.Nonempty
  nerve_lt : ∀ T ∈ nerve, ∀ c ∈ T, c < nextComp
  label_lt : ∀ c, c < nextComp → label c < nextLabel
  nerve_down : ∀ T ∈ nerve, ∀ T' ⊆ T, T'.Nonempty → T' ∈ nerve
  nerve_card : ∀ T ∈ nerve, T.card ≤ n
  nerve_labels : ∀ T ∈ nerve, Set.InjOn label T

namespace MonomialState

variable (st : MonomialState)

/-- The sum `a(T) = ∑_{c ∈ T} a_c` of the exponents of a set of components. -/
def total (T : Finset ℕ) : ℕ := ∑ c ∈ T, st.a c

/-- The set of labels of a set of components. -/
def labels (T : Finset ℕ) : Finset ℕ := T.image st.label

/-- The elements of a finset of naturals as an increasing list: the numbers below `sup + 1` that
lie in the set. (Mathlib's `Finset.sort` is defined by well-founded recursion and does not
reduce in the kernel; this enumeration does, so that the example computations run by
`decide`.) -/
def sortedList (s : Finset ℕ) : List ℕ := (List.range (s.sup id + 1)).filter (· ∈ s)

theorem mem_sortedList {s : Finset ℕ} {x : ℕ} : x ∈ sortedList s ↔ x ∈ s := by
  rw [sortedList, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) h), h⟩⟩

theorem sortedList_toFinset (s : Finset ℕ) : (sortedList s).toFinset = s := by
  ext x
  rw [List.mem_toFinset, mem_sortedList]

theorem sortedList_injective : Function.Injective sortedList := fun s t h => by
  rw [← sortedList_toFinset s, ← sortedList_toFinset t, h]

/-- `sortedList s` is increasing. -/
theorem sortedList_pairwise (s : Finset ℕ) : (sortedList s).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

/-- The label tuple of a face: its labels as an increasing list, Kollár's `(j₁ < ⋯ < j_r)`,
compared lexicographically. -/
def labelTuple (T : Finset ℕ) : List ℕ := sortedList (st.labels T)

theorem total_insert {T : Finset ℕ} {c : ℕ} (hc : c ∉ T) :
    st.total (insert c T) = st.a c + st.total T :=
  Finset.sum_insert hc

theorem total_erase_add {T : Finset ℕ} {c : ℕ} (hc : c ∈ T) :
    st.total (T.erase c) + st.a c = st.total T :=
  Finset.sum_erase_add _ _ hc

theorem total_empty : st.total ∅ = 0 := Finset.sum_empty

theorem labelTuple_eq_iff {T T' : Finset ℕ} :
    st.labelTuple T = st.labelTuple T' ↔ st.labels T = st.labels T' :=
  ⟨fun h => sortedList_injective h, fun h => by rw [labelTuple, labelTuple, h]⟩

/-- A face of the nerve has all its components below `nextComp`. -/
theorem lt_nextComp_of_mem {T : Finset ℕ} (hT : T ∈ st.nerve) {c : ℕ} (hc : c ∈ T) :
    c < st.nextComp :=
  st.nerve_lt T hT c hc

/-- The nonempty subsets of a face are faces. -/
theorem mem_nerve_of_subset {T T' : Finset ℕ} (hT : T ∈ st.nerve) (h : T' ⊆ T)
    (hne : T'.Nonempty) : T' ∈ st.nerve :=
  st.nerve_down T hT T' h hne

/-! ### Kollár's measure and `(∗_s)` -/

/-- The faces of size `r`. -/
def faces (r : ℕ) : Finset (Finset ℕ) := st.nerve.filter fun T => T.card = r

theorem mem_faces {r : ℕ} {T : Finset ℕ} : T ∈ st.faces r ↔ T ∈ st.nerve ∧ T.card = r :=
  Finset.mem_filter

/-- Kollár's `m_r(E)` of [Kol07, 111, Step 3.r]: the maximal sum of an `r`-face (`0` if there is
none). -/
def maxTotal (r : ℕ) : ℕ := (st.faces r).sup st.total

/-- Kollár's `n_r(E)` of [Kol07, 111, Step 3.r]: the number of `r`-faces achieving `m_r(E)`. -/
def numMax (r : ℕ) : ℕ := ((st.faces r).filter fun T => st.total T = st.maxTotal r).card

/-- Kollár's pair `(m_r(E), n_r(E))` of [Kol07, 111, Step 3.2 and 3.r] in the lexicographic
order `ℕ ×ₗ ℕ`. -/
def measure (r : ℕ) : ℕ ×ₗ ℕ := toLex (st.maxTotal r, st.numMax r)

/-- Kollár's condition `(∗_s)` of [Kol07, 111, Step 3.r]: every face of size `s` has sum `< m`. -/
def Star (s : ℕ) : Prop := ∀ T ∈ st.faces s, st.total T < st.m

theorem total_le_maxTotal {r : ℕ} {T : Finset ℕ} (hT : T ∈ st.faces r) :
    st.total T ≤ st.maxTotal r :=
  Finset.le_sup (f := st.total) hT

theorem maxTotal_le {r b : ℕ} (h : ∀ T ∈ st.faces r, st.total T ≤ b) : st.maxTotal r ≤ b :=
  Finset.sup_le h

/-- `(∗_0)` holds vacuously: faces are nonempty. -/
theorem star_zero : st.Star 0 := fun T hT => by
  have h := (st.mem_faces.mp hT)
  exact absurd (Finset.card_eq_zero.mp h.2) (st.nerve_nonempty T h.1).ne_empty

/-- `(∗_s)` holds vacuously for `s > n`: faces have size at most `n`. -/
theorem star_of_lt {s : ℕ} (hs : st.n < s) : st.Star s := fun T hT => by
  have h := st.mem_faces.mp hT
  exact absurd (h.2 ▸ st.nerve_card T h.1) (not_le.mpr hs)

/-! ### Kollár's choice -/

/-- The candidates at phase `r`: the faces of size `r` of sum `≥ m`. -/
def candidates (r : ℕ) : Finset (Finset ℕ) := (st.faces r).filter fun T => st.m ≤ st.total T

/-- The candidates of maximal sum. -/
def maximizers (r : ℕ) : Finset (Finset ℕ) :=
  (st.candidates r).filter fun T => st.total T = (st.candidates r).sup st.total

/-- Kollár's choice at phase `r` ([Kol07, 111, Steps 3.1, 3.2 and 3.r]): the faces of size `r`
of maximal sum among those of sum `≥ m` whose label tuple is lexicographically smallest among
the maximizers; empty when no `r`-face has sum `≥ m`. With one component per label these are
the faces of the lexicographically smallest `(j₁ < ⋯ < j_r)` with `E^{j₁} ∩ ⋯ ∩ E^{j_r} ≠ ∅` and
`a_{j₁} + ⋯ + a_{j_r} ≥ m` maximal, as in the source. -/
def choice (r : ℕ) : Finset (Finset ℕ) :=
  (st.maximizers r).filter fun T => ∀ T' ∈ st.maximizers r, st.labelTuple T ≤ st.labelTuple T'

theorem mem_candidates {r : ℕ} {T : Finset ℕ} :
    T ∈ st.candidates r ↔ T ∈ st.faces r ∧ st.m ≤ st.total T :=
  Finset.mem_filter

theorem mem_maximizers {r : ℕ} {T : Finset ℕ} :
    T ∈ st.maximizers r ↔ T ∈ st.faces r ∧ st.m ≤ st.total T ∧
      ∀ T' ∈ st.faces r, st.m ≤ st.total T' → st.total T' ≤ st.total T := by
  rw [maximizers, Finset.mem_filter, mem_candidates]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun T' hT' hm =>
      h3 ▸ Finset.le_sup (f := st.total) (st.mem_candidates.mpr ⟨hT', hm⟩)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, le_antisymm (Finset.le_sup (f := st.total) (st.mem_candidates.mpr ⟨h1, h2⟩))
      (Finset.sup_le fun T' hT' => ?_)⟩
    obtain ⟨hT', hm⟩ := st.mem_candidates.mp hT'
    exact h3 T' hT' hm

/-- The characterization of Kollár's choice: the faces of size `r` of sum `≥ m` and of maximal sum
among those, whose label tuple is lexicographically smallest among the faces of that sum. -/
theorem mem_choice {r : ℕ} {T : Finset ℕ} :
    T ∈ st.choice r ↔ T ∈ st.faces r ∧ st.m ≤ st.total T ∧
      (∀ T' ∈ st.faces r, st.m ≤ st.total T' → st.total T' ≤ st.total T) ∧
      ∀ T' ∈ st.faces r, st.total T' = st.total T → st.labelTuple T ≤ st.labelTuple T' := by
  rw [choice, Finset.mem_filter, mem_maximizers]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun T' hT' he => h4 T' (st.mem_maximizers.mpr ⟨hT', he ▸ h2, ?_⟩)⟩
    exact fun T'' hT'' hm => he ▸ h3 T'' hT'' hm
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h2, h3⟩, fun T' hT' => ?_⟩
    obtain ⟨h1', h2', h3'⟩ := st.mem_maximizers.mp hT'
    exact h4 T' h1' (le_antisymm (h3 T' h1' h2') (h3' T h1 h2))

theorem mem_faces_of_mem_choice {r : ℕ} {T : Finset ℕ} (h : T ∈ st.choice r) :
    T ∈ st.faces r :=
  (st.mem_choice.mp h).1

theorem mem_nerve_of_mem_choice {r : ℕ} {T : Finset ℕ} (h : T ∈ st.choice r) : T ∈ st.nerve :=
  (st.mem_faces.mp (st.mem_faces_of_mem_choice h)).1

theorem card_of_mem_choice {r : ℕ} {T : Finset ℕ} (h : T ∈ st.choice r) : T.card = r :=
  (st.mem_faces.mp (st.mem_faces_of_mem_choice h)).2

theorem m_le_total_of_mem_choice {r : ℕ} {T : Finset ℕ} (h : T ∈ st.choice r) :
    st.m ≤ st.total T :=
  (st.mem_choice.mp h).2.1

/-- The faces of the center have a common sum. -/
theorem total_eq_of_mem_choice {r : ℕ} {T T' : Finset ℕ} (h : T ∈ st.choice r)
    (h' : T' ∈ st.choice r) : st.total T = st.total T' := by
  obtain ⟨h1, h2, h3, -⟩ := st.mem_choice.mp h
  obtain ⟨h1', h2', h3', -⟩ := st.mem_choice.mp h'
  exact le_antisymm (h3' T h1 h2) (h3 T' h1' h2')

/-- The faces of the center have a common label tuple. -/
theorem labelTuple_eq_of_mem_choice {r : ℕ} {T T' : Finset ℕ} (h : T ∈ st.choice r)
    (h' : T' ∈ st.choice r) : st.labelTuple T = st.labelTuple T' := by
  obtain ⟨h1, -, -, h4⟩ := st.mem_choice.mp h
  obtain ⟨h1', -, -, h4'⟩ := st.mem_choice.mp h'
  exact le_antisymm (h4 T' h1' (st.total_eq_of_mem_choice h' h))
    (h4' T h1 (st.total_eq_of_mem_choice h h'))

/-- The faces of the center are the `r`-faces of sum `m_r`, when the center is nonempty. -/
theorem total_eq_maxTotal_of_mem_choice {r : ℕ} {T : Finset ℕ} (h : T ∈ st.choice r) :
    st.total T = st.maxTotal r := by
  obtain ⟨h1, h2, h3, -⟩ := st.mem_choice.mp h
  refine le_antisymm (st.total_le_maxTotal h1) (st.maxTotal_le fun T' hT' => ?_)
  by_cases hm : st.m ≤ st.total T'
  · exact h3 T' hT' hm
  · exact (not_le.mp hm).le.trans h2

/-- Kollár's choice is empty exactly when `(∗_r)` holds. -/
theorem choice_eq_empty_iff {r : ℕ} : st.choice r = ∅ ↔ st.Star r := by
  constructor
  · intro h T hT
    by_contra hm
    have hne : (st.candidates r).Nonempty := ⟨T, st.mem_candidates.mpr ⟨hT, not_lt.mp hm⟩⟩
    obtain ⟨T₀, hT₀, hsup⟩ := Finset.exists_mem_eq_sup _ hne st.total
    have hmax : (st.maximizers r).Nonempty := ⟨T₀, Finset.mem_filter.mpr ⟨hT₀, hsup.symm⟩⟩
    obtain ⟨T₁, hT₁, hmin⟩ := Finset.exists_min_image _ st.labelTuple hmax
    exact Finset.notMem_empty T₁ (h ▸ Finset.mem_filter.mpr ⟨hT₁, hmin⟩)
  · intro h
    refine Finset.eq_empty_of_forall_notMem fun T hT => ?_
    exact absurd (st.m_le_total_of_mem_choice hT) (not_le.mpr (h T (st.mem_faces_of_mem_choice hT)))

theorem choice_nonempty_iff {r : ℕ} : (st.choice r).Nonempty ↔ ¬ st.Star r := by
  rw [Finset.nonempty_iff_ne_empty, not_iff_not, choice_eq_empty_iff]

/-! ### The transition -/

/-- The nerve rule for the faces of a centre `S`, with `c P` the new component of the face `P`:
the old faces containing no face of the centre, and for each `P ∈ S` the faces `T₁ ∪ {c P}` with
`T₁ ∪ P` an old face and no face of the centre inside `T₁`. -/
def blowUpNerve (N S : Finset (Finset ℕ)) (c : Finset ℕ → ℕ) : Finset (Finset ℕ) :=
  (N.filter fun T => ∀ P ∈ S, ¬ P ⊆ T) ∪
    S.biUnion fun P =>
      ((insert ∅ N).filter fun T₁ => T₁ ∪ P ∈ N ∧ ∀ Q ∈ S, ¬ Q ⊆ T₁).image (insert (c P))

theorem mem_blowUpNerve {N S : Finset (Finset ℕ)} {c : Finset ℕ → ℕ} {T : Finset ℕ} :
    T ∈ blowUpNerve N S c ↔ (T ∈ N ∧ ∀ P ∈ S, ¬ P ⊆ T) ∨
      ∃ P ∈ S, ∃ T₁, (T₁ = ∅ ∨ T₁ ∈ N) ∧ T₁ ∪ P ∈ N ∧ (∀ Q ∈ S, ¬ Q ⊆ T₁) ∧
        T = insert (c P) T₁ := by
  simp only [blowUpNerve, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_insert]
  constructor
  · rintro (h | ⟨P, hP, T₁, ⟨h1, h2, h3⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨P, hP, T₁, h1, h2, h3, rfl⟩
  · rintro (h | ⟨P, hP, T₁, h1, h2, h3, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨P, hP, T₁, ⟨h1, h2, h3⟩, rfl⟩

/-- The components of a face as an increasing list: the key ordering the faces of a center. -/
def faceList (P : Finset ℕ) : List ℕ := sortedList P

theorem faceList_injective : Function.Injective faceList := fun _ _ h => sortedList_injective h

/-- The rank of the face `P` among the faces of the center `S`, in the order of `faceList`. -/
def rank (S : Finset (Finset ℕ)) (P : Finset ℕ) : ℕ :=
  (S.filter fun Q => faceList Q < faceList P).card

theorem rank_lt_card {S : Finset (Finset ℕ)} {P : Finset ℕ} (hP : P ∈ S) : rank S P < S.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨P, hP, lt_irrefl _⟩)

theorem rank_lt_rank {S : Finset (Finset ℕ)} {P Q : Finset ℕ} (hP : P ∈ S)
    (h : faceList P < faceList Q) : rank S P < rank S Q := by
  refine Finset.card_lt_card ⟨fun R hR => ?_, fun hsub => ?_⟩
  · obtain ⟨hR, hlt⟩ := Finset.mem_filter.mp hR
    exact Finset.mem_filter.mpr ⟨hR, hlt.trans h⟩
  · have := Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hP, h⟩))
    exact lt_irrefl _ this.2

theorem rank_injOn (S : Finset (Finset ℕ)) : Set.InjOn (rank S) S := by
  intro P hP Q hQ h
  by_contra hne : P ≠ Q
  rcases lt_or_gt_of_ne (faceList_injective.ne hne) with hlt | hlt
  · exact absurd h (ne_of_lt (rank_lt_rank hP hlt))
  · exact absurd h (ne_of_gt (rank_lt_rank hQ hlt))

/-- The new component allocated to the face `P` of the center `S`: `nextComp + rank S P`. -/
def newComp (S : Finset (Finset ℕ)) (P : Finset ℕ) : ℕ := st.nextComp + rank S P

theorem nextComp_le_newComp (S : Finset (Finset ℕ)) (P : Finset ℕ) :
    st.nextComp ≤ st.newComp S P :=
  Nat.le_add_right _ _

theorem newComp_lt {S : Finset (Finset ℕ)} {P : Finset ℕ} (hP : P ∈ S) :
    st.newComp S P < st.nextComp + S.card :=
  Nat.add_lt_add_left (rank_lt_card hP) _

theorem newComp_injOn (S : Finset (Finset ℕ)) : Set.InjOn (st.newComp S) S :=
  fun _ hP _ hQ h => rank_injOn S hP hQ (Nat.add_left_cancel h)

theorem newComp_notMem {S : Finset (Finset ℕ)} {P T : Finset ℕ} (hT : T ∈ st.nerve) :
    st.newComp S P ∉ T := fun h =>
  absurd (st.lt_nextComp_of_mem hT h) (not_lt.mpr (st.nextComp_le_newComp S P))

/-- The transition for a centre `S` ([Kol07, 111, Step 3.2 and 3.r]: the new divisor is put
last with exponent `a_{j₁} + ⋯ + a_{j_r} - m`). New label `nextLabel`; for each `P ∈ S` a new
component `newComp S P` with label `nextLabel` and exponent `a(P) - m`; the other exponents and
labels unchanged; the nerve transformed by the rule of `blowUpNerve`. -/
def blowUp (S : Finset (Finset ℕ)) : MonomialState where
  n := st.n
  m := st.m
  one_le_m := st.one_le_m
  nextComp := st.nextComp + S.card
  nextLabel := st.nextLabel + 1
  label c := if c < st.nextComp then st.label c else st.nextLabel
  a c := if c < st.nextComp then st.a c
    else (S.filter fun P => st.newComp S P = c).sup fun P => st.total P - st.m
  nerve := blowUpNerve st.nerve S (st.newComp S)
  nerve_nonempty T hT := by
    rcases mem_blowUpNerve.mp hT with ⟨h, -⟩ | ⟨P, -, T₁, -, -, -, rfl⟩
    · exact st.nerve_nonempty T h
    · exact Finset.insert_nonempty _ _
  nerve_lt T hT c hc := by
    rcases mem_blowUpNerve.mp hT with ⟨h, -⟩ | ⟨P, hP, T₁, -, h1, -, rfl⟩
    · exact (st.lt_nextComp_of_mem h hc).trans_le (Nat.le_add_right _ _)
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · exact st.newComp_lt hP
      · exact (st.lt_nextComp_of_mem h1 (Finset.mem_union_left _ hc)).trans_le
          (Nat.le_add_right _ _)
  label_lt c _ := by
    split_ifs with h
    · exact (st.label_lt c h).trans (Nat.lt_succ_self _)
    · exact Nat.lt_succ_self _
  nerve_down T hT T' hT'T hne := by
    rcases mem_blowUpNerve.mp hT with ⟨h, hS⟩ | ⟨P, hP, T₁, -, h1, h3, rfl⟩
    · exact mem_blowUpNerve.mpr (Or.inl ⟨st.mem_nerve_of_subset h hT'T hne,
        fun P hP hPT' => hS P hP (hPT'.trans hT'T)⟩)
    · by_cases hc : st.newComp S P ∈ T'
      · refine mem_blowUpNerve.mpr (Or.inr ⟨P, hP, T'.erase (st.newComp S P), ?_, ?_, ?_,
          (Finset.insert_erase hc).symm⟩)
        · by_cases he : T'.erase (st.newComp S P) = ∅
          · exact Or.inl he
          · refine Or.inr (st.mem_nerve_of_subset h1 ?_ (Finset.nonempty_iff_ne_empty.mpr he))
            exact ((Finset.erase_subset_erase _ hT'T).trans
              (Finset.erase_insert_subset _ _)).trans Finset.subset_union_left
        · refine st.mem_nerve_of_subset h1 (Finset.union_subset_union
            ((Finset.erase_subset_erase _ hT'T).trans (Finset.erase_insert_subset _ _))
            subset_rfl) ?_
          have hP0 : P.Nonempty := by
            by_contra hP0
            rw [Finset.not_nonempty_iff_eq_empty] at hP0
            exact h3 P hP (hP0 ▸ Finset.empty_subset _)
          exact hP0.mono Finset.subset_union_right
        · intro Q hQ hQT'
          exact h3 Q hQ (hQT'.trans ((Finset.erase_subset_erase _ hT'T).trans
            (Finset.erase_insert_subset _ _)))
      · have hT'₁ : T' ⊆ T₁ := fun x hx => by
          rcases Finset.mem_insert.mp (hT'T hx) with rfl | hx'
          · exact absurd hx hc
          · exact hx'
        exact mem_blowUpNerve.mpr (Or.inl ⟨st.mem_nerve_of_subset h1
          (hT'₁.trans Finset.subset_union_left) hne, fun Q hQ hQT' => h3 Q hQ (hQT'.trans hT'₁)⟩)
  nerve_card T hT := by
    rcases mem_blowUpNerve.mp hT with ⟨h, -⟩ | ⟨P, hP, T₁, -, h1, h3, rfl⟩
    · exact st.nerve_card T h
    · have hnot : st.newComp S P ∉ T₁ := fun hc =>
        st.newComp_notMem h1 (Finset.mem_union_left _ hc)
      rw [Finset.card_insert_of_notMem hnot]
      refine le_trans ?_ (st.nerve_card _ h1)
      obtain ⟨p, hpP, hpT₁⟩ := Finset.not_subset.mp (h3 P hP)
      have : insert p T₁ ⊆ T₁ ∪ P :=
        Finset.insert_subset (Finset.mem_union_right _ hpP) Finset.subset_union_left
      exact (Finset.card_insert_of_notMem hpT₁).symm.le.trans (Finset.card_le_card this)
  nerve_labels T hT := by
    rcases mem_blowUpNerve.mp hT with ⟨h, -⟩ | ⟨P, hP, T₁, -, h1, -, rfl⟩
    · intro x hx y hy hxy
      have hx' : x < st.nextComp := st.lt_nextComp_of_mem h hx
      have hy' : y < st.nextComp := st.lt_nextComp_of_mem h hy
      simp only [hx', hy', ite_true] at hxy
      exact st.nerve_labels T h hx hy hxy
    · intro x hx y hy hxy
      have hlt : ∀ z ∈ T₁, z < st.nextComp := fun z hz =>
        st.lt_nextComp_of_mem h1 (Finset.mem_union_left _ hz)
      have hnew : ¬ st.newComp S P < st.nextComp := not_lt.mpr (st.nextComp_le_newComp S P)
      rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
      · rfl
      · simp only [hnew, hlt y hy, ite_true, ite_false] at hxy
        exact absurd hxy.symm (st.label_lt y (hlt y hy)).ne
      · simp only [hnew, hlt x hx, ite_true, ite_false] at hxy
        exact absurd hxy (st.label_lt x (hlt x hx)).ne
      · simp only [hlt x hx, hlt y hy, ite_true] at hxy
        exact st.nerve_labels _ h1 (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hy) hxy

/-! ### The transition, read off -/

variable (S : Finset (Finset ℕ))

@[simp] theorem blowUp_n : (st.blowUp S).n = st.n := rfl
@[simp] theorem blowUp_m : (st.blowUp S).m = st.m := rfl
@[simp] theorem blowUp_nextComp : (st.blowUp S).nextComp = st.nextComp + S.card := rfl
@[simp] theorem blowUp_nextLabel : (st.blowUp S).nextLabel = st.nextLabel + 1 := rfl
theorem blowUp_nerve : (st.blowUp S).nerve = blowUpNerve st.nerve S (st.newComp S) := rfl

theorem blowUp_label_of_lt {c : ℕ} (hc : c < st.nextComp) : (st.blowUp S).label c = st.label c :=
  ite_eq_left hc

theorem blowUp_a_of_lt {c : ℕ} (hc : c < st.nextComp) : (st.blowUp S).a c = st.a c :=
  ite_eq_left hc

/-- The new components carry the new label. -/
theorem blowUp_label_newComp (P : Finset ℕ) : (st.blowUp S).label (st.newComp S P) = st.nextLabel :=
  ite_eq_right (not_lt.mpr (st.nextComp_le_newComp S P))

/-- The new component of the face `P` has exponent `a(P) - m`. -/
theorem blowUp_a_newComp {P : Finset ℕ} (hP : P ∈ S) :
    (st.blowUp S).a (st.newComp S P) = st.total P - st.m := by
  change (if st.newComp S P < st.nextComp then st.a (st.newComp S P)
    else (S.filter fun Q => st.newComp S Q = st.newComp S P).sup fun Q => st.total Q - st.m) = _
  rw [ite_eq_right (not_lt.mpr (st.nextComp_le_newComp S P))]
  have : (S.filter fun Q => st.newComp S Q = st.newComp S P) = {P} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hP, rfl⟩,
      fun Q hQ => st.newComp_injOn S (Finset.mem_filter.mp hQ).1 hP (Finset.mem_filter.mp hQ).2⟩
  rw [this, Finset.sup_singleton]

/-- The sum of a set of old components is unchanged. -/
theorem blowUp_total_of_lt {T : Finset ℕ} (hT : ∀ c ∈ T, c < st.nextComp) :
    (st.blowUp S).total T = st.total T :=
  Finset.sum_congr rfl fun c hc => st.blowUp_a_of_lt S (hT c hc)

/-- The sum of a new face `T₁ ∪ {c_P}`: `a(T₁) + (a(P) - m)`. -/
theorem blowUp_total_insert_newComp {P T₁ : Finset ℕ} (hP : P ∈ S)
    (hT₁ : ∀ c ∈ T₁, c < st.nextComp) :
    (st.blowUp S).total (insert (st.newComp S P) T₁) = (st.total P - st.m) + st.total T₁ := by
  have hnot : st.newComp S P ∉ T₁ := fun h =>
    absurd (hT₁ _ h) (not_lt.mpr (st.nextComp_le_newComp S P))
  rw [total_insert _ hnot, st.blowUp_a_newComp S hP, st.blowUp_total_of_lt S hT₁]

/-- A centre: a finset of faces with a common label tuple (each face of sum `≥ m` is the
admissibility condition, not part of this predicate). -/
def IsCenter : Prop := S ⊆ st.nerve ∧ ∀ P ∈ S, ∀ Q ∈ S, st.labels P = st.labels Q

/-- Kollár's choice is a center. -/
theorem isCenter_choice (r : ℕ) : st.IsCenter (st.choice r) :=
  ⟨fun _ hP => st.mem_nerve_of_mem_choice hP, fun _ hP _ hQ =>
    st.labelTuple_eq_iff.mp (st.labelTuple_eq_of_mem_choice hP hQ)⟩

/-- Two faces of a center contained in a common face are equal (the components of a label are
disjoint: a face has injective labels). -/
theorem eq_of_isCenter_of_subset {P Q T : Finset ℕ} (hS : st.IsCenter S) (hP : P ∈ S) (hQ : Q ∈ S)
    (hT : T ∈ st.nerve) (hPT : P ⊆ T) (hQT : Q ⊆ T) : P = Q := by
  have hinj := st.nerve_labels T hT
  have key : ∀ {A B : Finset ℕ}, A ∈ S → B ∈ S → A ⊆ T → B ⊆ T → A ⊆ B := by
    intro A B hA hB hAT hBT x hx
    have hlx : st.label x ∈ st.labels B := hS.2 A hA B hB ▸ Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hlx
    exact hinj (hBT hy) (hAT hx) hxy ▸ hy
  exact le_antisymm (key hP hQ hPT hQT) (key hQ hP hQT hPT)

/-- For a centre, the rule reads as stated in the module docstring: the new faces of `P` are
the `T₁ ∪ {c_P}` with `T₁ ∪ P ∈ N` and `P ⊄ T₁`. -/
theorem mem_blowUp_nerve {T : Finset ℕ} (hS : st.IsCenter S) :
    T ∈ (st.blowUp S).nerve ↔ (T ∈ st.nerve ∧ ∀ P ∈ S, ¬ P ⊆ T) ∨
      ∃ P ∈ S, ∃ T₁, T₁ ∪ P ∈ st.nerve ∧ ¬ P ⊆ T₁ ∧ T = insert (st.newComp S P) T₁ := by
  rw [blowUp_nerve, mem_blowUpNerve]
  constructor
  · rintro (h | ⟨P, hP, T₁, -, h1, h3, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨P, hP, T₁, h1, h3 P hP, rfl⟩
  · rintro (h | ⟨P, hP, T₁, h1, h3, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨P, hP, T₁, ?_, h1, fun Q hQ hQT₁ => ?_, rfl⟩
      · by_cases he : T₁ = ∅
        · exact Or.inl he
        · exact Or.inr (st.mem_nerve_of_subset h1 Finset.subset_union_left
            (Finset.nonempty_iff_ne_empty.mpr he))
      · exact h3 (st.eq_of_isCenter_of_subset S hS hQ hP h1
          (hQT₁.trans Finset.subset_union_left) Finset.subset_union_right ▸ hQT₁)

/-! ### A decidable constructor (for the example computations by `decide`) -/

/-- The invariants of a state with bounded quantifiers, decidable for concrete data. -/
def Valid (n m k L : ℕ) (label : ℕ → ℕ) (N : Finset (Finset ℕ)) : Prop :=
  1 ≤ m ∧ (∀ T ∈ N, T.Nonempty) ∧ (∀ T ∈ N, ∀ c ∈ T, c < k) ∧
  (∀ c, c < L + k → c < k → label c < L) ∧
  (∀ T ∈ N, ∀ T' ∈ T.powerset, T'.Nonempty → T' ∈ N) ∧ (∀ T ∈ N, T.card ≤ n) ∧
  ∀ T ∈ N, Set.InjOn label T

instance decidableValid (n m k L : ℕ) (label : ℕ → ℕ) (N : Finset (Finset ℕ)) :
    Decidable (Valid n m k L label N) := by
  unfold Valid; infer_instance

/-- A state from checked data (the invariants by `decide` on concrete data). -/
def ofValid (n m k L : ℕ) (label a : ℕ → ℕ) (N : Finset (Finset ℕ))
    (h : Valid n m k L label N) : MonomialState where
  n := n
  m := m
  one_le_m := h.1
  nextComp := k
  nextLabel := L
  label := label
  a := a
  nerve := N
  nerve_nonempty := h.2.1
  nerve_lt := h.2.2.1
  label_lt c hc := h.2.2.2.1 c (by omega) hc
  nerve_down T hT T' hT' hne := h.2.2.2.2.1 T hT T' (Finset.mem_powerset.mpr hT') hne
  nerve_card := h.2.2.2.2.2.1
  nerve_labels := h.2.2.2.2.2.2

/-- The data of a monomial state are `Valid` (its six invariants). -/
theorem valid_self (st : MonomialState) :
    MonomialState.Valid st.n st.m st.nextComp st.nextLabel st.label st.nerve :=
  ⟨st.one_le_m, st.nerve_nonempty, st.nerve_lt, fun c _ hc => st.label_lt c hc,
    fun T hT T' hT' hne => st.nerve_down T hT T' (Finset.mem_powerset.mp hT') hne, st.nerve_card,
    st.nerve_labels⟩

end MonomialState

end Hironaka.Monomial
