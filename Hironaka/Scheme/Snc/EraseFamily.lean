/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.Snc.LiftHypersurface
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Deleting a member of an ordered divisor family: `E − E^j`

Kollár writes `E − E^j` for the divisor `E = ∑_i E^i` with its member `E^j` removed (the proof of
[Kol07, Lemma 102]: "`E_S := (E − E^j)|_S`"; Step 2.1 of [Kol07, 104] clears the members
`E^1, E^2, …` in index order). This module holds that operation on `DivisorFamily`:

* `DivisorFamily.erase E j` — the family with the member `E^j` deleted, indexed by `{i // i ≠ j}`
  with the induced linear order (the boundary is an ordered set of divisors,
  [Kol07, Notation 64 (3)]); its members are `E`'s (`erase_component`).
* `eraseAppendSumEquiv`, `eraseAppendEquiv` — `(E − E^j) + E^j` is `E` up to reindexing, the deleted
  member going to the appended last position (`append_erase_component_eraseAppendEquiv_symm`); hence
  `(E − E^j) + E^j` is snc when `E` is (`isSnc_erase_append`).
* `hasSncWith_component` — a family with Definition 24's coordinates at every point has simple
  normal crossings with each of its own members (`E^i = (z_{c(i)} = 0)`).
* `IsEraseOf F E σ j` — "`F` is `E` with the member `E^j` deleted, up to a reindexing `σ`",
  preserved by total transforms (`IsEraseOf.isEraseOf_totalTransform`), which is what carries
  "`E − E^j`" along a blow-up sequence; and the snc bookkeeping of the proof of Lemma 102: a centre
  `Z ⊆ E^j` with simple normal crossings with `E − E^j` has simple normal crossings with `E`
  (`IsEraseOf.hasSncWith_of_le`, `hasSncWith_of_erase`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.DivisorFamily

open IdealSheafData

variable {X : Scheme.{u}}

/-- The family `E − E^j` — `E` with its member `E^j` deleted, indexed by `{i // i ≠ j}` with the
induced linear order (the proof of [Kol07, Lemma 102], "`E_S := (E − E^j)|_S`"; the order is the one
induced from the ordered set of divisors of [Kol07, Notation 64 (3)]). -/
def erase (E : DivisorFamily X) (j : E.ι) : DivisorFamily X where
  ι := {i : E.ι // i ≠ j}
  component := fun i => E.component i.1

/-- `(E − E^j) + E^j` is `E` up to reindexing — the equivalence of the plain index sums, the deleted
member going to the appended position. -/
def eraseAppendSumEquiv (E : DivisorFamily X) (j : E.ι) :
    {i : E.ι // i ≠ j} ⊕ PUnit.{u + 1} ≃ E.ι where
  toFun := Sum.elim Subtype.val fun _ => j
  invFun i := if h : i = j then Sum.inr PUnit.unit else Sum.inl ⟨i, h⟩
  left_inv := by
    rintro (⟨a, ha⟩ | ⟨⟩)
    · simp [ha]
    · simp
  right_inv i := by
    by_cases h : i = j
    · subst h
      simp
    · simp [h]

/-- `(E − E^j) + E^j` is `E` up to reindexing — the equivalence of index sets, the deleted member
going to the appended last position. -/
def eraseAppendEquiv (E : DivisorFamily X) (j : E.ι) :
    ((E.erase j).append (E.component j)).ι ≃ E.ι :=
  ofLex.trans (eraseAppendSumEquiv E j)

theorem erase_component (E : DivisorFamily X) (j : E.ι) (i : (E.erase j).ι) :
    (E.erase j).component i = E.component i.1 :=
  rfl

theorem append_erase_component_eraseAppendEquiv_symm (E : DivisorFamily X) (j : E.ι) (i : E.ι) :
    ((E.erase j).append (E.component j)).component ((eraseAppendEquiv E j).symm i) =
      E.component i := by
  by_cases h : i = j
  · subst h
    change Sum.elim (E.erase i).component (fun _ => E.component i)
      (if h : i = i then Sum.inr PUnit.unit else Sum.inl ⟨i, h⟩) = E.component i
    rw [dite_eq_left rfl]
    rfl
  · change Sum.elim (E.erase j).component (fun _ => E.component j)
      (if h : i = j then Sum.inr PUnit.unit else Sum.inl ⟨i, h⟩) = E.component i
    rw [dite_eq_right h]
    rfl

/-- If `E` is snc, so is `(E − E^j) + E^j` (the reindexing lemma `isSnc_of_equiv`). -/
theorem isSnc_erase_append (E : DivisorFamily X) (j : E.ι) (hE : E.IsSnc) :
    ((E.erase j).append (E.component j)).IsSnc :=
  isSnc_of_equiv (eraseAppendEquiv E j).symm
    (append_erase_component_eraseAppendEquiv_symm E j) hE

/-- [Kol07, Definition 24 (4)] for the family's own members: a family with the snc coordinates of
Definition 24 at every point has simple normal crossings with each of its members
(`E^i = (z_{c(i)} = 0)`). -/
theorem hasSncWith_component (E : DivisorFamily X)
    (hE : ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), E.IsSncAt x z) (i : E.ι) :
    E.HasSncWith (E.component i) := by
  intro x hx
  obtain ⟨n, z, hz⟩ := hE x
  obtain ⟨-, c, -, hc⟩ := id hz
  exact ⟨n, z, hz, {c ⟨i, hx⟩}, by rw [hc ⟨i, hx⟩]; simp⟩

/-- **`F` is `E` with the member `E^j` deleted**, up to the reindexing `σ`: `σ` is injective,
matches the members, and its range is exactly the indices other than `j`. `E.erase j` is the case
`σ = Subtype.val`; the relation is preserved by total transforms (the appended exceptional members
line up), which is what carries "`E − E^j`" along a blow-up sequence. -/
structure IsEraseOf (F E : DivisorFamily X) (σ : F.ι → E.ι) (j : E.ι) : Prop where
  /-- `σ` is injective. -/
  injective : Function.Injective σ
  /-- `σ` matches the members. -/
  component : ∀ a, E.component (σ a) = F.component a
  /-- The range of `σ` is the set of indices other than `j`. -/
  range : ∀ i, i ≠ j ↔ i ∈ Set.range σ

/-- `E.erase j` is `E` with `E^j` deleted, via `Subtype.val`. -/
theorem isEraseOf_erase (E : DivisorFamily X) (j : E.ι) :
    IsEraseOf (E.erase j) E Subtype.val j where
  injective := Subtype.val_injective
  component := fun _ => rfl
  range := fun i => ⟨fun h => ⟨⟨i, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩

/-- The bookkeeping along a blow-up: if `F` is `E` with `E^j` deleted, then the total transform of
`F` is the total transform of `E` with the birational transform of `E^j` deleted — the exceptional
members line up. -/
theorem IsEraseOf.isEraseOf_totalTransform {F E : DivisorFamily X} {σ : F.ι → E.ι} {j : E.ι}
    (h : IsEraseOf F E σ j) (D : X.IdealSheafData) :
    IsEraseOf (F.totalTransform D) (E.totalTransform D)
      (fun a => toLex (Sum.map σ id (ofLex a))) (toLex (Sum.inl j)) where
  injective := fun a b hab =>
    ofLex.injective ((Sum.map_injective.mpr ⟨h.injective, Function.injective_id⟩)
      (toLex.injective hab))
  component := fun a => by
    have key : ∀ s : F.ι ⊕ PUnit.{u + 1},
        (E.totalTransform D).component (toLex (Sum.map σ id s)) =
          Sum.elim (fun b => (F.component b).strictTransform D)
            (fun _ => D.exceptionalDivisor) s := by
      rintro (b | u)
      · change (E.component (σ b)).strictTransform D = (F.component b).strictTransform D
        rw [h.component b]
      · rfl
    exact key (ofLex a)
  range := fun i => by
    rcases i with b | u
    · constructor
      · intro hne
        obtain ⟨a', ha'⟩ := (h.range b).mp fun hb => hne (by subst hb; rfl)
        exact ⟨toLex (Sum.inl a'), congrArg (fun x => toLex (Sum.inl x)) ha'⟩
      · rintro ⟨a, ha⟩ hb
        rcases a with a' | v
        · have hσ : σ a' = b := Sum.inl_injective ha
          have hbj : b = j := Sum.inl_injective hb
          exact (h.range b).mpr ⟨a', hσ⟩ hbj
        · exact Sum.inr_ne_inl ha
    · exact ⟨fun _ => ⟨toLex (Sum.inr u), rfl⟩, fun _ h => Sum.inr_ne_inl h⟩

/-- The snc bookkeeping of the proof of [Kol07, Lemma 102] ([Kol07, Definition 24 (4)]): on a smooth
`X` over `k`, if `F` is `E` with `E^j` deleted and a centre `Z ⊆ E^j` has simple normal crossings
with `F`, then it has simple normal crossings with `E` — the exchange of coordinates
`hasSncWith_append_of_le` (through `hasSncWith_iff_hasSncWith_append`) applied to `F + E^j`, which
is `E` up to the reindexing. -/
theorem IsEraseOf.hasSncWith_of_le {F E : DivisorFamily X} {σ : F.ι → E.ι} {j : E.ι}
    (h : IsEraseOf F E σ j) {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [Smooth f]
    (hE : E.IsSnc) {Z : X.IdealSheafData} (hZ : E.component j ≤ Z) (hF : F.HasSncWith Z) :
    E.HasSncWith Z := by
  classical
  have hj : j ∉ Set.range σ := fun hj => (h.range j).mpr hj rfl
  let g : (F.append (E.component j)).ι → E.ι := fun a => Sum.elim σ (fun _ => j) (ofLex a)
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      rcases a with a' | u <;> rcases b with b' | v
      · exact congrArg (fun x => toLex (Sum.inl x)) (h.injective hab)
      · exact absurd ⟨a', hab⟩ hj
      · exact absurd ⟨b', hab.symm⟩ hj
      · rfl
    · intro i
      by_cases hij : i = j
      · exact ⟨toLex (Sum.inr PUnit.unit), hij.symm⟩
      · obtain ⟨a, ha⟩ := (h.range i).mp hij
        exact ⟨toLex (Sum.inl a), ha⟩
  let e : (F.append (E.component j)).ι ≃ E.ι := Equiv.ofBijective g hg
  have he : ∀ a, E.component (e a) = (F.append (E.component j)).component a := by
    intro a
    rcases a with a' | u
    · exact h.component a'
    · rfl
  have hE' : (F.append (E.component j)).IsSnc :=
    isSnc_of_equiv e.symm (fun i => by rw [← he (e.symm i), Equiv.apply_symm_apply]) hE
  exact hasSncWith_of_equiv e he ((hasSncWith_iff_hasSncWith_append f hE' hZ).mp hF)

/-- The snc bookkeeping of the proof of [Kol07, Lemma 102]: on a smooth `X` over `k`, a centre
`Z ⊆ E^j` with simple normal crossings with `E − E^j` has simple normal crossings with `E` —
`IsEraseOf.hasSncWith_of_le` for `E.erase j`. -/
theorem hasSncWith_of_erase (E : DivisorFamily X) (j : E.ι) {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (hE : E.IsSnc) {Z : X.IdealSheafData}
    (hZ : E.component j ≤ Z) (h : (E.erase j).HasSncWith Z) : E.HasSncWith Z :=
  (isEraseOf_erase E j).hasSncWith_of_le f hE hZ h

end AlgebraicGeometry.Scheme.DivisorFamily
