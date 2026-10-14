/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUpSequence.InducedData
public import Hironaka.Scheme.BlowUpSequence.PullbackInduced
public import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Deleting the empty blow-ups of a pullback, and the pulled-back triple

Kollár's functoriality for smooth morphisms [Kol07, 34.1] pulls a smooth blow-up sequence
`B(X, I, E)` back along a smooth `h : Y ⟶ X` and then deletes every blow-up whose center
`h^{-1} Z_i` is empty (the empty blow-up convention [Kol07, 32]). The deletion `eraseEmpty`
carries the tail of an empty blow-up back along the isomorphism `blowUpπ X ⊤` [Kol07, Warning 20],
a pullback along an isomorphism; this module shows that the order predicates of
[Kol07, Definition 66] survive it.

The one subtlety is bookkeeping. Kollár's divisor families are *sets* of divisors, on which the
empty exceptional divisor of an empty blow-up is invisible; a `DivisorFamily` indexes components,
so the empty blow-up adds an empty component to the induced family. The relation
`ExtendsByEmpty E₁ E₂` (`E₂` is `E₁` with extra empty components) is preserved by inverse images
and total transforms and is invisible to `IsSncAt`, `HasSncWith` and hence to the order predicates
(`ExtendsByEmpty.isOrderSeq`); under the empty blow-up the induced ideal returns to `I`
(`weakTransform_top_left`, `markedTransform_top_left`) and the induced family to `E` extended by
one empty component (`extendsByEmpty_totalTransform_top_comap_inv`). `IsOrderSeq.eraseEmpty` then
follows from `IsOrderSeq.pullback` (`Hironaka/Scheme/BlowUpSequence/PullbackSnc.lean`) with `d = 0`,
and Kollár's conclusion for a general smooth `h` (`isOrderSeq_eraseEmpty_pullback`) is the
composite.

The module also defines the pulled-back triple `Triple.pullback` and marked triple
`MarkedTriple.pullback`, the triple `(Y, h^* I, h^{-1}(E))` of [Kol07, 34.1 and Notation 64], used
in the statement of the functoriality clauses of the blow-up sequence functors; see also
[Wlo05, Proposition 2.4.2].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### The empty blow-up -/

/-- The exceptional divisor of the empty blow-up is empty (the unit ideal sheaf)
[Kol07, Warning 20]. -/
theorem exceptionalDivisor_top : (⊤ : X.IdealSheafData).exceptionalDivisor = ⊤ :=
  Scheme.IdealSheafData.comap_top _

/-- The saturation by the unit ideal sheaf is the identity (`colon_top`). -/
theorem saturate_top (I : X.IdealSheafData) : I.saturate ⊤ = I := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_saturate I ⊤)
  refine iSup_le fun i => ?_
  rw [show (⊤ : X.IdealSheafData) ^ i = ⊤ from one_pow i, Scheme.IdealSheafData.colon_top]

/-- The strict transform under the empty blow-up is the total transform. -/
theorem strictTransform_top_left (J : X.IdealSheafData) :
    J.strictTransform ⊤ = J.comap (⊤ : X.IdealSheafData).blowUpπ := by
  unfold strictTransform strictTransformAlong
  rw [exceptionalDivisor_top, saturate_top]

/-- The strict transform of the empty subscheme is empty. -/
theorem strictTransform_top_right (D :
    X.IdealSheafData) : Scheme.IdealSheafData.strictTransform ⊤ D = ⊤ := by
  unfold strictTransform strictTransformAlong
  rw [Scheme.IdealSheafData.comap_top]
  exact eq_top_iff.mpr (Scheme.IdealSheafData.le_saturate _ _)

/-- The marked transform under the empty blow-up is the total transform (`colon_top`). -/
theorem markedTransform_top_left (I : X.IdealSheafData) (m : ℕ) :
    I.markedTransform ⊤ m = I.comap (⊤ : X.IdealSheafData).blowUpπ := by
  unfold markedTransform controlledTransformAlong
  rw [exceptionalDivisor_top, show (⊤ : (⊤ : X.IdealSheafData).blowUp.IdealSheafData) ^ m = ⊤ from
      one_pow m,
    Scheme.IdealSheafData.colon_top]

/-- The exceptional order with respect to the unit ideal sheaf is `0` (the convention for an
unbounded set of controls, `sSup ℕ = 0`). -/
theorem exceptionalOrderAlong_top {B : Scheme.{u}} (π : B ⟶ X) (J : X.IdealSheafData) :
    exceptionalOrderAlong π ⊤ J = 0 := by
  unfold exceptionalOrderAlong
  have : {c : ℕ | (⊤ : B.IdealSheafData) ^ c ∣ J.comap π} = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    change (⊤ : B.IdealSheafData) ^ c ∣ J.comap π
    rw [show (⊤ : B.IdealSheafData) ^ c = ⊤ from one_pow c]
    exact one_dvd _
  rw [this, csSup_of_not_bddAbove not_bddAbove_univ, csSup_empty]
  rfl

/-- Under the empty blow-up the weak transform is the total transform [Kol07, Warning 20]. -/
theorem weakTransform_top_left (I : X.IdealSheafData) :
    I.weakTransform ⊤ = I.comap (⊤ : X.IdealSheafData).blowUpπ := by
  unfold weakTransform weakTransformAlong
  rw [exceptionalDivisor_top, exceptionalOrderAlong_top,
    controlledTransformAlong_zero]

/-! ### Families that differ by empty components -/

/-- `E₂` extends `E₁` by empty components: an injection of index sets carrying the components of
`E₁` to those of `E₂`, every other component of `E₂` being the unit ideal sheaf (the empty
divisor). Kollár's divisor families are sets of divisors, on which the empty divisor is invisible;
a `DivisorFamily` indexes components, so the exceptional divisor of an empty blow-up appears as an
empty component of the induced family, and the order predicates must be shown insensitive to it
(the deletion of empty blow-ups, [Kol07, 32]). -/
def ExtendsByEmpty (E₁ E₂ : DivisorFamily X) : Prop :=
  ∃ ι : E₁.ι → E₂.ι, Function.Injective ι ∧ (∀ i, E₂.component (ι i) = E₁.component i) ∧
    ∀ j, j ∉ Set.range ι → E₂.component j = ⊤

/-- Snc data restrict along an extension by empty components: the components through `x` are the
same (the unit ideal sheaf has empty support). -/
theorem ExtendsByEmpty.isSncAt {E₁ E₂ : DivisorFamily X} (hext : ExtendsByEmpty E₁ E₂) {x : X}
    {n : ℕ} {z : Fin n → X.presheaf.stalk x} (h : E₂.IsSncAt x z) : E₁.IsSncAt x z := by
  obtain ⟨ι, hι, hcomp, -⟩ := hext
  obtain ⟨hz, c, hc, hcE⟩ := h
  refine ⟨hz, fun i => c ⟨ι i.1, by rw [hcomp]; exact i.2⟩, fun i j hij => ?_, fun i => ?_⟩
  · have := hc hij
    exact Subtype.ext (hι (congrArg Subtype.val this))
  · exact (congrArg (fun Z : X.IdealSheafData => Z.stalkIdeal x) (hcomp i.1)).symm.trans
      (hcE ⟨ι i.1, by rw [hcomp]; exact i.2⟩)

/-- Simple normal crossings with a subscheme restrict along an extension by empty components. -/
theorem ExtendsByEmpty.hasSncWith {E₁ E₂ : DivisorFamily X} (hext : ExtendsByEmpty E₁ E₂)
    {Z : X.IdealSheafData} (h : E₂.HasSncWith Z) : E₁.HasSncWith Z := by
  intro x hx
  obtain ⟨n, z, hsnc, s, hs⟩ := h x hx
  exact ⟨n, z, hext.isSncAt hsnc, s, hs⟩

/-- Extension by empty components is preserved by inverse image. -/
theorem ExtendsByEmpty.comap {E₁ E₂ : DivisorFamily X} (hext : ExtendsByEmpty E₁ E₂) (g : Y ⟶ X) :
    ExtendsByEmpty (E₁.comap g) (E₂.comap g) := by
  obtain ⟨ι, hι, hcomp, htop⟩ := hext
  refine ⟨ι, hι, fun i => ?_, fun j hj => ?_⟩
  · exact congrArg (fun Z : X.IdealSheafData => Z.comap g) (hcomp i)
  · change (E₂.component j).comap g = ⊤
    rw [htop j hj, Scheme.IdealSheafData.comap_top]

/-- Extension by empty components is preserved by the total transform (the strict transform of the
empty subscheme is empty, `strictTransform_top_right`). -/
theorem ExtendsByEmpty.totalTransform {E₁ E₂ : DivisorFamily X} (hext : ExtendsByEmpty E₁ E₂)
    (D : X.IdealSheafData) : ExtendsByEmpty (E₁.totalTransform D) (E₂.totalTransform D) := by
  obtain ⟨ι, hι, hcomp, htop⟩ := hext
  change ∃ ι' : E₁.ι ⊕ₗ PUnit.{u + 1} → E₂.ι ⊕ₗ PUnit.{u + 1}, Function.Injective ι' ∧
    (∀ i, (E₂.totalTransform D).component (ι' i) = (E₁.totalTransform D).component i) ∧
      ∀ j, j ∉ Set.range ι' → (E₂.totalTransform D).component j = ⊤
  refine ⟨fun i => toLex (Sum.map ι id (ofLex i)), ?_, fun i => ?_, fun j hj => ?_⟩
  · intro i i' h
    have := Sum.map_injective.mpr ⟨hι, Function.injective_id⟩ (toLex.injective h)
    exact ofLex.injective this
  · obtain ⟨a, rfl⟩ := toLex.surjective i
    rcases a with j | u
    · change (E₂.component (ι j)).strictTransform D = (E₁.component j).strictTransform D
      rw [hcomp]
    · rfl
  · obtain ⟨a, rfl⟩ := toLex.surjective j
    rcases a with j₂ | u
    · change (E₂.component j₂).strictTransform D = ⊤
      have hj₂ : j₂ ∉ Set.range ι := by
        rintro ⟨i, rfl⟩
        exact hj ⟨toLex (Sum.inl i), rfl⟩
      rw [htop j₂ hj₂, strictTransform_top_right]
    · exact (hj ⟨toLex (Sum.inr u), rfl⟩).elim

section Order

variable {k : Type u} [Field k]

/-- The order condition of [Kol07, Definition 66] is insensitive to empty components of `E`: by
induction along the sequence with `isOrderSeq_cons_iff`, `ExtendsByEmpty.hasSncWith` and
`ExtendsByEmpty.totalTransform`. -/
theorem ExtendsByEmpty.isOrderSeq {E₁ E₂ : DivisorFamily X} (hext : ExtendsByEmpty E₁ E₂)
    {S : BlowUpSequence X} {f : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {m : ℕ}
    (h : S.IsOrderSeq f I E₂ m) : S.IsOrderSeq f I E₁ m := by
  induction S with
  | nil X => exact ⟨h.1, fun i => i.elim0⟩
  | cons X D rest ih =>
    rw [isOrderSeq_cons_iff] at h ⊢
    exact ⟨⟨h.1.1, hext.hasSncWith h.1.2.1, h.1.2.2⟩, ih (hext.totalTransform D) h.2⟩

/-- The marked form of `ExtendsByEmpty.isOrderSeq`. -/
theorem ExtendsByEmpty.isOrderGeSeq {E₁ E₂ : DivisorFamily X} (hext : ExtendsByEmpty E₁ E₂)
    {S : BlowUpSequence X} {f : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {m : ℕ}
    (h : S.IsOrderGeSeq f I m E₂) : S.IsOrderGeSeq f I m E₁ := by
  induction S with
  | nil X => exact ⟨h.1, fun i => i.elim0⟩
  | cons X D rest ih =>
    rw [isOrderGeSeq_cons_iff] at h ⊢
    exact ⟨⟨h.1.1, hext.hasSncWith h.1.2.1, h.1.2.2⟩, ih (hext.totalTransform D) h.2⟩

/-- Under the empty blow-up (an isomorphism, [Kol07, Warning 20]) the total transform of `E`,
carried back along the inverse, is `E` extended by the empty exceptional component. -/
theorem extendsByEmpty_totalTransform_top_comap_inv [IsIso (⊤ : X.IdealSheafData).blowUpπ]
    (E : DivisorFamily X) :
    ExtendsByEmpty E ((E.totalTransform ⊤).comap (inv (⊤ : X.IdealSheafData).blowUpπ)) := by
  change ∃ ι' : E.ι → E.ι ⊕ₗ PUnit.{u + 1}, Function.Injective ι' ∧
    (∀ i, ((E.totalTransform ⊤).comap (inv (⊤ : X.IdealSheafData).blowUpπ)).component
        (ι' i) = E.component i) ∧
      ∀ j, j ∉ Set.range ι' → ((E.totalTransform ⊤).comap (inv
          (⊤ : X.IdealSheafData).blowUpπ)).component j = ⊤
  refine ⟨fun j => toLex (Sum.inl j), fun i i' h => Sum.inl_injective (toLex.injective h),
    fun i => ?_, fun j hj => ?_⟩
  · change ((E.component i).strictTransform ⊤).comap (inv (⊤ : X.IdealSheafData).blowUpπ) =
      E.component i
    rw [strictTransform_top_left, ← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  · obtain ⟨a, rfl⟩ := toLex.surjective j
    rcases a with j₂ | u
    · exact (hj ⟨j₂, rfl⟩).elim
    · change (⊤ : X.IdealSheafData).exceptionalDivisor.comap (inv
        (⊤ : X.IdealSheafData).blowUpπ) = ⊤
      rw [exceptionalDivisor_top, Scheme.IdealSheafData.comap_top]

/-! ### Deleting the empty blow-ups; the surjective forms -/

/-- Deleting the empty blow-ups of a smooth blow-up sequence of order `m` gives a smooth blow-up
sequence of order `m` for the same triple ([Kol07, 32 and 34.1], read on the order predicate):
each deletion carries the tail back along the isomorphism of the empty blow-up (`eraseEmpty`), a
pullback along an isomorphism, under which the induced data and the order conditions are
transported (`IsOrderSeq.pullback` with `d = 0`; the induced ideal and family return to `I` and to
`E` extended by an empty component, `weakTransform_top_left`,
`extendsByEmpty_totalTransform_top_comap_inv`). -/
theorem IsOrderSeq.eraseEmpty [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {S : BlowUpSequence X}
    {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) :
    S.eraseEmpty.IsOrderSeq f I E m := by
  induction S with
  | nil X => exact hS
  | cons X D rest ih =>
    obtain ⟨⟨hD, hsnc, hm⟩, ht⟩ := (isOrderSeq_cons_iff f I E m D rest).1 hS
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    by_cases hD' : D = ⊤
    · subst hD'
      have hiso : IsIso (⊤ : X.IdealSheafData).blowUpπ := blowUp.isIso_π_top
      rw [BlowUpSequence.eraseEmpty, dite_eq_left rfl]
      have key := IsOrderSeq.pullback ((⊤ : X.IdealSheafData).blowUpπ ≫ f) n (inv
          (⊤ : X.IdealSheafData).blowUpπ) (d := 0)
        (ih ((⊤ : X.IdealSheafData).blowUpπ ≫ f) ht)
      rw [IsIso.inv_hom_id_assoc, weakTransform_top_left, ← Scheme.IdealSheafData.comap_comp,
        IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id] at key
      exact (extendsByEmpty_totalTransform_top_comap_inv E).isOrderSeq key
    · rw [BlowUpSequence.eraseEmpty, dite_eq_right hD', isOrderSeq_cons_iff]
      exact ⟨⟨hD, hsnc, hm⟩, ih (D.blowUpπ ≫ f) ht⟩

/-- The marked form of `IsOrderSeq.eraseEmpty` [Kol07, 32 and 34.1]. -/
theorem IsOrderGeSeq.eraseEmpty [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {S : BlowUpSequence X}
    {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X} (hS : S.IsOrderGeSeq f I m E) :
    S.eraseEmpty.IsOrderGeSeq f I m E := by
  induction S with
  | nil X => exact hS
  | cons X D rest ih =>
    obtain ⟨⟨hD, hsnc, hm⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 hS
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    by_cases hD' : D = ⊤
    · subst hD'
      have hiso : IsIso (⊤ : X.IdealSheafData).blowUpπ := blowUp.isIso_π_top
      rw [BlowUpSequence.eraseEmpty, dite_eq_left rfl]
      have key := IsOrderGeSeq.pullback ((⊤ : X.IdealSheafData).blowUpπ ≫ f) n (inv
          (⊤ : X.IdealSheafData).blowUpπ) (d := 0)
        (ih ((⊤ : X.IdealSheafData).blowUpπ ≫ f) ht)
      rw [IsIso.inv_hom_id_assoc, markedTransform_top_left, ← Scheme.IdealSheafData.comap_comp,
        IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id] at key
      exact (extendsByEmpty_totalTransform_top_comap_inv E).isOrderGeSeq key
    · rw [BlowUpSequence.eraseEmpty, dite_eq_right hD', isOrderGeSeq_cons_iff]
      exact ⟨⟨hD, hsnc, hm⟩, ih (D.blowUpπ ≫ f) ht⟩

/-- The surjective case of [Kol07, 34.1], where no deletion is needed. The surjectivity hypothesis
`_hs` is present because the first bullet of [Kol07, 34.1] is stated for smooth surjections, the
case in which the pull-back has no empty blow-up to delete; the proof does not need it, because
the pull-back along any smooth morphism is a smooth blow-up sequence of the same order
(`IsOrderSeq.pullback`), surjectivity mattering only for `h^* B` to determine `B` [Kol07, 30.1]. -/
theorem IsOrderSeq.pullback_of_surjective [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
    (_hs : Function.Surjective h) {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) :
    (S.pullback h).IsOrderSeq (h ≫ f) (I.comap h) (E.comap h) m :=
  IsOrderSeq.pullback f n h (d := d) hS

/-- The marked form of the surjective case of [Kol07, 34.1]. As for
`IsOrderSeq.pullback_of_surjective`, the surjectivity hypothesis `_hs` is present because the
first bullet of [Kol07, 34.1] is stated for smooth surjections; the proof does not need it
(`IsOrderGeSeq.pullback`). -/
theorem IsOrderGeSeq.pullback_of_surjective [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
    (_hs : Function.Surjective h) {S : BlowUpSequence X} {I : X.IdealSheafData} {m : ℕ}
    {E : DivisorFamily X} (hS : S.IsOrderGeSeq f I m E) :
    (S.pullback h).IsOrderGeSeq (h ≫ f) (I.comap h) m (E.comap h) :=
  IsOrderGeSeq.pullback f n h (d := d) hS


/-- For a smooth `h` with equidimensional source, the pullback with its empty blow-ups deleted is
a smooth blow-up sequence of order `m` for `(Y, h^* I, h^{-1} E)`; no relative dimension of `h` is
needed. -/
theorem isOrderSeq_eraseEmpty_pullback_of_equidim [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) [Smooth h] (n' : ℕ)
    [SmoothOfRelativeDimension n' (h ≫ f)] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) :
    (S.pullback h).eraseEmpty.IsOrderSeq (h ≫ f) (I.comap h) (E.comap h) m :=
  IsOrderSeq.eraseEmpty (h ≫ f) n' (IsOrderSeq.pullback_of_equidim f n h n' hS)

/-- The marked form of `isOrderSeq_eraseEmpty_pullback_of_equidim`. -/
theorem isOrderGeSeq_eraseEmpty_pullback_of_equidim [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) [Smooth h] (n' : ℕ)
    [SmoothOfRelativeDimension n' (h ≫ f)] {S : BlowUpSequence X} {I : X.IdealSheafData} {m : ℕ}
    {E : DivisorFamily X} (hS : S.IsOrderGeSeq f I m E) :
    (S.pullback h).eraseEmpty.IsOrderGeSeq (h ≫ f) (I.comap h) m (E.comap h) :=
  IsOrderGeSeq.eraseEmpty (h ≫ f) n' (IsOrderGeSeq.pullback_of_smooth f n h hS)

/-- The functoriality clause of [Kol07, 34.1] for a general smooth `h`: the sequence obtained from
the pull-back `h^* B(X, I, E)` "by deleting every blow-up `h^* π_i` whose center is empty" and
reindexing is a smooth blow-up sequence of order `m` for `(Y, h^* I, h^{-1} E)`. -/
theorem isOrderSeq_eraseEmpty_pullback [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
    {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}
    (hS : S.IsOrderSeq f I E m) :
    (S.pullback h).eraseEmpty.IsOrderSeq (h ≫ f) (I.comap h) (E.comap h) m := by
  have := SmoothOfRelativeDimension.smooth d h
  have := smoothOfRelativeDimension_comp d n h f
  exact isOrderSeq_eraseEmpty_pullback_of_equidim f n h (d + n) hS

/-- The marked form of `isOrderSeq_eraseEmpty_pullback` [Kol07, 34.1]. -/
theorem isOrderGeSeq_eraseEmpty_pullback [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
    {S : BlowUpSequence X} {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    (hS : S.IsOrderGeSeq f I m E) :
    (S.pullback h).eraseEmpty.IsOrderGeSeq (h ≫ f) (I.comap h) m (E.comap h) := by
  have := SmoothOfRelativeDimension.smooth d h
  have := smoothOfRelativeDimension_comp d n h f
  exact isOrderGeSeq_eraseEmpty_pullback_of_equidim f n h (d + n) hS

end Order

end AlgebraicGeometry

/-! ### The pulled-back triple -/

namespace Hironaka

open AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The pullback of a triple along a smooth morphism `h : Y ⟶ T.X.left`: the triple
`(Y, h^* I, h^{-1}(E))` of [Kol07, 34.1], for `Y` of finite type, quasi-compact, separated and
equidimensional over `k` as in [Kol07, Notation 64]. Its data are `Y`, `T.I.comap h`,
`T.E.comap h`; nonvanishing on the components is `isNonzeroEverywhere_comap_of_flat` and simple
normal crossings is `isSnc_comap_of_smooth`. -/
noncomputable def _root_.AlgebraicGeometry.Triple.pullback [PerfectField k] (T : Triple k)
    {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (hY : ∃ n : ℕ, SmoothOfRelativeDimension n (Y ↘ Spec (.of k)))
    (h : Y ⟶ T.X.left) [Smooth h] : Triple k where
  X := .ofHom (Y ↘ Spec (.of k))
    (by
      obtain ⟨n, hn⟩ := hY
      have := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of k))
      infer_instance)
    inferInstance
  smoothOfRelativeDimension := hY
  I := T.I.comap h
  isNonzeroEverywhere := isNonzeroEverywhere_comap_of_flat h T.isNonzeroEverywhere
  E := T.E.comap h
  isSnc := isSnc_comap_of_smooth (T.X.left ↘ Spec (.of k)) h T.isSnc

/-- The pullback of a marked triple along a smooth `h`, the mark unchanged [Kol07, 34.1]. -/
noncomputable def MarkedTriple.pullback [PerfectField k] (T : MarkedTriple k) {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (hY : ∃ n : ℕ, SmoothOfRelativeDimension n (Y ↘ Spec (.of k)))
    (h : Y ⟶ T.X.left) [Smooth h] : MarkedTriple k :=
  { T.toTriple.pullback hY h with m := T.m }

section Fields

variable [PerfectField k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (hY : ∃ n : ℕ, SmoothOfRelativeDimension n (Y ↘ Spec (.of k)))

/-- The ambient scheme of the pulled-back triple is `Y`. -/
theorem _root_.AlgebraicGeometry.Triple.pullback_X (T : Triple k) (h : Y ⟶ T.X.left) [Smooth h] :
    (T.pullback hY h).X.left = Y := rfl

/-- The ideal of the pulled-back triple is `h^* I`. -/
theorem _root_.AlgebraicGeometry.Triple.pullback_I (T : Triple k) (h : Y ⟶ T.X.left) [Smooth h] :
    HEq (T.pullback hY h).I (T.I.comap h) := HEq.rfl

/-- The divisor family of the pulled-back triple is `h^{-1} E`. -/
theorem _root_.AlgebraicGeometry.Triple.pullback_E (T : Triple k) (h : Y ⟶ T.X.left) [Smooth h] :
    HEq (T.pullback hY h).E (T.E.comap h) := HEq.rfl

/-- The mark of the pulled-back marked triple is the mark of `T`. -/
theorem MarkedTriple.pullback_m (T : MarkedTriple k) (h : Y ⟶ T.X.left)
    [Smooth h] : (T.pullback hY h).m = T.m := rfl

/-- The underlying triple of the pulled-back marked triple is the pulled-back triple. -/
theorem MarkedTriple.pullback_toTriple (T : MarkedTriple k) (h : Y ⟶ T.X.left)
    [Smooth h] :
    (T.pullback hY h).toTriple = T.toTriple.pullback hY h := rfl

end Fields

end Hironaka
