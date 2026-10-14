/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.BlowUp.Glue.Trivial
public import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.Smooth.BlowUpSmooth
import Hironaka.Scheme.Smooth.ExceptionalDivisor
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# Blow-up sequences: stages, composites, smoothness, and the deletion of empty blow-ups

A blow-up sequence on a scheme `X` in the sense of [Kol07, Definition 29] is a chain
`X_r → X_{r-1} → ⋯ → X_1 → X_0 = X` of blow-ups `π_i : X_{i+1} → X_i` with centers `Z_i ⊆ X_i`
and exceptional divisors `F_{i+1} ⊆ X_{i+1}`. In this library it is a term of the inductive
family `AlgebraicGeometry.Scheme.BlowUpSequence X`: `nil X`, and `cons X D rest` with
`rest : BlowUpSequence (D.blowUp)`. Everything Kollár attaches to a sequence is a recursive
function of that list of centers: the stages `X_i`, the centers `Z_i`, the composites `Π_i`, the
deletion of empty blow-ups, and the notions this module defines — the blow-up maps `π_i`
(`step`), the composites `Π_{ij} = π_j ∘ ⋯ ∘ π_{i-1}` (`stageMapBetween`), the exceptional
divisors `F_{i+1}` (`exceptionalAt`), the predicates "smooth" (`IsSmooth`,
`IsSmoothOfRelativeDimension`), "trivial" (`IsTrivialAt`) and "empty" (`IsEmptyAt`,
`NoEmptyCenters`), and the marked transforms `(I_i, m)` along the sequence (`markedTransformSeq`).
This module proves the basic identities about them.

**The recursion.** Every proof here is an induction on the sequence and, on the shape
`cons X D rest`, a case split on the index: index `0` speaks about the first blow-up, `X_0 = X`,
`Z_0 = D`, `π_0 = D.blowUpπ`, `F_1 = D.comap π_0`; index `j + 1` speaks about the tail `rest`,
a sequence on `D.blowUp`, to which the induction hypothesis applies with the structure morphism
`D.blowUpπ ≫ f` in place of `f`. Two features of the inductive definition drive the
bookkeeping. First, `S.stage 0` is `X` only after `S` is split into `nil` or `cons`
(`stage_zero`); so the equalities `Π_0 = 𝟙` and `Π_{i0} = Π_i` are proved on the constructor
shapes, and `π_0` on the `cons` shape carries the cast `eqToHom (stage_zero rest)`
(`step_cons_zero`). Second, the composite `Π_{i+1} = Π_i ∘ π_i` (`stageMap_succ`) and the cocycle
`Π_{jl} ∘ Π_{ij} = Π_{il}` (`stageMapBetween_comp`) are the associativity of composition threaded
through the recursion. The inductions are run with the indices in the form `⟨j, h⟩`, where the
recursive definitions unfold; the `Fin.succ`/`Fin.castSucc` forms of the statements are recovered
at the end by definitional unfolding.

**Smoothness** ([Kol07, Notation 19 and Definition 29]). A sequence is smooth when each center
`Z_i ⊆ X_i` is smooth over `k` (`IsSmooth`). In the equidimensional form
(`IsSmoothOfRelativeDimension`: `X` of pure relative dimension `n`, each `Z_i` of pure
codimension `r_i ≤ n`) the stages are smooth of relative dimension `n`, because the blow-up of a
smooth center of pure codimension is (`AlgebraicGeometry.smoothOfRelativeDimension_blowUpπ_comp`),
and the exceptional divisors are smooth of relative dimension `n − 1`, because the exceptional
divisor of such a blow-up is (`AlgebraicGeometry.smoothOfRelativeDimension_exceptional`), by
induction along the sequence.

**Trivial and empty blow-ups** ([Kol07, Warning 20 and 32]). A trivial blow-up has an invertible
center and its `π_i` is an isomorphism
(`AlgebraicGeometry.Scheme.IdealSheafData.blowUp.isIso_π_of_isInvertible`); the empty blow-up,
center `⊤`, is trivial with exceptional divisor `⊤.comap π_i = ⊤`, and under the isomorphism the
exceptional divisor of a trivial blow-up is the center (Warning 20 (2):
`comap_inv_step_exceptionalAt`). `eraseEmpty` deletes the empty blow-ups by carrying each tail back
along the inverse of its empty blow-up through `pullback`; pulling back along an isomorphism neither
creates nor removes empty centers (`noEmptyCenters_pullback_iff`, from the pullback square of
blow-up maps `AlgebraicGeometry.isPullback_blowUpMap` and `comap_eq_top_iff_of_isIso`), which gives
`noEmptyCenters_eraseEmpty`, `eraseEmpty_eq_self_iff`, idempotence, and the length count `r' + #{i :
Z_i = ∅} = r` (`length_eraseEmpty_add_card`).

`length_pullback` (pulling back does not change the length) is proved here because that count
needs it; the theory of the pullback is in `Hironaka/Scheme/BlowUpSequence/Pullback.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

noncomputable section

namespace AlgebraicGeometry.Scheme.BlowUpSequence

/-! ### The blow-up maps, predicates and marked transforms of a sequence -/

/-- The `i`-th monoidal transformation `π_i = π_{Z_i, X_i} : X_{i+1} ⟶ X_i` of the succession,
`0 ≤ i < r` [Kol07, Definition 29]: the projection `D_i.blowUpπ`, composed with the
identification `X_1 = D.blowUp` of the tail's zeroth stage (an `eqToHom`; the recursion `stage`
exposes `X_1 = D.blowUp` only once the tail's constructor is known). -/
def step : {X : Scheme.{u}} → (S : BlowUpSequence X) → (i : Fin S.length) →
    (S.stage i.succ ⟶ S.stage i.castSucc)
  | _, nil _, i => i.elim0
  | _, cons X D rest, ⟨0, _⟩ => eqToHom (by cases rest <;> rfl) ≫ D.blowUpπ
  | _, cons _ _ rest, ⟨j + 1, h⟩ => rest.step ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- `Π_{ij} := π_j ∘ ⋯ ∘ π_{i-1} : X_i ⟶ X_j` for `j ≤ i` [Kol07, Definition 29]; `Π_{i0} = Π_i` is
`stageMap`. -/
def stageMapBetween : {X : Scheme.{u}} → (S : BlowUpSequence X) → (i j : Fin (S.length + 1)) →
    j ≤ i → (S.stage i ⟶ S.stage j)
  | _, nil _, _, _, _ => 𝟙 _
  | _, cons X _ _, ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 X
  | _, cons _ _ _, ⟨0, _⟩, ⟨_ + 1, _⟩, h => (Nat.not_succ_le_zero _ h).elim
  | _, cons X D rest, ⟨i + 1, hi⟩, ⟨0, _⟩, _ =>
      rest.stageMap ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ
  | _, cons _ _ rest, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, h =>
      rest.stageMapBetween ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ⟨j, Nat.lt_of_succ_lt_succ hj⟩
        (Nat.le_of_succ_le_succ h)

/-- The exceptional divisor `F_{i+1} := π_i⁻¹(Z_i) ⊂ X_{i+1}` of the `i`-th monoidal transformation
[Kol07, Definition 29 and Notation 19], as the inverse image ideal sheaf of the centre. -/
def exceptionalAt {X : Scheme.{u}} (S : BlowUpSequence X) (i : Fin S.length) :
    (S.stage i.succ).IdealSheafData :=
  (S.center i).comap (S.step i)

/-- A **smooth** blow-up sequence over `f : X ⟶ Spec k` [Kol07, Definition 29 and Notation 19]: one
whose every centre `Z_i ⊂ X_i` is smooth over `k`, that is, every `π_i` is a smooth blow-up with its
specified centre (that the stages and the exceptional divisors are then smooth is a theorem, not
part of the definition). -/
def IsSmooth {k : Type u} [Field k] {X : Scheme.{u}} (S : BlowUpSequence X)
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∀ i : Fin S.length, Smooth ((S.center i).subschemeι ≫ S.stageMap i.castSucc ≫ f)

/-- The equidimensional form of `IsSmooth` [Kol07, Notation 64 (1)]: the ambient scheme is of pure
relative dimension `n` over `k`, and every centre is smooth of relative dimension `n − r_i` over `k`
for some `r_i ≤ n`. -/
def IsSmoothOfRelativeDimension {k : Type u} [Field k] {X : Scheme.{u}} (S : BlowUpSequence X)
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) : Prop :=
  ∀ i : Fin S.length, ∃ r ≤ n,
    SmoothOfRelativeDimension (n - r) ((S.center i).subschemeι ≫ S.stageMap i.castSucc ≫ f)

/-- The `i`-th blow-up is **trivial** [Kol07, Warning 20] if its centre is a Cartier divisor of its
stage (an invertible ideal sheaf); `π_i` is then an isomorphism. -/
def IsTrivialAt {X : Scheme.{u}} (S : BlowUpSequence X) (i : Fin S.length) : Prop :=
  (S.center i).IsInvertible

/-- The `i`-th blow-up is **empty** [Kol07, Warning 20] if its centre is empty, `Z_i = ⊤`. -/
def IsEmptyAt {X : Scheme.{u}} (S : BlowUpSequence X) (i : Fin S.length) : Prop :=
  S.center i = ⊤

/-- No centre is empty [Kol07, 32]. -/
def NoEmptyCenters {X : Scheme.{u}} (S : BlowUpSequence X) : Prop :=
  ∀ i, ¬ S.IsEmptyAt i

/-- The marked ideals `(I_i, m)` induced along the succession, `I_0 = I` and
`I_{i+1} = (π_i)_*^{-1}(I_i, m)` [Kol07, Warning 63, (63.1)]; [Kol07, Definition 66, (66.1′)].
This is a function of the succession — its list of centres — and not of the composite `Π` alone,
as Kollár's Warning 63 stresses. Defined for every succession; Kollár's order and normal-crossing
conditions at each stage are `BlowUpSequence.IsOrderGeSeq`
(`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean`).
-/
def markedTransformSeq : {X : Scheme.{u}} → (S : BlowUpSequence X) → X.IdealSheafData → ℕ →
    (i : Fin (S.length + 1)) → (S.stage i).IdealSheafData
  | _, nil _, J, _, _ => J
  | _, cons _ _ _, J, _, ⟨0, _⟩ => J
  | _, cons _ D rest, J, m, ⟨j + 1, h⟩ =>
    rest.markedTransformSeq (J.markedTransform D m) m ⟨j, Nat.lt_of_succ_lt_succ h⟩

end AlgebraicGeometry.Scheme.BlowUpSequence

end

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

attribute [local instance] IdealSheafData.blowUp.isIso_π_top

/-! ### The stages and composites of Definition 29 -/

/-- The first stage of a blow-up sequence is the scheme it starts with, `X_0 = X`
[Kol07, Definition 29]. -/
theorem stage_zero (S : BlowUpSequence X) : S.stage 0 = X := by
  cases S <;> rfl

/-- On the empty sequence every composite `Π_i` is the identity. -/
theorem stageMap_nil (i : Fin ((nil X).length + 1)) : (nil X).stageMap i = 𝟙 X := rfl

/-- `Π_0 = 𝟙 X` on the `cons` shape. -/
theorem stageMap_cons_zero (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).stageMap 0 = 𝟙 X := rfl

/-- `π_0` on the `cons` shape, with the cast `X_1 = D.blowUp` made explicit: the definition of
`step` splits on the tail's constructor, because `rest.stage 0` reduces to `D.blowUp` only
then. -/
theorem step_cons_zero (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).step ⟨0, Nat.succ_pos _⟩ = eqToHom (stage_zero rest) ≫ D.blowUpπ :=
  rfl

/-- `Π_{j+1} = Π_j ∘ π_j` in the `⟨j, h⟩` form of the indices, by induction. -/
theorem stageMap_mk_succ (S : BlowUpSequence X) (j : ℕ) (hj : j < S.length) :
    S.stageMap ⟨j + 1, Nat.succ_lt_succ hj⟩ =
      S.step ⟨j, hj⟩ ≫ S.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ := by
  induction S generalizing j with
  | nil _ => exact absurd hj (Nat.not_lt_zero _)
  | cons Y D rest ih =>
    cases j with
    | zero => cases rest <;> exact (Category.comp_id _).symm
    | succ j =>
      change rest.stageMap ⟨j + 1, hj⟩ ≫ D.blowUpπ =
        rest.step ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫
          rest.stageMap ⟨j, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt_succ hj)⟩ ≫ D.blowUpπ
      rw [← Category.assoc, ← ih j (Nat.lt_of_succ_lt_succ hj)]

/-- `Π_{i+1} = Π_i ∘ π_i` [Kol07, Definition 29]. -/
theorem stageMap_succ (S : BlowUpSequence X) (i : Fin S.length) :
    S.stageMap i.succ = S.step i ≫ S.stageMap i.castSucc := by
  obtain ⟨j, hj⟩ := i
  exact stageMap_mk_succ S j hj

/-- `Π_i = Π_{i0}` on the empty sequence [Kol07, Definition 29]. -/
theorem stageMapBetween_zero_nil (i : Fin ((nil X).length + 1)) :
    (nil X).stageMapBetween i 0 (Fin.zero_le i) = (nil X).stageMap i := rfl

/-- `Π_i = Π_{i0}` on the `cons` shape [Kol07, Definition 29]. -/
theorem stageMapBetween_zero_cons (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp)
    (i : Fin ((cons X D rest).length + 1)) :
    (cons X D rest).stageMapBetween i 0 (Fin.zero_le i) = (cons X D rest).stageMap i := by
  rcases i with ⟨_ | j, hi⟩ <;> rfl

/-- The empty composite `Π_{ii}` is the identity. -/
theorem stageMapBetween_self (S : BlowUpSequence X) (i : Fin (S.length + 1)) :
    S.stageMapBetween i i le_rfl = 𝟙 _ := by
  induction S with
  | nil _ => rfl
  | cons Y D rest ih =>
    rcases i with ⟨_ | j, hi⟩
    · rfl
    · exact ih ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- `Π_j ∘ Π_{ij} = Π_i`: the cocycle with the last index `0`, in the cast-free form. -/
theorem stageMapBetween_comp_stageMap (S : BlowUpSequence X) {i j : Fin (S.length + 1)}
    (hij : j ≤ i) : S.stageMapBetween i j hij ≫ S.stageMap j = S.stageMap i := by
  induction S with
  | nil _ => exact Category.id_comp _
  | cons Y D rest ih =>
    rcases i with ⟨_ | a, hi⟩ <;> rcases j with ⟨_ | b, hj⟩
    · exact Category.id_comp _
    · exact (Nat.not_succ_le_zero _ hij).elim
    · exact Category.comp_id _
    · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.blowUpπ)
        (ih (i := ⟨a, Nat.lt_of_succ_lt_succ hi⟩) (j := ⟨b, Nat.lt_of_succ_lt_succ hj⟩)
          (Nat.le_of_succ_le_succ hij)))

/-- The cocycle identity `Π_{jl} ∘ Π_{ij} = Π_{il}` for `l ≤ j ≤ i` [Kol07, Definition 29]. -/
theorem stageMapBetween_comp (S : BlowUpSequence X) {i j l : Fin (S.length + 1)} (hij : j ≤ i)
    (hjl : l ≤ j) :
    S.stageMapBetween i j hij ≫ S.stageMapBetween j l hjl =
      S.stageMapBetween i l (hjl.trans hij) := by
  induction S with
  | nil _ => exact Category.id_comp _
  | cons Y D rest ih =>
    rcases i with ⟨_ | a, hi⟩ <;> rcases j with ⟨_ | b, hj⟩ <;> rcases l with ⟨_ | c, hl⟩
    · exact Category.id_comp _
    · exact (Nat.not_succ_le_zero _ hjl).elim
    · exact (Nat.not_succ_le_zero _ hij).elim
    · exact (Nat.not_succ_le_zero _ hij).elim
    · exact Category.comp_id _
    · exact (Nat.not_succ_le_zero _ hjl).elim
    · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.blowUpπ)
        (stageMapBetween_comp_stageMap rest (i := ⟨a, Nat.lt_of_succ_lt_succ hi⟩)
          (j := ⟨b, Nat.lt_of_succ_lt_succ hj⟩) (Nat.le_of_succ_le_succ hij)))
    · exact ih (i := ⟨a, Nat.lt_of_succ_lt_succ hi⟩) (j := ⟨b, Nat.lt_of_succ_lt_succ hj⟩)
        (l := ⟨c, Nat.lt_of_succ_lt_succ hl⟩) (Nat.le_of_succ_le_succ hij)
        (Nat.le_of_succ_le_succ hjl)

/-- `Π_{j+1, j} = π_j` in the `⟨j, h⟩` form of the indices, by induction. -/
theorem stageMapBetween_mk_succ (S : BlowUpSequence X) (j : ℕ) (hj : j < S.length) :
    S.stageMapBetween ⟨j + 1, Nat.succ_lt_succ hj⟩ ⟨j, Nat.lt_succ_of_lt hj⟩ (Nat.le_succ j) =
      S.step ⟨j, hj⟩ := by
  induction S generalizing j with
  | nil _ => exact absurd hj (Nat.not_lt_zero _)
  | cons Y D rest ih =>
    cases j with
    | zero => cases rest <;> rfl
    | succ j => exact ih j (Nat.lt_of_succ_lt_succ hj)

/-- `Π_{i+1, i} = π_i` [Kol07, Definition 29]. -/
theorem stageMapBetween_succ_castSucc (S : BlowUpSequence X) (i : Fin S.length) :
    S.stageMapBetween i.succ i.castSucc Fin.castSucc_lt_succ.le = S.step i := by
  obtain ⟨j, hj⟩ := i
  exact stageMapBetween_mk_succ S j hj

/-- The points of the exceptional divisor `F_{i+1} = π_i⁻¹(Z_i)` are the points over the center
`Z_i` [Kol07, Notation 19]. -/
theorem mem_support_exceptionalAt_iff (S : BlowUpSequence X) (i : Fin S.length)
    (y : S.stage i.succ) :
    y ∈ (S.exceptionalAt i).support ↔ (S.step i).base y ∈ (S.center i).support := by
  change y ∈ ((S.center i).comap (S.step i)).support ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  exact Iff.rfl

/-! ### Smooth blow-up sequences -/

/-- The empty sequence is smooth. -/
theorem isSmooth_nil (f : X ⟶ Spec (.of k)) : (nil X).IsSmooth f := fun i => i.elim0

/-- The recursion of `IsSmooth` on the `cons` shape: the first center is smooth and the tail is a
smooth sequence on `D.blowUp`. -/
theorem isSmooth_cons_iff (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).IsSmooth f ↔ Smooth (D.subschemeι ≫ f) ∧ rest.IsSmooth (D.blowUpπ ≫ f) := by
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · have h0 := h (0 : Fin (rest.length + 1))
      change Smooth (D.subschemeι ≫ 𝟙 X ≫ f) at h0
      rwa [Category.id_comp] at h0
    · obtain ⟨j, hj⟩ := j
      have hs := h (Fin.succ ⟨j, hj⟩)
      change Smooth ((rest.center ⟨j, hj⟩).subschemeι ≫
        (rest.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ D.blowUpπ) ≫ f) at hs
      rwa [Category.assoc] at hs
  · rintro ⟨h0, hr⟩ i
    rcases i with ⟨_ | j, hi⟩
    · change Smooth (D.subschemeι ≫ 𝟙 X ≫ f)
      rwa [Category.id_comp]
    · have hs := hr ⟨j, Nat.lt_of_succ_lt_succ hi⟩
      change Smooth ((rest.center ⟨j, Nat.lt_of_succ_lt_succ hi⟩).subschemeι ≫
        (rest.stageMap ⟨j, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt_succ hi)⟩ ≫ D.blowUpπ) ≫ f)
      rwa [Category.assoc]

/-- The recursion of `IsSmoothOfRelativeDimension` on the `cons` shape. -/
theorem isSmoothOfRelativeDimension_cons_iff (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (n : ℕ) :
    (cons X D rest).IsSmoothOfRelativeDimension f n ↔
      (∃ r ≤ n, SmoothOfRelativeDimension (n - r) (D.subschemeι ≫ f)) ∧
        rest.IsSmoothOfRelativeDimension (D.blowUpπ ≫ f) n := by
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · obtain ⟨r, hr, hs⟩ := h (0 : Fin (rest.length + 1))
      refine ⟨r, hr, ?_⟩
      change SmoothOfRelativeDimension (n - r) (D.subschemeι ≫ 𝟙 X ≫ f) at hs
      rwa [Category.id_comp] at hs
    · obtain ⟨j, hj⟩ := j
      obtain ⟨r, hr, hs⟩ := h (Fin.succ ⟨j, hj⟩)
      refine ⟨r, hr, ?_⟩
      change SmoothOfRelativeDimension (n - r) ((rest.center ⟨j, hj⟩).subschemeι ≫
        (rest.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ D.blowUpπ) ≫ f) at hs
      rwa [Category.assoc] at hs
  · rintro ⟨⟨r, hr, hs⟩, ht⟩ i
    rcases i with ⟨_ | j, hi⟩
    · refine ⟨r, hr, ?_⟩
      change SmoothOfRelativeDimension (n - r) (D.subschemeι ≫ 𝟙 X ≫ f)
      rwa [Category.id_comp]
    · obtain ⟨r', hr', hs'⟩ := ht ⟨j, Nat.lt_of_succ_lt_succ hi⟩
      refine ⟨r', hr', ?_⟩
      change SmoothOfRelativeDimension (n - r')
        ((rest.center ⟨j, Nat.lt_of_succ_lt_succ hi⟩).subschemeι ≫
          (rest.stageMap ⟨j, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt_succ hi)⟩ ≫ D.blowUpπ) ≫ f)
      rwa [Category.assoc]

/-- The equidimensional form of smoothness implies that every center is smooth. -/
theorem Scheme.BlowUpSequence.IsSmoothOfRelativeDimension.isSmooth {S : BlowUpSequence X}
    {f : X ⟶ Spec (.of k)} {n : ℕ}
    (h : S.IsSmoothOfRelativeDimension f n) : S.IsSmooth f := fun i => by
  obtain ⟨r, -, hs⟩ := h i
  exact SmoothOfRelativeDimension.smooth (n - r) _

/-- Along a sequence that is smooth in the equidimensional sense, every stage `X_i` is smooth of
relative dimension `n` over the perfect field `k` [Kol07, Notation 19]: the blow-up of a smooth
center of pure codimension in a scheme smooth of relative dimension `n` is again smooth of
relative dimension `n`, and one inducts along the sequence. -/
theorem IsSmoothOfRelativeDimension.smoothOfRelativeDimension_stageMap [PerfectField k]
    {S : BlowUpSequence X} {f : X ⟶ Spec (.of k)} {n : ℕ} [SmoothOfRelativeDimension n f]
    (h : S.IsSmoothOfRelativeDimension f n) (i : Fin (S.length + 1)) :
    SmoothOfRelativeDimension n (S.stageMap i ≫ f) := by
  induction S with
  | nil Y =>
    change SmoothOfRelativeDimension n (𝟙 Y ≫ f)
    rw [Category.id_comp]
    infer_instance
  | cons Y D rest ih =>
    obtain ⟨⟨r, hr, hs⟩, ht⟩ := (isSmoothOfRelativeDimension_cons_iff f D rest n).1 h
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp f n r D hr
    rcases i with ⟨_ | j, hi⟩
    · change SmoothOfRelativeDimension n (𝟙 Y ≫ f)
      rw [Category.id_comp]
      infer_instance
    · change SmoothOfRelativeDimension n
        ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ) ≫ f)
      rw [Category.assoc]
      exact ih ht ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- Every stage `X_i` of a sequence smooth in the equidimensional sense is smooth over `k`
[Kol07, Notation 19]. -/
theorem IsSmoothOfRelativeDimension.smooth_stageMap [PerfectField k]
    {S : BlowUpSequence X} {f : X ⟶ Spec (.of k)} {n : ℕ} [SmoothOfRelativeDimension n f]
    (h : S.IsSmoothOfRelativeDimension f n) (i : Fin (S.length + 1)) :
    Smooth (S.stageMap i ≫ f) := by
  have := IsSmoothOfRelativeDimension.smoothOfRelativeDimension_stageMap h i
  exact SmoothOfRelativeDimension.smooth n _

/-- Every exceptional divisor `F_{i+1}` of a sequence smooth in the equidimensional sense is
smooth of relative dimension `n − 1` over `k` [Kol07, Notation 19]. -/
theorem IsSmoothOfRelativeDimension.smoothOfRelativeDimension_exceptionalAt [PerfectField k]
    {S : BlowUpSequence X} {f : X ⟶ Spec (.of k)} {n : ℕ} [SmoothOfRelativeDimension n f]
    (h : S.IsSmoothOfRelativeDimension f n) (i : Fin S.length) :
    SmoothOfRelativeDimension (n - 1)
      ((S.exceptionalAt i).subschemeι ≫ S.stageMap i.succ ≫ f) := by
  induction S with
  | nil _ => exact i.elim0
  | cons Y D rest ih =>
    obtain ⟨⟨r, hr, hs⟩, ht⟩ := (isSmoothOfRelativeDimension_cons_iff f D rest n).1 h
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp f n r D hr
    rcases i with ⟨_ | j, hi⟩
    · have key := smoothOfRelativeDimension_exceptional f n r D hr
      cases rest <;>
        (change SmoothOfRelativeDimension (n - 1)
          ((D.comap (𝟙 _ ≫ D.blowUpπ)).subschemeι ≫ (𝟙 _ ≫ D.blowUpπ) ≫ f)
         rw [Category.id_comp]
         exact key)
    · change SmoothOfRelativeDimension (n - 1)
        ((rest.exceptionalAt ⟨j, Nat.lt_of_succ_lt_succ hi⟩).subschemeι ≫
          (rest.stageMap (Fin.succ ⟨j, Nat.lt_of_succ_lt_succ hi⟩) ≫ D.blowUpπ) ≫ f)
      rw [Category.assoc]
      exact ih ht ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- Every exceptional divisor `F_{i+1}` of a sequence smooth in the equidimensional sense is
smooth over `k` [Kol07, Notation 19]. -/
theorem IsSmoothOfRelativeDimension.smooth_exceptionalAt [PerfectField k]
    {S : BlowUpSequence X} {f : X ⟶ Spec (.of k)} {n : ℕ} [SmoothOfRelativeDimension n f]
    (h : S.IsSmoothOfRelativeDimension f n) (i : Fin S.length) :
    Smooth ((S.exceptionalAt i).subschemeι ≫ S.stageMap i.succ ≫ f) := by
  have := IsSmoothOfRelativeDimension.smoothOfRelativeDimension_exceptionalAt h i
  exact SmoothOfRelativeDimension.smooth (n - 1) _

/-! ### Trivial and empty blow-ups -/

/-- The empty blow-up is trivial: the unit ideal sheaf is invertible [Kol07, Warning 20]. -/
theorem IsEmptyAt.isTrivialAt {S : BlowUpSequence X} {i : Fin S.length} (h : S.IsEmptyAt i) :
    S.IsTrivialAt i := by
  change (S.center i).IsInvertible
  rw [show S.center i = ⊤ from h]
  exact Scheme.IdealSheafData.isInvertible_top

/-- The blow-up map of a trivial blow-up is an isomorphism [Kol07, Warning 20]. -/
theorem IsTrivialAt.isIso_step {S : BlowUpSequence X} {i : Fin S.length} (h : S.IsTrivialAt i) :
    IsIso (S.step i) := by
  induction S with
  | nil _ => exact i.elim0
  | cons Y D rest ih =>
    rcases i with ⟨_ | j, hi⟩
    · have hπ : IsIso D.blowUpπ := IdealSheafData.blowUp.isIso_π_of_isInvertible D h
      cases rest <;> (change IsIso (𝟙 _ ≫ D.blowUpπ); rw [Category.id_comp]; exact hπ)
    · exact ih (i := ⟨j, Nat.lt_of_succ_lt_succ hi⟩) h

/-- The exceptional divisor of an empty blow-up is empty [Kol07, Warning 20]. -/
theorem IsEmptyAt.exceptionalAt_eq_top {S : BlowUpSequence X} {i : Fin S.length}
    (h : S.IsEmptyAt i) : S.exceptionalAt i = ⊤ := by
  change (S.center i).comap (S.step i) = ⊤
  rw [show S.center i = ⊤ from h]
  exact Scheme.IdealSheafData.comap_top _

/-- A center is the unit ideal sheaf iff its closed subscheme has no points: the two readings of
"`Z = ∅`" in [Kol07, Warning 20] agree. -/
theorem isEmptyAt_iff_support_eq_bot (S : BlowUpSequence X) (i : Fin S.length) :
    S.IsEmptyAt i ↔ (S.center i).support = ⊥ :=
  (Scheme.IdealSheafData.support_eq_bot_iff (S.center i)).symm

/-! ### The exceptional divisor of a trivial blow-up is its center -/

/-- When `π_i` is an isomorphism, the inverse image of `F_{i+1}` along `π_i⁻¹` is the center `Z_i`:
the exceptional divisor of a trivial blow-up is its center [Kol07, Warning 20 (2)]. -/
theorem comap_inv_step_exceptionalAt (S : BlowUpSequence X) (i : Fin S.length)
    [IsIso (S.step i)] : (S.exceptionalAt i).comap (inv (S.step i)) = S.center i := by
  change ((S.center i).comap (S.step i)).comap (inv (S.step i)) = _
  rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]

/-! ### Pullback along an isomorphism -/

/-- Pulling back a sequence does not change its length. -/
@[simp]
theorem length_pullback {X : Scheme.{u}} (S : BlowUpSequence X) {Y : Scheme.{u}} (h : Y ⟶ X) :
    (S.pullback h).length = S.length := by
  induction S generalizing Y with
  | nil _ => rfl
  | cons X D rest ih => exact congrArg (· + 1) (ih (Scheme.Hom.blowUpMap h D))

/-- The recursion of `NoEmptyCenters` on the `cons` shape. -/
@[simp]
theorem noEmptyCenters_cons_iff (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).NoEmptyCenters ↔ D ≠ ⊤ ∧ rest.NoEmptyCenters := by
  constructor
  · intro h
    refine ⟨h (0 : Fin (rest.length + 1)), fun j => ?_⟩
    obtain ⟨j, hj⟩ := j
    exact h (Fin.succ ⟨j, hj⟩)
  · rintro ⟨hD, hr⟩ i
    rcases i with ⟨_ | j, hi⟩
    · exact hD
    · exact hr ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- The inverse image of an ideal sheaf along an isomorphism is the unit ideal iff the ideal is. -/
theorem comap_eq_top_iff_of_isIso {Y : Scheme.{u}} (e : Y ⟶ X) [IsIso e] (D : X.IdealSheafData) :
    D.comap e = ⊤ ↔ D = ⊤ := by
  constructor
  · intro h
    have hD : (D.comap e).comap (inv e) = D := by
      rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
    rw [← hD, h, Scheme.IdealSheafData.comap_top]
  · rintro rfl
    exact Scheme.IdealSheafData.comap_top e

/-- Pulling a sequence back along an isomorphism neither creates nor removes empty centers: the
lifted maps are isomorphisms (the blow-up maps form a pullback square,
`AlgebraicGeometry.isPullback_blowUpMap`), and `comap` along an isomorphism preserves and reflects
`⊤`. -/
theorem noEmptyCenters_pullback_iff (S : BlowUpSequence X) {Y : Scheme.{u}} (e : Y ⟶ X) [IsIso e] :
    (S.pullback e).NoEmptyCenters ↔ S.NoEmptyCenters := by
  induction S generalizing Y with
  | nil _ => exact ⟨fun _ i => i.elim0, fun _ i => i.elim0⟩
  | cons X D rest ih =>
    have : IsIso (Scheme.Hom.blowUpMap e D) := (isPullback_blowUpMap e D).isIso_fst_of_isIso
    rw [show (cons X D rest).pullback e = cons Y (D.comap e)
        (rest.pullback (Scheme.Hom.blowUpMap e D))
      from rfl, noEmptyCenters_cons_iff, noEmptyCenters_cons_iff, ih (Scheme.Hom.blowUpMap e
          D), Ne, Ne,
      comap_eq_top_iff_of_isIso e D]

/-! ### Deleting the empty blow-ups -/

/-- Deleting the empty blow-ups of the empty sequence. -/
@[simp]
theorem eraseEmpty_nil : (nil X).eraseEmpty = nil X := rfl

/-- A nonempty first center is kept. -/
theorem eraseEmpty_cons_of_ne_top {D : X.IdealSheafData} (rest : BlowUpSequence D.blowUp)
    (h : D ≠ ⊤) : (cons X D rest).eraseEmpty = cons X D rest.eraseEmpty := by
  rw [eraseEmpty, dite_eq_right h]

/-- An empty first blow-up is deleted, its tail carried back to `X` along the inverse of the
isomorphism `blowUpπ X ⊤`. -/
theorem eraseEmpty_cons_top (rest : BlowUpSequence (⊤ : X.IdealSheafData).blowUp) :
    (cons X ⊤ rest).eraseEmpty = rest.eraseEmpty.pullback (inv (⊤ : X.IdealSheafData).blowUpπ) := by
  rw [eraseEmpty, dite_eq_left rfl]

/-- The result of `eraseEmpty` has no empty centers: the empty blow-up convention of [Kol07, 32]. -/
theorem noEmptyCenters_eraseEmpty (S : BlowUpSequence X) : S.eraseEmpty.NoEmptyCenters := by
  induction S with
  | nil _ => exact fun i => i.elim0
  | cons X D rest ih =>
    by_cases hD : D = ⊤
    · subst hD
      rw [eraseEmpty_cons_top]
      exact (noEmptyCenters_pullback_iff _ _).2 ih
    · rw [eraseEmpty_cons_of_ne_top rest hD, noEmptyCenters_cons_iff]
      exact ⟨hD, ih⟩

/-- Deleting the empty blow-ups changes nothing iff there are none. -/
theorem eraseEmpty_eq_self_iff (S : BlowUpSequence X) :
    S.eraseEmpty = S ↔ S.NoEmptyCenters := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := noEmptyCenters_eraseEmpty S
    rwa [h] at this
  · induction S with
    | nil _ => rfl
    | cons X D rest ih =>
      obtain ⟨hD, hr⟩ := (noEmptyCenters_cons_iff D rest).1 h
      rw [eraseEmpty_cons_of_ne_top rest hD, ih hr]

/-- Deleting the empty blow-ups is idempotent. -/
theorem eraseEmpty_eraseEmpty (S : BlowUpSequence X) :
    S.eraseEmpty.eraseEmpty = S.eraseEmpty :=
  (eraseEmpty_eq_self_iff _).2 (noEmptyCenters_eraseEmpty S)

open Classical in
/-- Counting a predicate on `Fin (n + 1)`: the value at `0` and the values on the successors. -/
theorem card_subtype_fin_succ {n : ℕ} (p : Fin (n + 1) → Prop) :
    Nat.card {i // p i} = (if p 0 then 1 else 0) + Nat.card {i : Fin n // p i.succ} := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype, Fin.card_filter_univ_succ']

/-- The length after deleting the empty blow-ups is the length minus the number of empty centers
(empty blow-ups "mess up the numbering", [Kol07, Warning 20]). -/
theorem length_eraseEmpty_add_card (S : BlowUpSequence X) :
    S.eraseEmpty.length + Nat.card {i : Fin S.length // S.IsEmptyAt i} = S.length := by
  classical
  induction S with
  | nil Y =>
    have : IsEmpty {i : Fin (nil Y).length // (nil Y).IsEmptyAt i} := ⟨fun ⟨i, _⟩ => i.elim0⟩
    rw [Nat.card_of_isEmpty]
    rfl
  | cons Y D rest ih =>
    have hc : Nat.card {i // (cons Y D rest).IsEmptyAt i} =
        (if D = ⊤ then 1 else 0) + Nat.card {i : Fin rest.length // rest.IsEmptyAt i} :=
      card_subtype_fin_succ fun i : Fin (rest.length + 1) => (cons Y D rest).IsEmptyAt i
    rw [hc]
    by_cases hD : D = ⊤
    · subst hD
      rw [eraseEmpty_cons_top, length_pullback, ite_eq_left rfl]
      change rest.eraseEmpty.length + (1 + Nat.card {i : Fin rest.length // rest.IsEmptyAt i}) =
        rest.length + 1
      omega
    · rw [eraseEmpty_cons_of_ne_top rest hD, ite_eq_right hD]
      change rest.eraseEmpty.length + 1 +
        (0 + Nat.card {i : Fin rest.length // rest.IsEmptyAt i}) = rest.length + 1
      omega

/-- Deleting the empty blow-ups does not increase the length. -/
theorem length_eraseEmpty_le (S : BlowUpSequence X) : S.eraseEmpty.length ≤ S.length := by
  have := length_eraseEmpty_add_card S
  omega

/-! ### A sequence is more than its end result -/

/-- Sequences with different first centers differ: a sequence carries its centers, not only its
maps [Kol07, Remark 33 and Warning 20 (1)]. -/
theorem ne_of_center_zero_ne {D D' : X.IdealSheafData} {r : BlowUpSequence D.blowUp}
    {r' : BlowUpSequence D'.blowUp} (h : D ≠ D') : cons X D r ≠ cons X D' r' :=
  fun e => h (BlowUpSequence.cons.inj e).1

/-! ### The composite along an equality of sequences -/

section M20

variable {X : Scheme.{u}}

/-- The composite along an equality of sequences: the `eqToHom` between the last stages is
absorbed. -/
theorem eqToHom_comp_composite_of_eq {S S' : BlowUpSequence X} (e : S = S') :
    eqToHom (congrArg BlowUpSequence.last e) ≫ S'.composite = S.composite := by
  subst e
  rw [eqToHom_refl, Category.id_comp]

end M20

end AlgebraicGeometry
