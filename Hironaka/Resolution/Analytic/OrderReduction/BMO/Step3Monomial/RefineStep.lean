/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.RefinesAlong
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.BlowUpPieces
public import Hironaka.Resolution.Analytic.MaximalContact.Theorem97Induction
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.OrderReduction.BDCosupp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A refinement persists across the blow-up of a centre

The run of the monomial procedure on a piece family `Ψ` refining a piece family `Φ` along a local
analytic isomorphism `ρ` is compared with the run on `Φ` one step at a time
(`BMO/Step3Monomial/RealizePullback.lean`). This file proves the step in which `Φ` blows up a centre
`S` some of whose faces have preimages: `Ψ` blows up the faces mapping into `S` (`preimageFaces`),
and the two transformed families again refine one another along any local analytic isomorphism `ℓ`
between the two blow-ups lying over `ρ` (`RefinesAlong.blowUpPieces`). The parent map is extended so
that the new piece of a face `Q` of `Ψ` goes to the new piece of its image `Q.image p`
(`extendParent`), and the label map sends the new label to the new label (`extendLabel`). The strict
transforms of the old pieces correspond because the square commutes; the new pieces of `Ψ` over a
face `P` of `S` are the preimages of the loci of the faces of `Ψ` over `P`, whose union is the
preimage of the locus of `P` (`preimage_faceSet`); and two faces of `Ψ` over one face of `Φ` with a
common point coincide (`eq_of_image_eq_of_mem`), so the new children are disjoint. The other case of
the step, a centre none of whose faces has a preimage, is `RefinesAlong.of_empty_step` in
`BMO/Step3Monomial/RealizePullback.lean`.

The bookkeeping of the new pieces uses the rank of a face in the centre
(`Hironaka.Monomial.MonomialState.rank`): every index in `[nextComp, nextComp + |S|)` is the new
piece of exactly one face. Two general facts on strict transforms, of a finite union and of disjoint
closed sets, sit here beside their use.
-/

@[expose] public section

open Set Topology TopologicalSpace Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace PieceFamily

variable {N : AnalyticManifold.{u} 𝕜 E} (Φ : PieceFamily N)

/-! ### Bookkeeping of the new pieces -/

/-- Every index in `[nextComp, nextComp + |S|)` is the new piece of exactly one face of `S`: the
rank is a bijection of `S` onto `range |S|`. -/
theorem exists_newComp_eq (S : Finset (Finset ℕ)) {c : ℕ} (h1 : Φ.nextComp ≤ c)
    (h2 : c < Φ.nextComp + S.card) : ∃ P ∈ S, Φ.newComp S P = c := by
  classical
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := S) (t := Finset.range S.card)
    (fun P _ => MonomialState.rank S P)
    (fun P hP => Finset.mem_range.mpr (MonomialState.rank_lt_card hP))
    (fun P₁ P₂ hP₁ hP₂ h => MonomialState.rank_injOn S hP₁ hP₂ h)
    (by rw [Finset.card_range])
  obtain ⟨P, hP, hrk⟩ := hsurj (c - Φ.nextComp) (Finset.mem_range.mpr (by omega))
  refine ⟨P, hP, ?_⟩
  unfold PieceFamily.newComp
  omega

/-- The new piece of a face of `S` has index below `nextComp + |S|`. -/
theorem newComp_lt' (S : Finset (Finset ℕ)) {P : Finset ℕ} (hP : P ∈ S) :
    Φ.newComp S P < Φ.nextComp + S.card :=
  Nat.add_lt_add_left (MonomialState.rank_lt_card hP) _

/-- The new piece of a face has index at least `nextComp`. -/
theorem nextComp_le_newComp' (S : Finset (Finset ℕ)) (P : Finset ℕ) :
    Φ.nextComp ≤ Φ.newComp S P :=
  Nat.le_add_right _ _

/-- Distinct faces of `S` get distinct new pieces. -/
theorem newComp_injOn' (S : Finset (Finset ℕ)) {P Q : Finset ℕ} (hP : P ∈ S) (hQ : Q ∈ S)
    (h : Φ.newComp S P = Φ.newComp S Q) : P = Q :=
  MonomialState.rank_injOn S hP hQ (Nat.add_left_cancel h)

end PieceFamily

/-! ### General facts on strict transforms -/

section StrictGeneral

variable {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] {π : B → A} (Z : Set A)

omit [TopologicalSpace A] in
/-- The strict transform of a finite union is the union of the strict transforms. -/
theorem strictTransformSet_biUnion_finset {ι : Type*} (s : Finset ι) (H : ι → Set A) :
    strictTransformSet π Z (⋃ i ∈ s, H i) = ⋃ i ∈ s, strictTransformSet π Z (H i) := by
  classical
  unfold strictTransformSet
  refine le_antisymm ?_ ?_
  · refine closure_minimal ?_ (isClosed_biUnion_finset fun i _ => isClosed_closure)
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_preimage.mp hq
    obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.mp hq1
    exact Set.mem_iUnion₂.mpr ⟨i, hi, subset_closure ⟨hqi, hq2⟩⟩
  · refine Set.iUnion₂_subset fun i hi => closure_mono ?_
    intro q hq
    exact ⟨Set.mem_iUnion₂.mpr ⟨i, hi, hq.1⟩, hq.2⟩

/-- Strict transforms of disjoint closed sets are disjoint. -/
theorem strictTransformSet_disjoint (hπ : Continuous π) {H₁ H₂ : Set A} (h₁ : IsClosed H₁)
    (h₂ : IsClosed H₂) (hd : Disjoint H₁ H₂) :
    Disjoint (strictTransformSet π Z H₁) (strictTransformSet π Z H₂) := by
  refine Set.disjoint_left.mpr fun q hq₁ hq₂ => ?_
  have hp₁ := strictTransform_subset_preimage (Y := Z) hπ h₁ hq₁
  have hp₂ := strictTransform_subset_preimage (Y := Z) hπ h₂ hq₂
  exact Set.disjoint_left.mp hd hp₁ hp₂

end StrictGeneral

namespace PieceFamily

variable {X Y : AnalyticManifold.{u} 𝕜 E} {Ψ : PieceFamily X} {Φ : PieceFamily Y}
  {ρ : AnalyticMap X Y} {p σ : ℕ → ℕ}

/-- The parent map extended to the new pieces: the new piece of a face `Q` of `Ψ` goes to the new
piece of its image `Q.image p`. -/
noncomputable def extendParent (Ψ : PieceFamily X) (Φ : PieceFamily Y) (p : ℕ → ℕ)
    (S' S : Finset (Finset ℕ)) (c : ℕ) : ℕ :=
  if c < Ψ.nextComp then p c
  else (S'.filter fun Q => Ψ.newComp S' Q = c).sup fun Q => Φ.newComp S (Q.image p)

/-- The label map extended by the new label: the new label of `Ψ` goes to the new label of `Φ`. -/
def extendLabel (Ψ : PieceFamily X) (Φ : PieceFamily Y) (σ : ℕ → ℕ) (ℓ : ℕ) : ℕ :=
  if ℓ < Ψ.nextLabel then σ ℓ else Φ.nextLabel

/-- The faces of `Ψ` mapping into the centre `S` of `Φ`. -/
noncomputable def preimageFaces (Ψ : PieceFamily X) (p : ℕ → ℕ) (S : Finset (Finset ℕ)) :
    Finset (Finset ℕ) := by
  classical exact Ψ.nerve.filter fun Q => Q.image p ∈ S

theorem mem_preimageFaces {S : Finset (Finset ℕ)} {Q : Finset ℕ} :
    Q ∈ Ψ.preimageFaces p S ↔ Q ∈ Ψ.nerve ∧ Q.image p ∈ S := by
  classical
  unfold preimageFaces
  exact Finset.mem_filter

theorem extendParent_of_lt (S' S : Finset (Finset ℕ)) {c : ℕ} (hc : c < Ψ.nextComp) :
    Ψ.extendParent Φ p S' S c = p c := by
  unfold extendParent
  rw [ite_eq_left hc]

theorem extendParent_newComp (S' S : Finset (Finset ℕ)) {Q : Finset ℕ} (hQ : Q ∈ S') :
    Ψ.extendParent Φ p S' S (Ψ.newComp S' Q) = Φ.newComp S (Q.image p) := by
  classical
  unfold extendParent
  rw [ite_eq_right (not_lt.mpr (Ψ.nextComp_le_newComp' S' Q)), Ψ.filter_newComp_eq S' hQ,
    Finset.sup_singleton]

theorem extendLabel_of_lt {ℓ : ℕ} (hℓ : ℓ < Ψ.nextLabel) : Ψ.extendLabel Φ σ ℓ = σ ℓ := by
  unfold extendLabel
  rw [ite_eq_left hℓ]

theorem extendLabel_nextLabel : Ψ.extendLabel Φ σ Ψ.nextLabel = Φ.nextLabel := by
  unfold extendLabel
  rw [ite_eq_right (lt_irrefl _)]

/-- Transporting an analytic map along an equality of its domain keeps surjectivity. -/
theorem _root_.Hironaka.Manifold.AnalyticMap.surjective_castDom
    {U U' N : AnalyticManifold.{u} 𝕜 E} (e : U = U') {f : AnalyticMap U' N}
    (hf : Function.Surjective f) :
    Function.Surjective (AnalyticMap.castDom e f) := by
  subst e
  exact hf

namespace RefinesAlong

open _root_.Manifold

variable (h : Ψ.RefinesAlong ρ p σ Φ)
include h

/-- The image of a face of `Ψ` under the parent map has the exponent sum of the face. -/
theorem total_image {Q : Finset ℕ} (hQ : Q ∈ Ψ.nerve) : Φ.total (Q.image p) = Ψ.total Q := by
  unfold PieceFamily.total
  rw [Finset.sum_image (h.image_mem_nerve hQ).2]
  exact Finset.sum_congr rfl fun c hc => h.a_eq c (Ψ.lt_nextComp_of_mem_nerve hQ hc)

/-- The preimage of the locus of a face is the union of the loci of the faces mapping onto it. -/
theorem preimage_faceSet {P : Finset ℕ} (hP : P ∈ Φ.nerve) :
    ⇑ρ ⁻¹' Φ.faceSet P = ⋃ Q ∈ Ψ.nerve.filter (fun Q => Q.image p = P), Ψ.faceSet Q := by
  classical
  ext x
  rw [Set.mem_preimage]
  constructor
  · intro hx
    obtain ⟨Q, hQ, hQP, hxQ⟩ := h.exists_lift hP hx
    exact Set.mem_iUnion₂.mpr ⟨Q, Finset.mem_filter.mpr ⟨hQ, hQP⟩, hxQ⟩
  · intro hx
    obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hQn, rfl⟩ := Finset.mem_filter.mp hQ
    refine Φ.mem_faceSet.mpr fun c' hc' => ?_
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    exact h.piece_subset c (Ψ.lt_nextComp_of_mem_nerve hQn hc) (Ψ.mem_faceSet.mp hxQ c hc)

/-- Two faces of `Ψ` with the same image and a common point coincide. -/
theorem eq_of_image_eq_of_mem {Q₁ Q₂ : Finset ℕ} (hQ₁ : Q₁ ∈ Ψ.nerve) (hQ₂ : Q₂ ∈ Ψ.nerve)
    (hQ : Q₁.image p = Q₂.image p) {x : X} (hx₁ : x ∈ Ψ.faceSet Q₁) (hx₂ : x ∈ Ψ.faceSet Q₂) :
    Q₁ = Q₂ := by
  have key : ∀ {Q₁ Q₂ : Finset ℕ}, Q₁ ∈ Ψ.nerve → Q₂ ∈ Ψ.nerve → Q₁.image p ⊆ Q₂.image p →
      x ∈ Ψ.faceSet Q₁ → x ∈ Ψ.faceSet Q₂ → Q₁ ⊆ Q₂ := by
    intro Q₁ Q₂ hQ₁ hQ₂ hQ hx₁ hx₂ c hc
    obtain ⟨c₂, hc₂, hpc⟩ := Finset.mem_image.mp (hQ (Finset.mem_image_of_mem p hc))
    by_contra hne
    have hne' : c₂ ≠ c := fun e => hne (e ▸ hc₂)
    exact Set.disjoint_left.mp
      (h.disjoint c₂ c (Ψ.lt_nextComp_of_mem_nerve hQ₂ hc₂) (Ψ.lt_nextComp_of_mem_nerve hQ₁ hc) hne'
        hpc)
      (Ψ.mem_faceSet.mp hx₂ c₂ hc₂) (Ψ.mem_faceSet.mp hx₁ c hc)
  exact Finset.Subset.antisymm (key hQ₁ hQ₂ hQ.le hx₁ hx₂) (key hQ₂ hQ₁ hQ.ge hx₂ hx₁)

/-- The lift of `ρ` to the blow-ups of the preimage centre, transported to the centre of `Ψ` by the
set equality of `preimage_centerOf`, is a local analytic isomorphism lying over `ρ`, surjective when
`ρ` is. -/
theorem exists_lift_over (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ) (S : Finset (Finset ℕ))
    (hS : ∀ P ∈ S, P ∈ Φ.nerve) {r : ℕ} (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r)
    (hZ' : IsClosedSubmanifold ψ₀ (Ψ.centerOf (Ψ.preimageFaces p S)) r) :
    ∃ ℓ : AnalyticMap (Manifold.blowUp ψ₀ hZ') (Manifold.blowUp ψ₀ hZ), IsLocalDiffeomorph 𝓘(𝕜,
        E) 𝓘(𝕜, E) ω ℓ ∧
      (∀ q, Manifold.blowUpπ ψ₀ hZ (ℓ q) = ρ (Manifold.blowUpπ ψ₀ hZ' q)) ∧
      (Function.Surjective ρ → Function.Surjective ℓ) := by
  have hZeq : Ψ.centerOf (Ψ.preimageFaces p S) = ⇑ρ ⁻¹' Φ.centerOf S :=
    (h.preimage_centerOf S hS).symm
  refine ⟨AnalyticMap.castDom
      (AnalyticManifold.BlowUpSequence.blowUp_congr hZeq hZ' (hZ.preimage_of_isLocalDiffeomorph hρ))
      (AnalyticManifold.BlowUpSequence.liftStep ρ hρ hZ),
    AnalyticMap.isLocalDiffeomorph_castDom _
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep ρ hρ hZ),
    fun q => AnalyticManifold.BlowUpSequence.blowUpπ_castDom_liftStep ρ hρ hZ hZ' hZeq q, fun hs =>
        ?_⟩
  exact AnalyticMap.surjective_castDom _ (AnalyticManifold.BlowUpSequence.surjective_liftStep ρ hρ
      hZ hs)

/-- The step of the comparison in which `Φ` blows up a centre `S` and `Ψ` blows up the faces mapping
into `S`: the transformed families refine one another along any local analytic isomorphism `ℓ` of
the blow-ups lying over `ρ`, with the extended parent and label maps. -/
theorem blowUpPieces (S : Finset (Finset ℕ))
    (hS : ∀ P ∈ S, P ∈ Φ.nerve) (m : ℕ) {r : ℕ} (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r)
    (hZ' : IsClosedSubmanifold ψ₀ (Ψ.centerOf (Ψ.preimageFaces p S)) r)
    (ℓ : AnalyticMap (Manifold.blowUp ψ₀ hZ') (Manifold.blowUp ψ₀ hZ))
        (hℓ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ℓ)
    (hsq : ∀ q, Manifold.blowUpπ ψ₀ hZ (ℓ q) = ρ (Manifold.blowUpπ ψ₀ hZ' q)) :
    (Ψ.blowUpPieces (Ψ.preimageFaces p S) m hZ').RefinesAlong ℓ
      (Ψ.extendParent Φ p (Ψ.preimageFaces p S) S) (Ψ.extendLabel Φ σ) (Φ.blowUpPieces S m hZ) := by
  classical
  set S' := Ψ.preimageFaces p S with hS'def
  have hS'S : ∀ Q ∈ S', Q.image p ∈ S := fun Q hQ => (mem_preimageFaces.mp hQ).2
  have hS'n : ∀ Q ∈ S', Q ∈ Ψ.nerve := fun Q hQ => (mem_preimageFaces.mp hQ).1
  have hZeq : Ψ.centerOf S' = ⇑ρ ⁻¹' Φ.centerOf S := (h.preimage_centerOf S hS).symm
  -- the square, as `strictTransformSet_preimage_of_square` wants it
  have hsq' : ∀ H : Set Y, ⇑ℓ ⁻¹' strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S) H =
      strictTransformSet (Manifold.blowUpπ ψ₀ hZ') (Ψ.centerOf S') (⇑ρ ⁻¹' H) := fun H =>
    strictTransformSet_preimage_of_square ρ hZ hZ' hZeq ℓ hℓ hsq H
  have hsq'' : ∀ A : Set Y, ⇑ℓ ⁻¹' (⇑(Manifold.blowUpπ ψ₀ hZ) ⁻¹' A) = ⇑(Manifold.blowUpπ ψ₀ hZ')
      ⁻¹' (⇑ρ ⁻¹' A) := by
    intro A; ext q; simp only [Set.mem_preimage, hsq]
  -- every component of the transitions is old or the new component of a face
  have hcases : ∀ c, c < (Ψ.blowUpPieces S' m hZ').nextComp →
      c < Ψ.nextComp ∨ ∃ Q ∈ S', Ψ.newComp S' Q = c := by
    intro c hc
    rw [Ψ.blowUpPieces_nextComp] at hc
    rcases lt_or_ge c Ψ.nextComp with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (Ψ.exists_newComp_eq S' hge hc)
  have hcasesΦ : ∀ c, c < (Φ.blowUpPieces S m hZ).nextComp →
      c < Φ.nextComp ∨ ∃ P ∈ S, Φ.newComp S P = c := by
    intro c hc
    rw [Φ.blowUpPieces_nextComp] at hc
    rcases lt_or_ge c Φ.nextComp with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (Φ.exists_newComp_eq S hge hc)
  refine
    { p_lt := ?_, σ_lt := ?_, σ_strictMonoOn := ?_, label_eq := ?_, a_eq := ?_,
      piece_subset := ?_, preimage_eq := ?_, disjoint := ?_ }
  · -- p_lt
    intro c hc
    rw [Φ.blowUpPieces_nextComp]
    rcases hcases c hc with hlt | ⟨Q, hQ, rfl⟩
    · rw [Ψ.extendParent_of_lt S' S hlt]
      exact (h.p_lt c hlt).trans_le (Nat.le_add_right _ _)
    · rw [Ψ.extendParent_newComp S' S hQ]
      exact Φ.newComp_lt' S (hS'S Q hQ)
  · -- σ_lt
    intro l hl
    rw [Ψ.blowUpPieces_nextLabel] at hl
    rw [Φ.blowUpPieces_nextLabel]
    rcases lt_or_ge l Ψ.nextLabel with hlt | hge
    · rw [Ψ.extendLabel_of_lt hlt]; exact (h.σ_lt l hlt).trans (Nat.lt_succ_self _)
    · have : l = Ψ.nextLabel := by omega
      subst this
      rw [Ψ.extendLabel_nextLabel]; exact Nat.lt_succ_self _
  · -- σ_strictMonoOn
    intro l₁ hl₁ l₂ hl₂ hlt
    rw [Ψ.blowUpPieces_nextLabel] at hl₁ hl₂
    have hl₁' : l₁ < Ψ.nextLabel := by
      have := Set.mem_Iio.mp hl₁; have := Set.mem_Iio.mp hl₂; omega
    rw [Ψ.extendLabel_of_lt hl₁']
    rcases lt_or_ge l₂ Ψ.nextLabel with h2 | h2
    · rw [Ψ.extendLabel_of_lt h2]
      exact h.σ_strictMonoOn (Set.mem_Iio.mpr hl₁') (Set.mem_Iio.mpr h2) hlt
    · have : l₂ = Ψ.nextLabel := by have := Set.mem_Iio.mp hl₂; omega
      subst this
      rw [Ψ.extendLabel_nextLabel]
      exact h.σ_lt l₁ hl₁'
  · -- label_eq
    intro c hc
    rcases hcases c hc with hlt | ⟨Q, hQ, rfl⟩
    · rw [Ψ.extendParent_of_lt S' S hlt, Φ.blowUpPieces_label_of_lt S m hZ (h.p_lt c hlt),
        Ψ.blowUpPieces_label_of_lt S' m hZ' hlt, h.label_eq c hlt,
        Ψ.extendLabel_of_lt (Ψ.label_lt c hlt)]
    · rw [Ψ.extendParent_newComp S' S hQ,
        Φ.blowUpPieces_label_of_le S m hZ (Φ.nextComp_le_newComp' S _),
        Ψ.blowUpPieces_label_of_le S' m hZ' (Ψ.nextComp_le_newComp' S' _), Ψ.extendLabel_nextLabel]
  · -- a_eq
    intro c hc
    rcases hcases c hc with hlt | ⟨Q, hQ, rfl⟩
    · rw [Ψ.extendParent_of_lt S' S hlt, Φ.blowUpPieces_a_of_lt S m hZ (h.p_lt c hlt),
        Ψ.blowUpPieces_a_of_lt S' m hZ' hlt, h.a_eq c hlt]
    · rw [Ψ.extendParent_newComp S' S hQ, Φ.blowUpPieces_a_newComp S m hZ (hS'S Q hQ),
        Ψ.blowUpPieces_a_newComp S' m hZ' hQ, h.total_image (hS'n Q hQ)]
  · -- piece_subset
    intro c hc
    rcases hcases c hc with hlt | ⟨Q, hQ, rfl⟩
    · rw [Ψ.extendParent_of_lt S' S hlt, Φ.blowUpPieces_piece_of_lt S m hZ (h.p_lt c hlt),
        Ψ.blowUpPieces_piece_of_lt S' m hZ' hlt, hsq']
      exact strictTransformSet_mono _ _ (h.piece_subset c hlt)
    · rw [Ψ.extendParent_newComp S' S hQ, Φ.blowUpPieces_piece_newComp S m hZ (hS'S Q hQ),
        Ψ.blowUpPieces_piece_newComp S' m hZ' hQ, hsq'']
      refine Set.preimage_mono fun x hx => ?_
      refine Φ.mem_faceSet.mpr fun c' hc' => ?_
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
      exact h.piece_subset c (Ψ.lt_nextComp_of_mem_nerve (hS'n Q hQ) hc) (Ψ.mem_faceSet.mp hx c hc)
  · -- preimage_eq
    intro c hc
    rcases hcasesΦ c hc with hlt | ⟨P, hP, rfl⟩
    · -- an old parent: strict transforms of the children
      rw [Φ.blowUpPieces_piece_of_lt S m hZ hlt, hsq', h.preimage_eq c hlt,
        strictTransformSet_biUnion_finset]
      ext q
      simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨c', ⟨hc'lt, hpc'⟩, hq⟩
        refine ⟨c', ⟨?_, ?_⟩, ?_⟩
        · rw [Ψ.blowUpPieces_nextComp]; omega
        · rw [Ψ.extendParent_of_lt S' S hc'lt]; exact hpc'
        · rw [Ψ.blowUpPieces_piece_of_lt S' m hZ' hc'lt]; exact hq
      · rintro ⟨c', ⟨hc'lt, hpc'⟩, hq⟩
        rcases hcases c' hc'lt with hlt' | ⟨Q, hQ, rfl⟩
        · refine ⟨c', ⟨hlt', ?_⟩, ?_⟩
          · rw [Ψ.extendParent_of_lt S' S hlt'] at hpc'; exact hpc'
          · rw [Ψ.blowUpPieces_piece_of_lt S' m hZ' hlt'] at hq; exact hq
        · exfalso
          rw [Ψ.extendParent_newComp S' S hQ] at hpc'
          have := Φ.nextComp_le_newComp' S (Q.image p)
          omega
    · -- a new parent: the loci of the faces over it
      rw [Φ.blowUpPieces_piece_newComp S m hZ hP, hsq'', h.preimage_faceSet (hS P hP)]
      ext q
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨Q, ⟨hQn, hQP⟩, hq⟩
        have hQS' : Q ∈ S' := mem_preimageFaces.mpr ⟨hQn, hQP ▸ hP⟩
        refine ⟨Ψ.newComp S' Q, ⟨?_, ?_⟩, ?_⟩
        · rw [Ψ.blowUpPieces_nextComp]; exact Ψ.newComp_lt' S' hQS'
        · rw [Ψ.extendParent_newComp S' S hQS', hQP]
        · rw [Ψ.blowUpPieces_piece_newComp S' m hZ' hQS']; exact hq
      · rintro ⟨c', ⟨hc'lt, hpc'⟩, hq⟩
        rcases hcases c' hc'lt with hlt' | ⟨Q, hQ, rfl⟩
        · exfalso
          rw [Ψ.extendParent_of_lt S' S hlt'] at hpc'
          have := h.p_lt c' hlt'
          have := Φ.nextComp_le_newComp' S P
          omega
        · rw [Ψ.extendParent_newComp S' S hQ] at hpc'
          have hQP : Q.image p = P := Φ.newComp_injOn' S (hS'S Q hQ) hP hpc'
          refine ⟨Q, ⟨hS'n Q hQ, hQP⟩, ?_⟩
          rw [Ψ.blowUpPieces_piece_newComp S' m hZ' hQ] at hq; exact hq
  · -- disjoint
    intro c₁ c₂ hc₁ hc₂ hne hpe
    rcases hcases c₁ hc₁ with hlt₁ | ⟨Q₁, hQ₁, rfl⟩ <;>
      rcases hcases c₂ hc₂ with hlt₂ | ⟨Q₂, hQ₂, rfl⟩
    · rw [Ψ.blowUpPieces_piece_of_lt S' m hZ' hlt₁, Ψ.blowUpPieces_piece_of_lt S' m hZ' hlt₂]
      rw [Ψ.extendParent_of_lt S' S hlt₁, Ψ.extendParent_of_lt S' S hlt₂] at hpe
      exact strictTransformSet_disjoint _ (Manifold.blowUpπ ψ₀ hZ').contMDiff.continuous
        (Ψ.isClosed_piece c₁) (Ψ.isClosed_piece c₂) (h.disjoint c₁ c₂ hlt₁ hlt₂ hne hpe)
    · exfalso
      rw [Ψ.extendParent_of_lt S' S hlt₁, Ψ.extendParent_newComp S' S hQ₂] at hpe
      have := h.p_lt c₁ hlt₁; have := Φ.nextComp_le_newComp' S (Q₂.image p); omega
    · exfalso
      rw [Ψ.extendParent_newComp S' S hQ₁, Ψ.extendParent_of_lt S' S hlt₂] at hpe
      have := h.p_lt c₂ hlt₂; have := Φ.nextComp_le_newComp' S (Q₁.image p); omega
    · rw [Ψ.blowUpPieces_piece_newComp S' m hZ' hQ₁, Ψ.blowUpPieces_piece_newComp S' m hZ' hQ₂]
      rw [Ψ.extendParent_newComp S' S hQ₁, Ψ.extendParent_newComp S' S hQ₂] at hpe
      have hQimg : Q₁.image p = Q₂.image p := Φ.newComp_injOn' S (hS'S Q₁ hQ₁) (hS'S Q₂ hQ₂) hpe
      refine Set.disjoint_left.mpr fun q hq₁ hq₂ => hne ?_
      have hQ : Q₁ = Q₂ :=
        h.eq_of_image_eq_of_mem (hS'n Q₁ hQ₁) (hS'n Q₂ hQ₂) hQimg hq₁ hq₂
      rw [hQ]

end RefinesAlong

end PieceFamily

end Hironaka.Manifold.BMO
