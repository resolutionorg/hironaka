/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Basic
public import Hironaka.Manifold.FiniteSuccession.Cons
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Pieces
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The piece family after the blow-up of a centre

After blowing up the locus `Z` of a centre `S` of the state, the old pieces go to their strict
transforms with their labels and exponents unchanged, and each face `P ∈ S` gives one new piece,
`π⁻¹(locus of P)`, with the new label (the exceptional divisor is appended last, [Kol07, Definition
65]) and the exponent `total P − m` ([Kol07, Definition 60]; in [Kol07, 111, Step 3] the new divisor
gets the coefficient `a_{j₁} + ⋯ + a_{j_r} − m`). This file defines that transition,
`PieceFamily.blowUpPieces`. Its labels and exponents are those of the combinatorial transition
`Hironaka.Monomial.MonomialState.blowUp`, so that as soon as the nerve of the transition is the
combinatorial one (`BMO/Step3Monomial/Kernel.lean`) the state of the transition is the combinatorial
blow-up of the state (`toState_blowUpPieces_of_nerve_eq`). The label embedding into the members of
the transformed boundary family is extended by the exceptional member, placed last (`extendEmb`).
-/

@[expose] public section

open Set Topology Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The label embedding extended by the exceptional member -/

/-- The label embedding of a family extended by the exceptional member, placed last: the labels
`< L` go to the old members, the new label `L` to the exceptional member `inr ()`, the top of the
lexicographic sum ([Kol07, Definition 65]: the exceptional divisor is added as the last divisor). -/
noncomputable def extendEmb {ι : Type u} [LinearOrder ι] {L : ℕ} (e : Fin L ↪o ι) :
    Fin (L + 1) ↪o (ι ⊕ₗ PUnit.{u + 1}) :=
  OrderEmbedding.ofStrictMono
    (fun i => if h : i.1 < L then toLex (Sum.inl (e ⟨i.1, h⟩)) else toLex (Sum.inr PUnit.unit))
    (by
      intro i j hij
      have hij' : i.1 < j.1 := hij
      dsimp only
      by_cases hi : i.1 < L
      · by_cases hj : j.1 < L
        · rw [dite_eq_left hi, dite_eq_left hj]
          exact Sum.Lex.inl_lt_inl_iff.mpr (e.strictMono (Fin.mk_lt_mk.mpr hij'))
        · rw [dite_eq_left hi, dite_eq_right hj]
          exact Sum.Lex.inl_lt_inr _ _
      · exfalso
        have := j.2
        omega)

theorem extendEmb_apply_of_lt {ι : Type u} [LinearOrder ι] {L : ℕ} (e : Fin L ↪o ι)
    {i : Fin (L + 1)} (h : i.1 < L) : extendEmb e i = toLex (Sum.inl (e ⟨i.1, h⟩)) := by
  change (if h' : i.1 < L then toLex (Sum.inl (e ⟨i.1, h'⟩)) else toLex (Sum.inr PUnit.unit)) = _
  rw [dite_eq_left h]

theorem extendEmb_castSucc {ι : Type u} [LinearOrder ι] {L : ℕ} (e : Fin L ↪o ι) (i : Fin L) :
    extendEmb e i.castSucc = toLex (Sum.inl (e i)) := by
  rw [extendEmb_apply_of_lt e (i := i.castSucc) i.2]
  rfl

theorem extendEmb_last {ι : Type u} [LinearOrder ι] {L : ℕ} (e : Fin L ↪o ι) :
    extendEmb e (Fin.last L) = toLex (Sum.inr PUnit.unit) := by
  change (if h : (Fin.last L).1 < L then toLex (Sum.inl (e ⟨(Fin.last L).1, h⟩))
    else toLex (Sum.inr PUnit.unit)) = _
  have h : ¬ ((Fin.last L).1 < L) := lt_irrefl L
  rw [dite_eq_right h]

namespace PieceFamily

open _root_.Manifold

variable {N : AnalyticManifold.{u} 𝕜 E} (Φ : PieceFamily N)

/-! ### The transition -/

/-- The piece family after blowing up the locus of the centre `S`: old pieces go to their strict
transforms with labels and exponents kept; each face `P ∈ S` gives one new piece, the preimage of
its locus, at the index `newComp S P`, with the new label `nextLabel` and the exponent `total P − m`
([Kol07, 111, Step 3], [Kol07, Definition 60]). The labels and exponents are those of the
combinatorial transition `Hironaka.Monomial.MonomialState.blowUp`. -/
noncomputable def blowUpPieces (S : Finset (Finset ℕ)) (m : ℕ) {r : ℕ}
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r) : PieceFamily (Manifold.blowUp ψ₀ hZ) where
  nextComp := Φ.nextComp + S.card
  nextLabel := Φ.nextLabel + 1
  piece c :=
    if c < Φ.nextComp then strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S) (Φ.piece c)
    else ⋃ P ∈ S.filter (fun P => Φ.newComp S P = c), (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.faceSet P
  label c := if c < Φ.nextComp then Φ.label c else Φ.nextLabel
  a c :=
    if c < Φ.nextComp then Φ.a c
    else (S.filter fun P => Φ.newComp S P = c).sup fun P => Φ.total P - m
  label_lt c _ := by
    by_cases h : c < Φ.nextComp
    · simp only [ite_eq_left h]
      exact (Φ.label_lt c h).trans (Nat.lt_succ_self _)
    · simp only [ite_eq_right h]
      exact Nat.lt_succ_self _
  isClosed_piece c := by
    by_cases h : c < Φ.nextComp
    · simp only [ite_eq_left h]
      exact isClosed_closure
    · simp only [ite_eq_right h]
      exact isClosed_biUnion_finset fun P _ =>
        (Φ.isClosed_faceSet P).preimage (isBlowUp_blowUpπ ψ₀ hZ).contMDiff.continuous

variable (S : Finset (Finset ℕ)) (m : ℕ) {r : ℕ} (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r)

@[simp] theorem blowUpPieces_nextComp : (Φ.blowUpPieces S m hZ).nextComp = Φ.nextComp + S.card :=
  rfl

@[simp] theorem blowUpPieces_nextLabel : (Φ.blowUpPieces S m hZ).nextLabel = Φ.nextLabel + 1 :=
  rfl

theorem blowUpPieces_piece_of_lt {c : ℕ} (hc : c < Φ.nextComp) :
    (Φ.blowUpPieces S m hZ).piece c =
      strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S) (Φ.piece c) :=
  ite_eq_left hc

theorem blowUpPieces_label_of_lt {c : ℕ} (hc : c < Φ.nextComp) :
    (Φ.blowUpPieces S m hZ).label c = Φ.label c :=
  ite_eq_left hc

theorem blowUpPieces_a_of_lt {c : ℕ} (hc : c < Φ.nextComp) :
    (Φ.blowUpPieces S m hZ).a c = Φ.a c :=
  ite_eq_left hc

theorem blowUpPieces_label_of_le {c : ℕ} (hc : Φ.nextComp ≤ c) :
    (Φ.blowUpPieces S m hZ).label c = Φ.nextLabel :=
  ite_eq_right (not_lt.mpr hc)

/-- The faces of `S` allocated to the index `newComp S P` are exactly `P`. -/
theorem filter_newComp_eq {P : Finset ℕ} (hP : P ∈ S) :
    (S.filter fun Q => Φ.newComp S Q = Φ.newComp S P) = {P} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨Finset.mem_filter.mpr ⟨hP, rfl⟩, fun Q hQ => ?_⟩
  obtain ⟨hQS, hQ⟩ := Finset.mem_filter.mp hQ
  exact MonomialState.rank_injOn S hQS hP (Nat.add_left_cancel hQ)

/-- The new piece of a face carries the new label. -/
theorem blowUpPieces_label_newComp (P : Finset ℕ) :
    (Φ.blowUpPieces S m hZ).label (Φ.newComp S P) = Φ.nextLabel :=
  Φ.blowUpPieces_label_of_le S m hZ (Nat.le_add_right _ _)

/-- The new piece of the face `P ∈ S` is the preimage of its locus. -/
theorem blowUpPieces_piece_newComp {P : Finset ℕ} (hP : P ∈ S) :
    (Φ.blowUpPieces S m hZ).piece (Φ.newComp S P) = (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.faceSet P := by
  change (if Φ.newComp S P < Φ.nextComp then _ else
    ⋃ Q ∈ S.filter (fun Q => Φ.newComp S Q = Φ.newComp S P), (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.faceSet
        Q) = _
  have hnl : ¬ Φ.newComp S P < Φ.nextComp := not_lt.mpr (Nat.le_add_right _ _)
  rw [ite_eq_right hnl, Φ.filter_newComp_eq S hP, Finset.set_biUnion_singleton]

/-- The new piece of the face `P ∈ S` carries the exponent `total P − m` [Kol07, Definition 60]. -/
theorem blowUpPieces_a_newComp {P : Finset ℕ} (hP : P ∈ S) :
    (Φ.blowUpPieces S m hZ).a (Φ.newComp S P) = Φ.total P - m := by
  change (if Φ.newComp S P < Φ.nextComp then _ else
    (S.filter fun Q => Φ.newComp S Q = Φ.newComp S P).sup fun Q => Φ.total Q - m) = _
  have hnl : ¬ Φ.newComp S P < Φ.nextComp := not_lt.mpr (Nat.le_add_right _ _)
  rw [ite_eq_right hnl, Φ.filter_newComp_eq S hP, Finset.sup_singleton]

/-! ### The seam with the imported engine -/

/-- The state of the transition is the combinatorial blow-up of the state as soon as the nerves
agree: every other data field is definitionally the combinatorial one. The nerve equality is proved
in `BMO/Step3Monomial/Kernel.lean`. -/
theorem toState_blowUpPieces_of_nerve_eq {n' : ℕ} (hV : Φ.IsValid n' m)
    (hV' : (Φ.blowUpPieces S m hZ).IsValid n' m)
    (h : (Φ.blowUpPieces S m hZ).nerve = ((Φ.toState n' m hV).blowUp S).nerve) :
    (Φ.blowUpPieces S m hZ).toState n' m hV' = (Φ.toState n' m hV).blowUp S :=
  MonomialState.ext rfl rfl rfl rfl rfl rfl h

end PieceFamily

end Hironaka.Manifold.BMO
