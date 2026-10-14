/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.PullbackRun
import Hironaka.Scheme.BlowUpSequence.Pullback
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The geometric Step 3 does not depend on the enumeration of the components

The input family `ofDivisorFamily E a e σ` of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Pieces.lean` enumerates the irreducible components
of the members of `E` by `σ : Fin k ≃ Components E`. Kollár's Step 3 ([Kol07, 111, Step 3]) does not
depend on that enumeration: its choices are made on faces compared by their label tuples and sums,
never by the numbering of the pieces. Two enumerations of the same components give the same input
family up to a permutation of the pieces, and the permutation is a refinement along the identity in
the sense of `Hironaka/Resolution/Algebraic/Monomial/Geometric/Refinement.lean`
(`refinesAlong_id_ofDivisorFamily`): the same label count, labels and exponents through the
relabelling `σ₁⁻¹ ∘ σ₂`, every piece inside (indeed equal to) its parent, every parent the union of
its unique child, and no two children of one parent. The functoriality of the geometric Step 3 under
smooth surjections (`realize_pullback_of_surjective` of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackRun.lean`) at `h = 𝟙 X` then identifies
the two runs (`realize_ofDivisorFamily_indep`; the pull-back along the identity is the sequence
itself). Also here: two exponent functions agreeing at the generic points of the members give the
same input family (`ofDivisorFamily_congr`: `ofDivisorFamily` reads its exponents there only). Not
in the sources. Used in `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Functorial.lean` to
show that the third step of `BMO_{n,m}` is well defined.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Scheme.IdealSheafData

namespace Hironaka.Monomial.PieceFamily

section Congr

variable {X : Scheme.{u}} {E : DivisorFamily X}

/-- Two exponent functions agreeing at the generic points of the members give the same input
family. -/
theorem ofDivisorFamily_congr_of_forall {L k' : ℕ} (a a' : X → ℕ) (e : E.ι ≃o Fin L)
    (σ : Fin k' ≃ Components E) (h : ∀ c : Components E, a (c.2 : X) = a' (c.2 : X)) :
    ofDivisorFamily E a e σ = ofDivisorFamily E a' e σ := by
  unfold ofDivisorFamily
  congr 1
  funext c
  split_ifs with hc
  · exact h _
  · rfl

/-- Two exponent functions agreeing at the generic points of the members give the same input
family: `ofDivisorFamily` reads its exponents there only. The structure morphism `f` is present
because the statements about the input family of a triple over `k` are all made over its structure
morphism; the proof does not need it, the equality being one of definitions on any scheme
(`ofDivisorFamily_congr_of_forall`). -/
theorem ofDivisorFamily_congr {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    {E : DivisorFamily X} {L k' : ℕ} (a a' : X → ℕ) (e : E.ι ≃o Fin L)
    (σ : Fin k' ≃ Components E) (h : ∀ c : Components E, a (c.2 : X) = a' (c.2 : X)) :
    ofDivisorFamily E a e σ = ofDivisorFamily E a' e σ := by
  have _ := f
  exact ofDivisorFamily_congr_of_forall a a' e σ h

end Congr

section Relabel

variable {X : Scheme.{u}} {E : DivisorFamily X} {k₁ k₂ : ℕ} (σ₁ : Fin k₁ ≃ Components E)
  (σ₂ : Fin k₂ ≃ Components E)

/-- The relabelling of the pieces between two enumerations of the components: the piece `c` of the
second enumeration is the piece `σ₁⁻¹ (σ₂ c)` of the first (and `0` off the range). -/
noncomputable def relabel (c : ℕ) : ℕ :=
  if h : c < k₂ then (σ₁.symm (σ₂ ⟨c, h⟩) : ℕ) else 0

theorem relabel_of_lt {c : ℕ} (hc : c < k₂) : relabel σ₁ σ₂ c = (σ₁.symm (σ₂ ⟨c, hc⟩) : ℕ) :=
  dite_eq_left hc

theorem relabel_lt {c : ℕ} (hc : c < k₂) : relabel σ₁ σ₂ c < k₁ := by
  rw [relabel_of_lt σ₁ σ₂ hc]
  exact (σ₁.symm _).isLt

theorem apply_relabel {c : ℕ} (hc : c < k₂) (h : relabel σ₁ σ₂ c < k₁) :
    σ₁ ⟨relabel σ₁ σ₂ c, h⟩ = σ₂ ⟨c, hc⟩ := by
  have : (⟨relabel σ₁ σ₂ c, h⟩ : Fin k₁) = σ₁.symm (σ₂ ⟨c, hc⟩) :=
    Fin.ext (relabel_of_lt σ₁ σ₂ hc)
  rw [this, Equiv.apply_symm_apply]

variable {L : ℕ} (a : X → ℕ) (e : E.ι ≃o Fin L)

theorem ofDivisorFamily_piece_of_lt' {k : ℕ} (σ : Fin k ≃ Components E) {c : ℕ} (hc : c < k) :
    (ofDivisorFamily E a e σ).piece c = Closeds.closure {((σ ⟨c, hc⟩).2 : X)} :=
  dite_eq_left hc

theorem ofDivisorFamily_label_of_lt' {k : ℕ} (σ : Fin k ≃ Components E) {c : ℕ} (hc : c < k) :
    (ofDivisorFamily E a e σ).label c = (e (σ ⟨c, hc⟩).1 : ℕ) :=
  dite_eq_left hc

theorem ofDivisorFamily_a_of_lt' {k : ℕ} (σ : Fin k ≃ Components E) {c : ℕ} (hc : c < k) :
    (ofDivisorFamily E a e σ).a c = a ((σ ⟨c, hc⟩).2 : X) :=
  dite_eq_left hc

/-- The piece of the relabelled index is the piece itself. -/
theorem piece_relabel {c : ℕ} (hc : c < k₂) :
    (ofDivisorFamily E a e σ₁).piece (relabel σ₁ σ₂ c) = (ofDivisorFamily E a e σ₂).piece c := by
  rw [ofDivisorFamily_piece_of_lt' a e σ₁ (relabel_lt σ₁ σ₂ hc),
    ofDivisorFamily_piece_of_lt' a e σ₂ hc, apply_relabel σ₁ σ₂ hc]

/-- The input family of one enumeration of the components refines the input family of another
along `𝟙 X` through the relabelling `σ₁⁻¹ ∘ σ₂`: the same label count, labels and exponents
through the relabelling, each piece equal to its parent, each parent the union of its unique
child, and no two children of one parent. -/
theorem refinesAlong_id_ofDivisorFamily :
    (ofDivisorFamily E a e σ₂).RefinesAlong (𝟙 X) (relabel σ₁ σ₂) (ofDivisorFamily E a e σ₁) where
  nextLabel_eq := rfl
  lt c hc := relabel_lt σ₁ σ₂ hc
  label_eq c hc := by
    rw [ofDivisorFamily_label_of_lt' a e σ₁ (relabel_lt σ₁ σ₂ hc),
      ofDivisorFamily_label_of_lt' a e σ₂ hc, apply_relabel σ₁ σ₂ hc]
  a_eq c hc := by
    rw [ofDivisorFamily_a_of_lt' a e σ₁ (relabel_lt σ₁ σ₂ hc),
      ofDivisorFamily_a_of_lt' a e σ₂ hc, apply_relabel σ₁ σ₂ hc]
  piece_le c hc := by
    rw [piece_relabel σ₁ σ₂ a e hc]
    intro x hx
    exact hx
  preimage_eq c hc := by
    classical
    have hc₀ : (σ₂.symm (σ₁ ⟨c, hc⟩) : ℕ) < k₂ := (σ₂.symm _).isLt
    have hfilter : ((Finset.range k₂).filter fun c' => relabel σ₁ σ₂ c' = c) =
        {(σ₂.symm (σ₁ ⟨c, hc⟩) : ℕ)} := by
      ext c'
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hc', hρ⟩
        have h1 : σ₁ ⟨c, hc⟩ = σ₂ ⟨c', hc'⟩ := by
          rw [← apply_relabel σ₁ σ₂ hc' (relabel_lt σ₁ σ₂ hc')]
          congr 1
          exact Fin.ext hρ.symm
        have h2 : σ₂.symm (σ₁ ⟨c, hc⟩) = ⟨c', hc'⟩ := by rw [h1, Equiv.symm_apply_apply]
        exact (congrArg Fin.val h2).symm
      · rintro rfl
        refine ⟨hc₀, ?_⟩
        rw [relabel_of_lt σ₁ σ₂ hc₀]
        have : σ₂ ⟨(σ₂.symm (σ₁ ⟨c, hc⟩) : ℕ), hc₀⟩ = σ₁ ⟨c, hc⟩ := by
          rw [Fin.eta, Equiv.apply_symm_apply]
        rw [this, Equiv.symm_apply_apply]
    change ((ofDivisorFamily E a e σ₁).piece c).preimage (𝟙 X : X ⟶ X).continuous =
      ((Finset.range k₂).filter fun c' => relabel σ₁ σ₂ c' = c).sup (ofDivisorFamily E a e σ₂).piece
    rw [hfilter, Finset.sup_singleton, ofDivisorFamily_piece_of_lt' a e σ₂ hc₀,
      ofDivisorFamily_piece_of_lt' a e σ₁ hc]
    have : σ₂ ⟨(σ₂.symm (σ₁ ⟨c, hc⟩) : ℕ), hc₀⟩ = σ₁ ⟨c, hc⟩ := by
      rw [Fin.eta, Equiv.apply_symm_apply]
    rw [this]
    exact SetLike.ext fun x => Iff.rfl
  disjoint c c' hc hc' hne hρ := by
    exfalso
    apply hne
    have h1 : σ₂ ⟨c, hc⟩ = σ₂ ⟨c', hc'⟩ := by
      rw [← apply_relabel σ₁ σ₂ hc (relabel_lt σ₁ σ₂ hc),
        ← apply_relabel σ₁ σ₂ hc' (relabel_lt σ₁ σ₂ hc')]
      congr 1
      exact Fin.ext hρ
    exact congrArg Fin.val (σ₂.injective h1)

end Relabel

section Indep

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [Smooth f] [QuasiCompact f] {E : DivisorFamily X} {n m : ℕ}

/-- *The geometric Step 3 does not depend on the enumeration of the components*: for two
enumerations of the components of `E` (the same label isomorphism) the realised runs coincide,
by `realize_pullback_of_surjective` at `h = 𝟙 X` with the identity refinement
`refinesAlong_id_ofDivisorFamily` and `pullback_id`. -/
theorem realize_ofDivisorFamily_indep (hE : E.IsSnc) (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f)
    {L k₁ k₂ : ℕ} (a : X → ℕ) (e : E.ι ≃o Fin L) (σ₁ : Fin k₁ ≃ Components E)
    (σ₂ : Fin k₂ ≃ Components E) (hV₁ : (ofDivisorFamily E a e σ₁).IsValid n m)
    (hV₂ : (ofDivisorFamily E a e σ₂).IsValid n m) :
    (ofDivisorFamily E a e σ₁).realize n m hV₁ = (ofDivisorFamily E a e σ₂).realize n m hV₂ := by
  have hρ := refinesAlong_id_ofDivisorFamily σ₁ σ₂ a e
  have hΦ : (ofDivisorFamily E a e σ₁).Realizes E e := ofDivisorFamily_realizes E a e σ₁ hE
  have hΦ₂ : (ofDivisorFamily E a e σ₂).Realizes E e := ofDivisorFamily_realizes E a e σ₂ hE
  have hΦ' : (ofDivisorFamily E a e σ₂).Realizes (E.comap (𝟙 X))
      (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) := by
    refine ⟨fun j => ?_, hΦ₂.disjoint⟩
    have hc : (E.comap (𝟙 X)).component j = E.component j := Scheme.IdealSheafData.comap_id _
    change ((E.comap (𝟙 X)).component j).support =
      ((Finset.range (ofDivisorFamily E a e σ₂).nextComp).filter
        fun c => (ofDivisorFamily E a e σ₂).label c = (e j : ℕ)).sup
          (ofDivisorFamily E a e σ₂).piece
    rw [hc]
    exact hΦ₂.support_eq j
  have hs : Function.Surjective (𝟙 X : X ⟶ X) := fun x => ⟨x, rfl⟩
  have hn' : ∃ n' ≤ n, SmoothOfRelativeDimension n' (𝟙 X ≫ f) := by
    rwa [Category.id_comp]
  have : QuasiCompact (𝟙 X ≫ f) := by
    rw [Category.id_comp]
    infer_instance
  have key := realize_pullback_of_surjective f hs hE hΦ hV₁ hn hn' hρ hΦ' hV₂
  rw [key, pullback_id]

end Indep

end Hironaka.Monomial.PieceFamily
