/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The input piece family, the face through a point, the centres of the fold

Three facts about the piece families of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Pieces.lean`, not in the sources:

* `ofDivisorFamily_realizes`: the family of the irreducible components of the members realises
  `E`, the input of [Kol07, 111, Step 3]. A closed set of a sober space is the union of the
  closures of its generic points, and two irreducible components of a member through a common
  point coincide because the member's stalk ideal is prime (the member is a regular subscheme,
  [Kol07, Definition 24] (1)): the reduced components through the point are minimal primes over
  it, hence equal (`Hironaka.Sequence.eq_of_specializes_of_isRegular` of
  `Hironaka/Resolution/Algebraic/Snc/DictionaryRegular.lean`).
* `faceAt_mem_nerve`: the set of pieces through a point of `E` is a face.
* `realizeAux_center`: the `i`-th centre of the fold is the centre of the `i`-th listed finset
  of faces, read on the stage-`i` family, by structural recursion on the list.

The first is what makes `step3Family` of
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Input.lean` a realising family; the third
is how the centres of the geometric Step 3 are read off.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme Scheme.IdealSheafData

namespace Hironaka.Monomial

variable {X : Scheme.{u}}

namespace PieceFamily

/-! ### The face through a point -/

section FaceAt

variable (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}

theorem faceAt_subset_range (x : X) : Φ.faceAt x ⊆ Finset.range Φ.nextComp :=
  fun _ hc => Finset.mem_range.mpr (Φ.mem_faceAt.mp hc).1

theorem mem_faceSet_faceAt (x : X) : x ∈ Φ.faceSet (Φ.faceAt x) :=
  Φ.mem_faceSet.mpr fun _ hc => (Φ.mem_faceAt.mp hc).2

/-- The set of pieces through a point of `E` is a face of the nerve: some piece passes through
the point (`Realizes.support_eq`). -/
theorem faceAt_mem_nerve (hΦ : Φ.Realizes E e) {x : X} (hx : x ∈ E.support) :
    Φ.faceAt x ∈ Φ.nerve := by
  classical
  obtain ⟨j, hj⟩ := (DivisorFamily.mem_support_iff_exists E x).mp hx
  rw [hΦ.support_eq, mem_finset_sup_iff] at hj
  obtain ⟨c, hc, hxc⟩ := hj
  have hcr := Finset.mem_range.mp (Finset.mem_filter.mp hc).1
  exact Φ.mem_nerve_of_mem_faceSet (Φ.faceAt_subset_range x) ⟨c, Φ.mem_faceAt.mpr ⟨hcr, hxc⟩⟩
    (Φ.mem_faceSet_faceAt x)

end FaceAt

/-! ### The input piece family realises `E` -/

section Input

variable (E : DivisorFamily X) {k L : ℕ} (a : X → ℕ) (e : E.ι ≃o Fin L) (σ : Fin k ≃ Components E)

/-- The input piece family of [Kol07, 111, Step 3], the irreducible components of the members
enumerated by `σ`, realises `E`: each member is the union of its irreducible components and two
irreducible components of a regular divisor are disjoint. -/
theorem ofDivisorFamily_realizes (hE : E.IsSnc) : (ofDivisorFamily E a e σ).Realizes E e where
  support_eq j := by
    classical
    apply le_antisymm
    · intro x hx
      obtain ⟨η, hη, hηx⟩ := Closeds.exists_mem_genericPoints_specializes _ hx
      obtain ⟨c, hc⟩ := σ.surjective ⟨j, ⟨η, hη⟩⟩
      have hc' : σ ⟨c.1, c.2⟩ = ⟨j, ⟨η, hη⟩⟩ := hc
      rw [mem_finset_sup_iff]
      refine ⟨c.1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr c.2, ?_⟩, ?_⟩
      · change (if h : c.1 < k then (e (σ ⟨c.1, h⟩).1 : ℕ) else 0) = (e j : ℕ)
        rw [dite_eq_left c.2, hc']
      · change x ∈ (if h : c.1 < k then Closeds.closure {((σ ⟨c.1, h⟩).2 : X)} else ⊥)
        rw [dite_eq_left c.2, hc']
        exact specializes_iff_mem_closure.mp hηx
    · rw [Finset.sup_le_iff]
      intro c hc
      obtain ⟨hcr, hlab⟩ := Finset.mem_filter.mp hc
      have hck : c < k := Finset.mem_range.mp hcr
      have hlab' : (if h : c < k then (e (σ ⟨c, h⟩).1 : ℕ) else 0) = (e j : ℕ) := hlab
      rw [dite_eq_left hck] at hlab'
      have hj : (σ ⟨c, hck⟩).1 = j := e.injective (Fin.ext hlab')
      change (if h : c < k then Closeds.closure {((σ ⟨c, h⟩).2 : X)} else ⊥) ≤ _
      rw [dite_eq_left hck]
      rcases hp : σ ⟨c, hck⟩ with ⟨jc, ηc⟩
      rw [hp] at hj
      change jc = j at hj
      subst hj
      exact Closeds.closure_le.mpr (Set.singleton_subset_iff.mpr ηc.2.1)
  disjoint c c' hc hc' hne hlab := by
    have hck : c < k := hc
    have hck' : c' < k := hc'
    have hlab' : (if h : c < k then (e (σ ⟨c, h⟩).1 : ℕ) else 0) =
        (if h : c' < k then (e (σ ⟨c', h⟩).1 : ℕ) else 0) := hlab
    rw [dite_eq_left hck, dite_eq_left hck'] at hlab'
    have hj : (σ ⟨c, hck⟩).1 = (σ ⟨c', hck'⟩).1 := e.injective (Fin.ext hlab')
    change Disjoint (if h : c < k then Closeds.closure {((σ ⟨c, h⟩).2 : X)} else ⊥)
      (if h : c' < k then Closeds.closure {((σ ⟨c', h⟩).2 : X)} else ⊥)
    rw [dite_eq_left hck, dite_eq_left hck', disjoint_iff_inf_le]
    intro x hx
    rw [← SetLike.mem_coe, Closeds.coe_inf] at hx
    obtain ⟨h1, h2⟩ := hx
    have hηx : ((σ ⟨c, hck⟩).2 : X) ⤳ x := specializes_iff_mem_closure.mpr h1
    have hη'x : ((σ ⟨c', hck'⟩).2 : X) ⤳ x := specializes_iff_mem_closure.mpr h2
    -- the two generic points of the common member coincide, so the components coincide
    exfalso
    apply hne
    have hgen : ∀ (p q : Components E), p.1 = q.1 → (p.2 : X) ⤳ x → (q.2 : X) ⤳ x → p = q := by
      rintro ⟨jp, ηp⟩ ⟨jq, ηq⟩ hpq hp hq
      simp only at hpq
      subst hpq
      have := Hironaka.Sequence.eq_of_specializes_of_isRegular _ (hE.1 jp) ηp.2 ηq.2 hp hq
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext this))
    have := σ.injective (hgen _ _ hj hηx hη'x)
    exact congrArg Fin.val this

end Input

/-! ### The centres of the fold -/

/-- The `i`-th centre of the fold is the centre of the `i`-th listed finset of faces, read on
the stage-`i` piece family. -/
theorem realizeAux_center (Φ : PieceFamily X) (m : ℕ) (L : List (Finset (Finset ℕ)))
    (i : Fin (realizeAux Φ m L).length) :
    (realizeAux Φ m L).center i =
      (stagePieces Φ m L i.castSucc).centerOf (L.get (Fin.cast (realizeAux_length Φ m L) i)) := by
  induction L generalizing X with
  | nil => exact i.elim0
  | cons S L ih =>
    rcases i with ⟨_ | j, h⟩
    · rfl
    · exact ih (Φ.blowUpPieces S m) ⟨j, Nat.lt_of_succ_lt_succ h⟩

end PieceFamily

end Hironaka.Monomial
