/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Restrict
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Exponent
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Snc.ComponentStalks
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The refinement of a piece family along a smooth morphism

For a smooth `h : Y ⟶ X` and a piece family `Φ` realising an snc boundary `E` on `X`, the
irreducible components of the preimages `h⁻¹(D_c)` of the pieces form a piece family of `Y`
*refining `Φ` along `h`* (`RefinesAlong` of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Pieces.lean`): each child lies in the preimage of
its parent, the preimage of a piece is the disjoint union of its children, and labels and exponents
pass through the parent map. This is the geometric side of the functoriality of Step 3 under smooth
morphisms, [Kol07, 34.1] for the third step of `BMO_{n,m}`, which Kollár dismisses with "the
functoriality conditions are just as obvious as before" at the end of [Kol07, 111]. Not in the
sources as statements. This module proves the combinatorial and local facts:

* `exists_refinesAlong`: such a family exists, `ofDivisorFamily` on `h⁻¹E` with the exponent
  `Φ.exponentAt ∘ h`. The parent of a component is the unique piece through the image of its
  generic point, which is a generic point of the parent member since a flat morphism is
  generalising (`mem_genericPoints_support_of_flat` of
  `Hironaka/Scheme/BlowUpSequence/PullbackInduced.lean`).
* `refines_toState`, `refines_toState_of_surjective`: the state of a refining family is
  `Refines` (`Hironaka/Resolution/Algebraic/Monomial/Restrict.lean`) the state of `X` restricted to
  the faces with a point over `Y` (the full state when `h` is surjective). Faces map to faces (a
  common point maps to a common point), the parent map is injective on a face (children of one
  parent are disjoint), and a face with a point over `Y` lifts (one child of each parent through
  that point).
* `sub_restrictState`, `mem_nerve_restrictState`: the restricted state is `Sub` the state, with
  the nerve `{T : Z_T ∩ im h ≠ ∅}` (definitional).
* `monomial_comap_exponentAt`: the marked monomial ideal of the refining family is the pull-back
  of the marked monomial ideal. Stalk by stalk, the components of `h⁻¹E^i` through `y` map to the
  components of `E^i` through `h y` with the same exponent (`stalkIdeal_monomial` of
  `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Split.lean` on both sides, and `Ideal.map` of
  the finite product).

The runs are compared in `Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackRun.lean` and
`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackErase.lean`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal Scheme
  Scheme.IdealSheafData

namespace Hironaka.Monomial.PieceFamily

variable {X Y : Scheme.{u}}

/-! ### The label-free part of `RefinesAlong` -/

/-- *The label-free part of `RefinesAlong`*: the parent map, the exponents and the pieces without
the two label clauses. It is the invariant of the general fold (`realizeAux_pullback_eraseEmpty`
of `Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackErase.lean`): across an empty blow-up
of `X` (a centre missing the image of `h`) the family on `X` gains a label the family on `Y` does
not, so `nextLabel_eq` fails while everything geometric survives; the labels are then carried by the
member transport `hlab`. -/
structure RefinesAlongW (Φ' : PieceFamily Y) (h : Y ⟶ X) (ρ : ℕ → ℕ) (Φ : PieceFamily X) :
    Prop where
  lt : ∀ c, c < Φ'.nextComp → ρ c < Φ.nextComp
  a_eq : ∀ c, c < Φ'.nextComp → Φ.a (ρ c) = Φ'.a c
  piece_le : ∀ c, c < Φ'.nextComp → Φ'.piece c ≤ (Φ.piece (ρ c)).preimage h.continuous
  preimage_eq : ∀ c, c < Φ.nextComp → (Φ.piece c).preimage h.continuous =
    ((Finset.range Φ'.nextComp).filter fun c' => ρ c' = c).sup Φ'.piece
  disjoint : ∀ c c', c < Φ'.nextComp → c' < Φ'.nextComp → c ≠ c' → ρ c = ρ c' →
    Disjoint (Φ'.piece c) (Φ'.piece c')

/-- `RefinesAlong` forgets to its label-free part. -/
theorem RefinesAlong.toW {Φ : PieceFamily X} {h : Y ⟶ X} {ρ : ℕ → ℕ} {Φ' : PieceFamily Y}
    (hρ : Φ'.RefinesAlong h ρ Φ) : Φ'.RefinesAlongW h ρ Φ :=
  ⟨hρ.lt, hρ.a_eq, hρ.piece_le, hρ.preimage_eq, hρ.disjoint⟩

/-! ### Consequences of `RefinesAlongW` -/

namespace RefinesAlongW

variable {Φ : PieceFamily X} {h : Y ⟶ X} {ρ : ℕ → ℕ} {Φ' : PieceFamily Y}
  (hρ : Φ'.RefinesAlongW h ρ Φ)
include hρ

/-- A point of a child lies over a point of its parent. -/
theorem mem_piece_of_mem {c' : ℕ} (hc' : c' < Φ'.nextComp) {y : Y} (hy : y ∈ Φ'.piece c') :
    h y ∈ Φ.piece (ρ c') :=
  hρ.piece_le c' hc' hy

/-- A point over a piece lies on one of its children. -/
theorem exists_child {c : ℕ} (hc : c < Φ.nextComp) {y : Y} (hy : h y ∈ Φ.piece c) :
    ∃ c', c' < Φ'.nextComp ∧ ρ c' = c ∧ y ∈ Φ'.piece c' := by
  classical
  have hmem : y ∈ (Φ.piece c).preimage h.continuous := hy
  rw [hρ.preimage_eq c hc, mem_finset_sup_iff] at hmem
  obtain ⟨c', hc', hy'⟩ := hmem
  obtain ⟨hcr, hρc⟩ := Finset.mem_filter.mp hc'
  exact ⟨c', Finset.mem_range.mp hcr, hρc, hy'⟩

/-- The parent map is injective on a set of children with a common point (children of one parent
are disjoint). -/
theorem injOn_of_mem_faceSet {T : Finset ℕ} (hT : T ⊆ Finset.range Φ'.nextComp) {y : Y}
    (hy : y ∈ Φ'.faceSet T) : Set.InjOn ρ ↑T := by
  intro c₁ hc₁ c₂ hc₂ heq
  by_contra hne
  have hd := hρ.disjoint c₁ c₂ (Finset.mem_range.mp (hT hc₁)) (Finset.mem_range.mp (hT hc₂)) hne
    heq
  have hmem : y ∈ Φ'.piece c₁ ⊓ Φ'.piece c₂ := by
    rw [← SetLike.mem_coe, Closeds.coe_inf]
    exact ⟨Φ'.mem_faceSet.mp hy c₁ hc₁, Φ'.mem_faceSet.mp hy c₂ hc₂⟩
  have h0 : y ∈ (⊥ : Closeds Y) := (disjoint_iff_inf_le.mp hd) hmem
  rw [← SetLike.mem_coe, Closeds.coe_bot] at h0
  exact h0

/-- A common point of a face of `Y` maps to a common point of the image face. -/
theorem mem_faceSet_image {T : Finset ℕ} (hT : T ⊆ Finset.range Φ'.nextComp) {y : Y}
    (hy : y ∈ Φ'.faceSet T) : h y ∈ Φ.faceSet (T.image ρ) := by
  classical
  refine Φ.mem_faceSet.mpr fun c hc => ?_
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
  exact hρ.mem_piece_of_mem (Finset.mem_range.mp (hT hc')) (Φ'.mem_faceSet.mp hy c' hc')

/-- The image of a face of `Y` is a face of `X`. -/
theorem image_mem_nerve {T : Finset ℕ} (hT : T ∈ Φ'.nerve) : T.image ρ ∈ Φ.nerve := by
  classical
  obtain ⟨hTr, hTne, hTb⟩ := Φ'.mem_nerve.mp hT
  obtain ⟨y, hy⟩ := Closeds.coe_nonempty.mpr hTb
  refine Φ.mem_nerve_of_mem_faceSet ?_ (hTne.image ρ) (x := h y) (hρ.mem_faceSet_image hTr hy)
  intro c hc
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
  exact Finset.mem_range.mpr (hρ.lt c' (Finset.mem_range.mp (hTr hc')))

/-- A face of `X` with a point over `Y` is the image of a face of `Y` through that point: one child
of each of its pieces through the point. -/
theorem exists_image_eq {T' : Finset ℕ} (hT' : T' ∈ Φ.nerve) {y : Y}
    (hy : h y ∈ Φ.faceSet T') : ∃ T ∈ Φ'.nerve, T.image ρ = T' ∧ y ∈ Φ'.faceSet T := by
  classical
  obtain ⟨hT'r, hT'ne, -⟩ := Φ.mem_nerve.mp hT'
  have hch : ∀ c ∈ T', ∃ c', c' < Φ'.nextComp ∧ ρ c' = c ∧ y ∈ Φ'.piece c' := fun c hc =>
    hρ.exists_child (Finset.mem_range.mp (hT'r hc)) (Φ.mem_faceSet.mp hy c hc)
  choose! g hg using hch
  have hyT : y ∈ Φ'.faceSet (T'.image g) := by
    refine Φ'.mem_faceSet.mpr fun c' hc' => ?_
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    exact (hg c hc).2.2
  refine ⟨T'.image g, ?_, ?_, hyT⟩
  · refine Φ'.mem_nerve_of_mem_faceSet ?_ (hT'ne.image g) (x := y) hyT
    intro c' hc'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    exact Finset.mem_range.mpr (hg c hc).1
  · rw [Finset.image_image]
    exact (Finset.image_congr fun c hc => (hg c hc).2.1).trans Finset.image_id

end RefinesAlongW

/-! ### The restricted state and the refinement of states -/

variable (Φ : PieceFamily X) (h : Y ⟶ X) {n m : ℕ}

/-- The restricted state is `Sub` the state of `X`: the same counters, labels and exponents, a
subnerve. -/
theorem sub_restrictState (hV : Φ.IsValid n m) :
    (Φ.restrictState h n m hV).Sub (Φ.toState n m hV) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Φ.restrictNerve_subset h⟩

/-- The nerve of the restricted state: the faces whose face set meets the image of `h`. -/
theorem mem_nerve_restrictState (hV : Φ.IsValid n m) (T : Finset ℕ) :
    T ∈ (Φ.restrictState h n m hV).nerve ↔
      T ∈ Φ.nerve ∧ (Φ.faceSet T).preimage h.continuous ≠ ⊥ :=
  Φ.mem_restrictNerve h

variable {Φ h} {ρ : ℕ → ℕ} {Φ' : PieceFamily Y}

/-- The state of a refining family refines, along the parent map, the state of `X` restricted to
the faces with a point over `Y`. -/
theorem refines_toState (hρ : Φ'.RefinesAlong h ρ Φ) (hV : Φ.IsValid n m) (hV' : Φ'.IsValid n m) :
    MonomialState.Refines ρ (Φ'.toState n m hV') (Φ.restrictState h n m hV) where
  n_eq := rfl
  m_eq := rfl
  nextLabel_eq := hρ.nextLabel_eq
  lt := hρ.lt
  label_eq := hρ.label_eq
  a_eq := hρ.a_eq
  injOn T hT := by
    obtain ⟨hTr, -, hTb⟩ := Φ'.mem_nerve.mp hT
    obtain ⟨y, hy⟩ := Closeds.coe_nonempty.mpr hTb
    exact hρ.toW.injOn_of_mem_faceSet hTr hy
  image_mem T hT := by
    rw [restrictState_nerve, mem_restrictNerve]
    refine ⟨hρ.toW.image_mem_nerve hT, ?_⟩
    obtain ⟨hTr, -, hTb⟩ := Φ'.mem_nerve.mp hT
    obtain ⟨y, hy⟩ := Closeds.coe_nonempty.mpr hTb
    refine Closeds.coe_nonempty.mp ⟨y, ?_⟩
    change h y ∈ Φ.faceSet (T.image ρ)
    exact hρ.toW.mem_faceSet_image hTr hy
  exists_lift T' hT' := by
    rw [restrictState_nerve, mem_restrictNerve] at hT'
    obtain ⟨hT'N, hT'b⟩ := hT'
    obtain ⟨y, hy⟩ := Closeds.coe_nonempty.mpr hT'b
    obtain ⟨T, hT, hTeq, -⟩ := hρ.toW.exists_image_eq hT'N hy
    exact ⟨T, hT, hTeq⟩

/-- For surjective `h` every face of `X` has a point over `Y`, and the state of a refining family
refines the full state of `X`. This is why a smooth surjection needs no deletion of empty
blow-ups in the first clause of [Kol07, 34.1]. -/
theorem refines_toState_of_surjective (hρ : Φ'.RefinesAlong h ρ Φ) (hs : Function.Surjective h)
    (hV : Φ.IsValid n m) (hV' : Φ'.IsValid n m) :
    MonomialState.Refines ρ (Φ'.toState n m hV') (Φ.toState n m hV) where
  n_eq := rfl
  m_eq := rfl
  nextLabel_eq := hρ.nextLabel_eq
  lt := hρ.lt
  label_eq := hρ.label_eq
  a_eq := hρ.a_eq
  injOn T hT := by
    obtain ⟨hTr, -, hTb⟩ := Φ'.mem_nerve.mp hT
    obtain ⟨y, hy⟩ := Closeds.coe_nonempty.mpr hTb
    exact hρ.toW.injOn_of_mem_faceSet hTr hy
  image_mem T hT := hρ.toW.image_mem_nerve hT
  exists_lift T' hT' := by
    obtain ⟨-, -, hT'b⟩ := Φ.mem_nerve.mp hT'
    obtain ⟨x, hx⟩ := Closeds.coe_nonempty.mpr hT'b
    obtain ⟨y, rfl⟩ := hs x
    obtain ⟨T, hT, hTeq, -⟩ := hρ.toW.exists_image_eq hT' hx
    exact ⟨T, hT, hTeq⟩

/-! ### The refining family: the components of the preimages -/

section Existence

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (h : Y ⟶ X)
  [Flat h] (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}

/-- The parent of a component of the pulled-back family: the piece of `Φ` through the image of its
generic point (a singleton face, `faceAt_eq_singleton_of_mem_genericPoints`). -/
noncomputable def parentOf {k' : ℕ} (σ' : Fin k' ≃ Components (E.comap h)) (c' : ℕ) : ℕ :=
  if hc : c' < k' then (Φ.faceAt (h ((σ' ⟨c', hc⟩).2 : Y))).sup id else 0

omit [Flat h] in
theorem parentOf_of_lt {k' : ℕ} (σ' : Fin k' ≃ Components (E.comap h)) {c' : ℕ} (hc : c' < k') :
    Φ.parentOf h σ' c' = (Φ.faceAt (h ((σ' ⟨c', hc⟩).2 : Y))).sup id :=
  dite_eq_left hc

include f in
/-- The parent of a component: the image of the generic point is a generic point of the parent
member (flat morphisms are generalizing), through which exactly one piece passes. -/
theorem parentOf_spec (hE : E.IsSnc) (hΦ : Φ.Realizes E e) {k' : ℕ}
    (σ' : Fin k' ≃ Components (E.comap h)) (c' : ℕ) (hc : c' < k') :
    Φ.parentOf h σ' c' < Φ.nextComp ∧
      Φ.label (Φ.parentOf h σ' c') = ((e (σ' ⟨c', hc⟩).1 : Fin Φ.nextLabel) : ℕ) ∧
      h ((σ' ⟨c', hc⟩).2 : Y) ∈ Φ.piece (Φ.parentOf h σ' c') ∧
      Φ.faceAt (h ((σ' ⟨c', hc⟩).2 : Y)) = {Φ.parentOf h σ' c'} ∧
      Φ.exponentAt (h ((σ' ⟨c', hc⟩).2 : Y)) = Φ.a (Φ.parentOf h σ' c') := by
  have hgen : h ((σ' ⟨c', hc⟩).2 : Y) ∈ (E.component (σ' ⟨c', hc⟩).1).support.genericPoints :=
    mem_genericPoints_support_of_flat h _ (σ' ⟨c', hc⟩).2.2
  obtain ⟨c, hcn, hlab, hmem, hface, hexp⟩ :=
    Φ.faceAt_eq_singleton_of_mem_genericPoints f hE hΦ hgen
  have hρ : Φ.parentOf h σ' c' = c := by
    rw [Φ.parentOf_of_lt h σ' hc, hface, Finset.sup_singleton]
    rfl
  rw [hρ]
  exact ⟨hcn, hlab, hmem, hface, hexp⟩

include f in
/-- The family of the irreducible components of the preimages `h⁻¹(D_c)`, `ofDivisorFamily` on
`h⁻¹E` with the exponent `Φ.exponentAt ∘ h`, refines `Φ` along a flat `h` through `parentOf`:
labels and exponents pass to the parent (the image of the generic point lies on the parent piece
only), each child lies in the preimage of its parent, the preimage of a piece is the union of
its children (a generic point of `h⁻¹(D_c)` is a generic point of the member's preimage, the
pieces of a label being disjoint), and children of one parent are disjoint (two components of
the regular member `h⁻¹E^j` through a point coincide). The snc of `h⁻¹E` is a hypothesis. -/
theorem refinesAlong_ofDivisorFamily (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    (hE' : (E.comap h).IsSnc) {k' : ℕ} (σ' : Fin k' ≃ Components (E.comap h)) :
    (ofDivisorFamily (E.comap h) (fun y => Φ.exponentAt (h y)) e σ').RefinesAlong h
      (Φ.parentOf h σ') Φ := by
  classical
  have hspec := fun (c' : ℕ) (hc : c' < k') => Φ.parentOf_spec f h hE hΦ σ' c' hc
  -- each child lies over its parent
  have hle : ∀ c', c' < k' → (ofDivisorFamily (E.comap h) (fun y => Φ.exponentAt (h y)) e σ').piece
      c' ≤ (Φ.piece (Φ.parentOf h σ' c')).preimage h.continuous := by
    intro c' hc'
    change (if hc : c' < k' then Closeds.closure {((σ' ⟨c', hc⟩).2 : Y)} else ⊥) ≤ _
    rw [dite_eq_left hc']
    exact Closeds.closure_le.mpr (Set.singleton_subset_iff.mpr (hspec c' hc').2.2.1)
  refine ⟨rfl, fun c' hc' => (hspec c' hc').1, fun c' hc' => ?_, fun c' hc' => ?_, hle, ?_, ?_⟩
  · have hck : c' < k' := hc'
    change Φ.label (Φ.parentOf h σ' c') =
      (if hc : c' < k' then ((e (σ' ⟨c', hc⟩).1 : Fin Φ.nextLabel) : ℕ) else 0)
    rw [dite_eq_left hck]
    exact (hspec c' hck).2.1
  · have hck : c' < k' := hc'
    change Φ.a (Φ.parentOf h σ' c') =
      (if hc : c' < k' then Φ.exponentAt (h ((σ' ⟨c', hc⟩).2 : Y)) else 0)
    rw [dite_eq_left hck]
    exact (hspec c' hck).2.2.2.2.symm
  · -- the preimage of a piece is the union of its children
    intro c hc
    apply le_antisymm
    · intro y hy
      have hhy : h y ∈ Φ.piece c := hy
      -- a generic point of the preimage through `y`
      obtain ⟨η', hη', hη'y⟩ :=
        Closeds.exists_mem_genericPoints_specializes ((Φ.piece c).preimage h.continuous) hy
      have hη'c : h η' ∈ Φ.piece c := hη'.1
      -- it is a generic point of the member's preimage
      have hgen : η' ∈ ((E.comap h).component (Φ.memberOf e c hc)).support.genericPoints := by
        refine ⟨(mem_support_comap_iff_apply _ h η').mpr
          (Φ.mem_support_component_of_mem_piece hΦ hc hη'c), fun η'' hη'' hη''η' => ?_⟩
        have hmem'' := (mem_support_comap_iff_apply _ h η'').mp hη''
        rw [hΦ.support_eq, mem_finset_sup_iff] at hmem''
        obtain ⟨c₂, hc₂, hη''c₂⟩ := hmem''
        obtain ⟨hc₂r, hlab₂⟩ := Finset.mem_filter.mp hc₂
        have hc₂n := Finset.mem_range.mp hc₂r
        have hη'c₂ : h η' ∈ Φ.piece c₂ :=
          (hη''η'.map h.continuous).mem_closed (Φ.piece c₂).isClosed hη''c₂
        have hcc₂ : c₂ = c := by
          by_contra hne
          exact Φ.not_mem_piece_of_label_eq hΦ hc₂n hc hne
            (hlab₂.trans (Φ.coe_apply_memberOf e c hc)) hη'c₂ hη'c
        subst hcc₂
        exact hη'.2 hη''c₂ hη''η'
      -- the component `⟨j, η'⟩` is the child through `y`
      let p : Components (E.comap h) := ⟨Φ.memberOf e c hc, ⟨η', hgen⟩⟩
      have hσ : σ' ⟨(σ'.symm p : ℕ), (σ'.symm p).isLt⟩ = p := σ'.apply_symm_apply p
      have hc' : (σ'.symm p : ℕ) < k' := (σ'.symm p).isLt
      have hρc : Φ.parentOf h σ' (σ'.symm p : ℕ) = c := by
        have hmemc : c ∈ Φ.faceAt (h ((σ' ⟨(σ'.symm p : ℕ), hc'⟩).2 : Y)) := by
          rw [hσ]
          exact Φ.mem_faceAt.mpr ⟨hc, hη'c⟩
        rw [(hspec _ hc').2.2.2.1, Finset.mem_singleton] at hmemc
        exact hmemc.symm
      rw [mem_finset_sup_iff]
      refine ⟨(σ'.symm p : ℕ), Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc', hρc⟩, ?_⟩
      change y ∈ (if hc'' : (σ'.symm p : ℕ) < k' then
        Closeds.closure {((σ' ⟨(σ'.symm p : ℕ), hc''⟩).2 : Y)} else ⊥)
      rw [dite_eq_left hc', hσ]
      exact specializes_iff_mem_closure.mp hη'y
    · rw [Finset.sup_le_iff]
      intro c' hc'
      obtain ⟨hcr, hρc⟩ := Finset.mem_filter.mp hc'
      rw [← hρc]
      exact hle c' (Finset.mem_range.mp hcr)
  · -- children of one parent are disjoint
    intro c₁ c₂ hc₁ hc₂ hne hρeq
    have hk₁ : c₁ < k' := hc₁
    have hk₂ : c₂ < k' := hc₂
    have hj : (σ' ⟨c₁, hk₁⟩).1 = (σ' ⟨c₂, hk₂⟩).1 := by
      apply e.injective
      apply Fin.ext
      rw [← (hspec c₁ hk₁).2.1, ← (hspec c₂ hk₂).2.1, hρeq]
    change Disjoint (if hc : c₁ < k' then Closeds.closure {((σ' ⟨c₁, hc⟩).2 : Y)} else ⊥)
      (if hc : c₂ < k' then Closeds.closure {((σ' ⟨c₂, hc⟩).2 : Y)} else ⊥)
    rw [dite_eq_left hk₁, dite_eq_left hk₂, disjoint_iff_inf_le]
    intro y hy
    rw [← SetLike.mem_coe, Closeds.coe_inf] at hy
    obtain ⟨h1, h2⟩ := hy
    have hη₁y : ((σ' ⟨c₁, hk₁⟩).2 : Y) ⤳ y := specializes_iff_mem_closure.mpr h1
    have hη₂y : ((σ' ⟨c₂, hk₂⟩).2 : Y) ⤳ y := specializes_iff_mem_closure.mpr h2
    exfalso
    apply hne
    have hgen : ∀ (p q : Components (E.comap h)), p.1 = q.1 → (p.2 : Y) ⤳ y → (q.2 : Y) ⤳ y →
        p = q := by
      rintro ⟨jp, ηp⟩ ⟨jq, ηq⟩ hpq hp hq
      simp only at hpq
      subst hpq
      have := Hironaka.Sequence.eq_of_specializes_of_isRegular _ (hE'.1 jp) ηp.2 ηq.2 hp hq
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext this))
    have := σ'.injective (hgen _ _ hj hη₁y hη₂y)
    exact congrArg Fin.val this

include f in
/-- A piece family of `Y` refining `Φ` along a flat `h` exists, the irreducible components of the
preimages of the pieces (finitely many, `Y` being Noetherian), and it realises `h^{-1}E` through
the same label isomorphism (`ofDivisorFamily_realizes` on the snc boundary `h^{-1}E`). -/
theorem exists_refinesAlong_of_flat [NoetherianSpace Y] (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    (hE' : (E.comap h).IsSnc) :
    ∃ (Φ' : PieceFamily Y) (ρ : ℕ → ℕ) (hρ : Φ'.RefinesAlong h ρ Φ),
      Φ'.Realizes (E.comap h) (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) := by
  classical
  have hfin : ∀ j : E.ι, Finite ↥((E.comap h).component j).support.genericPoints := fun j =>
    (Hironaka.BMO.Snc.genericPoints_component_finite (E.comap h) j).to_subtype
  have hfinC : Finite (Components (E.comap h)) := by
    unfold Components
    infer_instance
  let σ' : Fin (Nat.card (Components (E.comap h))) ≃ Components (E.comap h) :=
    (Finite.equivFin _).symm
  refine ⟨ofDivisorFamily (E.comap h) (fun y => Φ.exponentAt (h y)) e σ', Φ.parentOf h σ',
    Φ.refinesAlong_ofDivisorFamily f h hE hΦ hE' σ', ?_⟩
  exact ofDivisorFamily_realizes (E.comap h) _ e σ' hE'

omit [Flat h] in
include f in
/-- The smooth form: for a smooth `h` with `Y` quasi-compact over `k`, a refining family exists
(`exists_refinesAlong_of_flat`, with `h⁻¹E` snc by `isSnc_comap_of_smooth` of
`Hironaka/Scheme/BlowUpSequence/PullbackSnc.lean` and `Y` Noetherian). -/
theorem exists_refinesAlong [PerfectField k] [Smooth h]
    [QuasiCompact (h ≫ f)] (hE : E.IsSnc) (hΦ : Φ.Realizes E e) :
    ∃ (Φ' : PieceFamily Y) (ρ : ℕ → ℕ) (hρ : Φ'.RefinesAlong h ρ Φ),
      Φ'.Realizes (E.comap h) (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) := by
  have hN : IsNoetherian Y := (h ≫ f).isNoetherian_of_field
  exact Φ.exists_refinesAlong_of_flat f h hE hΦ (isSnc_comap_of_smooth f h hE)

end Existence

/-! ### The marked monomial ideal pulls back -/

section Monomial

variable {k : Type u} [Field k] [PerfectField k] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
  [QuasiCompact f] (h : Y ⟶ X) [Smooth h] [QuasiCompact (h ≫ f)]
  (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}

include f in
/-- The marked monomial ideal of the refining family is the pull-back of the marked monomial
ideal: stalk by stalk, the one component of `h⁻¹E^i` through `y` maps to the one component of
`E^i` through `h y` (flat morphisms are generalising), and the exponents agree, the child through
the generic point lying over the parent through its image. -/
theorem monomial_comap_exponentAt (hE : E.IsSnc) (hΦ : Φ.Realizes E e) {Φ' : PieceFamily Y}
    {ρ : ℕ → ℕ} (hρ : Φ'.RefinesAlong h ρ Φ)
    (hΦ' : Φ'.Realizes (E.comap h) (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm))) :
    (E.comap h).monomial Φ'.exponentAt = (E.monomial Φ.exponentAt).comap h := by
  classical
  have hNX : IsNoetherian X := f.isNoetherian_of_field
  have hNY : IsNoetherian Y := (h ≫ f).isNoetherian_of_field
  have hE' : (E.comap h).IsSnc := isSnc_comap_of_smooth f h hE
  refine IdealSheafData.ext_stalkIdeal fun y => ?_
  rw [IdealSheafData.stalkIdeal_comap,
    Hironaka.BMO.stalkIdeal_monomial (E.comap h)
      (fun i => Hironaka.BMO.Snc.genericPoints_component_finite _ i) _ y,
    Hironaka.BMO.stalkIdeal_monomial E
      (fun i => Hironaka.BMO.Snc.genericPoints_component_finite E i) _ (h y)]
  have hmap : ∀ F : E.ι → Ideal (X.presheaf.stalk (h y)),
      Ideal.map (h.stalkMap y).hom (∏ i, F i) = ∏ i, Ideal.map (h.stalkMap y).hom (F i) :=
    fun F => map_prod (Ideal.mapHom (h.stalkMap y).hom) F Finset.univ
  rw [hmap]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hx : h y ∈ (E.component i).support
  · have hy : y ∈ ((E.comap h).component i).support :=
      (mem_support_comap_iff_apply _ h y).mpr hx
    obtain ⟨η, hη, hηx⟩ := Hironaka.BMO.exists_genericPoint_specializes _ hx
    obtain ⟨η', hη', hη'y⟩ := Hironaka.BMO.exists_genericPoint_specializes _ hy
    rw [Hironaka.BMO.Snc.finprod_stalk_eq_of_specializes (E.comap h) hE' hη' hη'y,
      Hironaka.BMO.Snc.finprod_stalk_eq_of_specializes E hE hη hηx, Ideal.map_pow,
      ← IdealSheafData.stalkIdeal_comap]
    -- the generic point of `h⁻¹E^i` through `y` maps to the generic point of `E^i` through `h y`
    have hpη' : h η' ∈ (E.component i).support.genericPoints :=
      mem_genericPoints_support_of_flat h _ hη'
    have heq : h η' = η := Hironaka.BMO.Snc.genericPoint_eq_of_specializes E hE hpη' hη
      (hη'y.map h.continuous) hηx
    -- the exponents: the child through `η'` lies over the parent through `h η'`
    obtain ⟨c', hc', -, hη'c', -, hexp'⟩ :=
      Φ'.faceAt_eq_singleton_of_mem_genericPoints (h ≫ f) hE' hΦ' hη'
    obtain ⟨c, hcn, -, -, hface, hexp⟩ := Φ.faceAt_eq_singleton_of_mem_genericPoints f hE hΦ hpη'
    have hmem : ρ c' ∈ Φ.faceAt (h η') :=
      Φ.mem_faceAt.mpr ⟨hρ.lt c' hc', hρ.toW.mem_piece_of_mem hc' hη'c'⟩
    rw [hface, Finset.mem_singleton] at hmem
    change ((E.component i).comap h).stalkIdeal y ^ Φ'.exponentAt η' =
      ((E.component i).comap h).stalkIdeal y ^ Φ.exponentAt η
    rw [hexp', ← heq, hexp, ← hρ.a_eq c' hc', hmem]
  · have hy : y ∉ ((E.comap h).component i).support := fun hy =>
      hx ((mem_support_comap_iff_apply _ h y).mp hy)
    rw [Hironaka.BMO.Snc.finprod_stalk_eq_one_of_notMem (E.comap h) hy,
      Hironaka.BMO.Snc.finprod_stalk_eq_one_of_notMem E hx]
    simp only [Ideal.one_eq_top, Ideal.map_top]

end Monomial

end Hironaka.Monomial.PieceFamily
