/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Snc.MonomialComponents
import Hironaka.Scheme.BlowUp.Glue.Product
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The pulled-back exceptional divisors form a simple normal crossing divisor

In the proof of the principalization theorem [Kol07, 72], `Π^* I = I_r · 𝒪_{X_r}(F)` for an
effective divisor `F` "supported on the total transform of `∑ E^i`", and `F` is a simple normal
crossing divisor, where `F = ∑_j Π_{r,j+1}^* F_j` is the sum of the exceptional divisors of the
steps pulled back to the end result. This module proves that statement for every smooth blow-up
sequence of order `≥ m` starting with a marked triple: the ideal sheaf `∏_j Π_{r,j+1}^* F_j` is
invertible (each `F_j` is the inverse image of the center, an invertible ideal sheaf, and
invertible ideal sheaves pull back to invertible ones along blow-ups) and its support lies in the
final total transform `E_r` (`π^{-1}(V(E_i)) ⊆ V(E_{i+1})`: a point off the exceptional divisor
lies on the strict transform of the member below it). By the uniqueness in the decomposition of
an ideal into its monomial and nonmonomial parts [Kol07, Definition–Lemma 110], also
[BM08, equation (5.2)] (`eq_monomialPart_of_isInvertible_of_support_le`), it is therefore the
monomial of `E_r` with exponents `ord_D` at the irreducible components `D`, and a monomial of a
simple normal crossing family is the ideal sheaf of a simple normal crossing divisor
(`Hironaka/Resolution/Algebraic/Snc/MonomialComponents.lean`). The final family `E_r` has simple
normal crossings by condition (3′) of [Kol07, Definition 66] iterated
(`IsOrderGeSeq.isSnc_totalTransformSeq`), so the multiplicities accumulate exactly as Kollár's sum
does.

* `isInvertible_exceptionalAt`, `isInvertible_comap_stageMapBetween`;
* `preimage_support_subset_support_totalTransform`, `preimage_stageMap_support_subset`,
  `preimage_stageMapBetween_support_subset`, `support_exceptionalAt_le_support_totalTransformSeq`;
* `isIdealOfSncDivisor_prod_comap_exceptionalAt`: the theorem on a marked triple.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  IdealSheafData BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Invertibility -/

/-- The exceptional divisor `F_{i+1} = π_i^{-1}(Z_i)` of a step [Kol07, Notation 19] is an
invertible ideal sheaf (the exceptional ideal of a blow-up is invertible, carried across the cast
`X_1 = D.blowUp` at the first step). -/
theorem isInvertible_exceptionalAt :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (i : Fin S.length), (S.exceptionalAt i).IsInvertible
  | _, nil _, i => i.elim0
  | _, cons X D rest, ⟨0, _⟩ => by
    change (D.comap (eqToHom (stage_zero rest) ≫ D.blowUpπ)).IsInvertible
    rw [comap_comp]
    exact (blowUp.isInvertible_comap_π (I := D)).comap_of_isOpenImmersion _
  | _, cons _ D rest, ⟨j + 1, hj⟩ => isInvertible_exceptionalAt rest ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-- An invertible ideal sheaf on `X_j` pulls back along `Π_{ij} : X_i ⟶ X_j` to an invertible
one: the inverse image of an invertible ideal sheaf under a blow-up is invertible, iterated along
the sequence. -/
theorem isInvertible_comap_stageMapBetween :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) {i j : Fin (S.length + 1)} (h : j ≤ i)
      {K : (S.stage j).IdealSheafData}, K.IsInvertible →
      (K.comap (S.stageMapBetween i j h)).IsInvertible
  | _, nil _, _, _, _, K, hK =>
    (congrArg Scheme.IdealSheafData.IsInvertible (comap_id K)).mpr hK
  | _, cons _ _ _, ⟨0, _⟩, ⟨0, _⟩, _, K, hK =>
    (congrArg Scheme.IdealSheafData.IsInvertible (comap_id K)).mpr hK
  | _, cons _ _ _, ⟨0, _⟩, ⟨_ + 1, _⟩, h, _, _ => (Nat.not_succ_le_zero _ h).elim
  | _, cons X D rest, ⟨i + 1, hi⟩, ⟨0, _⟩, _, K, hK =>
    (congrArg Scheme.IdealSheafData.IsInvertible
      (comap_comp K (rest.stageMap ⟨i, Nat.lt_of_succ_lt_succ hi⟩) D.blowUpπ)).mpr
      (isInvertible_comap_stageMap rest
        (blowUp.isInvertible_comap_of_isInvertible (I := D) K hK) _)
  | _, cons _ _ rest, ⟨_ + 1, _⟩, ⟨_ + 1, _⟩, h, _, hK =>
    isInvertible_comap_stageMapBetween rest (Nat.le_of_succ_le_succ h) hK

/-! ### Supports -/

/-- The inverse image of `V(E)` under the blow-up lies in the support of the total transform
[Kol07, Definition 25]: a point off the exceptional divisor lies on the strict transform of a
member through its image (`mem_support_strictTransformAlong_iff_of_notMem_support`). -/
theorem preimage_support_subset_support_totalTransform (E : DivisorFamily X)
    (D : X.IdealSheafData) :
    D.blowUpπ ⁻¹' (E.support : Set X) ⊆ ((E.totalTransform D).support : Set
        D.blowUp) := by
  intro b hb
  obtain ⟨i, hbi⟩ := (DivisorFamily.mem_support_iff_exists E _).mp hb
  by_cases hF : b ∈ D.exceptionalDivisor.support
  · exact (DivisorFamily.mem_support_iff_exists _ b).mpr ⟨toLex (Sum.inr PUnit.unit), hF⟩
  · refine (DivisorFamily.mem_support_iff_exists _ b).mpr ⟨toLex (Sum.inl i), ?_⟩
    exact (mem_support_strictTransformAlong_iff_of_notMem_support D (E.component i)
      hF).mpr hbi

/-- `Π_i^{-1}(V(E)) ⊆ V(E_i)` ([Kol07, Definition 25] iterated). -/
theorem preimage_stageMap_support_subset :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E : DivisorFamily X) (i : Fin (S.length + 1)),
      (S.stageMap i) ⁻¹' (E.support : Set X) ⊆ ((S.totalTransformSeq E i).support : Set (S.stage i))
  | _, nil _, _, _ => fun _ hb => hb
  | _, cons _ _ _, _, ⟨0, _⟩ => fun _ hb => hb
  | _, cons X D rest, E, ⟨j + 1, hj⟩ => fun _ hb =>
    preimage_stageMap_support_subset rest (E.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩
      (preimage_support_subset_support_totalTransform E D hb)

/-- `Π_{li}^{-1}(V(E_i)) ⊆ V(E_l)` for `i ≤ l` ([Kol07, Definition 25] iterated between two
stages). -/
theorem preimage_stageMapBetween_support_subset :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E : DivisorFamily X) {i l : Fin (S.length + 1)}
      (h : i ≤ l),
      (S.stageMapBetween l i h) ⁻¹' ((S.totalTransformSeq E i).support : Set (S.stage i)) ⊆
        ((S.totalTransformSeq E l).support : Set (S.stage l))
  | _, nil _, _, _, _, _ => fun _ hb => hb
  | _, cons _ _ _, _, ⟨0, _⟩, ⟨0, _⟩, _ => fun _ hb => hb
  | _, cons _ _ _, _, ⟨_ + 1, _⟩, ⟨0, _⟩, h => (Nat.not_succ_le_zero _ h).elim
  | _, cons X D rest, E, ⟨0, _⟩, ⟨l + 1, hl⟩, _ => fun _ hb =>
    preimage_stageMap_support_subset rest (E.totalTransform D) ⟨l, Nat.lt_of_succ_lt_succ hl⟩
      (preimage_support_subset_support_totalTransform E D hb)
  | _, cons _ D rest, E, ⟨_ + 1, _⟩, ⟨_ + 1, _⟩, h =>
    preimage_stageMapBetween_support_subset rest (E.totalTransform D) (Nat.le_of_succ_le_succ h)

/-- The exceptional divisor `F_{j+1}` is the last member of `E_{j+1} = (π_j)^{-1}_{tot} E_j`
[Kol07, Definition 66, condition (1)], so its support lies in `V(E_{j+1})`. -/
theorem support_exceptionalAt_le_support_totalTransformSeq (S : BlowUpSequence X)
    (E : DivisorFamily X) (j : Fin S.length) :
    (S.exceptionalAt j).support ≤ (S.totalTransformSeq E j.succ).support := by
  rw [totalTransformSeq_succ E S j]
  exact IsConcreteLE.le_iff.mpr fun b hb =>
    (DivisorFamily.mem_support_iff_exists _ b).mpr ⟨toLex (Sum.inr PUnit.unit), hb⟩

/-! ### The theorem -/

variable {k : Type u} [Field k] [CharZero k]

/-- Along a smooth blow-up sequence of order `≥ m` starting with the marked triple `T`, the
product of the exceptional divisors of the steps pulled back to the end result along the later
steps, `∏_j Π_{r,j+1}^* F_j`, is the ideal sheaf of an effective divisor supported on a simple
normal crossing family ("`F` is a simple normal crossing divisor", [Kol07, 72]): it is
invertible, its support lies in the final total transform `E_r` (which has simple normal
crossings by condition (3′) of Definition 66 iterated), so it is its own monomial part
[Kol07, Definition–Lemma 110], a monomial of the family `E_r` with exponents `ord_D` at the
irreducible components `D`. -/
theorem isIdealOfSncDivisor_prod_comap_exceptionalAt (T : MarkedTriple k)
    (S : BlowUpSequence T.X.left) (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E) :
    IsIdealOfSncDivisor (∏ j : Fin S.length,
      (S.exceptionalAt j).comap (S.stageMapBetween (Fin.last _) j.succ (Fin.le_last _))) := by
  set K := ∏ j : Fin S.length,
    (S.exceptionalAt j).comap (S.stageMapBetween (Fin.last _) j.succ (Fin.le_last _)) with hK
  let T' : Triple k := (T.induced S hS (Fin.last _)).toTriple
  have hinv : K.IsInvertible := by
    refine Finset.prod_induction _
      (fun J : (S.stage (Fin.last _)).IdealSheafData => J.IsInvertible)
      (fun _ _ h₁ h₂ => h₁.mul h₂) (one_eq_top ▸ isInvertible_top) fun j _ => ?_
    exact isInvertible_comap_stageMapBetween S _ (isInvertible_exceptionalAt S j)
  have hsupp : K.support ≤ T'.E.support := by
    rw [hK, support_finset_prod]
    refine iSup₂_le fun j _ => IsConcreteLE.le_iff.mpr fun b hb => ?_
    rw [mem_support_comap_iff_apply] at hb
    exact preimage_stageMapBetween_support_subset S T.E (Fin.le_last _)
      (support_exceptionalAt_le_support_totalTransformSeq S T.E j hb)
  have hmono : K = T'.E.monomial fun η => (K.ord η).toNat :=
    (Hironaka.BMO.eq_monomialPart_of_isInvertible_of_support_le T' hinv hsupp).trans
      (Hironaka.BMO.monomialPart_eq_monomial K T'.E)
  have := Hironaka.BD.noetherianSpace_triple T'
  rw [hmono]
  exact Hironaka.Snc.isIdealOfSncDivisor_monomial T'.isSnc _

end Hironaka.Sequence
