/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Exhaustiveness: a component whose ideal ends in the unit ideal is absorbed

"Some blow-up center must contain `η_X`", since otherwise the composite would be a local
isomorphism around `η_X` and the pull-back of `I_X` could not be principal there [Kol07,
Corollary 22, proof]; in Włodarczyk's words, the resolution process of `(X, I_Y, ∅, 1)` blows up
the strict transform of `Y`, since otherwise "the generic points would be transformed
isomorphically" [Wlo05, 4.6]. This file proves the statement in
the marked form used by the embedded desingularization loop at a complete round
(`Hironaka.Resolution.Algebraic.Wlo05.Embedded`): if the marked transform of `(I, c)` at the end of
the sequence `S` is the unit ideal, then every integral `V(J)` whose generic point `η` is a generic
point of `supp I` with `I = J` at `η` has its strict transform contained in some centre of `S`
(`CenterContains`). Otherwise the unique point over `η` at the end
(`Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso`) would carry the proper stalk of `J`.

No hypothesis on the dimension of the local ring at `η` is needed, in contrast with the absorption
lemma of `Hironaka.Resolution.Algebraic.Kol07.Thm36.Absorption`, which argues from an invertible
pull-back by Krull's principal ideal theorem and needs `dim 𝒪_{A,η} ≥ 2`: here the hypothesis is the
vanishing of the marked transform at the end (clause (1) of [Kol07, Theorem 69] at the mark `1`),
which covers the components of codimension one as well.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {A : Scheme.{u}}

open Classical in
/-- If no centre of `S` contains the strict transform of `V(I)`, the first containing index is the
length of `S`. -/
theorem firstCenterIndex_eq_length_of_forall_not (S : BlowUpSequence A) (I : A.IdealSheafData)
    (h : ∀ n, ¬ CenterContains S I n) : firstCenterIndex S I = S.length := by
  unfold firstCenterIndex
  rw [dite_eq_right fun ⟨n, hn⟩ => h n hn]

/-- **Exhaustiveness** [Kol07, Corollary 22, proof; Wlo05, 4.6]: if the marked transform of
`(I, c)` at the end of `S` is the unit ideal, the strict transform of an integral `V(J)`, whose
generic point `η` is a generic point of `supp I` at which `I` and `J` agree, is contained in some
centre of `S`. Otherwise the unique point over `η` at the end result would carry, as the stalk of
the marked transform, the image of the proper stalk of `J` under an isomorphism
(`stalkIdeal_markedTransformSeq_of_forall_notMem`), not the unit ideal. -/
theorem exists_centerContains_of_markedTransformSeq_last_eq_top [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I J : A.IdealSheafData) [IsIntegral J.subscheme] (c : ℕ) {η : A}
    (hη : IsGenericPoint η (J.support : Set A)) (hηI : η ∈ I.support.genericPoints)
    (hIJ : I.stalkIdeal η = J.stalkIdeal η)
    (htop : S.markedTransformSeq I c (Fin.last _) = ⊤) : ∃ n, CenterContains S J n := by
  by_contra hnone
  have hnone' : ∀ n, ¬ CenterContains S J n := not_exists.mp hnone
  have hfirst : firstCenterIndex S J = S.length :=
    firstCenterIndex_eq_length_of_forall_not S J hnone'
  obtain ⟨η', -, hmap, huniq, havoid, -⟩ :=
    exists_isGenericPoint_strictTransformSeq_and_isIso_of_le_firstCenterIndex S J hη
      (Fin.last _) (by rw [hfirst]; exact le_of_eq (Fin.val_last _))
  have hgen := mem_genericPoints_markedTransformSeq_support_of_forall_notMem S I J c hη hηI hIJ
    (Fin.last _) hmap huniq havoid
  have hmem : η' ∈ (S.markedTransformSeq I c (Fin.last _)).support := hgen.1
  rw [htop, IdealSheafData.support_top] at hmem
  exact hmem

end Hironaka.Resolution
