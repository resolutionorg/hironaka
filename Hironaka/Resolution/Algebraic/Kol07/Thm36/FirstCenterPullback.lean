/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The first-centre index along a flat morphism meeting the generic point

The first-centre index `firstCenterIndex S I` (`Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine`),
the first stage whose centre contains the strict transform of `V(I)`, is intrinsic to `V(I)` and
transports along flat pullbacks of the sequence [Kol07, Corollary 22, proof; Definition 30, 30.1].
`Hironaka.Resolution.Algebraic.Kol07.Thm36.FlatTransport` proves this along a flat SURJECTION for
every ideal sheaf; the functoriality of the affine resolution functor
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback`) and its change of fields
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BaseChangeAffine`) need it component by component,
along a flat morphism that need not be surjective but whose image contains the generic point of the
component. This file proves that form: for an integral closed subscheme
`V(I)` whose generic point lies in the image of a flat `h`,
`firstCenterIndex (S.pullback h) (I.comap h) = firstCenterIndex S I`
(`firstCenterIndex_pullback_of_flat_of_mem_range`), and likewise for an integral component
`V(I')` of the preimage of `V(I)` dominating it (`firstCenterIndex_pullback_of_flat_of_le`).

The mechanism: downstairs to upstairs is monotonicity of `CenterContains` under pullback
(`centerContains_pullback_of_le`); upstairs to downstairs, before the first downstairs
absorption, uses the generic point `η_n` of the strict transform `X̄_n`: it lies over the generic
point `η` of `V(I)`, hence in the image of the stage lift `h_n` (`range_pullbackStageHom`:
`h_n(X_n ×_X Y) = Π_n⁻¹(h(Y))`), so a pulled-back centre `h_n⁻¹(Z_n)` containing `h_n⁻¹(X̄_n)`
forces `Z_n ∋ η_n`, that is, `Z_n ⊇ X̄_n`. Neither surjectivity nor smoothness of `h` is needed:
flatness suffices (open immersions are the case used).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {X Y : Scheme.{u}} (S : BlowUpSequence X) (h : Y ⟶ X)

/-- A point of stage `n` lying over a point of the image of `h` lies in the image of the stage lift
`h_n` [Kol07, Definition 30, 30.1] (`range_pullbackStageHom`). -/
theorem mem_range_pullbackStageHom_of_stageMap_mem_range [Flat h] (i : Fin (S.length + 1))
    {x : S.stage i} (hx : S.stageMap i x ∈ Set.range h) :
    x ∈ Set.range (S.pullbackStageHom h i) := by
  rw [range_pullbackStageHom]
  exact hx

/-- Along a flat `h` whose image contains the generic point `η` of the integral `V(I)`: before any
absorption of `V(I)`, a pulled-back centre containing the strict transform of `h⁻¹(V(I))` forces
the centre to contain the strict transform of `V(I)`, because the generic point `η_n` of `X̄_n`
lies over `η` and hence in the image of the stage lift [Kol07, Corollary 22, proof]. -/
theorem centerContains_of_centerContains_pullback_of_mem_range [Flat h] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme] {η : X}
    (hη : IsGenericPoint η (I.support : Set X)) (hmem : η ∈ Set.range h) {n : ℕ}
    (hhist : ∀ m < n, ¬ CenterContains S I m)
    (hc' : CenterContains (S.pullback h) (I.comap h) n) : CenterContains S I n := by
  obtain ⟨hn', hle'⟩ := hc'
  have hn : n < S.length := by rwa [length_pullback] at hn'
  refine ⟨hn, ?_⟩
  have hred : IsReduced I.subscheme := inferInstance
  obtain ⟨ηn, hgen, hmap, -⟩ := exists_isGenericPoint_strictTransformSeq_mk ‹_› S I hη hred n
    (Nat.lt_succ_of_lt hn) (fun m hm hle => hhist m hm ⟨by omega, hle⟩)
  obtain ⟨y, hy⟩ := mem_range_pullbackStageHom_of_stageMap_mem_range S h ⟨n, Nat.lt_succ_of_lt hn⟩
    (x := ηn) (by rw [hmap]; exact hmem)
  have e1 : (S.pullback h).center ⟨n, hn'⟩ =
      (S.center ⟨n, hn⟩).comap (S.pullbackStageHom h ⟨n, Nat.lt_succ_of_lt hn⟩) :=
    center_pullback_mk S h n hn
  have e2 : (S.pullback h).strictTransformSeq (I.comap h) ⟨n, Nat.lt_succ_of_lt hn'⟩ =
      (S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn⟩).comap
        (S.pullbackStageHom h ⟨n, Nat.lt_succ_of_lt hn⟩) :=
    strictTransformSeq_pullback_mk S h I n (Nat.lt_succ_of_lt hn)
  rw [e1, e2] at hle'
  have hyST : y ∈ ((S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn⟩).comap
      (S.pullbackStageHom h ⟨n, Nat.lt_succ_of_lt hn⟩)).support := by
    rw [mem_support_comap_iff_apply, hy]
    exact hgen.mem
  have hyZ := IdealSheafData.support_antitone hle' hyST
  rw [mem_support_comap_iff_apply, hy] at hyZ
  have hint : IsIntegral (S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn⟩).subscheme :=
    isIntegral_strictTransformSeq_mk ‹_› S I ‹_› n (Nat.lt_succ_of_lt hn)
      (fun m hm hle => hhist m hm ⟨by omega, hle⟩)
  refine le_of_support_subset _ _ ?_
  rw [← hgen.def]
  exact closure_minimal (Set.singleton_subset_iff.mpr hyZ) (S.center ⟨n, hn⟩).support.isClosed

/-- Below the first downstairs absorption of `V(I)` there is no upstairs absorption of a component
`V(I')` of its preimage dominating it (strong induction on the stage, the histories of both sides
carried along). -/
theorem not_centerContains_pullback_of_lt_firstCenterIndex [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (I : X.IdealSheafData) [IsIntegral I.subscheme] {η : X}
    (hη : IsGenericPoint η (I.support : Set X)) (I' : Y.IdealSheafData) [IsReduced I'.subscheme]
    {η' : Y} (hη' : IsGenericPoint η' (I'.support : Set Y)) (hηη' : h η' = η) :
    ∀ n, n < firstCenterIndex S I → ¬ CenterContains (S.pullback h) I' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hc'
  exact not_centerContains_of_lt_firstCenterIndex' S I hn
    (centerContains_of_centerContains_pullback S h I hη I' hη' hηη'
      (fun m hm => not_centerContains_of_lt_firstCenterIndex' S I (hm.trans hn))
      (fun m hm => ih m hm (hm.trans hn)) hc')

/-- Along a flat `h`, for an integral `V(I)` with generic point `η` and an integral component
`V(I')` of its preimage (`I.comap h ≤ I'`, with generic point `η'` over `η`), the first-centre index
of the pulled-back sequence for `V(I')` is the first-centre index of `V(I)` [Kol07, Corollary 22,
proof; Definition 30, 30.1]: downstairs to upstairs by monotonicity through `I.comap h ≤ I'`
(`centerContains_pullback_of_le`), upstairs to downstairs before the first downstairs absorption
by the generic points (`not_centerContains_pullback_of_lt_firstCenterIndex`). This is the form used
for the components of the affine resolution functor. -/
theorem firstCenterIndex_pullback_of_flat_of_le [Flat h] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (I : X.IdealSheafData) [IsIntegral I.subscheme] {η : X}
    (hη : IsGenericPoint η (I.support : Set X)) (I' : Y.IdealSheafData) [IsIntegral I'.subscheme]
    (hle : I.comap h ≤ I') {η' : Y} (hη' : IsGenericPoint η' (I'.support : Set Y))
    (hηη' : h η' = η) : firstCenterIndex (S.pullback h) I' = firstCenterIndex S I := by
  classical
  have hdown := not_centerContains_pullback_of_lt_firstCenterIndex S h I hη I' hη' hηη'
  by_cases hex : ∃ n, CenterContains S I n
  · have hex' : ∃ n, CenterContains (S.pullback h) I' n :=
      ⟨_, centerContains_pullback_of_le S h hle (firstCenterIndex_of_exists hex)⟩
    have hfirst : ∀ m, m < Nat.find hex → m < firstCenterIndex S I := by
      intro m hm
      unfold firstCenterIndex
      rw [dite_eq_left hex]
      exact hm
    unfold firstCenterIndex
    rw [dite_eq_left hex', dite_eq_left hex, Nat.find_eq_iff]
    exact ⟨centerContains_pullback_of_le S h hle (Nat.find_spec hex),
      fun m hm => hdown m (hfirst m hm)⟩
  · -- no downstairs absorption: `firstCenterIndex S I = S.length`, and no upstairs absorption at
    -- any stage below it, so the upstairs index is the length too
    have hlen : firstCenterIndex S I = S.length := by
      unfold firstCenterIndex
      rw [dite_eq_right hex]
    have hex' : ¬ ∃ n, CenterContains (S.pullback h) I' n := by
      rintro ⟨n, hc'⟩
      have hnlt : n < firstCenterIndex S I := by
        rw [hlen, ← length_pullback S h]
        exact hc'.1
      exact hdown n hnlt hc'
    unfold firstCenterIndex
    rw [dite_eq_right hex', dite_eq_right hex, length_pullback]

/-- Along a flat `h` whose image contains the generic point of the integral `V(I)`, the first-centre
index of the pulled-back sequence for `h⁻¹(V(I))` is the first-centre index of `V(I)` [Kol07,
Corollary 22, proof]: the counterpart of `firstCenterIndex_pullback_of_flat_surjective` for a flat
morphism that need not be surjective. -/
theorem firstCenterIndex_pullback_of_flat_of_mem_range [Flat h] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme] {η : X}
    (hη : IsGenericPoint η (I.support : Set X)) (hmem : η ∈ Set.range h) :
    firstCenterIndex (S.pullback h) (I.comap h) = firstCenterIndex S I := by
  classical
  have hdown : ∀ n, n < firstCenterIndex S I → ¬ CenterContains (S.pullback h) (I.comap h) n :=
    fun n hn hc' => not_centerContains_of_lt_firstCenterIndex' S I hn
      (centerContains_of_centerContains_pullback_of_mem_range S h I hη hmem
        (fun m hm => not_centerContains_of_lt_firstCenterIndex' S I (hm.trans hn)) hc')
  by_cases hex : ∃ n, CenterContains S I n
  · have hex' : ∃ n, CenterContains (S.pullback h) (I.comap h) n :=
      ⟨_, centerContains_pullback_of_le S h le_rfl (firstCenterIndex_of_exists hex)⟩
    have hfirst : ∀ m, m < Nat.find hex → m < firstCenterIndex S I := by
      intro m hm
      unfold firstCenterIndex
      rw [dite_eq_left hex]
      exact hm
    unfold firstCenterIndex
    rw [dite_eq_left hex', dite_eq_left hex, Nat.find_eq_iff]
    exact ⟨centerContains_pullback_of_le S h le_rfl (Nat.find_spec hex),
      fun m hm => hdown m (hfirst m hm)⟩
  · have hex' : ¬ ∃ n, CenterContains (S.pullback h) (I.comap h) n := by
      rintro ⟨n, hc'⟩
      exact hex ⟨n, centerContains_of_centerContains_pullback_of_mem_range S h I hη hmem
        (fun m _ hc => hex ⟨m, hc⟩) hc'⟩
    unfold firstCenterIndex
    rw [dite_eq_right hex', dite_eq_right hex, length_pullback]

end Hironaka.Resolution
