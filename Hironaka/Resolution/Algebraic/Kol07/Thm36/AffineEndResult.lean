/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Absorption
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Scheme.BlowUpSequence.CentersCosupport
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The end result of the affine resolution is smooth

Clause (1) of [Kol07, Theorem 36] for the resolution of an embedded affine scheme, after the proof
of [Kol07, Corollary 22]: the centre `Z_j` is smooth, being the centre of a smooth blow-up, so
`g : Z_j → X̄` is a resolution. The last stage of the truncated restriction
`BR_affine TA emb` embeds in the ambient stage `A_j` with kernel the strict transform `X̄_j`
(`ker_pullbackStageHom`); at the first index `j` whose centre `Z_j` contains `X̄_j`, the inclusion
`X̄_j → Z_j` is an open immersion (`Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification`), so
the smoothness of `Z_j` over `k` (clause (1) of [Kol07, Theorem 35]) descends to `X̄_j` and to the
end result.

* `comap_stageMap_le_strictTransformSeq`: the strict transform lies over `V(I)`;
  `stageMap_mem_support_of_mem_center_support_of_isOrderSeq`: the centres of a sequence of order
  `1` lie over `V(I)` (Kollár's `π_0 ⋯ π_{j−1}(Z_j) ⊂ X̄` by (21.2) in the proof of
  [Kol07, Corollary 22], the hypothesis of the identification), which holds for `BP TA` with empty
  boundary;
* `isRegular_of_smooth`: a scheme smooth over a field of characteristic zero is regular;
* `smooth_subschemeι_comp_of_heq`: transport of smoothness across the identifications of the
  stages of a truncated sequence with those of the sequence;
* `smooth_composite_pullback_take`: the general form; the composite of the restriction of a
  truncated sequence is smooth over the base once the last centre contains the strict transform
  by an open immersion;
* `smooth_composite_BR_affine_of_smooth_center`: clause (1) for `BR_affine`, with the smoothness
  of the centre at the first index (clause (1) of [Kol07, Theorem 35]) as the hypothesis, which
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36` discharges.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  Hironaka BlowUpSequence Hironaka.Sequence Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {A : Scheme.{u}}

/-! ### The strict transform lies over `V(I)` -/

/-- The strict transform at stage `n` contains the total transform `I·𝒪_{A_n}`, in the `⟨n, hn⟩`
form (each step: `π^* J ≤ (π^* J : E^∞)`, `le_saturate`). -/
theorem comap_stageMap_le_strictTransformSeq_mk (S : BlowUpSequence A) (I : A.IdealSheafData)
    (n : ℕ) (hn : n < S.length + 1) :
    I.comap (S.stageMap ⟨n, hn⟩) ≤ S.strictTransformSeq I ⟨n, hn⟩ := by
  induction S generalizing n with
  | nil X =>
    have h0 : (nil X).length = 0 := rfl
    obtain rfl : n = 0 := by omega
    change I.comap (𝟙 X) ≤ I
    rw [Scheme.IdealSheafData.comap_id]
  | cons X D rest ih =>
    cases n with
    | zero =>
      change I.comap (𝟙 X) ≤ I
      rw [Scheme.IdealSheafData.comap_id]
    | succ n =>
      have hn' : n < rest.length + 1 := Nat.lt_of_succ_lt_succ hn
      change I.comap (rest.stageMap ⟨n, hn'⟩ ≫ D.blowUpπ) ≤
        rest.strictTransformSeq (I.strictTransform D) ⟨n, hn'⟩
      rw [comap_comp]
      have h0 : I.comap D.blowUpπ ≤ I.strictTransform D := le_saturate _ _
      exact le_trans (comap_mono _ h0) (ih _ n hn')

/-- The strict transform at stage `i` contains the total transform `I·𝒪_{A_i}`. -/
theorem comap_stageMap_le_strictTransformSeq (S : BlowUpSequence A) (I : A.IdealSheafData)
    (i : Fin (S.length + 1)) : I.comap (S.stageMap i) ≤ S.strictTransformSeq I i := by
  obtain ⟨n, hn⟩ := i
  exact comap_stageMap_le_strictTransformSeq_mk S I n hn

/-- A point of the strict transform lies over `V(I)`. -/
theorem stageMap_mem_support_of_mem_strictTransformSeq_support (S : BlowUpSequence A)
    (I : A.IdealSheafData) (i : Fin (S.length + 1)) {y : S.stage i}
    (hy : y ∈ (S.strictTransformSeq I i).support) : S.stageMap i y ∈ I.support := by
  have h := support_antitone (comap_stageMap_le_strictTransformSeq S I i) hy
  rw [support_comap] at h
  exact h

section OrderSeq

variable {k : Type u} [Field k] [CharZero k]

/-- The centres lie over `V(I)` — Kollár's `π_0 ⋯ π_{j−1}(Z_j) ⊂ X̄` by (21.2) in the proof of
[Kol07, Corollary 22] — the hypothesis of the identification of the end result with a component of
the centre: the centres of a blow-up
sequence of order `1` for `(I, E)` (`IsOrderSeq`; the output of `BMO_1` on `(A, I, ∅)`, which is
`BP TA` when the boundary is empty) lie over `V(I)`, since a point of a centre has `ord I ≥ 1`
(`le_ord_stageMap_of_mem_center`). -/
theorem stageMap_mem_support_of_mem_center_support_of_isOrderSeq (f : A ⟶ Spec (CommRingCat.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] {S : BlowUpSequence A} {I : A.IdealSheafData}
    {E : DivisorFamily A} (hS : S.IsOrderSeq f I E 1) (i : Fin S.length) {z : S.stage i.castSucc}
    (hz : z ∈ (S.center i).support) : S.stageMap i.castSucc z ∈ I.support :=
  (one_le_ord_iff ..).mp (by exact_mod_cast le_ord_stageMap_of_mem_center f n hS i hz)

end OrderSeq

/-! ### Regularity from smoothness -/

section Field

variable {k : Type u} [Field k]

/-- A scheme smooth over a field of characteristic zero (a perfect field) is regular. -/
theorem isRegular_of_smooth [CharZero k] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of k))
    [Smooth f] : IsRegular Z :=
  (Scheme.smooth_iff_isRegular f).mp inferInstance

end Field

/-! ### Transport across the `take` identifications -/

/-- Smoothness of `V(J) → W → V` is invariant under the heterogeneous identifications of the stages
of a truncated sequence with those of the sequence (`stage_take_mk` and the `_take_heq_mk` lemmas of
`Hironaka.Scheme.BlowUpSequence.Truncate`). -/
theorem smooth_subschemeι_comp_of_heq {A B W V : Scheme.{u}} (e : A = B) {J : A.IdealSheafData}
    {J' : B.IdealSheafData} (hJ : HEq J J') {f : A ⟶ W} {f' : B ⟶ W} (hf : HEq f f') (g : W ⟶ V)
    (h : Smooth (J'.subschemeι ≫ f' ≫ g)) : Smooth (J.subschemeι ≫ f ≫ g) := by
  subst e
  cases hJ
  cases hf
  exact h

/-! ### The end result of the truncated restriction -/

/-- The end result of the truncated restriction is smooth, general form [Kol07, Corollary 22,
proof]: for a closed immersion `emb : X → A` with kernel `I`, if the centre `Z_j` of `S` contains
the strict transform `X̄_j` of `X` and the inclusion `X̄_j → Z_j` is an open immersion, then the
composite of the restriction to `X` of the first `j` steps, followed by `emb` and a morphism
`g : A → B` under which `Z_j` is smooth, is smooth: the end result `X_j` is `X̄_j`
(`ker_pullbackStageHom`), an open subscheme of `Z_j`. -/
theorem smooth_composite_pullback_take {X B : Scheme.{u}} (S : BlowUpSequence A) (emb : X ⟶ A)
    [IsClosedImmersion emb] (g : A ⟶ B) (I : A.IdealSheafData) (hI : emb.ker = I) (j : ℕ)
    (hj : j < S.length) (hle : S.center ⟨j, hj⟩ ≤ S.strictTransformSeq I ⟨j, Nat.lt_succ_of_lt hj⟩)
    [IsOpenImmersion (inclusion hle)]
    (hsm : Smooth ((S.center ⟨j, hj⟩).subschemeι ≫ S.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ g)) :
    Smooth (((S.take j).pullback emb).composite ≫ emb ≫ g) := by
  have := hsm
  -- on the full sequence: the strict transform is smooth over the base
  have h1 : Smooth ((S.strictTransformSeq I ⟨j, Nat.lt_succ_of_lt hj⟩).subschemeι ≫
      S.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ ≫ g) :=
    smooth_subschemeι_comp_of_isOpenImmersion_inclusion hle _
  -- transport to the truncation
  have hjT : j < (S.take j).length + 1 := by rw [length_take_of_le S hj.le]; omega
  have h2 : Smooth (((S.take j).strictTransformSeq I ⟨j, hjT⟩).subschemeι ≫
      (S.take j).stageMap ⟨j, hjT⟩ ≫ g) :=
    smooth_subschemeι_comp_of_heq (stage_take_mk S j j hjT (Nat.lt_succ_of_lt hj))
      (strictTransformSeq_take_heq_mk S I j j hjT (Nat.lt_succ_of_lt hj))
      (stageMap_take_heq_mk S j j hjT (Nat.lt_succ_of_lt hj)) g h1
  have hlast : (Fin.last (S.take j).length : Fin ((S.take j).length + 1)) = ⟨j, hjT⟩ :=
    Fin.ext (length_take_of_le S hj.le)
  -- the last stage of the restriction embeds with kernel the strict transform
  have hci : IsClosedImmersion ((S.take j).pullbackStageHom emb (Fin.last _)) :=
    isClosedImmersion_pullbackStageHom (S.take j) emb (Fin.last _)
  have hker : ((S.take j).pullbackStageHom emb (Fin.last _)).ker =
      (S.take j).strictTransformSeq I (Fin.last _) := by
    rw [ker_pullbackStageHom, hI]
  -- isomorphisms are smooth (open immersions)
  have hsmι : Smooth ((S.take j).pullbackStageHom emb (Fin.last _)).toImage := by
    have := IsOpenImmersion.of_isIso ((S.take j).pullbackStageHom emb (Fin.last _)).toImage
    infer_instance
  have hsme : ∀ {Y Y' : Scheme.{u}} (e : Y = Y'), Smooth (eqToHom e) := fun e => by
    have := IsOpenImmersion.of_isIso (eqToHom e)
    infer_instance
  rw [← Category.assoc, ← pullbackLastHom_comp_composite, Category.assoc]
  change Smooth ((eqToHom _ ≫ (S.take j).pullbackStageHom emb (Fin.last _)) ≫
    (S.take j).stageMap (Fin.last _) ≫ g)
  rw [Category.assoc]
  refine MorphismProperty.comp_mem @Smooth _ _ (hsme _) ?_
  rw [← Scheme.Hom.toImage_imageι ((S.take j).pullbackStageHom emb (Fin.last _)), Category.assoc]
  refine MorphismProperty.comp_mem @Smooth _ _ hsmι ?_
  change Smooth (((S.take j).pullbackStageHom emb (Fin.last _)).ker.subschemeι ≫
    (S.take j).stageMap (Fin.last _) ≫ g)
  rw [hker, hlast]
  exact h2

section Triple

variable {k : Type u} [Field k] [CharZero k]

/-- Clause (1) of [Kol07, Theorem 36] for the affine resolution, with the smoothness of the centre
at the first index as the hypothesis: for an integral `X ↪ A` with kernel `I_X`, if the
first-centre index `j` is an index of `BP TA`, the centre `Z_j` is smooth over `k` and lies over
`V(I_X)` (Kollár's `π_0 ⋯ π_{j−1}(Z_j) ⊂ X̄` by (21.2), [Kol07, Corollary 22, proof]; for
`BP TA` with empty boundary this comes from the order property of the centres of `BMO_1`), then
the end result of `BR_affine TA emb` is smooth over `k`. -/
theorem smooth_composite_BR_affine_of_smooth_center (TA : Triple k) {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] (emb : X ⟶ TA.X.left) [IsClosedImmersion emb]
    [emb.IsOver (Spec (CommRingCat.of k))] [IsIntegral X] (hI : emb.ker = TA.I)
    (hj : firstCenterIndex (BP TA) TA.I < (BP TA).length)
    (hsm : Smooth (((BP TA).center ⟨firstCenterIndex (BP TA) TA.I, hj⟩).subschemeι ≫
      (BP TA).stageMap ⟨firstCenterIndex (BP TA) TA.I, Nat.lt_succ_of_lt hj⟩ ≫
        (TA.X.left ↘ Spec (CommRingCat.of k))))
    (hcos : ∀ y ∈ ((BP TA).center ⟨firstCenterIndex (BP TA) TA.I, hj⟩).support,
      (BP TA).stageMap ⟨firstCenterIndex (BP TA) TA.I, Nat.lt_succ_of_lt hj⟩ y ∈ TA.I.support) :
    Smooth ((BR_affine TA emb).composite ≫ (X ↘ Spec (CommRingCat.of k))) := by
  classical
  -- the first centre contains the strict transform
  have hex : ∃ n, CenterContains (BP TA) TA.I n := by
    by_contra hno
    have : firstCenterIndex (BP TA) TA.I = (BP TA).length := by
      unfold firstCenterIndex
      rw [dite_eq_right hno]
    omega
  obtain ⟨hj', hle⟩ := firstCenterIndex_of_exists hex
  have : IsNoetherian TA.X.left := (TA.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have : IsIntegral TA.I.subscheme := by
    rw [← hI]
    exact isIntegral_image emb
  have := hsm
  have hZ : IsRegular ((BP TA).center ⟨firstCenterIndex (BP TA) TA.I, hj⟩).subscheme :=
    isRegular_of_smooth (((BP TA).center ⟨firstCenterIndex (BP TA) TA.I, hj⟩).subschemeι ≫
      (BP TA).stageMap ⟨firstCenterIndex (BP TA) TA.I, Nat.lt_succ_of_lt hj⟩ ≫
        (TA.X.left ↘ Spec (CommRingCat.of k)))
  have : IsOpenImmersion (inclusion hle) :=
    isOpenImmersion_inclusion_of_firstCenterIndex (BP TA) TA.I ⟨_, hj⟩ rfl hle hZ hcos
  have h := smooth_composite_pullback_take (BP TA) emb (TA.X.left ↘ Spec (CommRingCat.of k)) TA.I hI
    _ hj hle hsm
  rwa [comp_over] at h

end Triple

end Hironaka.Resolution
