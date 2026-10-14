/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Descent
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The proof of Theorem 105: the descent along a coproduct of open immersions and the extension

The second half of the proof of Kollár's globalization theorem [Kol07, Theorem 105]: for the
class of open immersions, Proposition 37 showed that the first centers `Z₀' ∩ Uₓᵢ` glue to a
center `Z₀ ⊂ X`, and one can "repeat the above argument" to obtain the whole blow-up sequence for
`(X, I, E)`; the conclusion is that `B` extends uniquely to a blow-up sequence functor `B̄` on
`GT` commuting with the surjections in `M`. This module proves it for
the class `openImmersionCoprods` of coproducts of open immersions. The first half (the local
cover, the kernel pair, uniqueness) is `Hironaka/Resolution/Algebraic/Kol07/Globalize.lean`; the
global case of the proof of Theorem 103 [Kol07, 104, Step 3] is the instance of this module for the
maximal contact classes of `Hironaka/Resolution/Algebraic/Kol07/MaximalContactGlobalization.lean`.

## The descent

Let `g : X' → X` be a surjective coproduct of open immersions, `ιᵢ : Uᵢ → X'` its summands, and
`S'` a blow-up sequence on `X'` whose two pullbacks to the kernel pair `X'' = X' ×_X X'` agree.
The summand inclusions composed with `g` are open immersions `ιᵢ ≫ g : Uᵢ → X` covering `X`, and
the restrictions `S'|_{Uᵢ}` agree on the overlaps `Uᵢ ×_X Uⱼ`: the overlap maps into `X''` (by
the universal property of the kernel pair, with the two projections restricting to the
projections of the overlap), and the agreement on `X''` restricts. This is exactly the descent
datum of the proof of Proposition 37 (`AgreeOnOverlaps`,
`Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Descent.lean`), so
`exists_pullback_eq_of_agreeOnOverlaps` descends the family to a sequence `S₀` on `X` with `S₀|_{Uᵢ}
= S'|_{Uᵢ}`; then `g^* S₀ = S'` because two sequences on `X'` agreeing on a nonempty covering family
of open immersions are equal (`eq_of_pullback_of_covers`). When `X'` is empty, `g` is an isomorphism
of empty schemes and `S'` pulled back along its inverse descends. The order condition and the empty
blow-up convention descend along `g`: the condition of [Kol07, Definition 66] is local on a covering
family of open immersions (`isOrderSeq_of_covers` of
`Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Local.lean`, fed the restrictions of `S'`, which
are order sequences by pullback along the open immersions `ιᵢ`), and a sequence whose pullback has
no empty centers has none (`NoEmptyCenters.of_pullback`).

## The extension

Two local covers `g₁ : T₁ → T`, `g₂ : T₂ → T` of a global triple have a fibre product `W` that is
a local triple (the hypothesis `LocalCoversFibreClosed`) with surjective projections in `M`, and
`B` commutes with both, so `p₁^* B(T₁) = B(W) = p₂^* B(T₂)` (`pullback_eq_of_localCovers`; the
kernel pair is the case `T₁ = T₂`). Hence the sequence `S` descended from one local cover
`g₀ : T₀ → T` satisfies `g^* S = B(T')` for every local cover `g : T' → T`: on `W = T' ×_T T₀`,
`p₁^* g^* S = p₂^* g₀^* S = p₂^* B(T₀) = p₁^* B(T')`, and pullback along the surjective flat `p₁`
is injective. This is `exists_globalizeSeq`; `globalize` chooses such an `S` for every nonempty
global triple and takes `nil` on the empty ones (where every sequence without empty centers is
`nil`). Its characterising lemma `globalize_seq_pullback` gives agreement with `B` on `LT ∩ GT`
through the identity cover, and commutation with a surjection `h : Y → X` in `M` through the
fibre product of the composite cover `Y' → Y → X` with a cover `X' → X`, comparing both sides
after pullback along the surjective flat `W → Y' → Y`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.BlowUpSequence

open Hironaka

variable {k : Type u} [Field k] {m : ℕ} {GT LT : Triple k → Prop}

open Hironaka.Sequence AlgebraicGeometry Scheme

/-! ### Descent of a sequence along a surjective coproduct of open immersions -/

/-- A sequence on the source of a surjective coproduct of open immersions whose pullbacks to the
kernel pair agree descends to the target (the proof of [Kol07, Theorem 105], "we can repeat the
above argument … and eventually get the whole blow-up sequence"): the descent of Proposition 37
on the summand family, then locality on `X'`. -/
theorem exists_pullback_eq_of_kernelPair {X' X : Scheme.{u}} (g : X' ⟶ X)
    (hg : openImmersionCoprods g) (hs : Function.Surjective g) {X'' : Scheme.{u}}
    (τ₁ τ₂ : X'' ⟶ X') (sq : IsPullback τ₁ τ₂ g g) (S' : BlowUpSequence X')
    (h : S'.pullback τ₁ = S'.pullback τ₂) : ∃ S : BlowUpSequence X, S.pullback g = S' := by
  obtain ⟨σ, U, ι, hc, hι⟩ := hg
  have hιo : ∀ i, IsOpenImmersion (ι i) := isOpenImmersion_of_isColimit_cofan ι hc
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · have hX' : IsEmpty X' := ⟨fun y => by
      obtain ⟨i, -, -⟩ := exists_eq_of_isColimit_cofan ι hc y
      exact hσ.false i⟩
    have hX : IsEmpty X := ⟨fun x => by
      obtain ⟨y, -⟩ := hs x
      exact hX'.false y⟩
    refine ⟨S'.pullback (inv g), ?_⟩
    rw [← pullback_comp, IsIso.hom_inv_id, pullback_id]
  · have hcov : ∀ x, ∃ i w, (ι i ≫ g) w = x := fun x => by
      obtain ⟨y, rfl⟩ := hs x
      obtain ⟨i, w, rfl⟩ := exists_eq_of_isColimit_cofan ι hc y
      exact ⟨i, w, Scheme.Hom.comp_apply _ _ _⟩
    have hc' : AgreeOnOverlaps (fun i => ι i ≫ g) (fun i => S'.pullback (ι i)) := by
      intro i j
      have w : (Limits.pullback.fst (ι i ≫ g) (ι j ≫ g) ≫ ι i) ≫ g =
          (Limits.pullback.snd (ι i ≫ g) (ι j ≫ g) ≫ ι j) ≫ g := by
        rw [Category.assoc, Category.assoc, Limits.pullback.condition]
      let l := sq.lift (Limits.pullback.fst (ι i ≫ g) (ι j ≫ g) ≫ ι i)
        (Limits.pullback.snd (ι i ≫ g) (ι j ≫ g) ≫ ι j) w
      have e1 : Limits.pullback.fst (ι i ≫ g) (ι j ≫ g) ≫ ι i = l ≫ τ₁ := (sq.lift_fst _ _ w).symm
      have e2 : Limits.pullback.snd (ι i ≫ g) (ι j ≫ g) ≫ ι j = l ≫ τ₂ := (sq.lift_snd _ _ w).symm
      calc (S'.pullback (ι i)).pullback (Limits.pullback.fst (ι i ≫ g) (ι j ≫ g))
          = S'.pullback (Limits.pullback.fst (ι i ≫ g) (ι j ≫ g) ≫ ι i) := (pullback_comp _ _
            _).symm
        _ = (S'.pullback τ₁).pullback l := by rw [e1, pullback_comp]
        _ = (S'.pullback τ₂).pullback l := by rw [h]
        _ = S'.pullback (Limits.pullback.snd (ι i ≫ g) (ι j ≫ g) ≫ ι j) := by rw [e2, pullback_comp]
        _ = (S'.pullback (ι j)).pullback (Limits.pullback.snd (ι i ≫ g) (ι j ≫ g)) :=
          pullback_comp _ _ _
    obtain ⟨S₀, hS₀⟩ := Hironaka.Sequence.exists_pullback_eq_of_agreeOnOverlaps
      (fun i => ι i ≫ g) hcov (fun i => S'.pullback (ι i)) hc'
    refine ⟨S₀, eq_of_pullback_of_covers (S₀.pullback g) S' ι
      (fun y => exists_eq_of_isColimit_cofan ι hc y) fun i => ?_⟩
    rw [← pullback_comp, hS₀ i]

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace Hironaka

variable {k : Type u} [Field k] {m : ℕ} {GT LT : Triple k → Prop}

open Hironaka.Sequence AlgebraicGeometry Scheme

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k] {m : ℕ} {GT LT : Triple k → Prop}

open Hironaka.Sequence AlgebraicGeometry Scheme

open AlgebraicGeometry Scheme

/-! ### The descended sequence is a smooth blow-up sequence of order `m` -/

/-- The descended sequence is a smooth blow-up sequence of order `m` for `T` (the condition of
[Kol07, Definition 66] is local on the summand family, `isOrderSeq_of_covers`, the restrictions
of `S'` being order sequences by pullback along the open immersions `ιᵢ`) with no empty centers
(`NoEmptyCenters.of_pullback`). -/
theorem exists_isOrderSeq_pullback_eq_of_kernelPair [CharZero k] {T T' : Triple k}
    {g : T'.X.left ⟶ T.X.left} (hg : openImmersionCoprods g) (hs : Function.Surjective g)
    (hp : T'.IsPullbackOf T g) {X'' : Scheme.{u}} (τ₁ τ₂ : X'' ⟶ T'.X.left)
    (sq : IsPullback τ₁ τ₂ g g)
    (S' : BlowUpSequence T'.X.left)
    (hS' : S'.IsOrderSeq (T'.X.left ↘ Spec (CommRingCat.of k)) T'.I T'.E m)
    (hne : S'.NoEmptyCenters) (h : S'.pullback τ₁ = S'.pullback τ₂) :
    ∃ S : BlowUpSequence T.X.left, S.IsOrderSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.E m ∧
      S.NoEmptyCenters ∧ S.pullback g = S' := by
  obtain ⟨S, hS⟩ := BlowUpSequence.exists_pullback_eq_of_kernelPair g hg hs τ₁ τ₂ sq S' h
  refine ⟨S, ?_, NoEmptyCenters.of_pullback g (hS ▸ hne), hS⟩
  obtain ⟨σ, U, ι, hc, hι⟩ := hg
  have hιo : ∀ i, IsOpenImmersion (ι i) := isOpenImmersion_of_isColimit_cofan ι hc
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  have hcov : ∀ x, ∃ i w, (ι i ≫ g) w = x := fun x => by
    obtain ⟨y, rfl⟩ := hs x
    obtain ⟨i, w, rfl⟩ := exists_eq_of_isColimit_cofan ι hc y
    exact ⟨i, w, Scheme.Hom.comp_apply _ _ _⟩
  refine isOrderSeq_of_covers S (T.X.left ↘ Spec (CommRingCat.of k)) n
    (fun i => ι i ≫ g) hcov T.I T.E fun i => ?_
  have := hιo i
  have h1 := IsOrderSeq.pullback (T'.X.left ↘ Spec (CommRingCat.of k)) n' (ι i) (d := 0) hS'
  rw [pullback_comp, hS, Category.assoc, hp.1, Scheme.IdealSheafData.comap_comp,
    DivisorFamily.comap_comp, ← hp.2.1, ← hp.2.2]
  exact h1

/-! ### The fibre product of two local covers -/

/-- The fibre product of two local `M`-covers of a global triple, as a local triple (the
hypothesis `LocalCoversFibreClosed`) whose projections are surjective members of `M` and along
both of which it carries the pullback data; `exists_kernelPair` is the case `T₁ = T₂`. -/
theorem exists_fibreTriple [CharZero k] (hF : LocalCoversFibreClosed openImmersionCoprods GT LT)
    {T T₁ T₂ : Triple k} {g₁ : T₁.X.left ⟶ T.X.left} {g₂ : T₂.X.left ⟶ T.X.left}
    (hc₁ : IsLocalCover openImmersionCoprods GT LT T T₁ g₁)
    (hc₂ : IsLocalCover openImmersionCoprods GT LT T T₂ g₂) :
    ∃ (W : Triple k) (p₁ : W.X.left ⟶ T₁.X.left) (p₂ : W.X.left ⟶ T₂.X.left),
      IsPullback p₁ p₂ g₁ g₂ ∧ W.IsPullbackOf T₁ p₁ ∧ W.IsPullbackOf T₂ p₂ ∧
      openImmersionCoprods p₁ ∧ openImmersionCoprods p₂ ∧
      Function.Surjective p₁ ∧ Function.Surjective p₂ ∧ LT W := by
  obtain ⟨hT, hT₁, hM₁, hs₁, hp₁⟩ := hc₁
  obtain ⟨-, hT₂, hM₂, hs₂, hp₂⟩ := hc₂
  have sq : IsPullback (Limits.pullback.fst g₁ g₂) (Limits.pullback.snd g₁ g₂) g₁ g₂ :=
    IsPullback.of_hasPullback g₁ g₂
  have hMp₁ : openImmersionCoprods (Limits.pullback.fst g₁ g₂) :=
    isStableUnderBaseChange_openImmersionCoprods.of_isPullback sq.flip hM₂
  have hMp₂ : openImmersionCoprods (Limits.pullback.snd g₁ g₂) :=
    isStableUnderBaseChange_openImmersionCoprods.of_isPullback sq hM₁
  have hsp₁ : Function.Surjective (Limits.pullback.fst g₁ g₂) := fun y => by
    obtain ⟨y₂, hy₂⟩ := hs₂ (g₁ y)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g₁) (g := g₂) y y₂ hy₂.symm
    exact ⟨z, hz⟩
  have hsp₂ : Function.Surjective (Limits.pullback.snd g₁ g₂) := fun y => by
    obtain ⟨y₁, hy₁⟩ := hs₁ (g₂ y)
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := g₁) (g := g₂) y₁ y hy₁
    exact ⟨z, hz⟩
  have hsm : Smooth (Limits.pullback.fst g₁ g₂) := openImmersionCoprods.smooth hMp₁
  have hsep : IsSeparated (Limits.pullback.fst g₁ g₂) := openImmersionCoprods_isSeparated hMp₁
  have het : Etale (Limits.pullback.fst g₁ g₂) := openImmersionCoprods_etale _ hMp₁
  let _ : (Limits.pullback g₁ g₂).Over (Spec (CommRingCat.of k)) :=
    ⟨Limits.pullback.fst g₁ g₂ ≫ (T₁.X.left ↘ Spec (CommRingCat.of k))⟩
  have _ : (Limits.pullback.fst g₁ g₂).IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have hqc : QuasiCompact g₂ := by
    have : QuasiCompact (g₂ ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := by
      rw [hp₂.1]
      infer_instance
    exact QuasiCompact.of_comp g₂ (T.X.left ↘ Spec (CommRingCat.of k))
  have hcpt : CompactSpace T₁.X.left :=
    QuasiCompact.compactSpace_of_compactSpace (T₁.X.left ↘ Spec (CommRingCat.of k))
  have : LocallyOfFiniteType ((Limits.pullback g₁ g₂) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs
      (LocallyOfFiniteType (Limits.pullback.fst g₁ g₂ ≫ (T₁.X.left ↘ Spec (CommRingCat.of k))))
  have : IsSeparated ((Limits.pullback g₁ g₂) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (IsSeparated (Limits.pullback.fst g₁ g₂ ≫
      (T₁.X.left ↘ Spec (CommRingCat.of k))))
  have : QuasiCompact ((Limits.pullback g₁ g₂) ↘ Spec (CommRingCat.of k)) := inferInstance
  have hY : ∃ n : ℕ,
      SmoothOfRelativeDimension n ((Limits.pullback g₁ g₂) ↘ Spec (CommRingCat.of k)) := by
    obtain ⟨n, hn⟩ := T₁.smoothOfRelativeDimension
    exact ⟨n, by
      simpa using smoothOfRelativeDimension_comp 0 n (Limits.pullback.fst g₁ g₂)
        (T₁.X.left ↘ Spec (CommRingCat.of k))⟩
  have hW₁ := isPullbackOf_pullback T₁ hY (Limits.pullback.fst g₁ g₂)
  have hcond : Limits.pullback.fst g₁ g₂ ≫ g₁ = Limits.pullback.snd g₁ g₂ ≫ g₂ :=
    Limits.pullback.condition
  have hW₂ : (Triple.pullback T₁ hY (Limits.pullback.fst g₁ g₂)).IsPullbackOf T₂
      (Limits.pullback.snd g₁ g₂) := by
    refine ⟨?_, ?_, ?_⟩
    · change Limits.pullback.snd g₁ g₂ ≫ (T₂.X.left ↘ Spec (CommRingCat.of k)) =
        Limits.pullback.fst g₁ g₂ ≫ (T₁.X.left ↘ Spec (CommRingCat.of k))
      rw [← hp₁.1, ← hp₂.1, ← Category.assoc, ← Category.assoc, hcond]
    · change T₁.I.comap (Limits.pullback.fst g₁ g₂) = T₂.I.comap (Limits.pullback.snd g₁ g₂)
      rw [hp₁.2.1, hp₂.2.1, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        hcond]
    · change T₁.E.comap (Limits.pullback.fst g₁ g₂) = T₂.E.comap (Limits.pullback.snd g₁ g₂)
      rw [hp₁.2.2, hp₂.2.2, ← DivisorFamily.comap_comp, ← DivisorFamily.comap_comp, hcond]
  refine ⟨Triple.pullback T₁ hY (Limits.pullback.fst g₁ g₂), Limits.pullback.fst g₁ g₂,
    Limits.pullback.snd g₁ g₂, sq, hW₁, hW₂, hMp₁, hMp₂, hsp₁, hsp₂, ?_⟩
  exact hF ⟨hT, hT₁, hM₁, hs₁, hp₁⟩ ⟨hT, hT₂, hM₂, hs₂, hp₂⟩ sq hW₁

end AlgebraicGeometry.Triple

namespace Hironaka

variable {k : Type u} [Field k] {m : ℕ} {GT LT : Triple k → Prop}

open Hironaka.Sequence AlgebraicGeometry Scheme

namespace OrderSeqAssignment

open AlgebraicGeometry Scheme

/-! ### The extension `B̄` -/

/-- Two local `M`-covers of a global triple give the same sequence on their fibre product:
`p₁^* B(T₁) = B(W) = p₂^* B(T₂)` (the compatibility (105.4) of [Kol07, Theorem 105] for two
covers). -/
theorem pullback_eq_of_localCovers (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) {T T₁ T₂ W : Triple k}
    {g₁ : T₁.X.left ⟶ T.X.left} {g₂ : T₂.X.left ⟶ T.X.left} {p₁ : W.X.left ⟶ T₁.X.left}
    {p₂ : W.X.left ⟶ T₂.X.left}
    (hc₁ : Triple.IsLocalCover openImmersionCoprods GT LT T T₁ g₁)
    (hc₂ : Triple.IsLocalCover openImmersionCoprods GT LT T T₂ g₂) (hW₁ : W.IsPullbackOf T₁ p₁)
    (hW₂ : W.IsPullbackOf T₂ p₂) (hM₁ : openImmersionCoprods p₁) (hM₂ : openImmersionCoprods p₂)
    (hs₁ : Function.Surjective p₁) (hs₂ : Function.Surjective p₂) (hW : LT W) :
    (B.seq T₁ hc₁.2.1).pullback p₁ = (B.seq T₂ hc₂.2.1).pullback p₂ :=
  (hB T₁ W p₁ hM₁ hs₁ hW₁ hc₁.2.1 hW).symm.trans (hB T₂ W p₂ hM₂ hs₂ hW₂ hc₂.2.1 hW)

/-- The sequence descended along one local cover of a nonempty global triple pulls back to `B`
along every local cover (compared on the fibre product of the two covers, pullback along the
surjective flat projection being injective), and is a smooth blow-up sequence of order `m`
without empty centers. -/
theorem exists_globalizeSeq [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) {T : Triple k} (hG : GT T)
    [Nonempty T.X.left] :
    ∃ S : BlowUpSequence T.X.left, S.IsOrderSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.E m ∧
      S.NoEmptyCenters ∧ ∀ (T' : Triple k) (g : T'.X.left ⟶ T.X.left)
        (hc : Triple.IsLocalCover openImmersionCoprods GT LT T T' g), S.pullback g = B.seq T'
          hc.2.1 := by
  obtain ⟨T₀, g₀, hc₀⟩ := Triple.exists_isLocalCover D hG
  obtain ⟨T'', τ₁, τ₂, sq, h₁, h₂, hM₁, hM₂, hs₁, hs₂, hT''⟩ := Triple.exists_kernelPair hF hc₀
  obtain ⟨e₁, e₂⟩ := pullback_eq_of_kernelPair B hB hM₁ hM₂ hs₁ hs₂ h₁ h₂ hc₀.2.1 hT''
  obtain ⟨S, hS, hne, hS₀⟩ := Triple.exists_isOrderSeq_pullback_eq_of_kernelPair hc₀.2.2.1
    hc₀.2.2.2.1 hc₀.2.2.2.2 τ₁ τ₂ sq (B.seq T₀ hc₀.2.1) (B.isOrderSeq T₀ hc₀.2.1)
    (B.noEmptyCenters T₀ hc₀.2.1) (e₁.trans e₂)
  refine ⟨S, hS, hne, fun T' g hc => ?_⟩
  obtain ⟨W, p₁, p₂, sqW, hW₁, hW₂, hMp₁, hMp₂, hsp₁, hsp₂, hW⟩ := Triple.exists_fibreTriple hF hc
    hc₀
  have key := pullback_eq_of_localCovers B hB hc hc₀ hW₁ hW₂ hMp₁ hMp₂ hsp₁ hsp₂ hW
  have : Flat p₁ := openImmersionCoprods.flat hMp₁
  apply pullback_injective_of_surjective p₁ hsp₁
  rw [key, ← hS₀, ← pullback_comp, ← pullback_comp, sqW.w]

open scoped Classical in
/-- The sequence `B̄(T)`: on a nonempty global triple a sequence of `exists_globalizeSeq`, on an
empty one `nil`. -/
noncomputable def globalizeSeq [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT
LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) (T : Triple k) (hG : GT T) :
    BlowUpSequence T.X.left :=
  if hne : Nonempty T.X.left then Classical.choose (have := hne; exists_globalizeSeq
    (T := T) D hF B hB hG)
  else BlowUpSequence.nil T.X.left

theorem globalizeSeq_eq_choose [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT
LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) {T : Triple k} (hG : GT T)
    [hne : Nonempty T.X.left] :
    globalizeSeq D hF B hB T hG = Classical.choose (exists_globalizeSeq (T := T) D hF B hB hG) := by
  unfold globalizeSeq
  rw [dite_eq_left hne]

theorem globalizeSeq_of_isEmpty [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT
LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) {T : Triple k} (hG : GT T)
    [IsEmpty T.X.left] : globalizeSeq D hF B hB T hG = BlowUpSequence.nil T.X.left := by
  unfold globalizeSeq
  rw [dite_eq_right (not_nonempty_iff.mpr ‹_›)]

theorem globalizeSeq_isOrderSeq [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT
LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) {T : Triple k} (hG : GT T) :
    (globalizeSeq D hF B hB T hG).IsOrderSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.E m := by
  by_cases hne : Nonempty T.X.left
  · rw [globalizeSeq_eq_choose D hF B hB hG]
    exact (Classical.choose_spec (exists_globalizeSeq (T := T) D hF B hB hG)).1
  · have : IsEmpty T.X.left := not_nonempty_iff.mp hne
    rw [globalizeSeq_of_isEmpty D hF B hB hG]
    exact isOrderSeq_nil (f := T.X.left ↘ Spec (CommRingCat.of k)) (I := T.I) (E := T.E) (m := m)

theorem globalizeSeq_noEmptyCenters [CharZero k]
    (D : Triple.GlobalizationData openImmersionCoprods GT LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) {T : Triple k} (hG : GT T) :
    (globalizeSeq D hF B hB T hG).NoEmptyCenters := by
  by_cases hne : Nonempty T.X.left
  · rw [globalizeSeq_eq_choose D hF B hB hG]
    exact (Classical.choose_spec (exists_globalizeSeq (T := T) D hF B hB hG)).2.1
  · have : IsEmpty T.X.left := not_nonempty_iff.mp hne
    rw [globalizeSeq_of_isEmpty D hF B hB hG]
    intro i
    exact i.elim0

/-- The extension `B̄` of `B` to the global triples [Kol07, Theorem 105]: on a nonempty `T`, a
sequence descended from `B` along a local cover (`exists_globalizeSeq`); on an empty `T.X.left`,
`nil`. -/
noncomputable def globalize [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) : OrderSeqAssignment k m GT where
  seq := globalizeSeq D hF B hB
  isOrderSeq _ hG := globalizeSeq_isOrderSeq D hF B hB hG
  noEmptyCenters _ hG := globalizeSeq_noEmptyCenters D hF B hB hG

/-- The characterising property of `B̄`: along every local `M`-cover `g : T' → T`,
`g^* B̄(T) = B(T')`. -/
theorem globalize_seq_pullback [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT
LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) {T T' : Triple k}
    {g : T'.X.left ⟶ T.X.left}
    (hc : Triple.IsLocalCover openImmersionCoprods GT LT T T' g) :
    ((globalize D hF B hB).seq T hc.1).pullback g = B.seq T' hc.2.1 := by
  change (globalizeSeq D hF B hB T hc.1).pullback g = _
  by_cases hne : Nonempty T.X.left
  · rw [globalizeSeq_eq_choose D hF B hB hc.1]
    exact (Classical.choose_spec (exists_globalizeSeq (T := T) D hF B hB hc.1)).2.2 T' g hc
  · have hX : IsEmpty T.X.left := not_nonempty_iff.mp hne
    have hX' : IsEmpty T'.X.left := ⟨fun y => hX.false (g y)⟩
    rw [globalizeSeq_of_isEmpty D hF B hB hc.1, pullback_nil,
      BlowUpSequence.eq_nil_of_noEmptyCenters _ (B.noEmptyCenters T' hc.2.1)]

/-- `B̄` agrees with `B` on the local triples that are global (the identity is a local cover). -/
theorem globalize_seq_of_mem [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) {T : Triple k} (hL : LT T) (hG : GT T) :
    (globalize D hF B hB).seq T hG = B.seq T hL := by
  have hc : Triple.IsLocalCover openImmersionCoprods GT LT T T (𝟙 T.X.left) :=
    ⟨hG, hL, openImmersionCoprods_of_isOpenImmersion _, Function.surjective_id,
      ⟨Category.id_comp _, (Scheme.IdealSheafData.comap_id _).symm, (DivisorFamily.comap_id
        _).symm⟩⟩
  have := globalize_seq_pullback D hF B hB hc
  rwa [pullback_id] at this

/-- `B̄` commutes with the surjections in `M` [Kol07, Theorem 105]: for a surjection `h : Y → X`
in `M` with the pullback data, both `B̄(Y)` and `h^* B̄(X)` pull back to `B(W)` on the fibre
product `W` of the composite cover `Y' → Y → X` with a cover `X' → X`, and pullback along the
surjective flat `W → Y' → Y` is injective. -/
theorem globalize_commutesWithSurjectionsIn [CharZero k]
    (D : Triple.GlobalizationData openImmersionCoprods GT LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) :
    (globalize D hF B hB).CommutesWithSurjectionsIn openImmersionCoprods := by
  intro X Y h hM hs hp hGX hGY
  by_cases hne : Nonempty Y.X.left
  · have hneX : Nonempty X.X.left := ⟨h hne.some⟩
    obtain ⟨Y', gY, hcY⟩ := Triple.exists_isLocalCover D hGY
    obtain ⟨X', gX, hcX⟩ := Triple.exists_isLocalCover D hGX
    have hcYX : Triple.IsLocalCover openImmersionCoprods GT LT X Y' (gY ≫ h) :=
      ⟨hGX, hcY.2.1, openImmersionCoprods_comp _ _ hcY.2.2.1 hM, hs.comp hcY.2.2.2.1,
        hp.comp hcY.2.2.2.2⟩
    obtain ⟨W, p₁, p₂, sqW, hW₁, hW₂, hMp₁, hMp₂, hsp₁, hsp₂, hW⟩ :=
      Triple.exists_fibreTriple hF hcYX hcX
    have key := pullback_eq_of_localCovers B hB hcYX hcX hW₁ hW₂ hMp₁ hMp₂ hsp₁ hsp₂ hW
    have hflat : Flat (p₁ ≫ gY) :=
      have := openImmersionCoprods.flat hMp₁
      have := openImmersionCoprods.flat hcY.2.2.1
      inferInstance
    apply pullback_injective_of_surjective (p₁ ≫ gY) (hcY.2.2.2.1.comp hsp₁)
    calc ((globalize D hF B hB).seq Y hGY).pullback (p₁ ≫ gY)
        = (((globalize D hF B hB).seq Y hGY).pullback gY).pullback p₁ := pullback_comp _ _ _
      _ = (B.seq Y' hcY.2.1).pullback p₁ := by rw [globalize_seq_pullback D hF B hB hcY]
      _ = (B.seq X' hcX.2.1).pullback p₂ := key
      _ = (((globalize D hF B hB).seq X hGX).pullback gX).pullback p₂ := by
          rw [globalize_seq_pullback D hF B hB hcX]
      _ = ((globalize D hF B hB).seq X hGX).pullback (p₂ ≫ gX) := (pullback_comp _ _ _).symm
      _ = ((globalize D hF B hB).seq X hGX).pullback ((p₁ ≫ gY) ≫ h) := by
          rw [Category.assoc, sqW.w]
      _ = (((globalize D hF B hB).seq X hGX).pullback h).pullback (p₁ ≫ gY) := pullback_comp _ _ _
  · have hX : IsEmpty Y.X.left := not_nonempty_iff.mp hne
    have hX' : IsEmpty X.X.left := ⟨fun x => by
      obtain ⟨y, -⟩ := hs x
      exact hX.false y⟩
    rw [BlowUpSequence.eq_nil_of_noEmptyCenters _ ((globalize D hF B hB).noEmptyCenters X hGX),
      BlowUpSequence.eq_nil_of_noEmptyCenters _ ((globalize D hF B hB).noEmptyCenters Y hGY),
      pullback_nil]

/-- The existence statement of [Kol07, Theorem 105]: `B̄ := globalize` extends `B` and commutes
with the surjections in `M`. -/
theorem exists_globalization [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT LT)
    (hF : Triple.LocalCoversFibreClosed openImmersionCoprods GT LT) (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) :
    ∃ B' : OrderSeqAssignment k m GT,
      (∀ (T : Triple k) (hL : LT T) (hG : GT T), B'.seq T hG = B.seq T hL) ∧
        B'.CommutesWithSurjectionsIn openImmersionCoprods :=
  ⟨globalize D hF B hB, fun _ hL hG => globalize_seq_of_mem D hF B hB hL hG,
    globalize_commutesWithSurjectionsIn D hF B hB⟩

end OrderSeqAssignment

end Hironaka
