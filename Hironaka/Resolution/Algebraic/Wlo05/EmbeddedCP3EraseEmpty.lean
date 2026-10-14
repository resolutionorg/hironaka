/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.Kol07.RefineIrreducible
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Transport
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimCover
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimCoverTools
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP3 across the deletion of empty blow-ups and along a cover

Two more transports of the universal form `CP3For` of the statement CP3 of the embedded
desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates`): the convention of [Kol07, 34.1]
deletes the blow-ups with empty centre, and [Kol07, Theorem 105] builds the functor of the algorithm
on a coproduct of open immersions covering the triple. CP1 has both transports (`cp1For_eraseEmpty`,
`cp1For_of_pullback_cover`); here they are proved for CP3.

* `cp3For_eraseEmpty` — by structural induction on the sequence, as `IsOrderGeSeq.eraseEmpty`:
  `cp3For_cons_iff` splits the first centre from the tail; a non-empty first centre is kept; an
  empty one is deleted and the tail carried back along the inverse of the trivial blow-up
  (`cp3For_pullback_of_isIso`, the stalk-isomorphism transport at every stage, with the
  marked-transform identity of [Kol07, Lemma 62] under the order hypothesis, which is why the
  statement carries the order-sequence binders as `cp1For_eraseEmpty` does), the mark-`1` transform
  along the trivial blow-up being the pull-back (`markedTransform_top_left`) and the induced family
  the original one extended by an empty member (`extendsByEmpty_totalTransform_top_comap_inv`),
  which the classification ignores (`cp3For_iff_of_extendsByEmpty`, through
  `centerClassifiedAt_iff_of_embeds`).
* `cp3For_of_pullback_cover` — a point of a centre lifts to the pulled-back run
  (`surjective_pullbackStageHom`), where the centre, the marked transform ([Kol07, Lemma 62] under
  the order hypothesis) and the total transform are the pull-backs of the data of the run along the
  stage lift, whose stalk map is an isomorphism (`openImmersionCoprods_pullbackStageHom`); the
  classification descends (`centerClassifiedAt_comap_of_isIso_stalkMap`).

These transports are not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step21`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step22`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Tower` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  IdealSheafData BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-- `CP3For` on a `cons`: the first centre classified at each of its points for the starting data,
and `CP3For` for the tail with the transformed data. -/
theorem cp3For_cons_iff (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp)
    (I : X.IdealSheafData) (E : DivisorFamily X) :
    CP3For (cons X D rest) I E ↔
      (∀ q ∈ D.support, CenterClassifiedAt E I D q) ∧
        CP3For rest (I.markedTransform D 1) (E.totalTransform D) := by
  constructor
  · intro h
    refine ⟨fun q hq => h ⟨0, Nat.succ_pos _⟩ q hq, fun i q hq => ?_⟩
    exact h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ q hq
  · rintro ⟨h0, hr⟩ ⟨j, hj⟩ q hq
    cases j with
    | zero => exact h0 q hq
    | succ j => exact hr ⟨j, Nat.lt_of_succ_lt_succ hj⟩ q hq

/-- `CP3For` pulls back along an isomorphism of the ambient scheme ([Kol07, Lemma 62] for the
marked transform). -/
theorem cp3For_pullback_of_isIso {Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (S : BlowUpSequence X) (φ : Y ⟶ X) [IsIso φ]
    (I : X.IdealSheafData) (E : DivisorFamily X) (hS : S.IsOrderGeSeq f I 1 E)
    (h : CP3For S I E) : CP3For (S.pullback φ) (I.comap φ) (E.comap φ) := by
  intro i' q' hq'
  have hlen := length_pullback S φ
  have hiS : i'.val < S.length := by rw [← hlen]; exact i'.isLt
  have hc := center_pullback_mk' S φ hiS i'.isLt
  have hiso : IsIso (S.pullbackStageHom φ ⟨i'.val, Nat.lt_succ_of_lt hiS⟩) :=
    isIso_pullbackStageHom_of_isIso S φ _
  have hst : IsIso ((S.pullbackStageHom φ ⟨i'.val, Nat.lt_succ_of_lt hiS⟩).stalkMap q') :=
    ((isIso_iff_isIso_stalkMap _).mp hiso).2 q'
  have hq : S.pullbackStageHom φ ⟨i'.val, Nat.lt_succ_of_lt hiS⟩ q' ∈
      (S.center ⟨i'.val, hiS⟩).support := by
    have := hq'
    rw [hc, mem_support_comap_iff_apply] at this
    exact this
  have hY : CenterClassifiedAt (S.totalTransformSeq E ⟨i'.val, Nat.lt_succ_of_lt hiS⟩)
      (S.markedTransformSeq I 1 ⟨i'.val, Nat.lt_succ_of_lt hiS⟩) (S.center ⟨i'.val, hiS⟩)
      (S.pullbackStageHom φ ⟨i'.val, Nat.lt_succ_of_lt hiS⟩ q') := h ⟨i'.val, hiS⟩ _ hq
  have hE := totalTransformSeq_pullback_mk S φ E i'.val (Nat.lt_succ_of_lt hiS)
  have hI := IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk f n φ hS i'.val
    (Nat.lt_succ_of_lt hiS)
  have hres : CenterClassifiedAt
      ((S.totalTransformSeq E ⟨i'.val, Nat.lt_succ_of_lt hiS⟩).comap
        (S.pullbackStageHom φ ⟨i'.val, Nat.lt_succ_of_lt hiS⟩))
      ((S.markedTransformSeq I 1 ⟨i'.val, Nat.lt_succ_of_lt hiS⟩).comap
        (S.pullbackStageHom φ ⟨i'.val, Nat.lt_succ_of_lt hiS⟩))
      ((S.center ⟨i'.val, hiS⟩).comap (S.pullbackStageHom φ ⟨i'.val, Nat.lt_succ_of_lt hiS⟩)) q' :=
    centerClassifiedAt_of_comap_of_isIso_stalkMap _ hY
  rw [← hE, ← hI, ← hc] at hres
  intro n z c r σ a b hfree hb
  exact hres z c σ a b hfree hb

/-- An extension by empty components persists along the total transforms of a sequence. -/
theorem extendsByEmpty_totalTransformSeq : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    {E₁ E₂ : DivisorFamily X}, ExtendsByEmpty E₁ E₂ → ∀ i : Fin (S.length + 1),
      ExtendsByEmpty (S.totalTransformSeq E₁ i) (S.totalTransformSeq E₂ i)
  | _, nil _, _, _, h, _ => h
  | _, cons _ _ _, _, _, h, ⟨0, _⟩ => h
  | _, cons _ D rest, _, _, h, ⟨j + 1, hj⟩ =>
    extendsByEmpty_totalTransformSeq rest (h.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-- The classification sees a family only through its non-empty members. -/
theorem centerClassifiedAt_iff_of_extendsByEmpty {E₁ E₂ : DivisorFamily X}
    (hext : ExtendsByEmpty E₁ E₂) (K Z : X.IdealSheafData) (q : X) :
    CenterClassifiedAt E₁ K Z q ↔ CenterClassifiedAt E₂ K Z q := by
  obtain ⟨e, he, hcomp, htop⟩ := hext
  refine centerClassifiedAt_iff_of_embeds e he hcomp fun b hb hq => ?_
  rw [htop b hb, support_top, ← SetLike.mem_coe, Closeds.coe_bot] at hq
  exact hq

/-- `CP3For` sees a family only through its non-empty members. -/
theorem cp3For_iff_of_extendsByEmpty (S : BlowUpSequence X) (I : X.IdealSheafData)
    {E₁ E₂ : DivisorFamily X} (hext : ExtendsByEmpty E₁ E₂) : CP3For S I E₁ ↔ CP3For S I E₂ :=
  forall_congr' fun i => forall_congr' fun q => imp_congr_right fun _ =>
    centerClassifiedAt_iff_of_extendsByEmpty (extendsByEmpty_totalTransformSeq S hext i.castSucc)
      _ _ q

/-- **CP3 passes to the erased run** (the deletion of empty blow-ups of [Kol07, 34.1]; the
counterpart of `cp1For_eraseEmpty`). -/
theorem cp3For_eraseEmpty (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X)
    (hS : S.IsOrderGeSeq f I 1 E) (h : CP3For S I E) : CP3For S.eraseEmpty I E := by
  induction S with
  | nil X => exact h
  | cons X D rest ih =>
    obtain ⟨⟨hD, -, -⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E 1 D rest).1 hS
    obtain ⟨h0, hr⟩ := (cp3For_cons_iff D rest I E).1 h
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    by_cases hD' : D = ⊤
    · subst hD'
      have hiso : IsIso (⊤ : X.IdealSheafData).blowUpπ := blowUp.isIso_π_top
      rw [BlowUpSequence.eraseEmpty, dite_eq_left rfl]
      have hrest := ih ((⊤ : X.IdealSheafData).blowUpπ ≫ f) _ _ ht hr
      have key := cp3For_pullback_of_isIso ((⊤ : X.IdealSheafData).blowUpπ ≫ f) n rest.eraseEmpty
        (inv (⊤ : X.IdealSheafData).blowUpπ) _ _ (IsOrderGeSeq.eraseEmpty
            ((⊤ : X.IdealSheafData).blowUpπ ≫ f) n ht) hrest
      rw [markedTransform_top_left, ← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
        Scheme.IdealSheafData.comap_id] at key
      exact (cp3For_iff_of_extendsByEmpty _ _ (extendsByEmpty_totalTransform_top_comap_inv E)).2 key
    · rw [BlowUpSequence.eraseEmpty, dite_eq_right hD', cp3For_cons_iff]
      exact ⟨h0, ih (D.blowUpπ ≫ f) _ _ ht hr⟩

/-- **CP3 descends along a coproduct of open immersions** covering the triple ([Kol07, Theorem 105];
the counterpart of `cp1For_of_pullback_cover`). -/
theorem cp3For_of_pullback_cover (T T' : Triple k) (g : T'.X.left ⟶ T.X.left)
    (hg : openImmersionCoprods g)
    (hsurj : Function.Surjective g) (hpb : T'.IsPullbackOf T g) (S : BlowUpSequence T.X.left)
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E)
    (h : CP3For (S.pullback g) T'.I T'.E) : CP3For S T.I T.E := by
  obtain ⟨hover, hI', hE'⟩ := hpb
  have hfl : Flat g := Hironaka.Sequence.openImmersionCoprods.flat hg
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hlen := length_pullback S g
  intro i q hq
  obtain ⟨q', hq'⟩ := surjective_pullbackStageHom S g hsurj i.castSucc q
  have hiS' : i.val < (S.pullback g).length := by rw [hlen]; exact i.isLt
  have hc := center_pullback_mk' S g i.isLt hiS'
  have hq'mem : q' ∈ ((S.pullback g).center ⟨i.val, hiS'⟩).support := by
    rw [hc, mem_support_comap_iff_apply]
    have hq'' : S.pullbackStageHom g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ q' = q := hq'
    rw [hq'']
    exact hq
  have hY : CenterClassifiedAt
      ((S.pullback g).totalTransformSeq T'.E ⟨i.val, Nat.lt_succ_of_lt hiS'⟩)
      ((S.pullback g).markedTransformSeq T'.I 1 ⟨i.val, Nat.lt_succ_of_lt hiS'⟩)
      ((S.pullback g).center ⟨i.val, hiS'⟩) q' := h ⟨i.val, hiS'⟩ q' hq'mem
  have hE'' : (S.pullback g).totalTransformSeq T'.E (S.pullbackStageIdx g i.castSucc) =
      (S.totalTransformSeq T.E i.castSucc).comap (S.pullbackStageHom g i.castSucc) := by
    rw [hE']
    exact totalTransformSeq_pullback S g T.E i.castSucc
  have hI'' : (S.pullback g).markedTransformSeq T'.I 1 (S.pullbackStageIdx g i.castSucc) =
      (S.markedTransformSeq T.I 1 i.castSucc).comap (S.pullbackStageHom g i.castSucc) := by
    rw [hI']
    exact IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom (T.X.left ↘ Spec (.of k)) n' g hS
      i.castSucc
  have hcop := openImmersionCoprods_pullbackStageHom S hg i.castSucc
  have hiso := openImmersionCoprods.isIso_stalkMap hcop q'
  have hY' : CenterClassifiedAt
      ((S.totalTransformSeq T.E i.castSucc).comap (S.pullbackStageHom g i.castSucc))
      ((S.markedTransformSeq T.I 1 i.castSucc).comap (S.pullbackStageHom g i.castSucc))
      ((S.center i).comap (S.pullbackStageHom g i.castSucc)) q' := by
    rw [← hE'', ← hI'']
    rw [hc] at hY
    exact hY
  have hres : CenterClassifiedAt (S.totalTransformSeq T.E i.castSucc)
      (S.markedTransformSeq T.I 1 i.castSucc) (S.center i) (S.pullbackStageHom g i.castSucc q') :=
    centerClassifiedAt_comap_of_isIso_stalkMap (S.pullbackStageHom g i.castSucc) hY'
  rw [hq'] at hres
  intro n z c r σ a b hfree hb
  exact hres z c σ a b hfree hb

end Hironaka.Resolution
