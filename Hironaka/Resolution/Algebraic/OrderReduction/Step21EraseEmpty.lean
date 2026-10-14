/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferent
public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
public import Hironaka.Resolution.Algebraic.OrderReduction.Step21BoundaryClearing
public import Hironaka.Scheme.BlowUpSequence.EraseEmptyConcat
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeqFunctor
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step22RestrictToHypersurface
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.1 of order reduction under an arbitrary smooth morphism

Clause (2) of [Kol07, Theorem 103] with the second clause of [Kol07, 34.1]: for an arbitrary
smooth morphism `h : Y ⟶ X`, `BO^{h⁻¹H}_{n,m}(Y, h^*I, h⁻¹E)` is the pull-back of
`BO^H_{n,m}(X, I, E)` with the empty blow-ups deleted. This module proves it for Step 2.1 of the
proof ([Kol07, 104, Step 2.1], the sequence `step21Seq`), round by round through the concatenation
(`pullback_concat`, `eraseEmpty_concat`): after `j` rounds the Step 2.1 sequence of the pulled-back
data is the erased pull-back of the Step 2.1 sequence, and at the next round

* the triple induced by the erased pull-back `(S.pullback h).eraseEmpty` at its last stage is, up
  to its boundary, the exact pull-back of the triple induced by `S.pullback h` along the last-stage
  isomorphism `eraseEmptyLastHom` (`isPullbackOf_inducedErased`: the ideal by
  `weakTransformSeq_eraseEmpty_last`, the composite map by `eraseEmptyLastHom_comp_composite`);
* its boundary is the exact pull-back's boundary with the unit-ideal members deleted, the original
  positions preserved (`eraseEmbeds_eraseEmpty`, `monoEquivOfFin_totalTransformSeq_of_lt`), so the
  hypothesis `hind : BDFamily.IndifferentToEmptyMembers bd`, the indifference of the
  boundary-clearing data to empty boundary members
  (`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferent.lean`), identifies the value of
  the functor of [Kol07, Lemma 102] on the erased triple with its value on the exact pull-back;
* the second clause of [Kol07, 34.1] for Lemma 102 (the field `commutesWithSmooth`) on the exact
  pull-back along the smooth composite `eraseEmptyLastHom ≫ pullbackLastHom`, then `pullback_comp`
  and `eraseEmpty_pullback_of_flat_surjective` along the isomorphism.

Step 2.2 and the maximal-contact case are treated in
`Hironaka/Resolution/Algebraic/OrderReduction/Step2EraseEmpty.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence Hironaka.Sequence

namespace Hironaka.BO

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

section Induced

omit [CharZero k] in
/-- The boundary-clearing class `BDClass n m j` is closed under exact pull-back along a smooth
morphism with source of dimension `≤ n`: the maximal order does not rise
(`maxOrd_comap_le_of_smooth`) and the index set is unchanged. -/
theorem bdClass_of_isPullbackOf {T T' : Triple k} {j : ℕ} (g : T'.X.left ⟶ T.X.left) [Smooth g]
    (hpb : T'.IsPullbackOf T g) (hT : Triple.BDClass n m j T) (hn' : T'.HasDimLE n) :
    Triple.BDClass n m j T' := by
  refine ⟨hn', ?_, ?_⟩
  · rw [hpb.2.1]
    exact (maxOrd_comap_le_of_smooth g T.I).trans hT.2.1
  · have hcard : Fintype.card T'.E.ι = Fintype.card T.E.ι :=
      Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι hpb.2.2))
    exact hcard ▸ hT.2.2

/-- The inverse image of the boundary induced by `P` along the last-stage isomorphism has normal
crossings (`isSnc_comap_of_smooth`; the instances are supplied explicitly at the stage typing). -/
theorem isSnc_induced_E_comap_eraseEmptyLastHom {T' : Triple k} (P : BlowUpSequence T'.X.left)
    (hP : P.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m) :
    ((T'.induced P hP (Fin.last _)).E.comap P.eraseEmptyLastHom).IsSnc := by
  have h₂₀ : Smooth P.eraseEmptyLastHom := inferInstance
  exact @isSnc_comap_of_smooth _ _ k _ _ ((T'.induced P hP (Fin.last _)).X.left ↘ Spec (.of k))
    (T'.induced P hP (Fin.last _)).smooth P.eraseEmptyLastHom h₂₀ _
    (T'.induced P hP (Fin.last _)).isSnc

/-- The triple induced by the erased sequence `P.eraseEmpty` at its last stage, with its boundary
replaced by the inverse image, along the last-stage isomorphism, of the boundary induced by `P`:
the exact pull-back of the triple induced by `P` (`isPullbackOf_inducedErased`). The boundary
induced by `P.eraseEmpty` itself is this one with the unit-ideal members deleted. -/
noncomputable def inducedErased {T' : Triple k} (P : BlowUpSequence T'.X.left)
    (hP : P.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : P.eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m) : Triple k :=
  { T'.induced P.eraseEmpty hP' (Fin.last _) with
    E := (T'.induced P hP (Fin.last _)).E.comap P.eraseEmptyLastHom
    isSnc := isSnc_induced_E_comap_eraseEmptyLastHom P hP }

/-- Restoring the erased boundary in `inducedErased` gives back the triple induced by
`P.eraseEmpty` (structure eta). -/
theorem inducedErased_update_eq {T' : Triple k} (P : BlowUpSequence T'.X.left)
    (hP : P.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : P.eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m) :
    ({ inducedErased P hP hP' with
        E := (T'.induced P.eraseEmpty hP' (Fin.last _)).E
        isSnc := (T'.induced P.eraseEmpty hP' (Fin.last _)).isSnc } : Triple k) =
      T'.induced P.eraseEmpty hP' (Fin.last _) := rfl

/-- `inducedErased P` is the exact pull-back of the triple induced by `P` along the last-stage
isomorphism (`weakTransformSeq_eraseEmpty_last`, `eraseEmptyLastHom_comp_composite`). -/
theorem isPullbackOf_inducedErased {T' : Triple k} {P : BlowUpSequence T'.X.left}
    (hP : P.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : P.eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m) :
    (inducedErased P hP hP').IsPullbackOf (T'.induced P hP (Fin.last _)) P.eraseEmptyLastHom := by
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  refine ⟨?_, ?_, rfl⟩
  · change P.eraseEmptyLastHom ≫ (P.stageMap (Fin.last _) ≫ (T'.X.left ↘ Spec (.of k))) =
      P.eraseEmpty.stageMap (Fin.last _) ≫ (T'.X.left ↘ Spec (.of k))
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ (T'.X.left ↘ Spec (.of k))) (eraseEmptyLastHom_comp_composite P))
  · exact weakTransformSeq_eraseEmpty_last P (T'.X.left ↘ Spec (.of k)) n' T'.I T'.E m hP

/-- The smooth structure map of `inducedErased P` to the triple induced by `S` at the last stage:
the last-stage isomorphism followed by the last-stage lift of `h`. -/
theorem smooth_eraseEmptyLastHom_comp_pullbackLastHom {T T' : Triple k} (h : T'.X.left ⟶ T.X.left)
    [Smooth h] {S : BlowUpSequence T.X.left} (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m) :
    @Smooth (inducedErased (S.pullback h) hP hP').X.left (T.induced S hS (Fin.last _)).X.left
      ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h) := by
  have hsm₁ : Smooth (S.pullbackLastHom h) := smooth_pullbackLastHom S h
  have hsm₀ : Smooth ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h) := inferInstance
  exact hsm₀

/-- `inducedErased (S.pullback h)` is the exact pullback of the triple induced by `S` along
`eraseEmptyLastHom ≫ pullbackLastHom`. -/
theorem isPullbackOf_inducedErased_pullback {T T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m) :
    (inducedErased (S.pullback h) hP hP').IsPullbackOf (T.induced S hS (Fin.last _))
      ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h) :=
  (isPullbackOf_induced_last h hpb hS hP).comp (isPullbackOf_inducedErased hP hP')

/-- `inducedErased (S.pullback h)` lies in the boundary-clearing class at every position of the
original family. -/
theorem bdClass_inducedErased {T T' : Triple k} (hn : T.HasDimLE n) (hmax : T.I.maxOrd ≤ m)
    (hn' : T'.HasDimLE n) (h : T'.X.left ⟶ T.X.left) [Smooth h] (hpb : T'.IsPullbackOf T h)
    {S : BlowUpSequence T.X.left} (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hne : S.NoEmptyCenters) (hP : (S.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m) {j : ℕ}
    (hj : j < Fintype.card T.E.ι) :
    Triple.BDClass n m j (inducedErased (S.pullback h) hP hP') := by
  have hsm := smooth_eraseEmptyLastHom_comp_pullbackLastHom h hS hP hP'
  exact bdClass_of_isPullbackOf _ (isPullbackOf_inducedErased_pullback h hpb hS hP hP')
    (bdClass_induced_last T hn hmax hS hne hj) (hasDimLE_induced_last T' hn' hP')

/-- The original position `j` is carried to the original position `j` by an embedding compatible
with `originalIdx` (`monoEquivOfFin_totalTransformSeq_of_lt`). -/
theorem nthIdx_eraseEmpty_eq_of_originalIdx {Z : Scheme.{u}} (P : BlowUpSequence Z)
    (E : DivisorFamily Z)
    (e : (P.eraseEmpty.totalTransformSeq E (Fin.last _)).ι ↪o
      (P.totalTransformSeq E (Fin.last _)).ι)
    (ho : ∀ a, e (P.eraseEmpty.originalIdx E (Fin.last _) a) = P.originalIdx E (Fin.last _) a)
    {j : ℕ} (hj : j < Fintype.card E.ι)
    (hj₁ : j < Fintype.card (P.eraseEmpty.totalTransformSeq E (Fin.last _)).ι)
    (hj₂ : j < Fintype.card (P.totalTransformSeq E (Fin.last _)).ι) :
    e (DivisorFamily.nthIdx _ ⟨j, hj₁⟩) = DivisorFamily.nthIdx _ ⟨j, hj₂⟩ := by
  change e (monoEquivOfFin (P.eraseEmpty.totalTransformSeq E (Fin.last _)).ι rfl ⟨j, hj₁⟩) =
    monoEquivOfFin (P.totalTransformSeq E (Fin.last _)).ι rfl ⟨j, hj₂⟩
  rw [monoEquivOfFin_totalTransformSeq_of_lt _ E hj hj₁, monoEquivOfFin_totalTransformSeq_of_lt _ E
    hj hj₂]
  exact ho _

end Induced

section Step21

variable (T : Triple k) (hn : T.HasDimLE n) (hmax : T.I.maxOrd ≤ m) (bd : ∀ j : ℕ, BDData.{u} n m j)

/-- The boundary-clearing data at position `j`, if indifferent to empty boundary members, take the
same value on the triple induced by the erased pull-back and on its exact-pull-back version
`inducedErased`, whose boundary keeps the unit-ideal members. -/
theorem functor_seq_induced_eraseEmpty_eq_inducedErased {T' : Triple k} (hn' : T'.HasDimLE n)
    (hmax' : T'.I.maxOrd ≤ m) (h : T'.X.left ⟶ T.X.left) [Smooth h] (hpb : T'.IsPullbackOf T h)
    (hind : BDFamily.IndifferentToEmptyMembers bd) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) (hne : S.NoEmptyCenters)
    (hP : (S.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hne' : (S.pullback h).eraseEmpty.NoEmptyCenters) {j : ℕ} (hj : j < Fintype.card T.E.ι)
    (hj' : j < Fintype.card T'.E.ι) :
    ((bd j).functor k).seq (T'.induced (S.pullback h).eraseEmpty hP' (Fin.last _))
        (bdClass_induced_last T' hn' hmax' hP' hne' hj') =
      ((bd j).functor k).seq (inducedErased (S.pullback h) hP hP')
        (bdClass_inducedErased hn hmax hn' h hpb hS hne hP hP' hj) := by
  have hT₃ := bdClass_induced_last T' hn' hmax' hP' hne' hj'
  have hT₄ := bdClass_inducedErased hn hmax hn' h hpb hS hne hP hP' hj
  obtain ⟨e, hc, ht, ho⟩ := eraseEmbeds_eraseEmpty (S.pullback h) T'.E
  have hpos := nthIdx_eraseEmpty_eq_of_originalIdx (S.pullback h) T'.E e ho hj' hT₃.2.2 hT₄.2.2
  -- the data in the form the indifference hypothesis expects
  have hc' : ∀ i, (inducedErased (S.pullback h) hP hP').E.component (e i) =
      (T'.induced (S.pullback h).eraseEmpty hP' (Fin.last _)).E.component i := hc
  have ht' : ∀ b, b ∉ Set.range e → (inducedErased (S.pullback h) hP hP').E.component b = ⊤ := ht
  have hpos' : e ((T'.induced (S.pullback h).eraseEmpty hP' (Fin.last _)).E.nthIdx ⟨j, hT₃.2.2⟩) =
      (inducedErased (S.pullback h) hP hP').E.nthIdx ⟨j, hT₄.2.2⟩ := hpos
  have hT₃' : Triple.BDClass n m j ({ inducedErased (S.pullback h) hP hP' with
      E := (T'.induced (S.pullback h).eraseEmpty hP' (Fin.last _)).E
      isSnc := (T'.induced (S.pullback h).eraseEmpty hP' (Fin.last _)).isSnc } : Triple k) := hT₃
  have key := hind k (inducedErased (S.pullback h) hP hP')
    (T'.induced (S.pullback h).eraseEmpty hP' (Fin.last _)).E
    (T'.induced (S.pullback h).eraseEmpty hP' (Fin.last _)).isSnc e hc' ht' j j hT₄.2.2 hT₃.2.2
    hpos' hT₄ hT₃'
  exact (eq_of_heq (OrderSeqAssignment.seq_congr ((bd j).functor k)
    (inducedErased_update_eq (S.pullback h) hP hP').symm hT₃ hT₃')).trans key.symm

/-- The value of the boundary-clearing data on `inducedErased (S.pullback h)` is the pull-back of
its value on the triple induced by `S`, erased, then carried along the last-stage isomorphism: the
second clause of [Kol07, 34.1] for [Kol07, Lemma 102] on the exact pull-back. -/
theorem functor_seq_inducedErased_eq {T' : Triple k} (hn' : T'.HasDimLE n)
    (h : T'.X.left ⟶ T.X.left) [Smooth h] (hpb : T'.IsPullbackOf T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) (hne : S.NoEmptyCenters)
    (hP : (S.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m) {j : ℕ}
    (hj : j < Fintype.card T.E.ι) :
    ((bd j).functor k).seq (inducedErased (S.pullback h) hP hP')
        (bdClass_inducedErased hn hmax hn' h hpb hS hne hP hP' hj) =
      ((((bd j).functor k).seq (T.induced S hS (Fin.last _))
        (bdClass_induced_last T hn hmax hS hne hj)).pullback (S.pullbackLastHom
          h)).eraseEmpty.pullback
        (S.pullback h).eraseEmptyLastHom := by
  have hsm := smooth_eraseEmptyLastHom_comp_pullbackLastHom h hS hP hP'
  have key : ((bd j).functor k).seq (inducedErased (S.pullback h) hP hP')
        (bdClass_inducedErased hn hmax hn' h hpb hS hne hP hP' hj) =
      ((((bd j).functor k).seq (T.induced S hS (Fin.last _))
        (bdClass_induced_last T hn hmax hS hne hj)).pullback
          ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h)).eraseEmpty :=
    ((bd j).commutesWithSmooth k).2 (T.induced S hS (Fin.last _))
      (inducedErased (S.pullback h) hP hP')
      ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h)
      (isPullbackOf_inducedErased_pullback h hpb hS hP hP')
      (bdClass_induced_last T hn hmax hS hne hj)
      (bdClass_inducedErased hn hmax hn' h hpb hS hne hP hP' hj)
  exact key.trans ((congrArg BlowUpSequence.eraseEmpty
    (pullback_comp _ (S.pullback h).eraseEmptyLastHom (S.pullbackLastHom h))).trans
    (eraseEmpty_pullback_of_flat_surjective _ (S.pullback h).eraseEmptyLastHom
      (surjective_of_isIso _)))

/-- The inductive step of `step21Seq_eraseEmpty_pullback`, on the whole Step 2.1 values: if the
sequence after `j` rounds on the pulled-back data is the erased pull-back of the sequence after `j`
rounds, so is the sequence after `j + 1` rounds, by `pullback_concat`, `eraseEmpty_concat`, the
indifference of `bd j` to the deleted unit-ideal members of the erased boundary (`hind`), the
second clause of [Kol07, 34.1] for the boundary-clearing data on the exact pull-back of the induced
triple along the smooth `eraseEmptyLastHom ≫ pullbackLastHom`, and
`eraseEmpty_pullback_of_flat_surjective` along the isomorphism. -/
theorem step21Seq_eraseEmpty_pullback_succ_aux {T' : Triple k} (hn' : T'.HasDimLE n)
    (hmax' : T'.I.maxOrd ≤ m) (h : T'.X.left ⟶ T.X.left) [Smooth h] (hpb : T'.IsPullbackOf T h)
    (hind : BDFamily.IndifferentToEmptyMembers bd) {j : ℕ}
    (σ' : {S : BlowUpSequence T'.X.left //
      S.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m ∧ S.NoEmptyCenters})
    (σ : {S : BlowUpSequence T.X.left // S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m ∧
      S.NoEmptyCenters})
    (hσ : σ'.1 = (σ.1.pullback h).eraseEmpty) (hj' : j < Fintype.card T'.E.ι)
    (hj : j < Fintype.card T.E.ι) :
    σ'.1.concat (((bd j).functor k).seq (T'.induced σ'.1 σ'.2.1 (Fin.last _))
        (bdClass_induced_last T' hn' hmax' σ'.2.1 σ'.2.2 hj')) =
      ((σ.1.concat (((bd j).functor k).seq (T.induced σ.1 σ.2.1 (Fin.last _))
        (bdClass_induced_last T hn hmax σ.2.1 σ.2.2 hj))).pullback h).eraseEmpty := by
  obtain ⟨S', hS'⟩ := σ'
  obtain ⟨S, hS⟩ := σ
  dsimp only at hσ ⊢
  subst hσ
  have hP : (S.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m :=
    hpb.isOrderSeq_pullback hS.1
  refine Eq.trans ?_ ((congrArg BlowUpSequence.eraseEmpty (pullback_concat S _ h)).trans
    (eraseEmpty_concat (S.pullback h) _)).symm
  refine congrArg (S.pullback h).eraseEmpty.concat ?_
  exact (functor_seq_induced_eraseEmpty_eq_inducedErased T hn hmax bd hn' hmax' h hpb hind hS.1
    hS.2 hP hS'.1 hS'.2 hj hj').trans
    (functor_seq_inducedErased_eq T hn hmax bd hn' h hpb hS.1 hS.2 hP hS'.1 hj)

/-- For an arbitrary smooth morphism `h`, Step 2.1 on the pulled-back data is the pull-back of
Step 2.1 with the empty blow-ups deleted (clause (2) of [Kol07, Theorem 103] with the second
clause of [Kol07, 34.1], for Step 2.1), under the indifference of the boundary-clearing data to
empty boundary members. -/
theorem step21Seq_eraseEmpty_pullback {T' : Triple k} (hn' : T'.HasDimLE n)
    (hmax' : T'.I.maxOrd ≤ m) (h : T'.X.left ⟶ T.X.left) [Smooth h] (hpb : T'.IsPullbackOf T h)
    (hind : BDFamily.IndifferentToEmptyMembers bd) (j : ℕ) :
    (step21Seq T' hn' hmax' bd j).1 = ((step21Seq T hn hmax bd j).1.pullback h).eraseEmpty := by
  have hcard : Fintype.card T'.E.ι = Fintype.card T.E.ι :=
    Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι hpb.2.2))
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [step21Seq]
    by_cases hj : j < Fintype.card T.E.ι
    · have hj' : j < Fintype.card T'.E.ι := hcard ▸ hj
      rw [dite_eq_left hj', dite_eq_left hj]
      exact step21Seq_eraseEmpty_pullback_succ_aux T hn hmax bd hn' hmax' h hpb hind _ _ ih hj' hj
    · have hj' : ¬ j < Fintype.card T'.E.ι := hcard ▸ hj
      rw [dite_eq_right hj', dite_eq_right hj]
      exact ih

end Step21

end Hironaka.BO
