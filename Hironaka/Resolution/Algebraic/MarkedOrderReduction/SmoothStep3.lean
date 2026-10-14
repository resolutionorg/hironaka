/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.UpToUnits
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Congruence
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step3Input
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step3Functorial
import Hironaka.Resolution.Algebraic.Monomial.Geometric.EnumerationIndep
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Monomial.Geometric.PullbackErase
import Hironaka.Resolution.Algebraic.Monomial.Geometric.RealizeCongr
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Smooth
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The geometric Step 3 under an arbitrary smooth morphism, up to unit members

The second clause of [Kol07, 34.1] for Step 3 of the proof of [Kol07, Theorem 107], on a marked
triple `T'` that is the pull-back of `T` up to unit boundary members: the geometric Step 3 of `T'`
is the pull-back of the geometric Step 3 of `T` with the empty blow-ups deleted. Two facts combine:

* `realize_pullback_eraseEmpty`
  (`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackErase.lean`): for the full pull-back
  family `h^{-1} E`, the run on the refining family `refinesAlong_ofDivisorFamily` is the erased
  pull-back of the run on `X`; the exponents agree with Step 3's exponents at the generic points of
  the components (`exponentAt_step3Family_of_mem_genericPoints`, `ord_comap_of_smooth`), and the
  enumeration of the components is Step 3's own on `T'` transported by `compEquivOfIsTopErasure`;
* `realize_congr_of_rel` (`Hironaka/Resolution/Algebraic/Monomial/Geometric/RealizeCongr.lean`):
  Step 3's input family on `T'` (boundary `E'`) and the family on the full pull-back boundary
  `h^{-1} E` are related by a renumbering, since the components are the same (a unit member has no
  irreducible components, `compEquivOfIsTopErasure`), the pieces and exponents coincide, and the
  labels are re-embedded along the order embedding `E'.ι ↪o E.ι`
  (`rel_ofDivisorFamily_of_isTopErasure`).

The result `step3Seq_eraseEmpty_pullback` enters the assembly of clause (2) in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Smooth.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData Hironaka.Monomial Hironaka.Monomial.PieceFamily Hironaka.Sequence

namespace Hironaka.Monomial

variable {X : Scheme.{u}}

/-- The irreducible components of the members of a family with unit members deleted are those of
the family ([Kol07, 32]): a unit member has empty support, hence no generic point. -/
noncomputable def compEquivOfIsTopErasure {E' E : DivisorFamily X} {e : E'.ι ↪o E.ι}
    (he : IsTopErasure E' E e) : Components E' ≃ Components E :=
  Equiv.ofBijective (fun c => ⟨e c.1, ⟨(c.2 : X), by rw [he.1 c.1]; exact c.2.2⟩⟩) (by
    constructor
    · intro c₁ c₂ hc
      have hi : c₁.1 = c₂.1 := e.injective (congrArg Sigma.fst hc)
      have hpt : (c₁.2 : X) = (c₂.2 : X) := congrArg (fun c : Components E => (c.2 : X)) hc
      obtain ⟨i₁, x₁⟩ := c₁
      obtain ⟨i₂, x₂⟩ := c₂
      dsimp only at hi hpt
      subst hi
      exact congrArg _ (Subtype.ext hpt)
    · rintro ⟨j, ⟨p, hp⟩⟩
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        refine ⟨⟨i, ⟨p, by rw [← he.1 i]; exact hp⟩⟩, ?_⟩
        exact Sigma.ext rfl (heq_of_eq (Subtype.ext rfl))
      · rw [he.2 j hj, Scheme.IdealSheafData.support_top, Closeds.genericPoints_bot] at hp
        exact (Set.notMem_empty _ hp).elim)

theorem compEquivOfIsTopErasure_fst {E' E : DivisorFamily X} {e : E'.ι ↪o E.ι}
    (he : IsTopErasure E' E e) (c : Components E') : (compEquivOfIsTopErasure he c).1 = e c.1 :=
  rfl

theorem compEquivOfIsTopErasure_snd {E' E : DivisorFamily X} {e : E'.ι ↪o E.ι}
    (he : IsTopErasure E' E e) (c : Components E') :
    ((compEquivOfIsTopErasure he c).2 : X) = (c.2 : X) :=
  rfl

namespace PieceFamily

/-- The label renumbering of a deletion of unit members: the label of a member of `E'` (through
`f'`) goes to the label of the same member in `E` (through `f`, along `e`). -/
noncomputable def labelMapOfIsTopErasure {E' E : DivisorFamily X} (e : E'.ι ↪o E.ι) {L L' : ℕ}
    (f' : E'.ι ≃o Fin L') (f : E.ι ≃o Fin L) (ℓ : ℕ) : ℕ :=
  if hℓ : ℓ < L' then (f (e (f'.symm ⟨ℓ, hℓ⟩)) : ℕ) else ℓ

theorem labelMapOfIsTopErasure_apply {E' E : DivisorFamily X} (e : E'.ι ↪o E.ι) {L L' : ℕ}
    (f' : E'.ι ≃o Fin L') (f : E.ι ≃o Fin L) (i : E'.ι) :
    labelMapOfIsTopErasure e f' f (f' i : ℕ) = (f (e i) : ℕ) := by
  unfold labelMapOfIsTopErasure
  rw [dite_eq_left (Fin.isLt _)]
  have h1 : (⟨((f' i : Fin L') : ℕ), Fin.isLt _⟩ : Fin L') = f' i := Fin.ext rfl
  rw [h1, OrderIso.symm_apply_apply]

/-- **Step 3's input family for a boundary with unit members deleted is the input family for the
full boundary, renumbered**: the same components (enumerated through `compEquivOfIsTopErasure`),
the same pieces and exponents, the labels re-embedded along `e`. -/
theorem rel_ofDivisorFamily_of_isTopErasure {E' E : DivisorFamily X} {e : E'.ι ↪o E.ι}
    (he : IsTopErasure E' E e) (a : X → ℕ) {k : ℕ} (σ : Fin k ≃ Components E') {L L' : ℕ}
    (f' : E'.ι ≃o Fin L') (f : E.ι ≃o Fin L) :
    (ofDivisorFamily E' a f' σ).Rel id (labelMapOfIsTopErasure e f' f)
      (ofDivisorFamily E a f (σ.trans (compEquivOfIsTopErasure he))) where
  mono := fun _ _ _ _ h => h
  lt := fun _ hc => hc
  piece_eq := fun c hc => by
    dsimp only [id_eq]
    rw [ofDivisorFamily_piece_of_lt' a f (σ.trans (compEquivOfIsTopErasure he)) hc,
      ofDivisorFamily_piece_of_lt' a f' σ hc, Equiv.trans_apply, compEquivOfIsTopErasure_snd]
  a_eq := fun c hc => by
    dsimp only [id_eq]
    rw [ofDivisorFamily_a_of_lt' a f (σ.trans (compEquivOfIsTopErasure he)) hc,
      ofDivisorFamily_a_of_lt' a f' σ hc, Equiv.trans_apply, compEquivOfIsTopErasure_snd]
  label_eq := fun c hc => by
    dsimp only [id_eq]
    rw [ofDivisorFamily_label_of_lt' a f (σ.trans (compEquivOfIsTopErasure he)) hc,
      ofDivisorFamily_label_of_lt' a f' σ hc, Equiv.trans_apply, compEquivOfIsTopErasure_fst,
      labelMapOfIsTopErasure_apply]
  σmono := by
    intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hlt
    have h₁ : ℓ₁ < L' := hℓ₁
    have h₂ : ℓ₂ < L' := hℓ₂
    unfold labelMapOfIsTopErasure
    rw [dite_eq_left h₁, dite_eq_left h₂]
    exact Fin.lt_def.mp (f.strictMono (e.strictMono (f'.symm.strictMono (Fin.mk_lt_mk.mpr hlt))))
  σlt := by
    intro ℓ hℓ
    have h₁ : ℓ < L' := hℓ
    unfold labelMapOfIsTopErasure
    rw [dite_eq_left h₁]
    exact Fin.isLt _
  nerve_eq := by
    have hpiece : (ofDivisorFamily E a f (σ.trans (compEquivOfIsTopErasure he))).piece =
        (ofDivisorFamily E' a f' σ).piece := by
      funext c
      by_cases hc : c < k
      · rw [ofDivisorFamily_piece_of_lt' a f (σ.trans (compEquivOfIsTopErasure he)) hc,
          ofDivisorFamily_piece_of_lt' a f' σ hc, Equiv.trans_apply, compEquivOfIsTopErasure_snd]
      · change (if h : c < k then _ else ⊥) = (if h : c < k then _ else ⊥)
        rw [dite_eq_right hc, dite_eq_right hc]
    have hnc : (ofDivisorFamily E a f (σ.trans (compEquivOfIsTopErasure he))).nextComp =
        (ofDivisorFamily E' a f' σ).nextComp := rfl
    have hnerve : (ofDivisorFamily E a f (σ.trans (compEquivOfIsTopErasure he))).nerve =
        (ofDivisorFamily E' a f' σ).nerve := by
      unfold nerve faceSet
      rw [hpiece, hnc]
    have h : (ofDivisorFamily E' a f' σ).nerve.image (Finset.image (id : ℕ → ℕ)) =
        (ofDivisorFamily E' a f' σ).nerve.image id :=
      Finset.image_congr fun _ _ => Finset.image_id
    rw [hnerve, h, Finset.image_id]

end PieceFamily

end Hironaka.Monomial

namespace Hironaka.BMO

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

/-- **The geometric Step 3 of a marked triple that is a pull-back up to unit members is the
pull-back of the geometric Step 3 with the empty blow-ups deleted** (the second clause of
[Kol07, 34.1] for Step 3; `realize_pullback_eraseEmpty` with `refinesAlong_ofDivisorFamily` and
`realize_congr_of_rel`): Step 3's family on `T'` is, up to the renumbering of the labels along the
deletion (`rel_ofDivisorFamily_of_isTopErasure`), the family on the full pull-back boundary, which
is the refining family up to the exponents (they agree at the generic points of the components). -/
theorem step3Seq_eraseEmpty_pullback (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') :
    step3Seq T' hT' = ((step3Seq T hT).pullback h).eraseEmpty := by
  obtain ⟨hover, hI, hm, e, he⟩ := hp
  cases T' with
  | mk toT m' =>
  cases toT with
  | mk X' eq' I' hI' E' hE' =>
  obtain ⟨⟨X', _, hom'⟩, ft, sep⟩ := X'
  dsimp only at h hover hI hm e he
  change h ≫ (T.X.left ↘ Spec (.of k)) = hom' at hover
  subst hI hm hover
  have hsm := T.smooth
  have hqc' : QuasiCompact (h ≫ (T.X.left ↘ Spec (.of k))) := ft.toQuasiCompact
  have hN := Hironaka.BD.noetherianSpace_triple T.toTriple
  have hN' : NoetherianSpace X' := Hironaka.BD.noetherianSpace_triple
    (⟨.ofHom (h ≫ (T.X.left ↘ Spec (.of k))) ft sep, eq', T.I.comap h, hI', E', hE'⟩ : Triple k)
  have hE'' : (T.E.comap h).IsSnc := isSnc_comap_of_smooth (T.X.left ↘ Spec (.of k)) h T.isSnc
  -- Step 3's enumeration of the components of `E'`, carried to the full pull-back boundary
  set σ₁ : Fin (Nat.card (Components E')) ≃ Components E' := @componentsEquiv _ hN' E' with hσ₁
  set σ'' : Fin (Nat.card (Components E')) ≃ Components (T.E.comap h) :=
    σ₁.trans (compEquivOfIsTopErasure he) with hσ''
  -- the refining family on the full pull-back boundary
  have hρ := refinesAlong_ofDivisorFamily (f := T.X.left ↘ Spec (.of k)) (h := h)
    (Φ := step3Family T) T.isSnc (step3Family_realizes T) hE'' σ''
  have hreal : (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
      (labelIso T.E) σ'').Realizes (T.E.comap h) (labelIso T.E) :=
    ofDivisorFamily_realizes (T.E.comap h) _ (labelIso T.E) σ'' hE''
  have hΦ' : (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
      (labelIso T.E) σ'').Realizes (T.E.comap h)
      ((labelIso T.E).trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) := by
    refine ⟨fun j => ?_, hreal.disjoint⟩
    change ((T.E.comap h).component j).support =
      ((Finset.range (ofDivisorFamily (T.E.comap h)
        (fun y => (step3Family T).exponentAt (h y)) (labelIso T.E) σ'').nextComp).filter
        fun c => (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
          (labelIso T.E) σ'').label c = (labelIso T.E j : ℕ)).sup
        (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
          (labelIso T.E) σ'').piece
    exact hreal.support_eq j
  have hn' : ∃ n' ≤ n, SmoothOfRelativeDimension n' (h ≫ (T.X.left ↘ Spec (.of k))) := hT'.2.1
  have hV' : (ofDivisorFamily (T.E.comap h) (fun y => (step3Family T).exponentAt (h y))
      (labelIso T.E) σ'').IsValid n m :=
    valid_of_realizes _ (h ≫ (T.X.left ↘ Spec (.of k))) hE'' hreal hT.1 hn'
  have key := realize_pullback_eraseEmpty (f := T.X.left ↘ Spec (.of k)) (h := h) T.isSnc
    (step3Family_realizes T) (step3Family_isValid T hT) hT.2.1 hn' hρ hΦ' hV'
  -- the family on the full pull-back boundary with Step 3's exponents is the refining family
  have hagree : ∀ c : Components (T.E.comap h),
      ((T.I.comap h).ord (c.2 : X')).toNat = (step3Family T).exponentAt (h (c.2 : X')) := by
    intro c
    rw [IdealSheafData.ord_comap_of_smooth]
    exact (exponentAt_step3Family_of_mem_genericPoints T
      (mem_genericPoints_support_of_flat h _ c.2.2)).symm
  have hfam : ofDivisorFamily (T.E.comap h) (fun y => ((T.I.comap h).ord y).toNat)
      (labelIso T.E) σ'' = ofDivisorFamily (T.E.comap h)
        (fun y => (step3Family T).exponentAt (h y)) (labelIso T.E) σ'' :=
    ofDivisorFamily_congr_of_forall (E := T.E.comap h) _ _ (labelIso T.E) σ'' hagree
  -- the full-boundary family with Step 3's exponents is valid
  have hVfull : (ofDivisorFamily (T.E.comap h) (fun y => ((T.I.comap h).ord y).toNat)
      (labelIso T.E) σ'').IsValid n m := by
    rw [hfam]
    exact hV'
  -- Step 3's family on `T'` is the full-boundary family renumbered
  have hRel := rel_ofDivisorFamily_of_isTopErasure he (fun y => ((T.I.comap h).ord y).toNat) σ₁
    (labelIso E') (labelIso T.E)
  rw [← hσ''] at hRel
  change (ofDivisorFamily E' (fun y => ((T.I.comap h).ord y).toNat) (labelIso E')
      σ₁).realize n m _ =
    (((step3Family T).realize n m (step3Family_isValid T hT)).pullback h).eraseEmpty
  rw [← key]
  exact (Hironaka.Monomial.PieceFamily.realize_congr_of_rel hRel _ hVfull).trans
    (realize_congr_family hfam hVfull hV')

end Hironaka.BMO
