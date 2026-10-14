/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Concat
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Deleting the empty blow-ups of a concatenation

The second step of the proof of [Kol07, Theorem 103] concatenates the sequence built so far with a
sequence on its last stage, and the functors of this library delete the empty blow-ups
([Kol07, 34.1]: delete and reindex). To read the deletion through the concatenation one needs,
as for schemes (`AlgebraicGeometry.eraseEmpty_concat` of
`Hironaka.Scheme.BlowUpSequence.EraseEmptyConcat`), the isomorphism between the last stage of a list
and the last stage of the cleaned list, the composite of the lifts of the isomorphisms `Bl_∅ ≃ M` of
the deleted empty blowings-up, and the identity

  `(A ++ B).eraseEmpty = A.eraseEmpty ++ (B transported along that isomorphism).eraseEmpty`.

This file builds that isomorphism, `BlowUpSequence.eraseEmptyLast`, proves that it lies over the
base (`stageMap_last_eraseEmptyLast`, the analogue of `eraseEmptyLastHom_comp_composite` of
`Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced`), and proves
`BlowUpSequence.eraseEmpty_concat` and `eraseEmpty_concat_eraseEmpty`, with the general transport
tools it needs: the last-stage isomorphism `mapLast` of a transported list, the functoriality of
`map` (`map_refl`, `map_map`, `map_concat`), and its commutation with the deletion of empty blow-ups
(`eraseEmpty_map`). The casts along the two computation rules of `eraseEmpty` (`stageOfEq`) are
unavoidable: `eraseEmpty` decides `Y = ∅` classically, so `(cons hY rest).eraseEmpty` does not
reduce definitionally (the version for schemes uses `eqToHom` for the same reason).
-/

@[expose] public section

noncomputable section

open Set
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The last stage of a transported list -/

/-- The isomorphism of last stages induced by the transport `map g` of a list along `g : M ≃ N`:
the composite of the lifts `liftDiffeomorph` (the analogue of `pullbackLastHom` for schemes). -/
def mapLast : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (L : BlowUpSequence ψ₀ M),
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (L.stage (Fin.last _)) ((L.map g).stage (Fin.last _)) ω
  | _, _, g, nil _ => g
  | _, _, g, cons hY rest => rest.mapLast (liftDiffeomorph g hY)

variable {M N P : AnalyticManifold.{u} 𝕜 E}

theorem mapLast_nil (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) :
    (nil (ψ₀ := ψ₀) M).mapLast g = g := rfl

theorem mapLast_cons (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) :
    (cons hY rest).mapLast g = rest.mapLast (liftDiffeomorph g hY) := rfl

/-- The last-stage isomorphism of a transported list lies over `g`: `Π' ∘ g_r = g ∘ Π` for the
composite blow-downs `Π`, `Π'` of the list and of its transport. -/
theorem stageMap_last_mapLast : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (L : BlowUpSequence ψ₀ M) (p : L.stage (Fin.last _)),
    (L.map g).toSuccession.stageMap (Fin.last _) (L.mapLast g p) =
      g (L.toSuccession.stageMap (Fin.last _) p)
  | _, _, _, nil _, _ => rfl
  | _, _, g, cons hY rest, p =>
    (stageMapAux_cons_succ (hY.image_diffeomorph g) (rest.map (liftDiffeomorph g hY))
      (rest.map (liftDiffeomorph g hY)).length (Nat.lt_succ_self _)
      (rest.mapLast (liftDiffeomorph g hY) p)).trans
      ((congrArg (blowUpπ ψ₀ (hY.image_diffeomorph g))
        (stageMap_last_mapLast (liftDiffeomorph g hY) rest p)).trans
        ((blowDown_liftPoint _ _ _ _).trans
          (congrArg g (stageMapAux_cons_succ hY rest rest.length (Nat.lt_succ_self _) p).symm)))

/-! ### Functoriality of the transport along diffeomorphisms -/

/-- The transport along the identity is the identity (via `map_eq_pullback_symm` and
`pullback_id`). -/
theorem map_refl (L : BlowUpSequence ψ₀ M) : L.map (Diffeomorph.refl 𝓘(𝕜, E) M ω) = L := by
  have e : Diffeomorph.toAnalyticMap (Diffeomorph.refl 𝓘(𝕜, E) M ω).symm =
      (ContMDiffMap.id : AnalyticMap M M) := ContMDiffMap.ext fun _ => rfl
  exact (map_eq_pullback_symm L _).trans
    ((pullback_congr L e _ (isLocalDiffeomorph_id M)).trans (pullback_id L))

/-- The transport along a composite is the composite of the transports (via
`map_eq_pullback_symm` and `pullback_comp`). -/
theorem map_map (L : BlowUpSequence ψ₀ M) (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (g' : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N P ω) : (L.map g).map g' = L.map (g.trans g') := by
  have e : (Diffeomorph.toAnalyticMap g.symm).comp (Diffeomorph.toAnalyticMap g'.symm) =
      Diffeomorph.toAnalyticMap (g.trans g').symm := ContMDiffMap.ext fun _ => rfl
  rw [map_eq_pullback_symm L g, map_eq_pullback_symm _ g', map_eq_pullback_symm L (g.trans g')]
  exact (pullback_comp L _ _ _ _).trans (pullback_congr L e _ _)

/-- The transport of a concatenation is the concatenation of the transports, the second piece
transported along the last-stage isomorphism `mapLast` of the first (the analogue of
`pullback_concat` for schemes). -/
theorem map_concat : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (L : BlowUpSequence ψ₀ M) (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))),
    (L.concat L').map g = (L.map g).concat (L'.map (L.mapLast g))
  | _, _, _, nil _, _ => rfl
  | _, _, g, cons hY rest, L' =>
    congrArg (cons (hY.image_diffeomorph g)) (map_concat (liftDiffeomorph g hY) rest L')

/-- Deleting the empty blow-ups commutes with the transport along a diffeomorphism (the surjective
case of `eraseEmpty_pullback`, read through `map_eq_pullback_symm`). -/
theorem eraseEmpty_map (L : BlowUpSequence ψ₀ M) (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) :
    (L.map g).eraseEmpty = L.eraseEmpty.map g := by
  rw [map_eq_pullback_symm L g, map_eq_pullback_symm L.eraseEmpty g]
  exact (eraseEmpty_pullback L _ _ g.symm.toEquiv.surjective).symm

/-! ### Casts along an equality of lists -/

/-- The identification of the last stages of two equal lists (the analogue of `eqToHom (congrArg
BlowUpSequence.last e)` for schemes). -/
def stageOfEq : ∀ {L₁ L₂ : BlowUpSequence ψ₀ M}, L₁ = L₂ →
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (L₁.stage (Fin.last _)) (L₂.stage (Fin.last _)) ω
  | _, _, rfl => Diffeomorph.refl _ _ _

theorem stageOfEq_rfl (L : BlowUpSequence ψ₀ M) :
    stageOfEq (rfl : L = L) = Diffeomorph.refl 𝓘(𝕜, E) _ ω := rfl

theorem stageMap_last_stageOfEq {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (p : L₁.stage (Fin.last _)) :
    L₂.toSuccession.stageMap (Fin.last _) (stageOfEq e p) =
      L₁.toSuccession.stageMap (Fin.last _) p := by
  subst e
  rfl

/-- Transport of the second piece of a concatenation along an equality of first pieces: the cast
is absorbed (`concat_pullback_eqToHom`). -/
theorem concat_map_stageOfEq {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (R : BlowUpSequence ψ₀ (L₁.stage (Fin.last _))) :
    L₂.concat (R.map (stageOfEq e)) = L₁.concat R := by
  subst e
  exact congrArg L₁.concat (map_refl R)

/-! ### The last-stage isomorphism of the deletion of empty blow-ups -/

open scoped Classical in
/-- One step of `eraseEmptyLast` (the shape of `eraseEmptyCons`): given the last-stage isomorphism
`T` of the tail, the last-stage isomorphism of `cons hY rest` — at an empty step `T` followed by
the lift `mapLast` of `Bl_∅ M ≃ M` (the transport `eraseEmpty` performs), at a nonempty step `T`
itself; each followed by the cast along the computation rule of `eraseEmpty` at that step. -/
def eraseEmptyLastCons {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY))
    (T : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (rest.stage (Fin.last _))
      (rest.eraseEmpty.stage (Fin.last _)) ω) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (rest.stage (Fin.last _))
      ((cons hY rest).eraseEmpty.stage (Fin.last _)) ω :=
  if hY₀ : Y = ∅ then
    (T.trans (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀))).trans
      (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm)
  else
    T.trans (stageOfEq (L₁ := cons hY rest.eraseEmpty)
      (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm)

theorem eraseEmptyLastCons_of_eq_empty {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY))
    (T : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (rest.stage (Fin.last _))
      (rest.eraseEmpty.stage (Fin.last _)) ω)
    (hY₀ : Y = ∅) :
    eraseEmptyLastCons hY rest T =
      (T.trans (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀))).trans
        (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm) := by
  rw [eraseEmptyLastCons, dite_eq_left hY₀]

theorem eraseEmptyLastCons_of_ne_empty {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY))
    (T : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (rest.stage (Fin.last _))
      (rest.eraseEmpty.stage (Fin.last _)) ω)
    (hY₀ : Y ≠ ∅) :
    eraseEmptyLastCons hY rest T =
      T.trans (stageOfEq (L₁ := cons hY rest.eraseEmpty)
        (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm) := by
  rw [eraseEmptyLastCons, dite_eq_right hY₀]

/-- [Kol07, 34.1], the analogue of `eraseEmptyLastHom` for schemes: **the isomorphism from
the last stage of a list to the last stage of its cleaned list** — by recursion, one step
`eraseEmptyLastCons` per centre. -/
def eraseEmptyLast : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M),
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (L.stage (Fin.last _)) (L.eraseEmpty.stage (Fin.last _)) ω
  | _, nil _ => Diffeomorph.refl _ _ _
  | _, cons hY rest => eraseEmptyLastCons hY rest rest.eraseEmptyLast

theorem eraseEmptyLast_nil : (nil (ψ₀ := ψ₀) M).eraseEmptyLast = Diffeomorph.refl 𝓘(𝕜, E) M ω :=
  rfl

theorem eraseEmptyLast_cons {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) :
    (cons hY rest).eraseEmptyLast = eraseEmptyLastCons hY rest rest.eraseEmptyLast := rfl

theorem eraseEmptyLast_cons_of_eq_empty {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) (hY₀ : Y = ∅) :
    (cons hY rest).eraseEmptyLast =
      (rest.eraseEmptyLast.trans (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀))).trans
        (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm) :=
  eraseEmptyLastCons_of_eq_empty hY rest rest.eraseEmptyLast hY₀

theorem eraseEmptyLast_cons_of_ne_empty {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) (hY₀ : Y ≠ ∅) :
    (cons hY rest).eraseEmptyLast =
      rest.eraseEmptyLast.trans (stageOfEq (L₁ := cons hY rest.eraseEmpty)
        (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm) :=
  eraseEmptyLastCons_of_ne_empty hY rest rest.eraseEmptyLast hY₀

/-- The last-stage isomorphism of the deletion lies over the base: the composite blow-down of the
cleaned list after it is the composite blow-down of the list (`eraseEmptyLastHom_comp_composite`
for schemes; [Kol07, 34.1], the deleted blowings-up are isomorphisms `Bl_∅ M ≃ M` over `M`). -/
theorem stageMap_last_eraseEmptyLast : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (p : L.stage (Fin.last _)),
    L.eraseEmpty.toSuccession.stageMap (Fin.last _) (L.eraseEmptyLast p) =
      L.toSuccession.stageMap (Fin.last _) p
  | _, nil _, _ => rfl
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, p => by
    have hp : (cons hY rest).toSuccession.stageMap (Fin.last _) p =
        blowUpπ ψ₀ hY (rest.toSuccession.stageMap (Fin.last _) p) :=
      stageMapAux_cons_succ hY rest _ _ p
    by_cases hY₀ : Y = ∅
    · have h0 : (cons hY rest).eraseEmptyLast p =
          stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm
            (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀) (rest.eraseEmptyLast p)) :=
        congrArg (fun T : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((cons hY rest).stage (Fin.last _))
          ((cons hY rest).eraseEmpty.stage (Fin.last _)) ω => T p)
          (eraseEmptyLast_cons_of_eq_empty hY rest hY₀)
      calc (cons hY rest).eraseEmpty.toSuccession.stageMap (Fin.last _)
            ((cons hY rest).eraseEmptyLast p)
          = (cons hY rest).eraseEmpty.toSuccession.stageMap (Fin.last _)
              (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm
                (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀)
                  (rest.eraseEmptyLast p))) := congrArg _ h0
        _ = (rest.eraseEmpty.map (emptyBlowUpDiffeomorph hY hY₀)).toSuccession.stageMap
              (Fin.last _) (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀)
                (rest.eraseEmptyLast p)) :=
            stageMap_last_stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm _
        _ = emptyBlowUpDiffeomorph hY hY₀
              (rest.eraseEmpty.toSuccession.stageMap (Fin.last _) (rest.eraseEmptyLast p)) :=
            stageMap_last_mapLast (emptyBlowUpDiffeomorph hY hY₀) rest.eraseEmpty _
        _ = emptyBlowUpDiffeomorph hY hY₀ (rest.toSuccession.stageMap (Fin.last _) p) :=
            congrArg _ (stageMap_last_eraseEmptyLast rest p)
        _ = blowUpπ ψ₀ hY (rest.toSuccession.stageMap (Fin.last _) p) :=
            emptyBlowUpDiffeomorph_apply hY hY₀ _
        _ = (cons hY rest).toSuccession.stageMap (Fin.last _) p := hp.symm
    · have h0 : (cons hY rest).eraseEmptyLast p =
          stageOfEq (L₁ := cons hY rest.eraseEmpty) (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm
            (rest.eraseEmptyLast p) :=
        congrArg (fun T : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((cons hY rest).stage (Fin.last _))
          ((cons hY rest).eraseEmpty.stage (Fin.last _)) ω => T p)
          (eraseEmptyLast_cons_of_ne_empty hY rest hY₀)
      calc (cons hY rest).eraseEmpty.toSuccession.stageMap (Fin.last _)
            ((cons hY rest).eraseEmptyLast p)
          = (cons hY rest.eraseEmpty).toSuccession.stageMap (Fin.last _)
              (rest.eraseEmptyLast p) :=
            (congrArg _ h0).trans (stageMap_last_stageOfEq
              (L₁ := cons hY rest.eraseEmpty) (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm _)
        _ = blowUpπ ψ₀ hY
              (rest.eraseEmpty.toSuccession.stageMap (Fin.last _) (rest.eraseEmptyLast p)) :=
            stageMapAux_cons_succ hY rest.eraseEmpty _ _ _
        _ = blowUpπ ψ₀ hY (rest.toSuccession.stageMap (Fin.last _) p) :=
            congrArg _ (stageMap_last_eraseEmptyLast rest p)
        _ = (cons hY rest).toSuccession.stageMap (Fin.last _) p := hp.symm

/-! ### Deleting the empty blow-ups of a concatenation -/

/-- [Kol07, 32] and [Kol07, 34.1] for the concatenation in the second step of the proof of
[Kol07, Theorem 103]; the analogue of `eraseEmpty_concat` for schemes: **deleting the empty blow-ups
of a concatenation is deleting them in the first list, then in the second transported along the
last-stage isomorphism of the first**. -/
theorem eraseEmpty_concat : ∀ {M : AnalyticManifold.{u} 𝕜 E} (A : BlowUpSequence ψ₀ M)
    (B : BlowUpSequence ψ₀ (A.stage (Fin.last _))),
    (A.concat B).eraseEmpty = A.eraseEmpty.concat ((B.map A.eraseEmptyLast).eraseEmpty)
  | _, nil _, B => (congrArg eraseEmpty (map_refl B)).symm
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, B => by
    have ih := eraseEmpty_concat rest B
    by_cases hY₀ : Y = ∅
    · calc ((cons hY rest).concat B).eraseEmpty
          = (rest.concat B).eraseEmpty.map (emptyBlowUpDiffeomorph hY hY₀) :=
            eraseEmpty_cons_of_eq_empty hY (rest.concat B) hY₀
        _ = (rest.eraseEmpty.concat ((B.map rest.eraseEmptyLast).eraseEmpty)).map
              (emptyBlowUpDiffeomorph hY hY₀) :=
            congrArg (fun L : BlowUpSequence ψ₀ (blowUp ψ₀ hY) =>
              L.map (emptyBlowUpDiffeomorph hY hY₀)) ih
        _ = (rest.eraseEmpty.map (emptyBlowUpDiffeomorph hY hY₀)).concat
              (((B.map rest.eraseEmptyLast).eraseEmpty).map
                (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀))) :=
            map_concat _ _ _
        _ = (rest.eraseEmpty.map (emptyBlowUpDiffeomorph hY hY₀)).concat
              ((B.map (rest.eraseEmptyLast.trans
                (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀)))).eraseEmpty) :=
            congrArg _ ((eraseEmpty_map _ _).symm.trans (congrArg eraseEmpty (map_map B _ _)))
        _ = (cons hY rest).eraseEmpty.concat
              (((B.map (rest.eraseEmptyLast.trans
                (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀)))).eraseEmpty).map
                  (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm)) :=
            (concat_map_stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm _).symm
        _ = (cons hY rest).eraseEmpty.concat
              ((B.map ((rest.eraseEmptyLast.trans
                (rest.eraseEmpty.mapLast (emptyBlowUpDiffeomorph hY hY₀))).trans
                  (stageOfEq (eraseEmpty_cons_of_eq_empty hY rest hY₀).symm))).eraseEmpty) :=
            congrArg _ ((eraseEmpty_map _ _).symm.trans (congrArg eraseEmpty (map_map B _ _)))
        _ = (cons hY rest).eraseEmpty.concat ((B.map (cons hY rest).eraseEmptyLast).eraseEmpty) :=
            congrArg (fun G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((cons hY rest).stage (Fin.last _))
              ((cons hY rest).eraseEmpty.stage (Fin.last _)) ω =>
                (cons hY rest).eraseEmpty.concat ((B.map G).eraseEmpty))
              (eraseEmptyLast_cons_of_eq_empty hY rest hY₀).symm
    · calc ((cons hY rest).concat B).eraseEmpty
          = cons hY (rest.concat B).eraseEmpty := eraseEmpty_cons_of_ne_empty hY (rest.concat B) hY₀
        _ = cons hY (rest.eraseEmpty.concat ((B.map rest.eraseEmptyLast).eraseEmpty)) :=
            congrArg (cons hY) ih
        _ = (cons hY rest).eraseEmpty.concat
              (((B.map rest.eraseEmptyLast).eraseEmpty).map
                (stageOfEq (L₁ := cons hY rest.eraseEmpty)
                  (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm)) :=
            (concat_map_stageOfEq (L₁ := cons hY rest.eraseEmpty)
              (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm _).symm
        _ = (cons hY rest).eraseEmpty.concat
              ((B.map (rest.eraseEmptyLast.trans (stageOfEq (L₁ := cons hY rest.eraseEmpty)
                (eraseEmpty_cons_of_ne_empty hY rest hY₀).symm))).eraseEmpty) :=
            congrArg _ ((eraseEmpty_map _ _).symm.trans (congrArg eraseEmpty (map_map B _ _)))
        _ = (cons hY rest).eraseEmpty.concat ((B.map (cons hY rest).eraseEmptyLast).eraseEmpty) :=
            congrArg (fun G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((cons hY rest).stage (Fin.last _))
              ((cons hY rest).eraseEmpty.stage (Fin.last _)) ω =>
                (cons hY rest).eraseEmpty.concat ((B.map G).eraseEmpty))
              (eraseEmptyLast_cons_of_ne_empty hY rest hY₀).symm

/-- Deleting the empty blow-ups of a concatenation whose second piece is already clean is deleting
them from the concatenation itself (`eraseEmpty_concat_eraseEmpty`). -/
theorem eraseEmpty_concat_eraseEmpty (A : BlowUpSequence ψ₀ M)
    (B : BlowUpSequence ψ₀ (A.stage (Fin.last _))) :
    (A.concat B.eraseEmpty).eraseEmpty = (A.concat B).eraseEmpty := by
  rw [eraseEmpty_concat, eraseEmpty_concat, eraseEmpty_map, eraseEmpty_eraseEmpty,
    ← eraseEmpty_map]

end AnalyticManifold.BlowUpSequence

end
