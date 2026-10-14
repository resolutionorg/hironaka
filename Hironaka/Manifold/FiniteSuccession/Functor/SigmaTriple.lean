/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Basic
public import Hironaka.Manifold.SigmaManifold
import Hironaka.AnalyticSpace.Manifold.Sigma
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Disjoint unions of triples, and the unfolding of the commutation predicates

* The inclusion `sigmaMk N i` of a piece into the disjoint union `sigmaManifold N` is an analytic
  open embedding (`isLocalDiffeomorph_sigmaMk`: the local inverse is the projection to the piece
  on the open range, analytic because its composite with the inclusion is the identity,
  `contMDiffAt_sigmaMk_comp_iff`); a triple on the disjoint union whose data restrict along the
  inclusions to given triples on the pieces is their disjoint union (`isSigmaOf_sigma`,
  [Kol07, Warning 38]); the class of all triples is closed under disjoint unions.
* The equations of the push-forward of lists on `nil` and its length (`pushforward_nil`,
  `length_pushforward`; [Kol07, Definition 30, 30.3]).
* The unfolding lemmas of the two commutation classes of [Kol07, 34.1], the commutation with a
  composite (`commutesWith_comp`) and its converse along a surjective local isomorphism
  (`commutesWith_of_surjective_comp`, the "(34.1) is a local property" of the proof of
  [Kol07, Theorem 36]).
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

section Sigma

variable {σ : Type u} [Countable σ] (N : σ → AnalyticManifold.{u} 𝕜 E)

open scoped Classical in
/-- The projection of the disjoint union onto the `i`-th piece, `x` on the other pieces. -/
def sigmaProj (i : σ) (x : N i) : sigmaManifold N → N i := fun p =>
  if h : p.1 = i then h ▸ p.2 else x

open scoped Classical in
theorem sigmaProj_mk (i : σ) (x y : N i) : sigmaProj N i x (sigmaMk N i y) = y := by
  change (if h : (⟨i, y⟩ : Σ j, (N j : Type u)).1 = i then h ▸ (⟨i, y⟩ : Σ j, (N j : Type u)).2
    else x) = y
  rw [dite_eq_left rfl]

/-- The local inverse of the inclusion `sigmaMk N i`: the projection on the open range. -/
def sigmaMkPartialDiffeomorph (i : σ) (x : N i) :
    PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (N i) (sigmaManifold N) ω where
  toFun := sigmaMk N i
  invFun := sigmaProj N i x
  source := univ
  target := range (sigmaMk N i)
  map_source' y _ := mem_range_self y
  map_target' _ _ := mem_univ _
  left_inv' y _ := sigmaProj_mk N i x y
  right_inv' := by
    rintro _ ⟨y, rfl⟩
    rw [sigmaProj_mk]
  open_source := isOpen_univ
  open_target := by
    change IsOpen (range fun y => (Sigma.mk i y : Σ j, (N j : Type u)))
    exact isOpen_range_sigmaMk
  contMDiffOn_toFun := (sigmaMk N i).contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    rintro _ ⟨y, rfl⟩
    refine ContMDiffAt.contMDiffWithinAt ?_
    have hid : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        ((@Sigma.mk σ (fun j => (N j : Type u)) i) ∘ sigmaProj N i x) (sigmaMk N i y) := by
      refine contMDiffAt_id.congr_of_eventuallyEq ?_
      have hopen : IsOpen (range fun y => (Sigma.mk i y : Σ j, (N j : Type u))) :=
        isOpen_range_sigmaMk
      filter_upwards [hopen.mem_nhds (mem_range_self y)] with p hp
      obtain ⟨z, rfl⟩ := hp
      change (⟨i, sigmaProj N i x (sigmaMk N i z)⟩ : Σ j, (N j : Type u)) = ⟨i, z⟩
      rw [sigmaProj_mk]
    exact (contMDiffAt_sigmaMk_comp_iff (M := fun j => (N j : Type u)) (i := i)
      (h := sigmaProj N i x)).mp hid

/-- The inclusion of a piece into the disjoint union is a local analytic
isomorphism. -/
theorem isLocalDiffeomorph_sigmaMk (i : σ) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (sigmaMk N i) := fun x =>
  IsLocalDiffeomorphAt.of_eqOn (sigmaMkPartialDiffeomorph N i x) (mem_univ x) fun _ _ => rfl

/-- The inclusion of a piece is an analytic open embedding. -/
theorem isAnalyticOpenEmbedding_sigmaMk (i : σ) : IsAnalyticOpenEmbedding (sigmaMk N i) :=
  ⟨isLocalDiffeomorph_sigmaMk N i, fun _ _ h =>
    sigma_mk_injective (β := fun j => (N j : Type u)) (i := i) h⟩

/-- [Kol07, Warning 38]: a triple on the disjoint union whose data restrict along
the inclusions to given triples on the pieces is their disjoint union. -/
theorem AnalyticTriple.isSigmaOf_sigma (T : AnalyticTriple ψ₀ (sigmaManifold N))
    (Ts : ∀ i, AnalyticTriple ψ₀ (N i)) (hTs : ∀ i, (Ts i).IsPullbackOf T (sigmaMk N i)) :
    T.IsSigmaOf Ts (sigmaMk N) := by
  refine ⟨isAnalyticOpenEmbedding_sigmaMk N, fun i j hij => ?_, ?_, hTs⟩
  · change Disjoint (range (sigmaMk N i)) (range (sigmaMk N j))
    rw [Set.disjoint_left]
    rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
    exact hij (congrArg Sigma.fst hz).symm
  · refine eq_univ_of_forall fun p => mem_iUnion.mpr ⟨p.1, p.2, ?_⟩
    rfl

/-- [Kol07, Warning 38]: the class of all triples is closed under countable disjoint
unions. -/
theorem AnalyticTriple.closedUnderSigma_univ :
    AnalyticTriple.ClosedUnderSigma (ψ₀ := ψ₀)
      (fun {_ : AnalyticManifold.{u} 𝕜 E} (_ : AnalyticTriple ψ₀ _) => True) :=
  fun _ _ _ _ _ _ => trivial

end Sigma

end Manifold

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### [Kol07, Definition 30, 30.3] on lists: the equations of `pushforward` -/

variable {s : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

theorem length_pushforwardAux : ∀ {Tᵢ : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    (P : PushforwardStage ψ s Tᵢ)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Tᵢ),
    (pushforwardAux P L).length = L.length
  | _, _, nil _ => rfl
  | _, P, cons hZ rest => by
    change (pushforwardAux (P.blowUpStep hZ _) rest).length + 1 = rest.length + 1
    rw [length_pushforwardAux]

variable {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} (hS : IsClosedSubmanifold ψ S s)

theorem pushforward_nil :
    (nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      hS.toAnalyticManifold).pushforward hS = nil M := rfl

theorem length_pushforward
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) hS.toAnalyticManifold) :
    (L.pushforward hS).length = L.length :=
  length_pushforwardAux _ L

end AnalyticManifold.BlowUpSequence

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The unfolding of 34.1's classes -/

namespace AnalyticBlowUpSequenceAssignment

variable {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  {M N : AnalyticManifold.{u} 𝕜 E}

theorem CommutesWithSurjectiveLocalIsos.commutesWith {B : AnalyticBlowUpSequenceAssignment ψ₀ Dom}
    (hB : B.CommutesWithSurjectiveLocalIsos) {T : AnalyticTriple ψ₀ M} {T' : AnalyticTriple ψ₀ N}
    {h : AnalyticMap N M} (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) (hT' : T'.IsPullbackOf T h) : B.CommutesWith T T' h hh :=
  hB T T' h hh hs hT'

theorem CommutesWithOpenEmbeddings.seq_eq {B : AnalyticBlowUpSequenceAssignment ψ₀ Dom}
    (hB : B.CommutesWithOpenEmbeddings) {T : AnalyticTriple ψ₀ M} {T' : AnalyticTriple ψ₀ N}
    {h : AnalyticMap N M} (hh : IsAnalyticOpenEmbedding h) (hT' : T'.IsPullbackOf T h)
    (hT : Dom T) (hT'' : Dom T') :
    B.seq T' hT'' = ((B.seq T hT).pullback h hh.1).eraseEmpty :=
  hB T T' h hh hT' hT hT''

/-- [Kol07, 34.1] with 30.1's functoriality: a functor commutes with a composite of maps it commutes
with, the middle triple in the class. -/
theorem commutesWith_comp (B : AnalyticBlowUpSequenceAssignment ψ₀ Dom)
    {P : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M} {T' : AnalyticTriple ψ₀ N}
    {T'' : AnalyticTriple ψ₀ P} {h : AnalyticMap N M} {hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h}
    {k : AnalyticMap P N} {hk : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω k} (hT' : Dom T')
    (h₁ : B.CommutesWith T T' h hh) (h₂ : B.CommutesWith T' T'' k hk) :
    B.CommutesWith T T'' (h.comp k)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hh hk) := by
  intro hT hT''
  rw [h₂ hT' hT'', h₁ hT hT', AnalyticManifold.BlowUpSequence.pullback_comp]

/-- The proof of [Kol07, Theorem 36] ("(34.1) is a local property"): if `B` commutes with a
surjective local analytic isomorphism `g : P → N` and with `h ∘ g`, it commutes with `h : N → M`. -/
theorem commutesWith_of_surjective_comp (B : AnalyticBlowUpSequenceAssignment ψ₀ Dom)
    {P : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M} {T' : AnalyticTriple ψ₀ N}
    {T'' : AnalyticTriple ψ₀ P} {h : AnalyticMap N M} (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    {g : AnalyticMap P N} (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hgs : Function.Surjective g) (hT'' : Dom T'') (h₁ : B.CommutesWith T' T'' g hg)
    (h₂ : B.CommutesWith T T'' (h.comp g)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hh hg)) :
    B.CommutesWith T T' h hh := by
  intro hT hT'
  refine AnalyticManifold.BlowUpSequence.pullback_injective_of_surjective g hg hgs _ _ ?_
  rw [← h₁ hT' hT'', h₂ hT hT'', AnalyticManifold.BlowUpSequence.pullback_comp]

end AnalyticBlowUpSequenceAssignment

end Manifold

end
