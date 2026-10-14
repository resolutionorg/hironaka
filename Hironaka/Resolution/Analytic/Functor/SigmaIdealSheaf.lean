/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.SigmaTriple
public import Hironaka.Resolution.Analytic.Functor.EmbeddedDesingFam
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The disjoint union of ideal sheaves and of triples

The disjoint union of a family of triples ([Kol07, Warning 38]; the proof of
[Kol07, Proposition 37]). The triples on disjoint unions of
`Hironaka.Manifold.FiniteSuccession.Functor.SigmaTriple` are pull-backs of a global triple along
`sigmaDescMap`; when the pieces have no common global triple (as for the local pieces of an
embedded desingularization), the disjoint union of their ambient triples needs its ideal sheaf
built: `IdealSheaf.sigmaOf I`, at a point of the `i`-th summand the pull-back of `I i` along the
summand projection `sigmaProj` (analytic on the whole union, the local inverse of `sigmaMk` on the
summand), glued by `ofStalks` along the clopen summands. Its restriction to each summand is `I i`
(`comap_sigmaMk_sigmaOf`); reducedness and non-vanishing pass to it stalkwise.
`AnalyticTriple.sigmaOfEmpty` is the disjoint union of triples with empty divisors, with its
`IsSigmaOf`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology Opposite
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

section General

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E}

/-- Two ideal-sheaf pull-backs along maps agreeing on an open agree
there (`pullback_pullback`, `pullback_congr`). -/
theorem IdealSheaf.pullback_restrictOpens_congr {P : AnalyticManifold.{u} 𝕜 E}
    (J : AnalyticManifold.IdealSheaf P) (φ φ' : AnalyticMap M P)
        (V : Opens M)
    (h : Set.EqOn ⇑φ ⇑φ' (V : Set M)) :
    AnalyticManifold.IdealSheaf.restrict (J.pullback φ φ.contMDiff) V =
      AnalyticManifold.IdealSheaf.restrict (J.pullback φ' φ'.contMDiff) V := by
  change (J.pullback ⇑φ φ.contMDiff).pullback ⇑(M.inclusion V) (M.inclusion V).contMDiff =
    (J.pullback ⇑φ' φ'.contMDiff).pullback ⇑(M.inclusion V) (M.inclusion V).contMDiff
  rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr _ _ _ (funext fun v => h v.2)

/-- An ideal sheaf's stalk at a point of an open is determined by its
restriction there (the germ map of the inclusion is bijective). -/
theorem IdealSheaf.stalkIdeal_eq_of_restrictOpens_eq (K K' : AnalyticManifold.IdealSheaf M)
    (V : Opens M)
    (h : K.restrict V = K'.restrict V) (p : M) (hp : p ∈ V) :
    K.stalkIdeal p = K'.stalkIdeal p := by
  obtain ⟨g, hg⟩ : ∃ g, g = germMap (⇑(M.inclusion V)) (M.inclusion V).contMDiff
    (⟨p, hp⟩ : M.restrict V) := ⟨_, rfl⟩
  have hbij : Function.Bijective g := by
    rw [hg]
    exact germMap_bijective_of_isLocalDiffeomorphAt (⇑(M.inclusion V)) (M.inclusion V).contMDiff
      (isLocalDiffeomorph_inclusion M V ⟨p, hp⟩)
  have h1 : Ideal.map g (K.stalkIdeal p) = Ideal.map g (K'.stalkIdeal p) := by
    have e1 := IdealSheaf.stalkIdeal_pullback (⇑(M.inclusion V)) (M.inclusion V).contMDiff K
      (⟨p, hp⟩ : M.restrict V)
    have e2 := IdealSheaf.stalkIdeal_pullback (⇑(M.inclusion V)) (M.inclusion V).contMDiff K'
      (⟨p, hp⟩ : M.restrict V)
    have e3 := congrArg (fun L : AnalyticManifold.IdealSheaf (M.restrict V) =>
      L.stalkIdeal (⟨p, hp⟩ : M.restrict V)) h
    rw [hg]
    exact e1.symm.trans (e3.trans e2)
  have h2 := congrArg (Ideal.comap g) h1
  exact ((Ideal.comap_map_of_bijective g hbij).symm.trans h2).trans
    (Ideal.comap_map_of_bijective g hbij)

variable {σ : Type u} [Countable σ] (N : σ → AnalyticManifold.{u} 𝕜 E)

open scoped Classical in
/-- **The projection onto a summand is analytic on the whole disjoint
union**: the identity on the summand, constant elsewhere (`ContMDiff.sigmaDesc`). -/
theorem _root_.Hironaka.Manifold.contMDiff_sigmaProj (i : σ) (x : N i) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω (sigmaProj N i x) := by
  refine ContMDiff.sigmaDesc (I := 𝓘(𝕜, E)) (J := 𝓘(𝕜, E)) (n := ω)
    (M := fun k => (N k : Type u)) (P := (N i : Type u))
    (f := fun k (z : N k) => sigmaProj N i x ⟨k, z⟩) fun k => ?_
  by_cases hk : k = i
  · subst hk
    exact contMDiff_id.congr fun z => sigmaProj_mk N _ x z
  · exact contMDiff_const.congr fun z => dite_eq_right hk

/-- The projection is a local analytic isomorphism at the points of
its summand — the inverse of `sigmaMkPartialDiffeomorph`. -/
theorem _root_.Hironaka.Manifold.isLocalDiffeomorphAt_sigmaProj_mk (i : σ) (x y : N i) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (sigmaProj N i x) (sigmaMk N i y) :=
  IsLocalDiffeomorphAt.of_eqOn (sigmaMkPartialDiffeomorph N i x).symm ⟨y, rfl⟩ fun _ _ => rfl

/-- The summand projection as an analytic map. -/
abbrev _root_.Hironaka.Manifold.sigmaProjMap (i : σ) (x : N i) : AnalyticMap (sigmaManifold N)
    (N i) :=
  ⟨sigmaProj N i x, contMDiff_sigmaProj N i x⟩

/-- The stalk ideals of the disjoint union: at a point of the `i`-th summand, the
pull-back of `I i` along the projection based at that point. -/
def _root_.Hironaka.Manifold.sigmaStalkIdeals (I : ∀ i, AnalyticManifold.IdealSheaf (N i)) :
    ∀ p : (sigmaManifold N : Type u),
      Ideal ((structureSheaf 𝕜 E (sigmaManifold N)).presheaf.stalk p) :=
  fun p => ((I p.1).pullback (sigmaProj N p.1 p.2) (contMDiff_sigmaProj N p.1 p.2)).stalkIdeal p

/-- On the `i`-th summand the pull-backs along two projections agree. -/
theorem _root_.Hironaka.Manifold.stalkIdeal_pullback_sigmaProj_eq (I : ∀ i,
    AnalyticManifold.IdealSheaf (N i)) (i : σ)
    (x y z : N i) :
    ((I i).pullback (sigmaProj N i x) (contMDiff_sigmaProj N i x)).stalkIdeal (sigmaMk N i z) =
      ((I i).pullback (sigmaProj N i y) (contMDiff_sigmaProj N i y)).stalkIdeal (sigmaMk N i z) :=
  IdealSheaf.stalkIdeal_eq_of_restrictOpens_eq _ _ ⟨range (sigmaMk N i), isOpen_range_sigmaMk⟩
    (IdealSheaf.pullback_restrictOpens_congr (I i) (sigmaProjMap N i x) (sigmaProjMap N i y) _
      (by
        rintro _ ⟨w, rfl⟩
        exact (sigmaProj_mk N i x w).trans (sigmaProj_mk N i y w).symm))
    _ ⟨z, rfl⟩

/-- The stalk ideals have local generators: those of the pull-back at the point,
restricted to the clopen summand, where the pull-backs along the two projections agree. -/
theorem _root_.Hironaka.Manifold.hasLocalGenerators_sigmaStalkIdeals (I : ∀ i,
    AnalyticManifold.IdealSheaf (N i)) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E (sigmaManifold N))
      (sigmaStalkIdeals N I) := by
  intro p
  obtain ⟨U, hpU, k, f, -, hf⟩ :=
    ((I p.1).pullback (sigmaProj N p.1 p.2) (contMDiff_sigmaProj N p.1 p.2)).exists_generators p
  refine ⟨U ⊓ ⟨range (sigmaMk N p.1), isOpen_range_sigmaMk⟩, ⟨hpU, ⟨p.2, rfl⟩⟩, Fin k,
    inferInstance,
    fun j => (structureSheaf 𝕜 E (sigmaManifold N)).presheaf.map (homOfLE inf_le_left).op (f j),
    fun q hq => ?_⟩
  obtain ⟨hqU, y, hy⟩ := hq
  subst hy
  change ((I p.1).pullback (sigmaProj N p.1 y) (contMDiff_sigmaProj N p.1 y)).stalkIdeal
    (sigmaMk N p.1 y) = _
  rw [stalkIdeal_pullback_sigmaProj_eq N I p.1 y p.2 y, hf _ hqU]
  exact congrArg Ideal.span (congrArg Set.range
    (funext fun j => (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm))

/-- ([Kol07, Warning 38]) **The disjoint union of ideal sheaves** on the disjoint
union of manifolds: at a point of the `i`-th summand the pull-back of `I i` along the summand
projection (`ofStalks`). -/
def IdealSheaf.sigmaOf (I : ∀ i, AnalyticManifold.IdealSheaf (N i)) :
    AnalyticManifold.IdealSheaf (sigmaManifold N) :=
  IdealSheaf.ofStalks (structureSheaf 𝕜 E (sigmaManifold N)) (sigmaStalkIdeals N I)
    (hasLocalGenerators_sigmaStalkIdeals N I)

theorem IdealSheaf.stalkIdeal_sigmaOf (I : ∀ i, AnalyticManifold.IdealSheaf (N i))
    (p : sigmaManifold N) :
    (IdealSheaf.sigmaOf N I).stalkIdeal p =
      ((I p.1).pullback (sigmaProj N p.1 p.2) (contMDiff_sigmaProj N p.1 p.2)).stalkIdeal p :=
  IdealSheaf.stalkIdeal_ofStalks (𝒪 := structureSheaf 𝕜 E (sigmaManifold N)) (sigmaStalkIdeals N I)
    (hasLocalGenerators_sigmaStalkIdeals N I) p

/-- `stalkIdeal_sigmaOf` at a point of the `i`-th summand, spelled through
`sigmaMk`. -/
theorem IdealSheaf.stalkIdeal_sigmaOf_mk (I : ∀ i, AnalyticManifold.IdealSheaf (N i)) (i : σ)
    (y : N i) :
    (IdealSheaf.sigmaOf N I).stalkIdeal (sigmaMk N i y) =
      ((I i).pullback (sigmaProj N i y) (contMDiff_sigmaProj N i y)).stalkIdeal (sigmaMk N i y) :=
  IdealSheaf.stalkIdeal_ofStalks (𝒪 := structureSheaf 𝕜 E (sigmaManifold N)) (sigmaStalkIdeals N I)
    (hasLocalGenerators_sigmaStalkIdeals N I) _

/-- **Its restriction to each summand is the summand's ideal sheaf** (`pullback_pullback`,
`sigmaProj_mk`, `pullback_id_eq_self`). -/
theorem IdealSheaf.comap_sigmaMk_sigmaOf (I : ∀ i, AnalyticManifold.IdealSheaf (N i)) (i : σ) :
    (IdealSheaf.sigmaOf N I).pullback _ (sigmaMk N i).contMDiff = I i := by
  refine IdealSheaf.ext fun y => ?_
  have hcomp : sigmaProj N i y ∘ ⇑(sigmaMk N i) = id := funext (sigmaProj_mk N i y)
  change ((IdealSheaf.sigmaOf N I).pullback ⇑(sigmaMk N i) (sigmaMk N i).contMDiff).stalkIdeal y =
    _
  rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_sigmaOf_mk,
    ← IdealSheaf.stalkIdeal_pullback, IdealSheaf.pullback_pullback,
    IdealSheaf.pullback_congr _ _ contMDiff_id hcomp, IdealSheaf.pullback_id_eq_self]

/-- Reducedness passes to the disjoint union (stalkwise, along the bijective germ maps of the
projections). -/
theorem IdealSheaf.isReduced_sigmaOf (I : ∀ i, AnalyticManifold.IdealSheaf (N i))
    (h : ∀ i, (I i).IsReduced) : (IdealSheaf.sigmaOf N I).IsReduced := by
  intro p
  suffices key : ∀ (i : σ) (y : N i),
      ((IdealSheaf.sigmaOf N I).stalkIdeal (sigmaMk N i y)).IsRadical from key p.1 p.2
  intro i y
  rw [IdealSheaf.stalkIdeal_sigmaOf_mk, IdealSheaf.stalkIdeal_pullback]
  obtain ⟨hinj, hsurj⟩ := germMap_bijective_of_isLocalDiffeomorphAt _ _
    (isLocalDiffeomorphAt_sigmaProj_mk N i y y)
  have hker : RingHom.ker (germMap (sigmaProj N i y) (contMDiff_sigmaProj N i y) (sigmaMk N i y)) ≤
      (I i).stalkIdeal (sigmaProj N i y (sigmaMk N i y)) := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  rw [← Ideal.radical_eq_iff, ← Ideal.map_radical_of_surjective hsurj hker,
    Ideal.radical_eq_iff.mpr (h i _)]

/-- Non-vanishing everywhere passes to the disjoint union (the order is preserved under the
local isomorphism, `ord_pullback_of_isLocalDiffeomorphAt`). -/
theorem IdealSheaf.isNonzeroEverywhere_sigmaOf [FiniteDimensional 𝕜 E]
    (I : ∀ i, AnalyticManifold.IdealSheaf (N i)) (h : ∀ i, (I i).IsNonzeroEverywhere) :
    (IdealSheaf.sigmaOf N I).IsNonzeroEverywhere := by
  intro p hb
  suffices key : ∀ (i : σ) (y : N i), (IdealSheaf.sigmaOf N I).stalkIdeal (sigmaMk N i y) ≠ ⊥ from
    key p.1 p.2 hb
  intro i y hb
  rw [IdealSheaf.stalkIdeal_sigmaOf_mk] at hb
  have h1 : ((I i).pullback (sigmaProj N i y) (contMDiff_sigmaProj N i y)).ord (sigmaMk N i y) =
      ⊤ :=
    (IdealSheaf.ord_eq_top_iff _ _).mpr hb
  have h2 : (I i).ord (sigmaProj N i y (sigmaMk N i y)) = ⊤ :=
    (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt (sigmaProj N i y) (contMDiff_sigmaProj N i y)
      (I i) (isLocalDiffeomorphAt_sigmaProj_mk N i y y)).symm.trans h1
  exact h i _ ((IdealSheaf.ord_eq_top_iff _ _).mp h2)

variable {n : ℕ} (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜))

/-- ([Kol07, Warning 38]) **The disjoint union of triples with empty divisors.** -/
def AnalyticTriple.sigmaOfEmpty (Ts : ∀ i, AnalyticTriple ψ₀ (N i))
    (_hF : ∀ i, (Ts i).F = HypersurfaceFamily.empty _) : AnalyticTriple ψ₀ (sigmaManifold N) where
  I := IdealSheaf.sigmaOf N fun i => (Ts i).I
  isNonzeroEverywhere :=
    have := finiteDimensional_of_chartIso ψ₀
    IdealSheaf.isNonzeroEverywhere_sigmaOf N (fun i => (Ts i).I) fun i =>
      (Ts i).isNonzeroEverywhere
  F := HypersurfaceFamily.empty _
  isSnc := HypersurfaceFamily.isSnc_empty

/-- Each triple is the pull-back of the disjoint union along its summand's inclusion. -/
theorem AnalyticTriple.isPullbackOf_sigmaOfEmpty (Ts : ∀ i, AnalyticTriple ψ₀ (N i))
    (hF : ∀ i, (Ts i).F = HypersurfaceFamily.empty _) (i : σ) :
    (Ts i).IsPullbackOf (AnalyticTriple.sigmaOfEmpty N ψ₀ Ts hF) (sigmaMk N i) :=
  ⟨(IdealSheaf.comap_sigmaMk_sigmaOf N (fun i => (Ts i).I) i).symm,
    (hF i).trans (congrArg (HypersurfaceFamily.mk PEmpty.{u + 1}) (funext fun j => PEmpty.elim j))⟩

/-- The disjoint union IS the disjoint union of the triples (`isSigmaOf_sigma`). -/
theorem AnalyticTriple.isSigmaOf_sigmaOfEmpty (Ts : ∀ i, AnalyticTriple ψ₀ (N i))
    (hF : ∀ i, (Ts i).F = HypersurfaceFamily.empty _) :
    (AnalyticTriple.sigmaOfEmpty N ψ₀ Ts hF).IsSigmaOf Ts (sigmaMk N) :=
  AnalyticTriple.isSigmaOf_sigma N _ Ts (AnalyticTriple.isPullbackOf_sigmaOfEmpty N ψ₀ Ts hF)

end General

section BED

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {σ : Type u} [Countable σ]
  (N : σ → AnalyticManifold.{u} 𝕜 (Fin n → 𝕜))

/-- **The class of `bed` is closed under disjoint unions with empty divisors**: the divisor
is empty and the ideal reduced (`isReduced_sigmaOf`). -/
theorem _root_.Hironaka.Manifold.domBEDan_sigmaOfEmpty
    (Ts : ∀ i, AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (N i))
    (hF : ∀ i, (Ts i).F = HypersurfaceFamily.empty _) (h : ∀ i, DomBEDan 𝕜 (Ts i)) :
    DomBEDan 𝕜
      (AnalyticTriple.sigmaOfEmpty N (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Ts hF) :=
  ⟨inferInstanceAs (IsEmpty PEmpty.{u + 1}),
    IdealSheaf.isReduced_sigmaOf N (fun i => (Ts i).I) fun i => (h i).2⟩

end BED

end Manifold

end
