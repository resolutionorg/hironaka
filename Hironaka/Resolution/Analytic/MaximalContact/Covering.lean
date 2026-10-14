/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Resolution.Analytic.LocalIsoEquiv
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.Chart.MaximalContact
import Hironaka.Manifold.FiniteSuccession.Functor.LocalCover
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaLocalDiffeo
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.SigmaManifold
import Hironaka.Resolution.Analytic.MaximalContact.AgreeOnSubspaceLemmas
import Hironaka.Resolution.Analytic.MaximalContact.Propagation
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Uniqueness of maximal contact in local-isomorphism form

The covering step of Kollár's proof of the uniqueness of maximal contact [Kol07, 95]: "the images
of finitely many of the `U(p)` cover `X`; we can take `U` to be their disjoint union". On a second
countable analytic manifold, countably many of the neighbourhoods `U(p)` of
`locallyIsoEquivalent_on_nhd` (`Hironaka/Resolution/Analytic/MaximalContact/Propagation.lean`) cover
`cosupp(I, m)` (`TopologicalSpace.countable_cover_nhdsWithin`), and their disjoint union
`U := ∐ U(p)` (`sigmaManifold`) carries the two local analytic isomorphisms `ψ := ∐ (inclusions)`
and `ψ' := ∐ Φ(p)` (`ContMDiff.sigmaDesc`, `IsLocalDiffeomorph.sigmaDesc`). Their images contain
`cosupp(I, m)`: for `ψ` by the cover, for `ψ'` because `Φ(p)` fixes every point of
`cosupp(I, m) ∩ U(p)` — such a point lies on `V(MC(I))`, where (4′) forces `ψ' = ψ` (the order of
`MC(I) = D^{m−1}I` there is `1`, `ord_iteratedDeriv_eq_one`).

Conditions (1′)–(4′) of [Kol07, Definition 91] descend from the summands: (1′) and (3′) are
pointwise; for (2′) and (4′) the stalk map of the summand inclusion `σ_t : U(t) → ∐ U(p)` is
bijective — because `ψ ∘ σ_t = ι_{U(t)}` and both `ψ` and the inclusion have bijective stalk maps
(`germMap_val_bijective`, `germMap_bijective_of_isLocalDiffeomorphAt`) — so the stalks of `ψ^*I`,
`ψ'^*I` and of `MC(ψ^*I)` at `σ_t x` are read off from the stalks on `U(t)` through
`Ideal.comap_map_of_bijective`, where (2′) and (4′) hold.

The result (`maximalContact_locallyIsoEquivalent`) is Kollár's uniqueness of maximal contact
[Kol07, Theorem 92] on analytic manifolds, with local analytic isomorphisms in place of étale
surjections; it feeds the independence of the order-reduction algorithm from the choice of the
hypersurface of maximal contact
(`Hironaka/Resolution/Analytic/OrderReduction/FamilyIndependence.lean`).
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section Tools

variable {M N P : AnalyticManifold.{u} 𝕜 E}

/-- The stalk map of a composite of analytic maps is the composite of the stalk maps
(`germMapOn_germMapOn`, bundled). -/
theorem germMap_comp (f : AnalyticMap N M) (g : AnalyticMap P N) (x : P) :
    (germMap (⇑g) g.contMDiff x).comp (germMap (⇑f) f.contMDiff (g x)) =
      germMap (⇑(f.comp g)) (f.comp g).contMDiff x := by
  refine RingHom.ext fun s => ?_
  exact germMapOn_germMapOn f.contMDiff.contMDiffOn g.contMDiff.contMDiffOn (Opens.mem_top x) rfl
    (Opens.mem_top _) rfl (f.comp g).contMDiff.contMDiffOn (Opens.mem_top x) rfl s

end Tools

variable [FiniteDimensional 𝕜 E] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- **Uniqueness of maximal contact in local-isomorphism form** ([Kol07, Theorem 92], through the
covering step of [Kol07, 95]): for `I` MC-invariant with `ord I ≤ m` everywhere, `m ≥ 1`, `E` snc,
and `H, H'` smooth hypersurfaces of maximal contact for `I` (their ideal sheaves contained in
`MC(I) = D^{m−1}(I)`) such that `H + E` and `H' + E` both have simple normal crossings, `H` and `H'`
are local-isomorphism equivalent with respect to `(M, I, E)`: countably many of the neighbourhoods
`U(p)` of `locallyIsoEquivalent_on_nhd` cover `cosupp(I, m)`, and on their disjoint union `∐ U(p)`
the pair (`∐` inclusions, `∐ Φ(p)`) satisfies (1′)–(4′) summand by summand. -/
theorem maximalContact_locallyIsoEquivalent (I : AnalyticManifold.IdealSheaf M) {m : ℕ}
    (hm : 1 ≤ m)
    (hI : I.iteratedDeriv (m - 1) * I.deriv ≤ I) (hmax : ∀ y, I.ord y ≤ m)
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ) {H H' : Set M} (hH : IsClosedSubmanifold ψ H 1)
    (hH' : IsClosedSubmanifold ψ H' 1) (hHmc : hH.idealSheaf ≤ I.iteratedDeriv (m - 1))
    (hH'mc : hH'.idealSheaf ≤ I.iteratedDeriv (m - 1)) (hHF : (F.append H).IsSnc ψ)
    (hH'F : (F.append H').IsSnc ψ) : Nonempty (LocallyIsoEquivalentMC I m F H H') := by
  classical
  -- the neighbourhoods of `locallyIsoEquivalent_on_nhd` at every point of `cosupp(I, m)`
  have hE : ∀ p : {x : M // (m : ℕ∞) ≤ I.ord x}, ∃ (U : Opens M) (hpU : p.1 ∈ U)
      (Φ : AnalyticMap (M.restrict U) M),
      IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω Φ ∧ Topology.IsOpenEmbedding ⇑Φ ∧ Φ ⟨p.1, hpU⟩ = p.1 ∧
        ⇑(M.inclusion U) ⁻¹' H = ⇑Φ ⁻¹' H' ∧
        I.pullback _ (M.inclusion U).contMDiff =
            I.pullback Φ Φ.contMDiff ∧
        (∀ j, ⇑(M.inclusion U) ⁻¹' F.hyp j = ⇑Φ ⁻¹' F.hyp j) ∧
        AgreeOnSubspace (M.inclusion U) Φ
          ((I.pullback _ (M.inclusion U).contMDiff).iteratedDeriv (m - 1)) :=
    fun p => locallyIsoEquivalent_on_nhd ψ I hm hI F hF hH hH' hHmc hH'mc hHF hH'F p.1
      (le_antisymm (hmax p.1) p.2)
  choose U hpU Φ hloc _hemb _hΦp h1 h2 h3 h4 using hE
  -- a countable subcover of `cosupp(I, m)` by the `U(p)`
  let f : M → Set M := fun x =>
    if h : (m : ℕ∞) ≤ I.ord x then (U ⟨x, h⟩ : Set M) else Set.univ
  have hf : ∀ x ∈ {x : M | (m : ℕ∞) ≤ I.ord x}, f x ∈ 𝓝[{x : M | (m : ℕ∞) ≤ I.ord x}] x := by
    intro x hx
    have hx' : (m : ℕ∞) ≤ I.ord x := hx
    have hfx : f x = U ⟨x, hx'⟩ := dite_eq_left hx'
    rw [hfx]
    exact nhdsWithin_le_nhds ((U ⟨x, hx'⟩).2.mem_nhds (hpU ⟨x, hx'⟩))
  obtain ⟨T, hTS, hTc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hf
  have : Countable T := hTc.to_subtype
  let idx : T → {x : M // (m : ℕ∞) ≤ I.ord x} := fun t => ⟨t.1, hTS t.2⟩
  let N : T → AnalyticManifold.{u} 𝕜 E := fun t => M.restrict (U (idx t))
  -- the two maps out of the disjoint union
  let Ψ : AnalyticMap (sigmaManifold N) M :=
    ⟨fun q => (M.inclusion (U (idx q.1))) q.2,
      ContMDiff.sigmaDesc (M := fun t => (N t : Type u)) fun t =>
        (M.inclusion (U (idx t))).contMDiff⟩
  let Ψ' : AnalyticMap (sigmaManifold N) M :=
    ⟨fun q => Φ (idx q.1) q.2,
      ContMDiff.sigmaDesc (M := fun t => (N t : Type u)) fun t => (Φ (idx t)).contMDiff⟩
  have hΨloc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω Ψ :=
    IsLocalDiffeomorph.sigmaDesc (M := fun t => (N t : Type u)) fun t =>
      isLocalDiffeomorph_inclusion _ (U (idx t))
  have hΨ'loc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω Ψ' :=
    IsLocalDiffeomorph.sigmaDesc (M := fun t => (N t : Type u)) fun t => hloc (idx t)
  -- the cover: every point of `cosupp(I, m)` lies in some `U(t)`, where `Φ(t)` fixes it
  have hmemU : ∀ y ∈ {x : M | (m : ℕ∞) ≤ I.ord x}, ∃ t : T, y ∈ U (idx t) := by
    intro y hy
    obtain ⟨t, ht, hyt⟩ := Set.mem_iUnion₂.mp (hcov hy)
    refine ⟨⟨t, ht⟩, ?_⟩
    have hfy : f t = U ⟨t, hTS ht⟩ := dite_eq_left (hTS ht)
    rw [hfy] at hyt
    exact hyt
  have hfix : ∀ (t : T) (y : M.restrict (U (idx t))), (m : ℕ∞) ≤ I.ord y.1 →
      Φ (idx t) y = y.1 := by
    intro t y hy
    have hord : I.ord y.1 = m := le_antisymm (hmax _) hy
    have hcos : y.1 ∈ (I.iteratedDeriv (m - 1)).support := by
      by_contra h
      exact one_ne_zero ((ord_iteratedDeriv_eq_one (E := E) (I := I) hm hord).symm.trans
        ((IdealSheaf.ord_eq_zero_iff (J := I.iteratedDeriv (m - 1))).mpr h))
    have hKeq :
        (I.pullback _ (M.inclusion (U (idx t))).contMDiff).iteratedDeriv (m - 1) =
        (I.iteratedDeriv (m - 1)).pullback _ (M.inclusion (U (idx t))).contMDiff :=
      AnalyticManifold.IdealSheaf.iteratedDeriv_restrictOpens I _ (m - 1)
    have hK : ((I.pullback _ (M.inclusion (U (idx t))).contMDiff).iteratedDeriv
        (m - 1)).stalkIdeal y ≠ ⊤ := by
      rw [hKeq, stalkIdeal_comap_eq_map_germMap]
      intro htop
      have hne : (I.iteratedDeriv (m - 1)).stalkIdeal y.1 ≠ ⊤ := hcos
      have hbijι : Function.Bijective
          (germMap (⇑(M.inclusion (U (idx t)))) (M.inclusion (U (idx t))).contMDiff y) :=
        germMap_val_bijective (𝕜 := 𝕜) (E := E) (U (idx t)) y
      have h1 := Ideal.comap_map_of_bijective _ hbijι
        (I := (I.iteratedDeriv (m - 1)).stalkIdeal ((M.inclusion (U (idx t))) y))
      rw [htop, Ideal.comap_top] at h1
      exact hne h1.symm
    exact ((h4 (idx t)).apply_eq_of_mem_support hK).symm
  have hcovers : {x : M | (m : ℕ∞) ≤ I.ord x} ⊆ Set.range Ψ := by
    intro y hy
    obtain ⟨t, hyt⟩ := hmemU y hy
    exact ⟨⟨t, ⟨y, hyt⟩⟩, rfl⟩
  have hcovers' : {x : M | (m : ℕ∞) ≤ I.ord x} ⊆ Set.range Ψ' := by
    intro y hy
    obtain ⟨t, hyt⟩ := hmemU y hy
    exact ⟨⟨t, ⟨y, hyt⟩⟩, hfix t ⟨y, hyt⟩ hy⟩
  -- the stalk maps of the summand inclusions `σ_t` are bijective (through `Ψ ∘ σ_t = ι`)
  have hcompΨ : ∀ (t : T) (x : N t),
      (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x).comp
          (germMap (⇑Ψ) Ψ.contMDiff (sigmaMk N t x)) =
        germMap (⇑(M.inclusion (U (idx t)))) (M.inclusion (U (idx t))).contMDiff x :=
    fun t x => germMap_comp Ψ (sigmaMk N t) x
  have hcompΨ' : ∀ (t : T) (x : N t),
      (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x).comp
          (germMap (⇑Ψ') Ψ'.contMDiff (sigmaMk N t x)) =
        germMap (⇑(Φ (idx t))) (Φ (idx t)).contMDiff x :=
    fun t x => germMap_comp Ψ' (sigmaMk N t) x
  have hbij : ∀ (t : T) (x : N t),
      Function.Bijective (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x) := by
    intro t x
    have hι : Function.Bijective (⇑(germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x) ∘
        ⇑(germMap (⇑Ψ) Ψ.contMDiff (sigmaMk N t x))) := by
      rw [← RingHom.coe_comp, hcompΨ t x]
      exact germMap_val_bijective (𝕜 := 𝕜) (E := E) (U (idx t)) x
    have hΨ := germMap_bijective_of_isLocalDiffeomorphAt (⇑Ψ) Ψ.contMDiff (hΨloc (sigmaMk N t x))
    exact ⟨hι.1.of_comp_right hΨ.2, hι.2.of_comp⟩
  -- (1′) and (3′): pointwise
  have hh1 : ⇑Ψ ⁻¹' H = ⇑Ψ' ⁻¹' H' := by
    ext ⟨t, x⟩
    exact Set.ext_iff.mp (h1 (idx t)) x
  have hh3 : ∀ j, ⇑Ψ ⁻¹' F.hyp j = ⇑Ψ' ⁻¹' F.hyp j := by
    intro j
    ext ⟨t, x⟩
    exact Set.ext_iff.mp (h3 (idx t) j) x
  -- (2′): the stalks at `σ_t x` through the bijection
  have hh2 : I.pullback Ψ Ψ.contMDiff =
      I.pullback Ψ' Ψ'.contMDiff := by
    refine IdealSheaf.ext ?_
    rintro ⟨t, x⟩
    have e1 : Ideal.map (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x)
        ((I.pullback Ψ Ψ.contMDiff).stalkIdeal (sigmaMk N t x)) =
        (I.pullback _ (M.inclusion (U (idx t))).contMDiff).stalkIdeal x := by
      rw [stalkIdeal_comap_eq_map_germMap, stalkIdeal_comap_eq_map_germMap, Ideal.map_map,
        ← hcompΨ t x]
      rfl
    have e2 : Ideal.map (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x)
        ((I.pullback Ψ' Ψ'.contMDiff).stalkIdeal (sigmaMk N t x)) =
        (I.pullback _ (Φ (idx t)).contMDiff).stalkIdeal x := by
      rw [stalkIdeal_comap_eq_map_germMap, stalkIdeal_comap_eq_map_germMap, Ideal.map_map,
        ← hcompΨ' t x]
      rfl
    have hmap : Ideal.map (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x)
        ((I.pullback Ψ Ψ.contMDiff).stalkIdeal (sigmaMk N t x)) =
        Ideal.map (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x)
          ((I.pullback Ψ' Ψ'.contMDiff).stalkIdeal (sigmaMk N t x)) := by
      rw [e1, e2, h2 (idx t)]
    calc (I.pullback Ψ Ψ.contMDiff).stalkIdeal (sigmaMk N t x)
        = Ideal.comap (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x)
            (Ideal.map (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x)
              ((I.pullback Ψ Ψ.contMDiff).stalkIdeal (sigmaMk N t x))) :=
          (Ideal.comap_map_of_bijective _ (hbij t x)).symm
      _ = Ideal.comap (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x)
            (Ideal.map (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x)
              ((I.pullback Ψ' Ψ'.contMDiff).stalkIdeal (sigmaMk N t x))) :=
                  by rw [hmap]
      _ = (I.pullback Ψ' Ψ'.contMDiff).stalkIdeal (sigmaMk N t x) :=
          Ideal.comap_map_of_bijective _ (hbij t x)
  -- (4′): the agreement modulo `MC(Ψ^*I)` at `σ_t x` through the bijection
  have hh4 :
      AgreeOnSubspace Ψ Ψ' ((I.pullback Ψ Ψ.contMDiff).iteratedDeriv (m - 1)) := by
    rintro ⟨t, x⟩ W hu hu' h
    have hKt :
        (I.pullback _ (M.inclusion (U (idx t))).contMDiff).iteratedDeriv (m - 1) =
        ((I.pullback Ψ Ψ.contMDiff).iteratedDeriv (m - 1)).pullback _ (sigmaMk N t).contMDiff := by
      change _ = ((I.pullback Ψ Ψ.contMDiff).iteratedDeriv (m - 1)).pullback
        ⇑(sigmaMk N t) (sigmaMk N t).contMDiff
      rw [← iteratedDeriv_pullback_of_bijective (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff
        (I.pullback Ψ Ψ.contMDiff) (fun y => hbij t y) (m - 1)]
      congr 1
      exact (IdealSheaf.pullback_pullback I (⇑Ψ) Ψ.contMDiff (⇑(sigmaMk N t))
        (sigmaMk N t).contMDiff).symm
    have hstalk : ((I.pullback _ (M.inclusion (U (idx t))).contMDiff).iteratedDeriv
          (m - 1)).stalkIdeal x =
        Ideal.map (germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x)
          (((I.pullback Ψ Ψ.contMDiff).iteratedDeriv (m - 1)).stalkIdeal
            (sigmaMk N t x)) := by
      rw [hKt]
      exact stalkIdeal_comap_eq_map_germMap _ _ x
    have hpiece := h4 (idx t) x W hu hu' h
    rw [hstalk] at hpiece
    have hl : germMap (⇑(M.inclusion (U (idx t)))) (M.inclusion (U (idx t))).contMDiff x
        ((structureSheaf 𝕜 E M).presheaf.germ W ((M.inclusion (U (idx t))) x) hu h) =
        germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x
          (germMap (⇑Ψ) Ψ.contMDiff (sigmaMk N t x)
            ((structureSheaf 𝕜 E M).presheaf.germ W (Ψ (sigmaMk N t x)) hu h)) :=
      (RingHom.congr_fun (hcompΨ t x) _).symm
    have hl' : germMap (⇑(Φ (idx t))) (Φ (idx t)).contMDiff x
        ((structureSheaf 𝕜 E M).presheaf.germ W (Φ (idx t) x) hu' h) =
        germMap (⇑(sigmaMk N t)) (sigmaMk N t).contMDiff x
          (germMap (⇑Ψ') Ψ'.contMDiff (sigmaMk N t x)
            ((structureSheaf 𝕜 E M).presheaf.germ W (Ψ' (sigmaMk N t x)) hu' h)) :=
      (RingHom.congr_fun (hcompΨ' t x) _).symm
    rw [hl, hl', ← map_sub] at hpiece
    have hd := Ideal.mem_comap.mpr hpiece
    rw [Ideal.comap_map_of_bijective _ (hbij t x)] at hd
    exact hd
  exact ⟨⟨⟨sigmaManifold N, Ψ, Ψ', hΨloc, hΨ'loc, hcovers, hcovers'⟩, hh1, hh2, hh3, hh4⟩⟩

end Hironaka.Manifold

end
