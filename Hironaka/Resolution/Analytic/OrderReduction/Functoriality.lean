/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Basic
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.FiniteSuccession.Restrict.Fields
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Submanifold.Components
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The first step of Lemma 102 under pull-back

The proof of [Kol07, Lemma 102] checks that the construction commutes with smooth morphisms
`h : Y → X`: the restriction `h|_{E^j_Y} : E^j_Y → E^j` "is also a smooth surjection", and pulling
back by `h` and then restricting to `E^j_Y` gives the same result as restricting to `E^j` and then
pulling back by `h|_{E^j_Y}`. This module proves the corresponding facts for a local analytic
isomorphism `h : N → M` and the first step of the construction (`FirstStep.lean`):

* `Zminus1_comap` — the first centre of the pulled-back data `(h^* 𝓘, h⁻¹(E^j))` is the preimage of
  the first centre: a connected component of `h⁻¹(E^j)` lies in `cosupp(h^* 𝓘, m)` iff the component
  of `E^j` it maps into lies in `cosupp(𝓘, m)`. Kollár argues at the generic point; here the
  identity theorem on the connected hypersurface stands in: the order of `𝓘` along `E^j` is
  constant on a component (`ordAlong_eq_of_isPreconnected`), it is at least `m` at `h x` when
  `ord 𝓘 ≥ m` on the open piece `h(component of x)` of `E^j` near `h x` (a local analytic
  isomorphism is an open map), and `ord_{E^j} 𝓘 ≤ ord 𝓘` pointwise. No surjectivity is needed.
* `firstStep_pullback` — the one-step sequence blowing up `Z_{-1}` pulls back to the one-step
  sequence blowing up the first centre of the pulled-back data.
* `isLocalDiffeomorph_restrictMap`, `surjective_restrictMap` — the restriction `h⁻¹(S) → S` of `h`
  to the preimage of a closed hypersurface is a local analytic isomorphism between the bundled
  hypersurfaces (the local inverses of `h` restrict), and a surjection when `h` is.
* `pullback_inclusionMap_pullback`, `comap_inclusionMap_comap` — restriction and pull-back
  commute, for the ideal sheaf (the pull-back of ideal sheaves is functorial) and for the boundary
  family (componentwise, the index set kept).

These are the ingredients of the commutation of Lemma 102's functor with local analytic
isomorphisms ([Kol07, Lemma 102 (2)]), assembled in `BDOf.lean` (and `BDErase.lean`).
-/

@[expose] public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BD

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}
  (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

-- The finite-dimensionality `[FiniteDimensional 𝕜 E]` of the model space belongs to every statement
-- here, as to Kollár's varieties; a proof that does not need it names it (`have _hfd := hfd`) so
-- that it remains part of the statement.

/-! ### The first centre of the pulled-back data -/

include hh in
/-- The first centre of the pulled-back data is the preimage of the first centre (the
functoriality part of the proof of [Kol07, Lemma 102], with the identity theorem on the connected
hypersurface in place of Kollár's generic-point argument): a connected component of `h⁻¹(E^j)`
lies in `cosupp(h^* 𝓘, m)` iff the component of `E^j` it maps into lies in `cosupp(𝓘, m)`. The
component maps into the component by continuity; conversely, `ord 𝓘 ≥ m` on the open piece of `E^j`
that is the image of the component near `h x` forces `ord_{E^j} 𝓘 ≥ m` at `h x`, hence along the
whole connected component of `h x` (the order along `E^j` is locally constant), hence `ord 𝓘 ≥ m`
there. -/
theorem Zminus1_comap (I : AnalyticManifold.IdealSheaf M) (m : ℕ) {Y : Set M}
    (hY : IsClosedSubmanifold ψ₀ Y 1) :
    Zminus1 (I.pullback h h.contMDiff) m (⇑h ⁻¹' Y) = ⇑h ⁻¹' Zminus1 I m Y := by
  have _hfd := hfd
  have hord : ∀ y, (I.pullback h h.contMDiff).ord y = I.ord (h y) := fun y =>
    IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ I (hh y)
  ext x
  constructor
  · rintro ⟨hxY, hsub⟩
    refine ⟨hxY, ?_⟩
    -- `ord 𝓘 ≥ m` on the points of `Y` near `h x`: images of points of the component of `x`
    have hev : ∀ᶠ y : Y in 𝓝 (⟨h x, hxY⟩ : Y), (m : ℕ∞) ≤ I.ord (y : M) := by
      obtain ⟨φ, -, hxφ, -, hφC⟩ :=
        (hY.preimage_of_isLocalDiffeomorph hh).exists_adaptedChart_source_inter_subset hxY
      have hopen : IsOpen (⇑h '' φ.source) := hh.isOpenMap _ φ.open_source
      have hmem : (⟨h x, hxY⟩ : Y) ∈ (Subtype.val : Y → M) ⁻¹' (⇑h '' φ.source) :=
        ⟨x, hxφ, rfl⟩
      filter_upwards [(hopen.preimage continuous_subtype_val).mem_nhds hmem] with y hy
      obtain ⟨w, hwφ, hwy⟩ := hy
      have hwC : w ∈ connectedComponentIn (⇑h ⁻¹' Y) x :=
        hφC ⟨hwφ, show h w ∈ Y by rw [hwy]; exact y.2⟩
      have := hsub hwC
      rwa [Set.mem_ofPred_eq, hord, hwy] at this
    -- `ord_Y 𝓘 ≥ m` at `h x`, hence on the whole component of `h x`, hence `ord 𝓘 ≥ m` there
    have hm : (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I (h x) := by
      rw [IdealSheaf.le_ordAlongIdeal_iff]
      exact stalkIdeal_le_pow_of_eventually_le_ord hY I hxY hev
    intro z hz
    change (m : ℕ∞) ≤ I.ord z
    calc (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I (h x) := hm
      _ = IdealSheaf.ordAlongIdeal hY.idealSheaf I z :=
        ordAlong_eq_of_isPreconnected hY I (connectedComponentIn_subset Y (h x))
          isPreconnected_connectedComponentIn (mem_connectedComponentIn hxY) hz
      _ ≤ I.ord z := ordAlong_le_ord hY I (connectedComponentIn_subset Y (h x) hz)
  · rintro ⟨hxY, hsub⟩
    refine ⟨hxY, fun w hw => ?_⟩
    change (m : ℕ∞) ≤ (I.pullback h h.contMDiff).ord w
    rw [hord]
    refine hsub ?_
    -- the image of the component of `x` lies in the component of `h x`
    exact (isPreconnected_connectedComponentIn.image _ h.contMDiff.continuous.continuousOn)
      |>.subset_connectedComponentIn ⟨x, mem_connectedComponentIn hxY, rfl⟩
        (Set.image_subset_iff.mpr (connectedComponentIn_subset _ _)) (Set.mem_image_of_mem _ hw)

/-- The one-step sequence blowing up `Z_{-1}` pulls back along a local analytic isomorphism to the
one-step sequence blowing up the first centre of the pulled-back data
(`BlowUpSequence.pullback_cons` and `Zminus1_comap`, the two centres being the same set). -/
theorem firstStep_pullback (I : AnalyticManifold.IdealSheaf M) (m : ℕ) {Y : Set M}
    (hY : IsClosedSubmanifold ψ₀ Y 1) (hZ : IsClosedSubmanifold ψ₀ (Zminus1 I m Y) 1)
    (hZ' : IsClosedSubmanifold ψ₀ (Zminus1 (I.pullback h h.contMDiff) m (⇑h ⁻¹' Y)) 1) :
    (AnalyticManifold.BlowUpSequence.cons hZ (AnalyticManifold.BlowUpSequence.nil _)).pullback h hh
        =
      AnalyticManifold.BlowUpSequence.cons hZ' (AnalyticManifold.BlowUpSequence.nil _) := by
  have _hfd := hfd
  rw [AnalyticManifold.BlowUpSequence.pullback_cons, AnalyticManifold.BlowUpSequence.pullback_nil]
  have key : ∀ {Y₁ Y₂ : Set N} (h₁ : IsClosedSubmanifold ψ₀ Y₁ 1)
      (h₂ : IsClosedSubmanifold ψ₀ Y₂ 1), Y₁ = Y₂ →
      AnalyticManifold.BlowUpSequence.cons h₁ (AnalyticManifold.BlowUpSequence.nil _) =
          AnalyticManifold.BlowUpSequence.cons h₂ (AnalyticManifold.BlowUpSequence.nil _) := by
    rintro Y₁ Y₂ h₁ h₂ rfl
    rfl
  exact key _ _ (Zminus1_comap h hh I m hY).symm

/-! ### The restriction of a local analytic isomorphism to the preimage of a hypersurface -/

variable {S : Set M} (hS : IsClosedSubmanifold ψ₀ S 1)

omit hfd in
open scoped Classical in
/-- The local inverse `Ψ` of `h` read on the bundled hypersurfaces: `Ψ⁻¹(y)` for `y ∈ S ∩ Ψ.target`,
which lies in `h⁻¹(S)` since `h (Ψ⁻¹ y) = y`; a default value `p₀` elsewhere. An auxiliary
construction for `restrictPartialDiffeomorphOfPreimage`. -/
def restrictInvFunOfPreimage (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω)
    (hΨ : Set.EqOn h Ψ Ψ.source) (p₀ : (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold)
    (y : hS.toAnalyticManifold) : (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold :=
  if hy : (y : S).1 ∈ Ψ.target then
    ⟨Ψ.invFun (y : S).1, by
      change h (Ψ.invFun (y : S).1) ∈ S
      have hm : Ψ.invFun (y : S).1 ∈ Ψ.source := Ψ.map_target hy
      rw [(hΨ hm).trans (Ψ.right_inv hy)]
      exact (y : S).2⟩
  else p₀

omit hfd in
/-- The value of `restrictInvFunOfPreimage` on the target of `Ψ`. -/
theorem restrictInvFunOfPreimage_of_mem (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω)
    (hΨ : Set.EqOn h Ψ Ψ.source) (p₀ : (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold)
    {y : hS.toAnalyticManifold}
    (hy : (y : S).1 ∈ Ψ.target) :
    restrictInvFunOfPreimage h hh hS Ψ hΨ p₀ y =
      ⟨Ψ.invFun (y : S).1, by
        change h (Ψ.invFun (y : S).1) ∈ S
        have hm : Ψ.invFun (y : S).1 ∈ Ψ.source := Ψ.map_target hy
        rw [(hΨ hm).trans (Ψ.right_inv hy)]
        exact (y : S).2⟩ := by
  unfold restrictInvFunOfPreimage
  exact dite_eq_left hy

omit hfd in
/-- A local inverse of `h` restricted to the bundled hypersurfaces `h⁻¹(S)` and `S` is a partial
diffeomorphism agreeing with the restricted map on `h⁻¹(S) ∩ Ψ.source`. -/
def restrictPartialDiffeomorphOfPreimage (Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω)
    (hΨ : Set.EqOn h Ψ Ψ.source) (p₀ : (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold) :
    PartialDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜)
      (hS.preimage_of_isLocalDiffeomorph hh).toAnalyticManifold
      hS.toAnalyticManifold ω where
  toFun := (hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff fun _ hx => hx
  invFun := restrictInvFunOfPreimage h hh hS Ψ hΨ p₀
  source := {p | (p : ⇑h ⁻¹' S).1 ∈ Ψ.source}
  target := {y | (y : S).1 ∈ Ψ.target}
  map_source' p hp := by
    change h (p : ⇑h ⁻¹' S).1 ∈ Ψ.target
    rw [hΨ hp]
    exact Ψ.map_source hp
  map_target' y hy := by
    change (restrictInvFunOfPreimage h hh hS Ψ hΨ p₀ y : ⇑h ⁻¹' S).1 ∈ Ψ.source
    rw [restrictInvFunOfPreimage_of_mem h hh hS Ψ hΨ p₀ hy]
    exact Ψ.map_target hy
  left_inv' p hp := by
    have hc : h (p : ⇑h ⁻¹' S).1 ∈ Ψ.target := by
      rw [hΨ hp]
      exact Ψ.map_source hp
    apply Subtype.ext
    change (restrictInvFunOfPreimage h hh hS Ψ hΨ p₀
      (((hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff fun _ hx => hx) p) :
        ⇑h ⁻¹' S).1 = (p : ⇑h ⁻¹' S).1
    rw [restrictInvFunOfPreimage_of_mem h hh hS Ψ hΨ p₀ hc]
    change Ψ.invFun (h (p : ⇑h ⁻¹' S).1) = (p : ⇑h ⁻¹' S).1
    rw [hΨ hp]
    exact Ψ.left_inv hp
  right_inv' y hy := by
    apply Subtype.ext
    change (((hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff fun _ hx => hx)
      (restrictInvFunOfPreimage h hh hS Ψ hΨ p₀ y) : S).1 = (y : S).1
    rw [restrictInvFunOfPreimage_of_mem h hh hS Ψ hΨ p₀ hy]
    change h (Ψ.invFun (y : S).1) = (y : S).1
    have hm : Ψ.invFun (y : S).1 ∈ Ψ.source := Ψ.map_target hy
    exact (hΨ hm).trans (Ψ.right_inv hy)
  open_source := Ψ.open_source.preimage continuous_subtype_val
  open_target := Ψ.open_target.preimage continuous_subtype_val
  contMDiffOn_toFun :=
    ((hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff
      fun _ hx => hx).contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    intro y hy
    have hT : IsOpen {y : hS.toAnalyticManifold | (y : S).1 ∈ Ψ.target} :=
      Ψ.open_target.preimage continuous_subtype_val
    refine ContMDiffAt.contMDiffWithinAt ?_
    refine (hS.preimage_of_isLocalDiffeomorph hh).contMDiffAt_of_val ?_
    have hev : (Subtype.val ∘ restrictInvFunOfPreimage h hh hS Ψ hΨ p₀) =ᶠ[𝓝 y]
        fun z : hS.toAnalyticManifold => Ψ.invFun (z : S).1 := by
      filter_upwards [hT.mem_nhds hy] with z hz
      change (restrictInvFunOfPreimage h hh hS Ψ hΨ p₀ z : ⇑h ⁻¹' S).1 = Ψ.invFun (z : S).1
      rw [restrictInvFunOfPreimage_of_mem h hh hS Ψ hΨ p₀ hz]
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
    exact (Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds hy)).comp y
      (hS.contMDiff_val y)

/-- "`h|_{E^j_Y} : E^j_Y → E^j` is also a smooth surjection" (the proof of [Kol07, Lemma 102]), the
local-isomorphism part: the restriction of a local analytic isomorphism to the preimage of a closed
hypersurface is a local analytic isomorphism between the bundled hypersurfaces, the local inverses
of `h` restricting to the submanifolds. -/
theorem isLocalDiffeomorph_restrictMap :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      ((hS.preimage_of_isLocalDiffeomorph hh).restrictMap hS h h.contMDiff fun _ hx => hx) := by
  have _hfd := hfd
  intro p
  obtain ⟨Ψ, hpΨ, hΨ⟩ := (hh (p : ⇑h ⁻¹' S).1).exists_partialDiffeomorph
  exact IsLocalDiffeomorphAt.of_eqOn (restrictPartialDiffeomorphOfPreimage h hh hS Ψ hΨ p) hpΨ
    fun _ _ => rfl

/-- The restriction of a surjection to the preimage of a hypersurface is a surjection onto the
hypersurface (true for every analytic map). -/
theorem surjective_restrictMap (hs : Function.Surjective h) {S : Set M}
    (hS : IsClosedSubmanifold ψ₀ S 1) (hS' : IsClosedSubmanifold ψ₀ (⇑h ⁻¹' S) 1) :
    Function.Surjective (hS'.restrictMap hS h h.contMDiff fun _ hx => hx) := by
  have _hfd := hfd
  intro q
  obtain ⟨x, hx⟩ := hs (q : S).1
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change h x ∈ S
  rw [hx]
  exact (q : S).2

/-! ### Restriction and pull-back commute -/

/-- Pulling back by `h` and then restricting to `E^j_Y` gives "the same result" as restricting to
`E^j` and then pulling back by `h|_{E^j_Y}` (the proof of [Kol07, Lemma 102]), for
the ideal sheaf: the restriction to `h⁻¹(S)` of the pull-back of `𝓘` is the pull-back along
`h|_{h⁻¹(S)}` of the restriction of `𝓘` to `S`, because the pull-back of ideal sheaves is functorial
and `ι_S ∘ h|_{h⁻¹(S)} = h ∘ ι_{h⁻¹(S)}`. -/
theorem pullback_inclusionMap_pullback (I : AnalyticManifold.IdealSheaf M) {S : Set M}
    (hS : IsClosedSubmanifold ψ₀ S 1) (hS' : IsClosedSubmanifold ψ₀ (⇑h ⁻¹' S) 1) :
    (I.pullback h h.contMDiff).pullback ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff =
      (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).pullback
        ⇑(hS'.restrictMap hS h h.contMDiff fun _ hx => hx)
        (hS'.restrictMap hS h h.contMDiff fun _ hx => hx).contMDiff := by
  have _hfd := hfd
  rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  rfl

/-- The same for the boundary `(E − E^j)|_{E^j}`: the restriction to `h⁻¹(S)` of the pulled-back
family is the pull-back along `h|_{h⁻¹(S)}` of the restricted family (componentwise, the index set
kept; true for every map). -/
theorem comap_inclusionMap_comap (F : HypersurfaceFamily M) {S : Set M}
    (hS : IsClosedSubmanifold ψ₀ S 1) (hS' : IsClosedSubmanifold ψ₀ (⇑h ⁻¹' S) 1) :
    (F.comap h).comap ⇑hS'.inclusionMap =
      (F.comap ⇑hS.inclusionMap).comap ⇑(hS'.restrictMap hS h h.contMDiff fun _ hx => hx) := by
  have _hfd := hfd
  rfl

end Hironaka.Manifold.BD

end
