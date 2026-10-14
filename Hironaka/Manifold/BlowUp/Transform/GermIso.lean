/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Defs
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Stalk isomorphisms along an open inclusion and along a local isomorphism

The birational transform of a marked ideal commutes with restriction to open subsets and with
local isomorphisms [Kol07, Definition 30, 30.1]. The content of that statement, on the analytic
side, is the pair of stalk isomorphisms provided here, together with the transport of colon
ideals along them:

* the stalk map `germMap Subtype.val` of the inclusion of an open subset `U ⊆ M` is bijective:
  injective because the inclusion maps the neighbourhood filter of a point of `U` onto its
  neighbourhood filter in `M` (`map_nhds_subtype_val`, `IsOpen.nhdsWithin_eq`), surjective
  because a germ on `U` has an analytic representative near the point which, extended by `0`, is
  analytic on `M` (analyticity on `U` is analyticity on `M` at points of `U`: Mathlib's
  `liftPropAt_iff_comp_subtype_val`);
* the stalk map `germMapOn g` of a partial analytic diffeomorphism `g` at a point of its source is
  bijective: injective because `g` maps neighbourhood filters onto neighbourhood filters
  (`OpenPartialHomeomorph.map_nhds_eq`), surjective because a representative composed with `g⁻¹`
  is a representative at `g x` (`eventually_left_inverse`);
* under a ring isomorphism the colon `(I : J^m)` goes to `(e(I) : e(J)^m)`;
* stalk maps compose and depend only on the map near the point; pullbacks of ideal sheaves
  compose.

Everything is read through the characterization `stalkToGerm_germMapOn` of the stalk map as
composition of germs of functions. The transport of the birational transform along an open
inclusion is `Hironaka.Manifold.BlowUp.Transform.OpenSubset`. The arguments are routine and not
in the sources.
-/

public section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Under a ring isomorphism `e`, the image of
the colon `(I : J^m)` is the colon `(e(I) : e(J)^m)` — the algebraic step by which the colon stalks
are transported along the stalk isomorphisms of an open inclusion or a local
isomorphism. -/
theorem _root_.Ideal.map_colon_pow_equiv (e : R ≃+* S) (I J : Ideal R) (m : ℕ) :
    Ideal.map (e : R →+* S) (I.colon ↑(J ^ m)) =
      (Ideal.map (e : R →+* S) I).colon ↑(Ideal.map (e : R →+* S) J ^ m) := by
  rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  ext y
  simp only [Ideal.mem_comap, Submodule.mem_colon, SetLike.mem_coe, smul_eq_mul, map_mul]
  constructor
  · intro hy z hz
    exact hy _ hz
  · intro hy z hz
    have := hy (e z) (by rw [e.symm_apply_apply]; exact hz)
    rwa [e.symm_apply_apply] at this

/-- The colon by a power transports along a bijective ring
homomorphism (the ring-isomorphism form applied to `RingEquiv.ofBijective`). -/
theorem _root_.Ideal.map_colon_pow_of_bijective (e : R →+* S) (he : Function.Bijective e)
    (I J : Ideal R)
    (m : ℕ) :
    Ideal.map e (I.colon ↑(J ^ m)) = (Ideal.map e I).colon ↑(Ideal.map e J ^ m) :=
  Ideal.map_colon_pow_equiv (RingEquiv.ofBijective e he) I J m

end Algebra

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {N : Type u} [TopologicalSpace N] [ChartedSpace E N]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace E₁ M₁]
  {M₂ : Type u} [TopologicalSpace M₂] [ChartedSpace E₂ M₂]

section Comp

/-- Composition of stalk maps — `(s ∘ φ₁) ∘ φ₂ = s ∘ (φ₁ ∘ φ₂)`, for any
open domain of analyticity of the composite (the stalk map depends on it only through proofs). -/
theorem germMapOn_germMapOn {φ₁ : M₂ → M₁} {V₁ : Opens M₂}
    (hφ₁ : ContMDiffOn 𝓘(𝕜, E₂) 𝓘(𝕜, E₁) ω φ₁ V₁) {φ₂ : N → M₂} {V₂ : Opens N}
    (hφ₂ : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E₂) ω φ₂ V₂) {b : N} (hb : b ∈ V₂) {c₂ : M₂} (hc₂ : φ₂ b = c₂)
    (hc₂V : c₂ ∈ V₁) {c₁ : M₁} (hc₁ : φ₁ c₂ = c₁) {V₃ : Opens N}
    (hφ₃ : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E₁) ω (φ₁ ∘ φ₂) V₃) (hb₃ : b ∈ V₃) (hc₃ : (φ₁ ∘ φ₂) b = c₁)
    (s : (structureSheaf 𝕜 E₁ M₁).presheaf.stalk c₁) :
    germMapOn φ₂ hφ₂ hb hc₂ (germMapOn φ₁ hφ₁ hc₂V hc₁ s) = germMapOn (φ₁ ∘ φ₂) hφ₃ hb₃ hc₃ s := by
  apply stalkToGerm_injective 𝓘(𝕜, E) ω N b
  rw [stalkToGerm_germMapOn, stalkToGerm_germMapOn, stalkToGerm_germMapOn]
  induction stalkToGerm 𝓘(𝕜, E₁) ω M₁ c₁ s using Germ.inductionOn with
  | h f => rfl

/-- The stalk map depends only on the map on the open set. -/
theorem germMapOn_congr {φ φ' : N → M₁} {V : Opens N} (hφ : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E₁) ω φ V)
    (hφ' : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E₁) ω φ' V) {b : N} (hb : b ∈ V) {c : M₁} (hc : φ b = c)
    (hc' : φ' b = c) (heq : ∀ x ∈ V, φ x = φ' x) (s : (structureSheaf 𝕜 E₁ M₁).presheaf.stalk c) :
    germMapOn φ hφ hb hc s = germMapOn φ' hφ' hb hc' s := by
  apply stalkToGerm_injective 𝓘(𝕜, E) ω N b
  rw [stalkToGerm_germMapOn, stalkToGerm_germMapOn]
  induction stalkToGerm 𝓘(𝕜, E₁) ω M₁ c s using Germ.inductionOn with
  | h f =>
    rw [Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_eq]
    filter_upwards [V.2.mem_nhds hb] with x hx
    simp only [Function.comp_apply, heq x hx]

/-- Transport of the image of a stalk ideal along an equality of base
points. -/
theorem germMapOn_map_stalkIdeal_congr {φ : N → M₁} {V : Opens N}
    (hφ : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E₁) ω φ V) {b : N} (hb : b ∈ V) {c c' : M₁} (hcc' : c = c')
    (hc : φ b = c) (hc' : φ b = c') (J : IdealSheaf (structureSheaf 𝕜 E₁ M₁)) :
    Ideal.map (germMapOn φ hφ hb hc) (J.stalkIdeal c) =
      Ideal.map (germMapOn φ hφ hb hc') (J.stalkIdeal c') := by
  subst hcc'
  rfl

/-- Pulling back twice is pulling back along the composite. -/
@[simp]
theorem IdealSheaf.pullback_pullback (J : IdealSheaf (structureSheaf 𝕜 E₁ M₁)) (φ₁ : M₂ → M₁)
    (hφ₁ : ContMDiff 𝓘(𝕜, E₂) 𝓘(𝕜, E₁) ω φ₁) (φ₂ : N → M₂)
    (hφ₂ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E₂) ω φ₂) :
    (J.pullback φ₁ hφ₁).pullback φ₂ hφ₂ = J.pullback (φ₁ ∘ φ₂) (hφ₁.comp hφ₂) := by
  refine IdealSheaf.ext fun b => ?_
  rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback,
    IdealSheaf.stalkIdeal_pullback, Ideal.map_map]
  congr 1
  ext s
  exact germMapOn_germMapOn hφ₁.contMDiffOn hφ₂.contMDiffOn (Opens.mem_top b) rfl (Opens.mem_top _)
    rfl (hφ₁.comp hφ₂).contMDiffOn (Opens.mem_top b) rfl s

/-- The pullback depends only on the map. -/
theorem IdealSheaf.pullback_congr (J : IdealSheaf (structureSheaf 𝕜 E₁ M₁)) {φ φ' : N → M₁}
    (hφ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E₁) ω φ) (hφ' : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E₁) ω φ') (h : φ = φ') :
    J.pullback φ hφ = J.pullback φ' hφ' := by
  subst h
  rfl

end Comp

section OpenInclusion

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- Analyticity of a function on `M` at a point of an open subset `U`
is analyticity of its restriction to the manifold `U` (Mathlib's `liftPropAt_iff_comp_subtype_val`).
-/
theorem contMDiffAt_iff_comp_subtype_val {U : Opens M} (f : M → 𝕜) (x : U) :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω f x ↔ ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (f ∘ Subtype.val) x :=
  (contDiffWithinAt_localInvariantProp ω).liftPropAt_iff_comp_subtype_val f x

/-- The stalk map along the inclusion of an open subset is injective
(the inclusion maps neighbourhood filters onto neighbourhood filters). -/
theorem germMap_val_injective (U : Opens M) (p : U) :
    Function.Injective
      (germMap (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E))) p) := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs => ?_
  apply stalkToGerm_injective 𝓘(𝕜, E) ω M (p : M)
  have := congrArg (stalkToGerm 𝓘(𝕜, E) ω U p) hs
  rw [stalkToGerm_germMap, map_zero] at this
  rw [map_zero]
  revert this
  induction stalkToGerm 𝓘(𝕜, E) ω M (p : M) s using Germ.inductionOn with
  | h f =>
    intro this
    rw [Germ.coe_compTendsto, ← Germ.coe_zero, Germ.coe_eq] at this
    rw [← Germ.coe_zero, Germ.coe_eq]
    have h1 : ∀ᶠ y in map (Subtype.val : U → M) (𝓝 p), f y = 0 :=
      eventually_map.mpr (this.mono fun _ hx => hx)
    rwa [map_nhds_subtype_val, U.isOpen.nhdsWithin_eq p.2] at h1

/-- The stalk map along the inclusion of an open subset is surjective —
a germ on `U`, represented near the point, extends by `0` to an analytic representative on `M`. -/
theorem germMap_val_surjective (U : Opens M) (p : U) :
    Function.Surjective
      (germMap (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E))) p) := by
  intro t
  obtain ⟨h, ht, W, hpW, hW⟩ :=
    (mem_range_stalkToGerm_iff 𝓘(𝕜, E) ω U p (stalkToGerm 𝓘(𝕜, E) ω U p t)).mp ⟨t, rfl⟩
  classical
  let h' : M → 𝕜 := fun x => if hx : x ∈ U then h ⟨x, hx⟩ else 0
  have hh' : h' ∘ (Subtype.val : U → M) = h := by
    funext x
    simp only [h', Function.comp_apply, dite_eq_left x.2]
  have hW' : IsOpen ((Subtype.val : U → M) '' W) := U.isOpen.isOpenMap_subtype_val _ W.2
  have hsm : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω h' ((Subtype.val : U → M) '' W) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ContMDiffAt.contMDiffWithinAt ?_
    rw [contMDiffAt_iff_comp_subtype_val, hh']
    exact hW.contMDiffAt (W.2.mem_nhds hy)
  obtain ⟨s, hs⟩ := (mem_range_stalkToGerm_iff 𝓘(𝕜, E) ω M (p : M) (↑h')).mpr
    ⟨h', rfl, ⟨_, hW'⟩, ⟨p, hpW, rfl⟩, hsm⟩
  refine ⟨s, stalkToGerm_injective 𝓘(𝕜, E) ω U p ?_⟩
  rw [stalkToGerm_germMap, hs, Germ.coe_compTendsto, hh', ht]

/-- **The stalk isomorphism along an open inclusion** — the stalk map
`𝒪_{M,p} → 𝒪_{U,p}` of `Subtype.val : U → M` is bijective. -/
theorem germMap_val_bijective (U : Opens M) (p : U) :
    Function.Bijective
      (germMap (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(𝕜, E))) p) :=
  ⟨germMap_val_injective U p, germMap_val_surjective U p⟩

end OpenInclusion

section PartialDiffeo

variable {M₁' : Type u} [TopologicalSpace M₁'] [ChartedSpace E M₁']
  {M₂' : Type u} [TopologicalSpace M₂'] [ChartedSpace E M₂']
  (g : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁' M₂' ω)

/-- The stalk map along a partial diffeomorphism, at a point of its
source, is injective (`g` maps the neighbourhood filter onto that of `g x`). -/
theorem germMapOn_partialDiffeomorph_injective {x : M₁'} (hx : x ∈ g.source) :
    Function.Injective (germMapOn (g : M₁' → M₂') (V := ⟨g.source, g.open_source⟩)
      g.contMDiffOn_toFun hx rfl) := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs => ?_
  apply stalkToGerm_injective 𝓘(𝕜, E) ω M₂' (g x)
  have := congrArg (stalkToGerm 𝓘(𝕜, E) ω M₁' x) hs
  rw [stalkToGerm_germMapOn, map_zero] at this
  rw [map_zero]
  revert this
  induction stalkToGerm 𝓘(𝕜, E) ω M₂' (g x) s using Germ.inductionOn with
  | h f =>
    intro this
    rw [Germ.coe_compTendsto, ← Germ.coe_zero, Germ.coe_eq] at this
    rw [← Germ.coe_zero, Germ.coe_eq]
    have h1 : ∀ᶠ y in map (g : M₁' → M₂') (𝓝 x), f y = 0 :=
      eventually_map.mpr (this.mono fun _ hx => hx)
    have h2 : map (g : M₁' → M₂') (𝓝 x) = 𝓝 (g x) := g.toOpenPartialHomeomorph.map_nhds_eq hx
    rwa [h2] at h1

/-- The stalk map along a partial diffeomorphism, at a point of its
source, is surjective — a representative near `x` composed with `g⁻¹` represents a germ at `g x`.
-/
theorem germMapOn_partialDiffeomorph_surjective {x : M₁'} (hx : x ∈ g.source) :
    Function.Surjective (germMapOn (g : M₁' → M₂') (V := ⟨g.source, g.open_source⟩)
      g.contMDiffOn_toFun hx rfl) := by
  intro t
  obtain ⟨h, ht, W, hxW, hW⟩ :=
    (mem_range_stalkToGerm_iff 𝓘(𝕜, E) ω M₁' x (stalkToGerm 𝓘(𝕜, E) ω M₁' x t)).mp ⟨t, rfl⟩
  have hWo : IsOpen (g.target ∩ g.invFun ⁻¹' (W : Set M₁')) :=
    g.toOpenPartialHomeomorph.isOpen_inter_preimage_symm W.2
  have hsm : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (h ∘ g.invFun) (g.target ∩ g.invFun ⁻¹' (W : Set M₁')) :=
    hW.comp (g.contMDiffOn_invFun.mono inter_subset_left) fun _ hy => hy.2
  have hgx : g x ∈ g.target ∩ g.invFun ⁻¹' (W : Set M₁') :=
    ⟨g.toPartialEquiv.map_source hx, by
      rw [mem_preimage]
      change g.toPartialEquiv.symm (g.toPartialEquiv x) ∈ (W : Set M₁')
      rw [g.toPartialEquiv.left_inv hx]
      exact hxW⟩
  obtain ⟨s, hs⟩ := (mem_range_stalkToGerm_iff 𝓘(𝕜, E) ω M₂' (g x) (↑(h ∘ g.invFun))).mpr
    ⟨_, rfl, ⟨_, hWo⟩, hgx, hsm⟩
  refine ⟨s, stalkToGerm_injective 𝓘(𝕜, E) ω M₁' x ?_⟩
  rw [stalkToGerm_germMapOn, hs, Germ.coe_compTendsto, ht, Germ.coe_eq]
  filter_upwards [g.toOpenPartialHomeomorph.eventually_left_inverse hx] with y hy
  exact congrArg h hy

/-- **The stalk isomorphism along a local
analytic isomorphism** — the stalk map `𝒪_{M₂, g x} → 𝒪_{M₁, x}` of a partial diffeomorphism `g`
at a point `x` of its source is bijective. -/
theorem germMapOn_partialDiffeomorph_bijective {x : M₁'} (hx : x ∈ g.source) :
    Function.Bijective (germMapOn (g : M₁' → M₂') (V := ⟨g.source, g.open_source⟩)
      g.contMDiffOn_toFun hx rfl) :=
  ⟨germMapOn_partialDiffeomorph_injective g hx, germMapOn_partialDiffeomorph_surjective g hx⟩

end PartialDiffeo

end Manifold
