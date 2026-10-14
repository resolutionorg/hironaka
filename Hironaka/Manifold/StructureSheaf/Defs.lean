/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits

/-!
# The structure sheaf of an analytic manifold

For a manifold `M` modelled on a normed space `E` over a field `𝕜` with analytic (`C^ω`) chart
changes, the **structure sheaf** `𝒪_M` is the sheaf of commutative rings
`U ↦ {f : U → 𝕜 : f is C^ω}`, the sheaf of regular functions of Bierstone–Milman's regular
coordinate charts [BM97, (0.3)], which for an analytic manifold is the sheaf of analytic functions
[BM97, §3, "Regular coordinate charts"].

* **The sheaf of `C^n` functions.** For a manifold `M` modelled on `(EM, HM)`, a manifold `N`
  modelled on `(E, H)` and any smoothness `n : ℕ∞ω`, `contMDiffSheaf IM I n M N` is the sheaf of
  types of `C^n` functions `M → N` (the local predicate `contMDiffLocalPredicate`, Mathlib's
  `LocalInvariantProp.localPredicate` for `contDiffWithinAt_localInvariantProp n`), whose sections
  over `U` are definitionally the bundled maps `C^n⟮IM, U; I, N⟯`; for a `C^n` commutative ring
  `R`, `contMDiffSheafCommRing IM I n M R` is the sheaf of commutative rings of `C^n` functions
  `M → R`. Mathlib's `smoothSheaf` and `smoothSheafCommRing` are the case `n = ∞` with `M` and `N`
  in one universe; here the target lives in `Type` and the manifold in `Type u`, so that the sheaf
  of rings is an object of `CommRingCat.{u}` over `TopCat.of M` and Mathlib's stalk API applies to
  manifolds whose carrier is in any universe. A section over `U` valued in `𝕜` extends by zero to a
  function on `M` (`extendBy0`).
* **The structure sheaf** `structureSheaf 𝕜 E M` is the case `n = ω`, `R = 𝕜`. Its global
  constants are the ring homomorphism `constHom : 𝕜 →+* Γ(M, 𝒪_M)`; a chart `φ` of the maximal atlas
  with coordinates `ψ : E ≃L[𝕜] (Fin n → 𝕜)` has the coordinate sections `ψ_i ∘ φ` over its source
  (`chartSection`) and their germs `x_i ∈ 𝒪_{M,a}` (`coord`).
* **The stalk as a ring of germs.** The stalk `𝒪_{M,a}` of the sheaf of `C^n` functions valued in
  `𝕜` embeds into `Filter.Germ (𝓝 a) 𝕜`: `stalkToGerm` sends the germ of a section `f` to the germ
  of its extension by zero (`stalkToGerm_germ`); it is injective (`stalkToGerm_injective`: two
  sections with the same germ agree on an open neighbourhood of `a`), and its range is the set of
  germs of functions `C^n` on a neighbourhood of `a` (`mem_range_stalkToGerm_iff`).
* **The stalk map of an analytic map.** For `φ : N → M` analytic on an open `V ∋ b` with
  `φ b = c`, `germMapOn φ hφ hb hc : 𝒪_{M,c} →+* 𝒪_{N,b}` is `s ↦ s ∘ φ`: the germ of `s` is
  composed with `φ` (`stalkGermComp`, through `germCompRingHom`, Mathlib's
  `Filter.Germ.compTendsto` as a ring homomorphism), the composite is again the germ of a section
  (`stalkGermComp_mem_range`, by the description of the range of `stalkToGerm`), and it is lifted
  back to the stalk along `stalkEquivRange`. The target point `c` is a parameter with
  `hc : φ b = c`, so that the stalk map of a local inverse at `φ b` lands in `𝒪_{N,b}` without
  transport; `germMap φ hφ b` is the case of a global analytic map. It is the stalk map along
  which ideal sheaves are pulled back (`IdealSheaf.pullback`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped Manifold ContDiff

universe u v

namespace Manifold

/-! ### The sheaf of `C^n` functions -/

section ContMDiff

open CategoryTheory.Limits

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (n : ℕ∞ω)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  (N : Type) [TopologicalSpace N] [ChartedSpace H N]

/-- The local predicate "`f : U → N` is `C^n`" on the open sets of `M`: Mathlib's
`LocalInvariantProp.localPredicate` for `contDiffWithinAt_localInvariantProp n`, with the target in
`Type` (Mathlib's version needs `M` and `N` in one universe). -/
def contMDiffLocalPredicate : TopCat.LocalPredicate fun _ : TopCat.of M => N where
  pred {U : Opens (TopCat.of M)} := fun f : U → N =>
    ChartedSpace.LiftProp (ContDiffWithinAtProp IM I n) f
  res := by
    intro U V i f h x
    have hUV : U ≤ V := CategoryTheory.leOfHom i
    change ChartedSpace.LiftPropAt (ContDiffWithinAtProp IM I n) (f ∘ Opens.inclusion hUV) x
    rw [← (contDiffWithinAt_localInvariantProp n).liftPropAt_iff_comp_inclusion hUV]
    apply h
  locality := by
    intro V f h x
    obtain ⟨U, hxU, i, hU⟩ := h x
    let x' : U := ⟨x, hxU⟩
    have hUV : U ≤ V := CategoryTheory.leOfHom i
    have : ChartedSpace.LiftPropAt (ContDiffWithinAtProp IM I n) f (Opens.inclusion hUV x') := by
      rw [(contDiffWithinAt_localInvariantProp n).liftPropAt_iff_comp_inclusion hUV]
      exact hU x'
    convert! this

/-- The sheaf of types of `C^n` functions from `M` to `N`. -/
def contMDiffSheaf : TopCat.Sheaf (Type u) (TopCat.of M) :=
  TopCat.subsheafToTypes (contMDiffLocalPredicate IM I n M N)

variable {M}

instance contMDiffSheaf.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((contMDiffSheaf IM I n M N).presheaf.obj U) (fun _ => ↑(unop U) → N) where
  coe a := a.1

variable {N}

section CommRing

variable (M) (R : Type) [CommRing R] [TopologicalSpace R] [ChartedSpace H R] [ContMDiffRing I n R]

instance (U : (Opens (TopCat.of M))ᵒᵖ) : CommRing ((contMDiffSheaf IM I n M R).presheaf.obj U) :=
  inferInstanceAs <| CommRing C^n⟮IM, (unop U : Opens M); I, R⟯

/-- The presheaf of `C^n` functions from `M` to a `C^n` commutative ring `R`, as a presheaf of
commutative rings. -/
def contMDiffPresheafCommRing : TopCat.Presheaf CommRingCat.{u} (TopCat.of M) :=
  { obj := fun U => CommRingCat.of ((contMDiffSheaf IM I n M R).presheaf.obj U)
    map := fun h => CommRingCat.ofHom <|
      ContMDiffMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

/-- The sheaf of `C^n` functions from `M` to a `C^n` commutative ring `R`, as a sheaf of
commutative rings. -/
def contMDiffSheafCommRing : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) where
  obj := contMDiffPresheafCommRing IM I n M R
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (contMDiffSheaf IM I n M R).property

instance contMDiffSheafCommRing.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((contMDiffSheafCommRing IM I n M R).presheaf.obj U) (fun _ => ↑(unop U) → R) where
  coe a := a.1

end CommRing

section ExtendBy0

variable (M)

open Classical in
/-- The extension by zero of a `C^n` section over `U` (valued in `𝕜`) to a function on `M`. -/
def extendBy0 {U : Opens M} (f : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.obj (op U)) :
    M → 𝕜 :=
  fun x => if h : x ∈ U then f ⟨x, h⟩ else 0

@[simp]
theorem extendBy0_of_mem {U : Opens M}
    (f : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.obj (op U)) {x : M} (hx : x ∈ U) :
    extendBy0 IM n M f x = f ⟨x, hx⟩ := by
  simp only [extendBy0, dite_eq_left hx]

theorem extendBy0_comp_val {U : Opens M}
    (f : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.obj (op U)) :
    extendBy0 IM n M f ∘ Subtype.val = f := by
  ext x
  exact extendBy0_of_mem IM n M f x.2

end ExtendBy0

end ContMDiff

/-! ### The structure sheaf -/

section StructureSheaf

open Filter
open scoped Topology
open IsManifold (maximalAtlas)

section General

variable (𝕜 : Type) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] (M : Type u) [TopologicalSpace M] [ChartedSpace E M]

/-- **The structure sheaf** `𝒪_M` of analytic functions on the manifold `M` modelled on `E` over
`𝕜`: the sheaf of commutative rings `U ↦ {f : U → 𝕜 : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜) ω f}`, the sheaf of
regular functions of an analytic manifold [BM97, (0.3); §3, "Regular coordinate charts"]. -/
@[implicit_reducible]
def structureSheaf : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) :=
  contMDiffSheafCommRing 𝓘(𝕜, E) 𝓘(𝕜) ω M 𝕜

instance structureSheaf.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((structureSheaf 𝕜 E M).presheaf.obj U) (fun _ => ↑(unop U) → 𝕜) where
  coe a := a.1

variable {M}

variable (M) in
/-- The constant section `c` over `M`. -/
def constSection (c : 𝕜) : (structureSheaf 𝕜 E M).presheaf.obj (op ⊤) :=
  (⟨fun _ => c, contMDiff_const⟩ : C^ω⟮𝓘(𝕜, E), ((⊤ : Opens M) : Opens M); 𝓘(𝕜), 𝕜⟯)

variable (M) in
/-- The constants as the `𝕜`-algebra structure of `𝒪_M`: the ring homomorphism
`𝕜 →+* Γ(M, 𝒪_M)`, `c ↦` the constant section `c` (the structure used when `M` is regarded as
an analytic space over `𝕜`). -/
def constHom : 𝕜 →+* (structureSheaf 𝕜 E M).presheaf.obj (op ⊤) where
  toFun := constSection 𝕜 E M
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

end General

section RCLike

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- A chart `φ` of the maximal atlas with coordinates `ψ`: the coordinate function `ψ_i ∘ φ` as a
section of `𝒪_M` over the source of `φ`. -/
def chartSection (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (i : Fin n) :
    (structureSheaf 𝕜 E M).presheaf.obj (op ⟨φ.source, φ.open_source⟩) :=
  ⟨fun x => ψ (φ x) i, by
    have h1 : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        (fun x : (⟨φ.source, φ.open_source⟩ : Opens M) => φ x) :=
      (contMDiffOn_of_mem_maximalAtlas (n := ω) hφ).comp_contMDiff contMDiff_subtype_val
        fun x => x.2
    exact ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i).contMDiff.comp
      ((ψ : E →L[𝕜] (Fin n → 𝕜)).contMDiff)).comp h1⟩

/-- **The coordinate germs** `x_i := ψ_i ∘ φ ∈ 𝒪_{M,a}` of a chart `φ` of the maximal atlas
containing `a`, with coordinates `ψ`. -/
def coord (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M}
    (ha : a ∈ φ.source) (i : Fin n) : (structureSheaf 𝕜 E M).presheaf.stalk a :=
  (structureSheaf 𝕜 E M).presheaf.germ ⟨φ.source, φ.open_source⟩ a ha (chartSection E ψ φ hφ i)

end RCLike


end StructureSheaf

/-! ### The stalk as a ring of germs -/

section StalkGerm

open CategoryTheory.Limits Filter Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  (n : ℕ∞ω) (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]

/-- The germ at `a` of the extension by zero, on the sections over an open neighbourhood `U` of
`a`, as a ring homomorphism (on `U ∈ 𝓝 a` the extensions of sums and products are the pointwise
sums and products). -/
def germAt (a : TopCat.of M) (U : Opens M) (ha : a ∈ U) :
    (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.obj (op U) →+* (𝓝 a).Germ 𝕜 where
  toFun f := ↑(extendBy0 IM n M f)
  map_one' := Germ.coe_eq.mpr <| by
    filter_upwards [U.2.mem_nhds ha] with x hx
    rw [extendBy0_of_mem IM n M _ hx]
    rfl
  map_mul' f g := Germ.coe_eq.mpr <| by
    filter_upwards [U.2.mem_nhds ha] with x hx
    rw [extendBy0_of_mem IM n M _ hx, extendBy0_of_mem IM n M _ hx, extendBy0_of_mem IM n M _ hx]
    rfl
  map_zero' := Germ.coe_eq.mpr <| by
    filter_upwards [U.2.mem_nhds ha] with x hx
    rw [extendBy0_of_mem IM n M _ hx]
    rfl
  map_add' f g := Germ.coe_eq.mpr <| by
    filter_upwards [U.2.mem_nhds ha] with x hx
    rw [extendBy0_of_mem IM n M _ hx, extendBy0_of_mem IM n M _ hx, extendBy0_of_mem IM n M _ hx]
    rfl

/-- Naturality of the germs at `a` over the open neighbourhoods of `a`. -/
theorem germAt_naturality (a : TopCat.of M) (U V : (OpenNhds a)ᵒᵖ) (i : U ⟶ V)
    (f : ((OpenNhds.inclusion a).op ⋙ (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf).obj U) :
    germAt IM n M a ((OpenNhds.inclusion a).obj (unop V)) (unop V).2
        (((OpenNhds.inclusion a).op ⋙ (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf).map i f) =
      germAt IM n M a ((OpenNhds.inclusion a).obj (unop U)) (unop U).2 f := by
  change (↑(extendBy0 IM n M (U := (OpenNhds.inclusion a).obj (unop V))
      (((OpenNhds.inclusion a).op ⋙ (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf).map i f)) :
      (𝓝 a).Germ 𝕜) =
    ↑(extendBy0 IM n M (U := (OpenNhds.inclusion a).obj (unop U)) f)
  refine Germ.coe_eq.mpr ?_
  filter_upwards [((OpenNhds.inclusion a).obj (unop V)).2.mem_nhds (unop V).2] with x hx
  rw [extendBy0_of_mem IM n M _ hx,
    extendBy0_of_mem IM n M _ (leOfHom ((OpenNhds.inclusion a).map i.unop) hx)]
  rfl

/-- The cocone of the germs at `a` of the extensions by zero over the open neighbourhoods of `a`. -/
def stalkToGermCocone (a : TopCat.of M) :
    Cocone ((OpenNhds.inclusion a).op ⋙ (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf) where
  pt := CommRingCat.of ((𝓝 a).Germ 𝕜)
  ι :=
    { app := fun U =>
        CommRingCat.ofHom (germAt IM n M a ((OpenNhds.inclusion a).obj (unop U)) (unop U).2)
      naturality := fun U V i => by
        ext f
        exact germAt_naturality IM n M a U V i f }

/-- **The stalk as germs**: the ring homomorphism `𝒪_{M,a} →+* Filter.Germ (𝓝 a) 𝕜` sending the
germ of a section to the germ of its extension by zero, as a morphism of `CommRingCat` (the germ
ring `Filter.Germ (𝓝 a) 𝕜` lives in the universe of `M`). -/
def stalkToGermHom (a : TopCat.of M) :
    (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.stalk a ⟶ CommRingCat.of ((𝓝 a).Germ 𝕜) :=
  colimit.desc _ (stalkToGermCocone IM n M a)

/-- The stalk as germs, `stalkToGerm : 𝒪_{M,a} →+* Filter.Germ (𝓝 a) 𝕜`. -/
def stalkToGerm (a : M) :
    (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.stalk a →+* (𝓝 a).Germ 𝕜 :=
  (stalkToGermHom IM n M a).hom

@[simp]
theorem stalkToGerm_germ (a : M) (U : Opens M) (ha : a ∈ U)
    (f : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.obj (op U)) :
    stalkToGerm IM n M a ((contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.germ U a ha f) =
      ↑(extendBy0 IM n M f) :=
  ConcreteCategory.congr_hom (colimit.ι_desc (stalkToGermCocone IM n M a) (op ⟨U, ha⟩)) f

/-- Two sections with the same germ at `a` agree on an open neighbourhood of `a`, so the stalk
embeds into the germs. -/
theorem stalkToGerm_injective (a : M) : Function.Injective (stalkToGerm IM n M a) := by
  intro s t hst
  let S := (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf
  obtain ⟨U, haU, f, rfl⟩ := S.exists_germ_eq s
  obtain ⟨V, haV, g, rfl⟩ := S.exists_germ_eq t
  rw [stalkToGerm_germ, stalkToGerm_germ, Germ.coe_eq] at hst
  obtain ⟨W₀, hW₀, hW₀o, haW₀⟩ := eventually_nhds_iff.mp hst
  let W : Opens M := ⟨W₀ ∩ (U ∩ V), hW₀o.inter (U.2.inter V.2)⟩
  have haW : a ∈ W := ⟨haW₀, haU, haV⟩
  have hWU : W ≤ U := fun x hx => hx.2.1
  have hWV : W ≤ V := fun x hx => hx.2.2
  refine S.germ_ext W haW (homOfLE hWU) (homOfLE hWV) ?_
  apply Subtype.ext
  ext ⟨x, hxW⟩
  change f (Set.inclusion hWU ⟨x, hxW⟩) = g (Set.inclusion hWV ⟨x, hxW⟩)
  have := hW₀ x hxW.1
  rwa [extendBy0_of_mem IM n M f hxW.2.1, extendBy0_of_mem IM n M g hxW.2.2] at this

/-- The extension by zero of a `C^n` section over `U` is `C^n` on `U`. -/
theorem contMDiffOn_extendBy0 {U : Opens M}
    (f : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.obj (op U)) :
    ContMDiffOn IM 𝓘(𝕜) n (extendBy0 IM n M f) U := by
  intro x hx
  refine (ContMDiffAt.contMDiffWithinAt ?_)
  have hf : ContMDiffAt IM 𝓘(𝕜) n (extendBy0 IM n M f ∘ Subtype.val) (⟨x, hx⟩ : U) := by
    rw [extendBy0_comp_val]
    exact f.2 ⟨x, hx⟩
  exact ((contDiffWithinAt_localInvariantProp (I := IM) (I' := 𝓘(𝕜))
    n).liftPropAt_iff_comp_subtype_val (U := U) (extendBy0 IM n M f) ⟨x, hx⟩).mpr hf

/-- The range of `stalkToGerm` is the set of germs of functions `C^n` on an open neighbourhood of
`a`. -/
theorem mem_range_stalkToGerm_iff (a : M) (g : (𝓝 a).Germ 𝕜) :
    g ∈ Set.range (stalkToGerm IM n M a) ↔
      ∃ h : M → 𝕜, g = ↑h ∧ ∃ U : Opens M, a ∈ U ∧ ContMDiffOn IM 𝓘(𝕜) n h U := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨U, haU, f, rfl⟩ := (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.exists_germ_eq s
    exact ⟨extendBy0 IM n M f, stalkToGerm_germ IM n M a U haU f, U, haU,
      contMDiffOn_extendBy0 IM n M f⟩
  · rintro ⟨h, rfl, U, haU, hU⟩
    let sec : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.obj (op U) :=
      ⟨h ∘ Subtype.val, fun x =>
        ((contDiffWithinAt_localInvariantProp (I := IM) (I' := 𝓘(𝕜))
          n).liftPropAt_iff_comp_subtype_val (U := U) h x).mp
            (hU.contMDiffAt (U.2.mem_nhds x.2))⟩
    refine ⟨(contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.germ U a haU sec,
      (stalkToGerm_germ IM n M a U haU sec).trans (Germ.coe_eq.mpr ?_)⟩
    filter_upwards [U.2.mem_nhds haU] with x hx
    exact extendBy0_of_mem IM n M sec hx


end StalkGerm

/-! ### The stalk map of an analytic map -/

section StalkMap

open Filter
open scoped Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- Composition of germs of `𝕜`-valued functions with a map `g` tending to the base point, as a
ring homomorphism `Filter.Germ l' 𝕜 →+* Filter.Germ l 𝕜` (Mathlib's `Filter.Germ.compTendsto`
bundled; the stalk maps below, the chart transport and the coordinate change are its instances). -/
def germCompRingHom {α β : Type*} {l : Filter α} {l' : Filter β} (g : α → β)
    (hg : Tendsto g l l') : l'.Germ 𝕜 →+* l.Germ 𝕜 where
  toFun f := f.compTendsto g hg
  map_one' := rfl
  map_mul' f f' := Germ.inductionOn₂ f f' fun _ _ => rfl
  map_zero' := rfl
  map_add' f f' := Germ.inductionOn₂ f f' fun _ _ => rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {N : Type v} [TopologicalSpace N] [ChartedSpace E' N]

section GermMap

variable (φ : N → M) {V : Opens N} (hφ : ContMDiffOn 𝓘(𝕜, E') 𝓘(𝕜, E) ω φ V) {b : N} (hb : b ∈ V)
  {c : M} (hc : φ b = c)

include hφ hb hc in
theorem tendsto_of_contMDiffOn_of_eq : Tendsto φ (𝓝 b) (𝓝 c) :=
  hc ▸ (hφ.continuousOn.continuousAt (V.2.mem_nhds hb)).tendsto

/-- The germ at `c = φ b` of a section of `𝒪_M`, composed with `φ`, as a germ at `b`. -/
def stalkGermComp : (structureSheaf 𝕜 E M).presheaf.stalk c →+* (𝓝 b).Germ 𝕜 :=
  (germCompRingHom (𝕜 := 𝕜) φ (tendsto_of_contMDiffOn_of_eq φ hφ hb hc)).comp
    (stalkToGerm 𝓘(𝕜, E) ω M c)

theorem stalkGermComp_apply (s : (structureSheaf 𝕜 E M).presheaf.stalk c) :
    stalkGermComp φ hφ hb hc s =
      (stalkToGerm 𝓘(𝕜, E) ω M c s).compTendsto φ (tendsto_of_contMDiffOn_of_eq φ hφ hb hc) := rfl

theorem stalkGermComp_mem_range (s : (structureSheaf 𝕜 E M).presheaf.stalk c) :
    stalkGermComp φ hφ hb hc s ∈ (stalkToGerm 𝓘(𝕜, E') ω N b).range := by
  obtain ⟨h, hs, U, hcU, hU⟩ :=
    (mem_range_stalkToGerm_iff 𝓘(𝕜, E) ω M c (stalkToGerm 𝓘(𝕜, E) ω M c s)).mp ⟨s, rfl⟩
  rw [RingHom.mem_range, ← Set.mem_range, stalkGermComp_apply, hs, Germ.coe_compTendsto]
  refine (mem_range_stalkToGerm_iff 𝓘(𝕜, E') ω N b _).mpr ⟨h ∘ φ, rfl, ?_⟩
  refine ⟨⟨V ∩ φ ⁻¹' U, hφ.continuousOn.isOpen_inter_preimage V.2 U.2⟩,
    ⟨hb, by rw [Set.mem_preimage, hc]; exact hcU⟩, ?_⟩
  intro x hx
  refine ContMDiffAt.contMDiffWithinAt ?_
  exact (hU.contMDiffAt (U.2.mem_nhds hx.2)).comp x (hφ.contMDiffAt (V.2.mem_nhds hx.1))

/-- The stalk as its own image in the germs, a ring isomorphism. -/
def stalkEquivRange (b : N) :
    (structureSheaf 𝕜 E' N).presheaf.stalk b ≃+* (stalkToGerm 𝓘(𝕜, E') ω N b).range :=
  RingEquiv.ofBijective (stalkToGerm 𝓘(𝕜, E') ω N b).rangeRestrict
    ⟨fun _ _ hst => stalkToGerm_injective 𝓘(𝕜, E') ω N b (congrArg Subtype.val hst),
      (stalkToGerm 𝓘(𝕜, E') ω N b).rangeRestrict_surjective⟩

/-- **The stalk map of an analytic map** `φ`, analytic on the open `V ∋ b`, with `φ b = c`: the
ring homomorphism `𝒪_{M,c} →+* 𝒪_{N,b}`, `s ↦ s ∘ φ`. -/
def germMapOn :
    (structureSheaf 𝕜 E M).presheaf.stalk c →+* (structureSheaf 𝕜 E' N).presheaf.stalk b :=
  (stalkEquivRange b).symm.toRingHom.comp
    ((stalkGermComp φ hφ hb hc).codRestrict _ (stalkGermComp_mem_range φ hφ hb hc))

end GermMap

section GlobalMap

variable (φ : N → M) (hφ : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω φ)

/-- The stalk map `𝒪_{M, φ b} →+* 𝒪_{N, b}` of a global analytic map. -/
abbrev germMap (b : N) :
    (structureSheaf 𝕜 E M).presheaf.stalk (φ b) →+* (structureSheaf 𝕜 E' N).presheaf.stalk b :=
  germMapOn φ (V := ⊤) hφ.contMDiffOn (Opens.mem_top b) rfl

end GlobalMap

end StalkMap

end Manifold
