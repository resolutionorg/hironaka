/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.Manifold.StructureSheaf
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.Manifold.Chart
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.Germ.TaylorIdeal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The functor from analytic manifolds to analytic spaces is fully faithful

A `K`-morphism `F : Sp(M) ⟶ Sp(N)` between the analytic spaces of two manifolds is induced by a
unique analytic map, namely its underlying map `toSpaceFun ψ F : M → N` (`toSpace_fullyFaithful`).
This is not stated in the sources; it is what makes the local coordinations of
[Hir64, Ch. 0, §1, p. 120], which are `K`-morphisms into `(Kⁿ, 𝒜_{Kⁿ})`, the same thing as charts.
The proof:

* **Evaluation is preserved by the stalk maps** (`eval_stalkMap`): for a germ `σ` at `F y` with
  value `c`, `σ - c` is a non-unit; the stalk map is a local `K`-homomorphism sending constants to
  constants, so `F^*σ - c` is a non-unit, i.e. `F^*σ` has value `c`. Hence a pulled-back section has
  the composed values, `(F^*s)(y) = s(F y)` (`sheafHom_apply`): the sheaf map of a `K`-morphism of
  sheaves of functions is precomposition with the underlying map.
* **The underlying map is analytic** (`contMDiff_baseFun`): in a chart `χ` at `F x` with coordinates
  `ψ'`, the coordinate functions `ψ'_i ∘ χ` (`chartSection`) pull back to analytic functions on
  `F⁻¹(χ.source)` whose values are `ψ'_i (χ (F y))`, so `χ ∘ F` is analytic near `x`.
* **Two local `K`-homomorphisms out of a stalk `𝒪_{N,b}` agreeing on the coordinate germs of a chart
  agree** (`ringHom_ext_of_coord'`): Hadamard's lemma (`exists_eq_sum_coord_mul'`) gives the
  `𝔪`-adic approximation of every germ by polynomials in the coordinates, and Krull's intersection
  theorem in the Noetherian target finishes.
* **A `K`-morphism is determined by its underlying map** (`hom_ext_baseFun`): the stalk maps at `y`
  of two morphisms with the same base map are local `K`-homomorphisms `𝒪_{N, F y} → 𝒪_{M, y}` into a
  Noetherian local ring which agree on the coordinate germs, because the pulled-back coordinate
  sections have the same values; hence they agree, and a morphism of sheaves is determined by its
  stalk maps.

Then `toSpaceHom ψ : AnalyticMap M N → (Sp(M) ⟶ Sp(N))` is injective (`toSpaceHom_injective`) and
surjective (`exists_toSpaceHom_eq`, the analytic map being
`⟨toSpaceFun F, contMDiff_toSpaceFun F⟩`). The extensionality on points is used to show that a
comparison morphism is an isomorphism chart by chart (`Hironaka.AnalyticSpace.Manifold.StratumIso`)
and for morphisms into a non-singular space (`Hironaka.AnalyticSpace.HomExtNonSingular`); the stalk
lemma `ringHom_ext_of_coord'` is used for the uniqueness of lifts through a blow-up chart
(`Hironaka.AnalyticSpace.MonoidalUnique`) and in the gluing of local resolutions
(`Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Model`,
`Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Shear`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

noncomputable section

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace K E'] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] {N : Type u} [TopologicalSpace N] [ChartedSpace E' N]

/-- The underlying map `M → N` of a `K`-morphism `Sp(M) ⟶ Sp(N)`, with the manifolds' types. -/
def baseFun (F : ofManifold K E M ⟶ ofManifold K E' N) : M → N := fun x => F.1.base x

theorem baseFun_apply (F : ofManifold K E M ⟶ ofManifold K E' N) (x : M) :
    baseFun F x = F.1.base x :=
  rfl

theorem continuous_baseFun (F : ofManifold K E M ⟶ ofManifold K E' N) :
    Continuous (baseFun F) :=
  Hom.continuous_toFun F

/-- **The stalk map of a `K`-morphism preserves the value of a germ**: `σ - σ(F y)` is a non-unit,
so is its image, which is `F^*σ - σ(F y)`. -/
theorem eval_stalkMap (F : ofManifold K E M ⟶ ofManifold K E' N) (y : M)
    (σ : (structureSheaf K E' N).presheaf.stalk (F.1.base y)) :
    Manifold.eval K E M y ((F.1.stalkMap y).hom σ) = Manifold.eval K E' N (F.1.base y) σ := by
  let α : (structureSheaf K E' N).presheaf.stalk (F.1.base y) →+*
      (structureSheaf K E M).presheaf.stalk y := (F.1.stalkMap y).hom
  have hloc : IsLocalHom α := F.1.prop y
  change Manifold.eval K E M y (α σ) = _
  set c := Manifold.eval K E' N (F.1.base y) σ with hc
  have h1 : σ - const K E' N (F.1.base y) c ∈
      IsLocalRing.maximalIdeal ((structureSheaf K E' N).presheaf.stalk (F.1.base y)) :=
    (mem_maximalIdeal_iff_eval E' _).mpr (by rw [map_sub, eval_const, sub_self])
  have h2 : α (σ - const K E' N (F.1.base y) c) ∈
      IsLocalRing.maximalIdeal ((structureSheaf K E M).presheaf.stalk y) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun hu => h1 (hloc.map_nonunit _ hu)
  have h3 : α (const K E' N (F.1.base y) c) = const K E M y c := F.algebraMap_stalk y c
  rw [map_sub, h3] at h2
  have h4 := (mem_maximalIdeal_iff_eval E _).mp h2
  rw [map_sub, eval_const, sub_eq_zero] at h4
  exact h4

/-- **A pulled-back section has the composed values**, `(F^*s)(y) = s(F y)`. -/
theorem sheafHom_apply (F : ofManifold K E M ⟶ ofManifold K E' N) (U : Opens N)
    (s : (structureSheaf K E' N).presheaf.obj (op U)) (y : M) (hy : F.1.base y ∈ U) :
    ((F.1.c.app (op U)).hom s).1 ⟨y, hy⟩ = s.1 ⟨F.1.base y, hy⟩ := by
  have h := eval_stalkMap F y ((structureSheaf K E' N).presheaf.germ U (F.1.base y) hy s)
  have hl : (F.1.stalkMap y).hom ((structureSheaf K E' N).presheaf.germ U (F.1.base y) hy s) =
      (structureSheaf K E M).presheaf.germ ((Opens.map F.1.base).obj U) y hy
        ((F.1.c.app (op U)).hom s) :=
    PresheafedSpace.stalkMap_germ_apply F.1.toShHom.hom U y hy s
  rw [hl] at h
  exact (contMDiffSheafCommRing.eval_germ 𝓘(K, E) 𝓘(K) ω M K _ y hy _).symm.trans
    (h.trans (contMDiffSheafCommRing.eval_germ 𝓘(K, E') 𝓘(K) ω N K U (F.1.base y) hy s))

variable {n : ℕ}

/-- **The underlying map of a `K`-morphism between the spaces of two manifolds is analytic**: in a
chart `χ` at `F x`, the coordinate functions of `χ` pull back to analytic functions whose values are
the coordinates of `χ ∘ F`. -/
theorem contMDiff_baseFun [IsManifold 𝓘(K, E') ω N] (ψ' : E' ≃L[K] (Fin n → K))
    (F : ofManifold K E M ⟶ ofManifold K E' N) : ContMDiff 𝓘(K, E) 𝓘(K, E') ω (baseFun F) := by
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨(continuous_baseFun F).continuousAt, ?_⟩
  set χ := chartAt E' (baseFun F x) with hχdef
  have hχ : χ ∈ maximalAtlas 𝓘(K, E') ω N := IsManifold.chart_mem_maximalAtlas (baseFun F x)
  -- the open set `W = F⁻¹(χ.source)` and the pulled-back coordinate functions
  let W : Opens M := (Opens.map F.1.base).obj (chartSourceOpens χ)
  have hxW : x ∈ W := mem_chart_source E' (baseFun F x)
  let g : Fin n → M → K := fun i =>
    extendSection K E ((F.1.c.app (op (chartSourceOpens χ))).hom (chartSection E' ψ' χ hχ i))
  have hg : ∀ i, ContMDiffOn 𝓘(K, E) 𝓘(K) ω (g i) W := fun i => contMDiffOn_extendSection _
  have hval : ∀ y ∈ W, ∀ i, g i y = ψ' (χ (baseFun F y)) i := by
    intro y hy i
    have hy' : F.1.base y ∈ chartSourceOpens χ := hy
    exact (extendSection_of_mem K E _ hy).trans (sheafHom_apply F (chartSourceOpens χ) _ y hy')
  -- `χ ∘ F = ψ'⁻¹ ∘ (g i)_i` on `W`
  have hG : ContMDiffOn 𝓘(K, E) 𝓘(K, Fin n → K) ω (fun y i => g i y) W :=
    contMDiffOn_pi_module_iff.mpr hg
  have hχF : ContMDiffOn 𝓘(K, E) 𝓘(K, E') ω (χ ∘ baseFun F) W := by
    refine (((ψ'.symm : (Fin n → K) →L[K] E').contMDiff).comp_contMDiffOn hG).congr ?_
    intro y hy
    simp only [Function.comp_apply]
    have : (fun i => g i y) = ψ' (χ (baseFun F y)) := funext fun i => hval y hy i
    rw [this]
    exact (ψ'.symm_apply_apply _).symm
  have hext : (↑(extChartAt 𝓘(K, E') (baseFun F x)) ∘ baseFun F) = χ ∘ baseFun F := by
    rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
  rw [hext]
  exact hχF.contMDiffAt (W.isOpen.mem_nhds hxW)

/-- Two local ring homomorphisms from `𝒪_{M,a}` into a Noetherian local ring that agree on the
constants and on the coordinate germs of a chart at `a` agree: Hadamard's lemma gives the `𝔪`-adic
approximation by polynomials in the coordinates, and Krull's intersection theorem finishes (the form
of `ringHom_ext_of_coord` for the stalk of a manifold). -/
theorem ringHom_ext_of_coord' {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ψ : E ≃L[K] (Fin n → K)) {φ : OpenPartialHomeomorph M E} (hφ : φ ∈ maximalAtlas 𝓘(K, E) ω M)
    {a : M} (ha : a ∈ φ.source) (α β : (structureSheaf K E M).presheaf.stalk a →+* R)
    (hα : IsLocalHom α) (hβ : IsLocalHom β)
    (hc : ∀ c : K, α (const K E M a c) = β (const K E M a c))
    (hz : ∀ i, α (coord E ψ φ hφ ha i) = β (coord E ψ φ hφ ha i)) : α = β := by
  set S := RingHom.eqLocus α β
  have hcS : ∀ c, const K E M a c ∈ S := hc
  have hzS : ∀ i, coord E ψ φ hφ ha i ∈ S := hz
  have approx : ∀ N : ℕ, ∀ s : (structureSheaf K E M).presheaf.stalk a,
      ∃ P ∈ S,
        s - P ∈ (IsLocalRing.maximalIdeal ((structureSheaf K E M).presheaf.stalk a)) ^ N := by
    intro N
    induction N with
    | zero => intro s; exact ⟨0, S.zero_mem, by simp⟩
    | succ N ih =>
      intro s
      obtain ⟨g, hg⟩ := exists_eq_sum_coord_mul' E ψ φ ha hφ (s - const K E M a
          (Manifold.eval K E M a s))
        (by rw [map_sub, eval_const, sub_self])
      choose P hPS hP using fun i => ih (g i)
      refine ⟨const K E M a (Manifold.eval K E M a s) +
        ∑ i, (coord E ψ φ hφ ha i - const K E M a (Manifold.eval K E M a
            (coord E ψ φ hφ ha i))) * P i,
        ?_, ?_⟩
      · exact S.add_mem (hcS _)
          (S.sum_mem fun i _ => S.mul_mem (S.sub_mem (hzS i) (hcS _)) (hPS i))
      · have : s - (const K E M a (Manifold.eval K E M a s) +
            ∑ i, (coord E ψ φ hφ ha i - const K E M a (Manifold.eval K E M a
                (coord E ψ φ hφ ha i))) *
              P i) =
            ∑ i, (coord E ψ φ hφ ha i - const K E M a (Manifold.eval K E M a
                (coord E ψ φ hφ ha i))) *
              (g i - P i) := by
          rw [← sub_sub, hg, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
        rw [this, pow_succ']
        exact Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_mul (coord_sub_mem_maximalIdeal E ψ φ ha hφ i) (hP i)
  have hmap : ∀ (γ : (structureSheaf K E M).presheaf.stalk a →+* R) (_ : IsLocalHom γ) (N : ℕ)
      (t : (structureSheaf K E M).presheaf.stalk a),
      t ∈ (IsLocalRing.maximalIdeal ((structureSheaf K E M).presheaf.stalk a)) ^ N →
        γ t ∈ (IsLocalRing.maximalIdeal R) ^ N := by
    intro γ hγ N t ht
    have := hγ
    have hle : Ideal.map γ (IsLocalRing.maximalIdeal ((structureSheaf K E M).presheaf.stalk a)) ≤
        IsLocalRing.maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb
      exact fun hu => hb ((isUnit_map_iff γ b).mp hu)
    have := Ideal.pow_right_mono hle N
    rw [← Ideal.map_pow] at this
    exact this (Ideal.mem_map_of_mem γ ht)
  ext s
  have hdiff : ∀ N, α s - β s ∈ (IsLocalRing.maximalIdeal R) ^ N := by
    intro N
    obtain ⟨P, hPS, hP⟩ := approx N s
    have h1 : α s - β s = α (s - P) - β (s - P) := by
      rw [map_sub, map_sub, (hPS : α P = β P)]
      ring
    rw [h1]
    exact Ideal.sub_mem _ (hmap α hα N _ hP) (hmap β hβ N _ hP)
  have hmem : α s - β s ∈ ⨅ N, (IsLocalRing.maximalIdeal R) ^ N := Ideal.mem_iInf.mpr hdiff
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

/-- **A `K`-morphism between the spaces of two manifolds is determined by its underlying map**: its
stalk maps are local `K`-homomorphisms into Noetherian local rings agreeing on the coordinate germs
(the pulled-back coordinate sections have the same values), and a morphism of sheaves is determined
by its stalk maps. `ψ'` supplies the coordinates on the target's model space `E'`: the coordinate
germs `ψ'_i ∘ χ` of a chart `χ` at `F x` generate the maximal ideal of `𝒪_{N, F x}`, and the two
stalk maps agree on them because the pulled-back coordinate sections have the same values along the
common underlying map; `ψ` gives the Noetherianity of the stalks of the source through its charts.
-/
theorem hom_ext_baseFun [IsManifold 𝓘(K, E) ω M] [IsManifold 𝓘(K, E') ω N]
    (ψ : E ≃L[K] (Fin n → K)) {n' : ℕ} (ψ' : E' ≃L[K] (Fin n' → K))
    (F G : ofManifold K E M ⟶ ofManifold K E' N) (h : baseFun F = baseFun G) : F = G := by
  apply Hom.ext
  have hb : F.1.base = G.1.base := TopCat.ext fun x => congrFun h x
  obtain ⟨⟨⟨b₁, c₁⟩, p₁⟩, hF⟩ := F
  obtain ⟨⟨⟨b₂, c₂⟩, p₂⟩, hG⟩ := G
  change b₁ = b₂ at hb
  subst hb
  let f₁ : (ofManifold K E M).toLocallyRingedSpace ⟶ (ofManifold K E' N).toLocallyRingedSpace :=
    ⟨⟨b₁, c₁⟩, p₁⟩
  let f₂ : (ofManifold K E M).toLocallyRingedSpace ⟶ (ofManifold K E' N).toLocallyRingedSpace :=
    ⟨⟨b₁, c₂⟩, p₂⟩
  let F₁ : ofManifold K E M ⟶ ofManifold K E' N := ⟨f₁, hF⟩
  let F₂ : ofManifold K E M ⟶ ofManifold K E' N := ⟨f₂, hG⟩
  have hc : c₁ = c₂ := by
    ext U s
    apply TopCat.Presheaf.section_ext (structureSheaf K E M)
    intro y hy
    -- the stalk maps at `y` agree
    have hN : IsNoetherianRing ((structureSheaf K E M).presheaf.stalk y) :=
      isNoetherianRing_stalk_of_chart E ψ (chartAt E y) (mem_chart_source E y)
        (IsManifold.chart_mem_maximalAtlas y)
    let α : (structureSheaf K E' N).presheaf.stalk (b₁ y) →+*
        (structureSheaf K E M).presheaf.stalk y := (f₁.stalkMap y).hom
    let β : (structureSheaf K E' N).presheaf.stalk (b₁ y) →+*
        (structureSheaf K E M).presheaf.stalk y := (f₂.stalkMap y).hom
    have i₁ : IsLocalHom α := p₁ y
    have i₂ : IsLocalHom β := p₂ y
    set χ := chartAt E' (baseFun F₁ y) with hχdef
    have hχ : χ ∈ maximalAtlas 𝓘(K, E') ω N := IsManifold.chart_mem_maximalAtlas (baseFun F₁ y)
    have hby : baseFun F₁ y ∈ χ.source := mem_chart_source E' (baseFun F₁ y)
    have key : α = β := by
      refine ringHom_ext_of_coord' ψ' hχ hby α β i₁ i₂
        (fun c => (F₁.algebraMap_stalk y c).trans (F₂.algebraMap_stalk y c).symm) fun i => ?_
      -- the coordinate germs: both pulled-back sections have the same values
      have hsec : (c₁.app (op (chartSourceOpens χ))).hom (chartSection E' ψ' χ hχ i) =
          (c₂.app (op (chartSourceOpens χ))).hom (chartSection E' ψ' χ hχ i) := by
        apply Subtype.ext
        funext ⟨z, hz⟩
        exact (sheafHom_apply F₁ (chartSourceOpens χ) _ z hz).trans
          (sheafHom_apply F₂ (chartSourceOpens χ) _ z hz).symm
      exact (PresheafedSpace.stalkMap_germ_apply f₁.toShHom.hom (chartSourceOpens χ) y hby
        (chartSection E' ψ' χ hχ i)).trans ((congrArg
          ((structureSheaf K E M).presheaf.germ ((Opens.map b₁).obj (chartSourceOpens χ)) y hby)
            hsec).trans
          (PresheafedSpace.stalkMap_germ_apply f₂.toShHom.hom (chartSourceOpens χ) y hby
            (chartSection E' ψ' χ hχ i)).symm)
    refine (PresheafedSpace.stalkMap_germ_apply f₁.toShHom.hom U y hy s).symm.trans ?_
    refine Eq.trans ?_ (PresheafedSpace.stalkMap_germ_apply f₂.toShHom.hom U y hy s)
    exact DFunLike.congr_fun key _
  subst hc
  rfl

end AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace

open KLocallyRingedSpace

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ}
  (ψ : E ≃L[K] (Fin n → K)) {M N : AnalyticManifold.{u} K E}

/-- The underlying map `M → N` of a morphism `Sp(M) ⟶ Sp(N)`, with the manifolds' types (the base
map of the morphism of locally ringed spaces). -/
def toSpaceFun {M N : AnalyticManifold.{u} K E}
    (F : toSpace ψ M ⟶ toSpace ψ N) :
    M → N :=
  fun x => F.1.base x

theorem toSpaceFun_toSpaceHom {M N : AnalyticManifold.{u} K E}
    (f : AnalyticMap M N) : toSpaceFun ψ (toSpaceHom ψ f) = ⇑f :=
  rfl

/-- The underlying map of a morphism `Sp(M) ⟶ Sp(N)` is analytic. -/
theorem contMDiff_toSpaceFun (F : toSpace ψ M ⟶ toSpace ψ N) :
    ContMDiff 𝓘(K, E) 𝓘(K, E) ω (toSpaceFun ψ F) :=
  contMDiff_baseFun (M := M) (N := N) ψ F

/-- A morphism `Sp(M) ⟶ Sp(N)` is determined by its underlying map. -/
theorem hom_ext_toSpaceFun (F G : toSpace ψ M ⟶ toSpace ψ N)
    (h : toSpaceFun ψ F = toSpaceFun ψ G) : F = G :=
  hom_ext_baseFun (M := M) (N := N) ψ ψ F G h

/-- `Sp` is faithful. -/
theorem toSpaceHom_injective :
    Function.Injective
      (toSpaceHom ψ : AnalyticMap M N → (toSpace ψ M ⟶ toSpace ψ N)) := by
  intro f g hfg
  have h : toSpaceFun ψ (toSpaceHom ψ f) = toSpaceFun ψ (toSpaceHom ψ g) := by rw [hfg]
  rw [toSpaceFun_toSpaceHom, toSpaceFun_toSpaceHom] at h
  exact DFunLike.coe_injective h

/-- `Sp` is full: every morphism `Sp(M) ⟶ Sp(N)` is `Sp(f)` for the analytic map `f` underlying it.
-/
theorem exists_toSpaceHom_eq (F : toSpace ψ M ⟶ toSpace ψ N) :
    ∃ f : AnalyticMap M N, toSpaceHom ψ f = F :=
  ⟨⟨toSpaceFun ψ F, contMDiff_toSpaceFun ψ F⟩, hom_ext_toSpaceFun ψ _ _ rfl⟩

/-- **`Sp` is fully faithful**: analytic maps `M → N` correspond bijectively to morphisms
`Sp(M) ⟶ Sp(N)`. -/
theorem toSpace_fullyFaithful :
    Function.Bijective
      (toSpaceHom ψ : AnalyticMap M N → (toSpace ψ M ⟶ toSpace ψ N)) :=
  ⟨toSpaceHom_injective ψ, exists_toSpaceHom_eq ψ⟩

end AnalyticSpace
