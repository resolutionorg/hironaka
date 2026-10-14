/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.ModelChart
public import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Algebra.Local.QuotientParameters
import Hironaka.Algebra.Local.Regular
import Hironaka.AnalyticSpace.IsoCriterion
import Hironaka.AnalyticSpace.ModelSupport
import Hironaka.AnalyticSpace.RegularParameters
import Hironaka.AnalyticSpace.RegularStalk
import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.Submanifold.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The local model near a simple point is a manifold

Hironaka's "by means of jacobian criterion and the implicit function theorem"
[Hir64, Ch. 0, §1, p. 121]: at a point `z` of the local model `X = V(f) ⊆ G ⊆ Kⁿ` with the chart
data of `Hironaka/AnalyticSpace/ModelChart.lean` (an adapted chart `e` with `(f) = (e_σ)` near `z`),
the open `X|V` over the good neighbourhood `W` is `K`-isomorphic to the open `G' ⊆ K^{n−c}`,
`G' = {v | ι_σ v ∈ e.target, e⁻¹(ι_σ v) ∈ W}` with `ι_σ = embedCompl σ` the coordinate subspace
(`exists_kIso_analyticSpaceOfOpen_of_span_germ_eq`). This file builds the underlying homeomorphism
`G' ≃ₜ V` (`v ↦ e⁻¹(ι_σ v)`, inverse `w ↦ π_σ(e w)`), the evaluation of the fibres
`𝒜_{G,y}/𝓘_y → K` of the quotient sheaf (well defined because `𝓘_y ⊆ 𝔪_y`) through which the
`K`-morphism `(G', 𝒜_{G'}) → X|V` acts on sections, and proves it a `K`-isomorphism: its stalk
maps are surjective (a germ on `G'` pulls back along `π_σ ∘ e`) and injective (a surjection
between regular local rings of the same dimension `n − c` is an isomorphism). Used by
`Hironaka/AnalyticSpace/Jacobian.lean` and `Hironaka/AnalyticSpace/RegEval.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K] {n : ℕ} {G : Opens (Kn.{u} K n)} {k : ℕ}
  {f : Fin k → AnalyticFun K n G} {z : localModel K n G f} {c : ℕ}

namespace ModelChartData

variable (D : ModelChartData G f z c)

/-! ### The opens `V ⊆ X` and `G' ⊆ K^{n−c}` and the homeomorphism between them -/

/-- The open `V ∋ z` of the local model lying over the good neighbourhood `W`. -/
def V : Opens (localModel K n G f) := (Opens.map (localModel.ι K n G f).1.base).obj D.W

theorem mem_V {w : localModel K n G f} : w ∈ D.V ↔ w.1.1 ∈ D.W := Iff.rfl

theorem z_mem_V : z ∈ D.V := D.hzW

/-- The map `K^{n−c} → Kⁿ`, `v ↦ e⁻¹(ι_σ v)` (junk outside `e.target`). -/
def Θ (v : Kn.{u} K (n - c)) : Kn.{u} K n := D.e.symm ⟨embedCompl D.σ v.down⟩

/-- The coordinate-subspace inclusion `ι_σ : K^{n−c} → Kⁿ`, continuous. -/
theorem continuous_embed :
    Continuous fun v : Kn.{u} K (n - c) => (⟨embedCompl D.σ v.down⟩ : Kn.{u} K n) :=
  continuous_uliftUp.comp ((continuous_embedCompl D.σ).comp continuous_uliftDown)

/-- The open `G' ⊆ K^{n−c}`: the points `v` with `ι_σ v ∈ e.target` and `e⁻¹(ι_σ v) ∈ W`. -/
def G' : Opens (Kn.{u} K (n - c)) :=
  ⟨(fun v : Kn.{u} K (n - c) => (⟨embedCompl D.σ v.down⟩ : Kn.{u} K n)) ⁻¹'
      (D.e.target ∩ D.e.symm ⁻¹' D.W),
    (D.e.symm.isOpen_inter_preimage D.W.isOpen).preimage D.continuous_embed⟩

theorem mem_G' {v : Kn.{u} K (n - c)} :
    v ∈ D.G' ↔ (⟨embedCompl D.σ v.down⟩ : Kn.{u} K n) ∈ D.e.target ∧ D.Θ v ∈ D.W := Iff.rfl

theorem Θ_mem_W {v : Kn.{u} K (n - c)} (hv : v ∈ D.G') : D.Θ v ∈ D.W := hv.2

theorem Θ_mem_G {v : Kn.{u} K (n - c)} (hv : v ∈ D.G') : D.Θ v ∈ G := D.hU (D.hWU hv.2)

theorem e_Θ {v : Kn.{u} K (n - c)} (hv : v ∈ D.G') :
    D.e (D.Θ v) = ⟨embedCompl D.σ v.down⟩ := D.e.right_inv hv.1

theorem Θ_mem_cosupport {v : Kn.{u} K (n - c)} (hv : v ∈ D.G') :
    (⟨D.Θ v, D.Θ_mem_G hv⟩ : analyticSpaceOfOpen K n G) ∈ (modelIdeal K n G f).support :=
  (mem_cosupport_modelIdeal_iff K n G f ⟨D.Θ v, D.Θ_mem_G hv⟩).mpr
    ((D.eval_eq_zero_iff hv.2).mpr fun i => by
      change (D.e (D.Θ v)).down (D.σ i) = 0
      rw [D.e_Θ hv]
      exact embedCompl_apply_range D.σ v.down i)

/-- The underlying map `G' → V`, `v ↦ e⁻¹(ι_σ v)`. -/
def Ψ₀ (v : D.G') : D.V :=
  ⟨⟨⟨D.Θ v, D.Θ_mem_G v.2⟩, D.Θ_mem_cosupport v.2⟩, D.Θ_mem_W v.2⟩

theorem Ψ₀_val (v : D.G') : (D.Ψ₀ v).1.1.1 = D.Θ v := rfl

theorem mem_source_of_mem_V (w : D.V) : w.1.1.1 ∈ D.e.source := D.hWe w.2

theorem coord_eq_zero_of_mem_V (w : D.V) (i : Fin c) : (D.e w.1.1.1).down (D.σ i) = 0 :=
  (D.eval_eq_zero_iff w.2).mp ((mem_cosupport_modelIdeal_iff K n G f w.1.1).mp w.1.2) i

theorem embed_projCompl_e (w : D.V) :
    (⟨embedCompl D.σ (projCompl D.σ (D.e w.1.1.1).down)⟩ : Kn.{u} K n) = D.e w.1.1.1 := by
  rw [embedCompl_projCompl D.σ (D.coord_eq_zero_of_mem_V w)]

/-- The inverse map `V → G'`, `w ↦ π_σ(e w)`. -/
def Ψ₀inv (w : D.V) : D.G' :=
  ⟨⟨projCompl D.σ (D.e w.1.1.1).down⟩, by
    rw [mem_G', D.embed_projCompl_e w]
    refine ⟨D.e.map_source (D.mem_source_of_mem_V w), ?_⟩
    change D.e.symm ⟨embedCompl D.σ (projCompl D.σ (D.e w.1.1.1).down)⟩ ∈ D.W
    rw [D.embed_projCompl_e w, D.e.left_inv (D.mem_source_of_mem_V w)]
    exact w.2⟩

theorem Ψ₀inv_Ψ₀ (v : D.G') : D.Ψ₀inv (D.Ψ₀ v) = v := by
  apply Subtype.ext
  apply ULift.ext
  change projCompl D.σ (D.e (D.Θ v)).down = v.1.down
  rw [D.e_Θ v.2]
  exact projCompl_embedCompl D.σ v.1.down

theorem Ψ₀_Ψ₀inv (w : D.V) : D.Ψ₀ (D.Ψ₀inv w) = w := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change D.e.symm ⟨embedCompl D.σ (projCompl D.σ (D.e w.1.1.1).down)⟩ = w.1.1.1
  rw [D.embed_projCompl_e w, D.e.left_inv (D.mem_source_of_mem_V w)]

theorem continuous_Θ_restrict : Continuous fun v : D.G' => D.Θ v := by
  have h1 : Continuous fun v : D.G' => (⟨embedCompl D.σ v.1.down⟩ : Kn.{u} K n) :=
    D.continuous_embed.comp continuous_subtype_val
  exact D.e.continuousOn_symm.comp_continuous h1 fun v => v.2.1

/-- The inclusion `V → Kⁿ`, `w ↦ w`, is inducing (three subtype layers). -/
theorem isInducing_val : Topology.IsInducing fun w : D.V => w.1.1.1 :=
  Topology.IsInducing.subtypeVal.comp
    (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)

theorem continuous_Ψ₀ : Continuous D.Ψ₀ := by
  rw [D.isInducing_val.continuous_iff]
  exact D.continuous_Θ_restrict

theorem continuous_Ψ₀inv : Continuous D.Ψ₀inv := by
  have h2 : Continuous fun w : D.V => D.e w.1.1.1 :=
    D.e.continuousOn.comp_continuous D.isInducing_val.continuous D.mem_source_of_mem_V
  exact continuous_induced_rng.2 (continuous_uliftUp.comp ((continuous_projCompl D.σ).comp
    (continuous_uliftDown.comp h2)))

/-- The homeomorphism `G' ≃ₜ V` of Hironaka's implicit-function-theorem step. -/
def homeo : D.G' ≃ₜ D.V where
  toFun := D.Ψ₀
  invFun := D.Ψ₀inv
  left_inv := D.Ψ₀inv_Ψ₀
  right_inv := D.Ψ₀_Ψ₀inv
  continuous_toFun := D.continuous_Ψ₀
  continuous_invFun := D.continuous_Ψ₀inv

end ModelChartData

/-! ### Evaluation of the fibres of the quotient sheaf -/

variable (G f)

/-- The stalk `𝒜_{G,y}` of `(G, 𝒜_G)` read in `𝒜_{Kⁿ,y}` and evaluated at `y`. -/
def evalRestrict (y : analyticSpaceOfOpen K n G) :
    (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.stalk y →+* K :=
  (Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) y.1).comp
    ((affine K n).toLocallyRingedSpace.restrictStalkIso
      (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G) y).hom.hom

theorem evalRestrict_germ_toGlobal (y : analyticSpaceOfOpen K n G) (g : AnalyticFun K n G) :
    evalRestrict G (y := y)
      ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ ⊤ y (Opens.mem_top y)
        (toGlobal K n G g)) = g.eval y :=
  (congrArg (Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) y.1) (restrictStalkIso_germ_toGlobal K n G y
      g)).trans
    (contMDiffSheafCommRing.eval_germ 𝓘(K, Kn.{u} K n) 𝓘(K) ω (Kn.{u} K n) K G y.1 y.2 g)

/-- `evalRestrict` of the germ of a section `a` of `𝒜_G` over `W ∋ y` is the value `a y`. -/
theorem evalRestrict_germ (y : analyticSpaceOfOpen K n G) {W : Opens (analyticSpaceOfOpen K n G)}
    (hy : y ∈ W) (a : (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.obj (op W)) :
    evalRestrict G y ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ W y hy a) =
      extendSection K (Kn.{u} K n) a y.1 := by
  have h1 : ((affine K n).toLocallyRingedSpace.restrictStalkIso
        (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G) y).hom.hom
        ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ W y hy a) =
      (affine K n).toLocallyRingedSpace.presheaf.germ
        ((Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat)
          G).isOpenMap.functor.obj W) y.1 ⟨y, hy, rfl⟩ a :=
    congrArg (fun φ => CommRingCat.Hom.hom φ a)
      (PresheafedSpace.restrictStalkIso_hom_eq_germ
        (affine K n).toLocallyRingedSpace.toPresheafedSpace
        (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G) W y hy)
  exact (congrArg (Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) y.1) h1).trans
    ((contMDiffSheafCommRing.eval_germ 𝓘(K, Kn.{u} K n) 𝓘(K) ω (Kn.{u} K n) K _ _ _ a).trans
      (extendSection_of_mem K (Kn.{u} K n) a ⟨y, hy, rfl⟩).symm)

/-- The germs of the generators `f j` evaluate to `0` at a point of the support. -/
theorem stalkIdeal_le_ker_evalRestrict (w : localModel K n G f) :
    (modelIdeal K n G f).stalkIdeal w.1 ≤ RingHom.ker (evalRestrict G w.1) := by
  unfold modelIdeal
  erw [IdealSheaf.stalkIdeal_ofGlobal]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  exact RingHom.mem_ker.mpr ((evalRestrict_germ_toGlobal G w.1 (f j)).trans
    ((mem_cosupport_modelIdeal_iff K n G f w.1).mp w.2 j))

/-- Evaluation of the fibre `𝒜_{G,y}/𝓘_y` of the quotient sheaf at a point `y` of the support: the
value at `y`, well defined because `𝓘_y ⊆ 𝔪_y`. -/
def evalFiber (w : localModel K n G f) :
    QuotientSpace.fiber (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f) w →+*
      K :=
  Ideal.Quotient.lift _ (evalRestrict G w.1) fun _ ha => stalkIdeal_le_ker_evalRestrict G f w ha

theorem evalFiber_mk (w : localModel K n G f)
    (a : (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.stalk w.1) :
    evalFiber G f w (Ideal.Quotient.mk _ a) = evalRestrict G w.1 a :=
  Ideal.Quotient.lift_mk _ _ _


namespace ModelChartData

variable {G f} (D : ModelChartData G f z c)

/-! ### The sheaf component: evaluation of germ families along `Ψ₀` -/

/-- The coordinate embedding `ι_σ : K^{n−c} → Kⁿ` is analytic. -/
theorem contMDiff_embed :
    ContMDiff 𝓘(K, Kn.{u} K (n - c)) 𝓘(K, Kn.{u} K n) ω
      fun v : Kn.{u} K (n - c) => (⟨embedCompl D.σ v.down⟩ : Kn.{u} K n) := by
  rw [contMDiff_iff_contDiff]
  exact ((ContinuousLinearEquiv.ulift : Kn.{u} K n ≃L[K] (Fin n → K)).symm.contDiff.comp
    (contDiff_embedCompl D.σ)).comp
    (ContinuousLinearEquiv.ulift : Kn.{u} K (n - c) ≃L[K] (Fin (n - c) → K)).contDiff

/-- `Θ = e⁻¹ ∘ ι_σ` is analytic on `G'`. -/
theorem contMDiffOn_Θ : ContMDiffOn 𝓘(K, Kn.{u} K (n - c)) 𝓘(K, Kn.{u} K n) ω D.Θ D.G' :=
  (contMDiffOn_symm_of_mem_maximalAtlas (n := ω) D.he).comp D.contMDiff_embed.contMDiffOn
    fun _ hv => hv.1

/-- Membership in the image of an open of the subtype `U` under the inclusion. -/
theorem mem_functor_obj_iff {X : TopCat.{u}} (U : Opens X) (Ω : Opens ((Opens.toTopCat X).obj U))
    (x : X) :
    x ∈ (Opens.isOpenEmbedding U).isOpenMap.functor.obj Ω ↔ ∃ hx : x ∈ U, (⟨x, hx⟩ : U) ∈ Ω := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hΩ⟩
    exact ⟨⟨x, hx⟩, hΩ, rfl⟩

/-- The underlying continuous map `G' → V` as a morphism of `TopCat`. -/
def Ψtop : (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.toTopCat ⟶
    ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨D.Ψ₀, D.continuous_Ψ₀⟩

theorem Ψtop_apply (v : D.G') : D.Ψtop v = D.Ψ₀ v := rfl

/-- The open `Ω'' ⊆ K^{n−c}` under an open `Ω` of `V`: the image in `K^{n−c}` of `Ψ₀⁻¹ Ω ⊆ G'`. -/
def pullOpens (Ω : Opens ((localModel K n G f).restrictOpen D.V)) : Opens (Kn.{u} K (n - c)) :=
  (Opens.isOpenEmbedding (X := (affine K (n - c)).toLocallyRingedSpace.toTopCat)
    D.G').isOpenMap.functor.obj ((Opens.map D.Ψtop).obj Ω)

theorem mem_pullOpens {Ω : Opens ((localModel K n G f).restrictOpen D.V)} {v : Kn.{u} K (n - c)} :
    v ∈ D.pullOpens Ω ↔ ∃ hv : v ∈ D.G', D.Ψ₀ ⟨v, hv⟩ ∈ Ω :=
  mem_functor_obj_iff (X := (affine K (n - c)).toLocallyRingedSpace.toTopCat) D.G' _ v

theorem mem_G'_of_mem_pullOpens {Ω : Opens ((localModel K n G f).restrictOpen D.V)}
    {v : Kn.{u} K (n - c)} (h : v ∈ D.pullOpens Ω) : v ∈ D.G' :=
  (D.mem_pullOpens.mp h).elim fun hv _ => hv

theorem Ψ₀_mem_of_mem_pullOpens {Ω : Opens ((localModel K n G f).restrictOpen D.V)}
    {v : Kn.{u} K (n - c)} (h : v ∈ D.pullOpens Ω) :
    D.Ψ₀ ⟨v, D.mem_G'_of_mem_pullOpens h⟩ ∈ Ω := by
  obtain ⟨hv, hΩ⟩ := D.mem_pullOpens.mp h
  exact hΩ

/-- The point of the open `ι_V(Ω) ⊆ S` under `v ∈ Ω''`. -/
def ptOf {Ω : Opens ((localModel K n G f).restrictOpen D.V)} {v : Kn.{u} K (n - c)}
    (h : v ∈ D.pullOpens Ω) :
    (Opens.isOpenEmbedding (X := (localModel K n G f).toLocallyRingedSpace.toTopCat)
      D.V).isOpenMap.functor.obj Ω :=
  ⟨(D.Ψ₀ ⟨v, D.mem_G'_of_mem_pullOpens h⟩).1,
    (mem_functor_obj_iff (X := (localModel K n G f).toLocallyRingedSpace.toTopCat) D.V Ω _).mpr
      ⟨_, D.Ψ₀_mem_of_mem_pullOpens h⟩⟩

/-- The function on `K^{n−c}` obtained by evaluating a germ family `s` over `Ω ⊆ V` along `Ψ₀`
(and `0` outside `Ω''`). -/
def Fsec (Ω : Opens ((localModel K n G f).restrictOpen D.V))
    (s : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω))
    (v : Kn.{u} K (n - c)) : K :=
  open Classical in
  if h : v ∈ D.pullOpens Ω then evalFiber G f (D.ptOf h).1 (s.1 (D.ptOf h)) else 0

theorem Fsec_of_mem (Ω : Opens ((localModel K n G f).restrictOpen D.V))
    (s : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω))
    {v : Kn.{u} K (n - c)} (h : v ∈ D.pullOpens Ω) :
    D.Fsec Ω s v = evalFiber G f (D.ptOf h).1 (s.1 (D.ptOf h)) := by
  unfold Fsec
  rw [dite_eq_left h]


/-- The open of `K^{n−c}` under an open `T ⊆ S` of the local model: the points `v ∈ G'` with
`Ψ₀ v ∈ T`. -/
def pullOpensS (T : Opens (localModel K n G f)) : Opens (Kn.{u} K (n - c)) :=
  (Opens.isOpenEmbedding (X := (affine K (n - c)).toLocallyRingedSpace.toTopCat)
    D.G').isOpenMap.functor.obj ((Opens.map (D.Ψtop ≫ Opens.inclusion' D.V)).obj T)

theorem mem_pullOpensS {T : Opens (localModel K n G f)} {v : Kn.{u} K (n - c)} :
    v ∈ D.pullOpensS T ↔ ∃ hv : v ∈ D.G', (D.Ψ₀ ⟨v, hv⟩).1 ∈ T :=
  mem_functor_obj_iff (X := (affine K (n - c)).toLocallyRingedSpace.toTopCat) D.G' _ v

/-- The local formula: where the germ family `s` is the class of a section `a` of `𝒜_G`, the
evaluated function is `a ∘ Θ`. -/
theorem Fsec_eq_extendSection_Θ (Ω : Opens ((localModel K n G f).restrictOpen D.V))
    (s : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω))
    {v : Kn.{u} K (n - c)} (h : v ∈ D.pullOpens Ω) {W₁ : Opens (analyticSpaceOfOpen K n G)}
    {a : (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.obj (op W₁)}
    (hW : (D.ptOf h).1.1 ∈ W₁)
    (hs : s.1 (D.ptOf h) = Ideal.Quotient.mk _
      ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ W₁ (D.ptOf h).1.1 hW a)) :
    D.Fsec Ω s v = extendSection K (Kn.{u} K n) a (D.Θ v) := by
  refine (D.Fsec_of_mem Ω s h).trans ?_
  rw [hs]
  exact (evalFiber_mk G f _ _).trans (evalRestrict_germ G _ hW a)

/-- The evaluated function `F s` is analytic on `Ω''`: near each point it is `a ∘ Θ` for a section
`a` representing `s`, and `Θ` is analytic on `G'`. -/
theorem contMDiffOn_Fsec (Ω : Opens ((localModel K n G f).restrictOpen D.V))
    (s : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω)) :
    ContMDiffOn 𝓘(K, Kn.{u} K (n - c)) 𝓘(K) ω (D.Fsec Ω s) (D.pullOpens Ω) := by
  intro v hv
  apply ContMDiffAt.contMDiffWithinAt
  obtain ⟨U₁, hz₁, i₁, W₁, a, h₁⟩ := s.2 (D.ptOf hv)
  let N : Opens (Kn.{u} K (n - c)) := D.pullOpens Ω ⊓ D.pullOpensS U₁
  have hvN : v ∈ N :=
    Opens.mem_inf.mpr ⟨hv, D.mem_pullOpensS.mpr ⟨D.mem_G'_of_mem_pullOpens hv, hz₁⟩⟩
  have hloc : ∀ v' ∈ N, D.Fsec Ω s v' = extendSection K (Kn.{u} K n) a (D.Θ v') := by
    intro v' hv'
    have h' : v' ∈ D.pullOpens Ω := (Opens.mem_inf.mp hv').1
    obtain ⟨hv'G, hU₁⟩ := D.mem_pullOpensS.mp (Opens.mem_inf.mp hv').2
    obtain ⟨hW, hs⟩ := h₁ ⟨(D.ptOf h').1, hU₁⟩
    beta_reduce at hs
    exact D.Fsec_eq_extendSection_Θ Ω s h' hW hs
  have hΘ : ContMDiffAt 𝓘(K, Kn.{u} K (n - c)) 𝓘(K, Kn.{u} K n) ω D.Θ v :=
    D.contMDiffOn_Θ.contMDiffAt (D.G'.isOpen.mem_nhds (D.mem_G'_of_mem_pullOpens hv))
  have ha : ContMDiffAt 𝓘(K, Kn.{u} K n) 𝓘(K) ω (extendSection K (Kn.{u} K n) a) (D.Θ v) := by
    obtain ⟨hW, -⟩ := h₁ ⟨(D.ptOf hv).1, hz₁⟩
    exact (contMDiffOn_extendSection a).contMDiffAt
      (((Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat)
        G).isOpenMap.functor.obj W₁).isOpen.mem_nhds ⟨(D.ptOf hv).1.1, hW, rfl⟩)
  exact (ha.comp v hΘ).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (N.isOpen.mem_nhds hvN) hloc)


/-- The section of `𝒜_{K^{n−c}}` over `Ω''` obtained from a germ family `s` over `Ω`. -/
def secOf (Ω : Opens ((localModel K n G f).restrictOpen D.V))
    (s : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω)) :
    C^ω⟮𝓘(K, Kn.{u} K (n - c)), (D.pullOpens Ω : Opens (Kn.{u} K (n - c))); 𝓘(K), K⟯ :=
  sectionOfContMDiffOn (D.Fsec Ω s) (D.pullOpens Ω) (D.contMDiffOn_Fsec Ω s)

theorem secOf_apply (Ω : Opens ((localModel K n G f).restrictOpen D.V))
    (s : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω))
    (v : D.pullOpens Ω) :
    D.secOf Ω s v = evalFiber G f (D.ptOf v.2).1 (s.1 (D.ptOf v.2)) :=
  D.Fsec_of_mem Ω s v.2

theorem secOf_one (Ω : Opens ((localModel K n G f).restrictOpen D.V)) : D.secOf Ω 1 = 1 :=
  ContMDiffMap.ext fun v => by
    rw [D.secOf_apply]
    exact map_one _

theorem secOf_zero (Ω : Opens ((localModel K n G f).restrictOpen D.V)) : D.secOf Ω 0 = 0 :=
  ContMDiffMap.ext fun v => by
    rw [D.secOf_apply]
    exact map_zero _

theorem secOf_mul (Ω : Opens ((localModel K n G f).restrictOpen D.V))
    (s t : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω)) :
    D.secOf Ω (s * t) = D.secOf Ω s * D.secOf Ω t :=
  ContMDiffMap.ext fun v => by
    rw [ContMDiffMap.coe_mul, Pi.mul_apply, D.secOf_apply, D.secOf_apply, D.secOf_apply]
    exact map_mul _ _ _

theorem secOf_add (Ω : Opens ((localModel K n G f).restrictOpen D.V))
    (s t : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω)) :
    D.secOf Ω (s + t) = D.secOf Ω s + D.secOf Ω t :=
  ContMDiffMap.ext fun v => by
    rw [ContMDiffMap.coe_add, Pi.add_apply, D.secOf_apply, D.secOf_apply, D.secOf_apply]
    exact map_add _ _ _

theorem pullOpens_mono {Ω₁ Ω₂ : Opens ((localModel K n G f).restrictOpen D.V)} (h : Ω₁ ≤ Ω₂) :
    D.pullOpens Ω₁ ≤ D.pullOpens Ω₂ := fun v hv => by
  obtain ⟨hvG, hΩ⟩ := D.mem_pullOpens.mp hv
  exact D.mem_pullOpens.mpr ⟨hvG, h hΩ⟩

/-- Compatibility with restriction. -/
theorem secOf_res {Ω₁ Ω₂ : Opens ((localModel K n G f).restrictOpen D.V)} (h : Ω₁ ≤ Ω₂)
    (s : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω₂)) :
    D.secOf Ω₁ (((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.map
        (homOfLE h).op s) =
      (structureSheaf K (Kn.{u} K (n - c)) (Kn.{u} K (n - c))).presheaf.map
        (homOfLE (D.pullOpens_mono h)).op (D.secOf Ω₂ s) :=
  ContMDiffMap.ext fun v => by
    rw [D.secOf_apply]
    change _ = D.secOf Ω₂ s ⟨v.1, D.pullOpens_mono h v.2⟩
    rw [D.secOf_apply]
    rfl

/-- The component of the sheaf map at `Ω`: evaluation of germ families along `Ψ₀`, a ring
homomorphism `𝒪_{X|V}(Ω) →+* 𝒜_{K^{n−c}}(Ω'')`. -/
def secRingHom (Ω : Opens ((localModel K n G f).restrictOpen D.V)) :
    ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω) →+*
      (D.Ψtop _* (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf).obj
        (op Ω) where
  toFun := D.secOf Ω
  map_one' := D.secOf_one Ω
  map_mul' := D.secOf_mul Ω
  map_zero' := D.secOf_zero Ω
  map_add' := D.secOf_add Ω

/-- The component at `Ω` as a morphism of `CommRingCat`. -/
def ΨcApp (Ω : Opens ((localModel K n G f).restrictOpen D.V)) :
    ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω) ⟶
      (D.Ψtop _* (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf).obj (op Ω) :=
  CommRingCat.ofHom
    (R := ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω))
    (S := (D.Ψtop _* (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf).obj (op Ω))
    (D.secRingHom Ω)

theorem ΨcApp_apply (Ω : Opens ((localModel K n G f).restrictOpen D.V))
    (s : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω)) :
    D.ΨcApp Ω s = D.secOf Ω s := rfl

/-- The sheaf component `𝒪_{X|V} ⟶ Ψ₀_* 𝒜_{G'}`. -/
def Ψc : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf ⟶
    D.Ψtop _* (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf where
  app Ω := D.ΨcApp (unop Ω)
  naturality {_ _} i := by
    ext s
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
    exact D.secOf_res (leOfHom i.unop) s


/-! ### The morphism of presheafed spaces and its stalk maps -/

/-- The morphism of presheafed spaces `(G', 𝒜_{G'}) → X|V`: `Ψ₀` on points, evaluation of germ
families along `Ψ₀` on sections. -/
def ΨHom : (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.toPresheafedSpace ⟶
    ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.toPresheafedSpace where
  base := D.Ψtop
  c := D.Ψc

theorem ΨHom_base_apply (v : D.G') : D.ΨHom.base v = D.Ψ₀ v := rfl

/-- The stalk map of `ΨHom` on the germ of a section `s`: the germ of the evaluated section. -/
theorem ΨHom_stalkMap_germ (Ω : Opens ((localModel K n G f).restrictOpen D.V)) (v : D.G')
    (hv : D.Ψ₀ v ∈ Ω)
    (s : ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj (op Ω)) :
    D.ΨHom.stalkMap v
        (((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.germ Ω (D.Ψ₀ v)
          hv s) =
      (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf.germ
        ((Opens.map D.Ψtop).obj Ω) v hv (D.ΨcApp Ω s) :=
  congrArg (fun φ => CommRingCat.Hom.hom φ s) (PresheafedSpace.stalkMap_germ D.ΨHom Ω v hv)


/-! ### The stalks of `X|V` are regular of dimension `n − c` -/

/-- `d + c = n` in `WithBot ℕ∞` forces `d = n − c`. -/
theorem _root_.WithBot.eq_natCast_sub_of_add_natCast_eq {d : WithBot ℕ∞} {c n : ℕ}
    (h : d + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)) : d = ((n - c : ℕ) : WithBot ℕ∞) := by
  induction d with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    induction d with
    | top => exact absurd h (by simp)
    | coe d =>
      rw [← WithBot.coe_natCast]
      congr 1
      have hdc : d + c = n := by exact_mod_cast h
      rw [← hdc, Nat.add_sub_cancel]

/-- The germs of the `hs i` at a point of `V` lie in the maximal ideal (the `hs` vanish on the
support). -/
theorem germ_hs_mem_maximalIdeal (w : D.V) (i : Fin c) :
    (affine K n).toLocallyRingedSpace.presheaf.germ D.U w.1.1.1 (D.hWU w.2) (D.hs i) ∈
      IsLocalRing.maximalIdeal ((affine K n).toLocallyRingedSpace.presheaf.stalk w.1.1.1) := by
  have hval : (D.hs i).eval ⟨w.1.1.1, D.hWU w.2⟩ = 0 := by
    rw [show (D.hs i).eval ⟨w.1.1.1, D.hWU w.2⟩ = extendSection K (Kn.{u} K n) (D.hs i) w.1.1.1
      from (extendSection_of_mem K (Kn.{u} K n) (D.hs i) (D.hWU w.2)).symm,
      D.hcoord _ (D.mem_source_of_mem_V w) i]
    exact D.coord_eq_zero_of_mem_V w i
  exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu =>
    (isUnit_germ_affine_iff K n D.U ⟨_, D.hWU w.2⟩ (D.hs i)).mp hu hval)

/-- The germs of the `hs i` at a point of `V` have independent differentials. -/
theorem linearIndependent_dlin_germ_hs (w : D.V) :
    LinearIndependent K (fun i => dlin K n w.1.1.1
      ((affine K n).toLocallyRingedSpace.presheaf.germ D.U w.1.1.1 (D.hWU w.2) (D.hs i))) :=
  (linearIndependent_dlin_germ_iff_hasIndependentDifferentialsAt K n D.U D.hs w.1.1.1
    (D.hWU w.2)).mpr (D.hasIndependentDifferentialsAt (D.mem_source_of_mem_V w))

/-- The stalk ideal `𝓘_y` of the local model, transported to `𝒜_{Kⁿ,y}` along `restrictStalkIso`,
is the ideal generated by the germs of the `f j`. -/
theorem map_restrictStalkIso_stalkIdeal (y : analyticSpaceOfOpen K n G) :
    Ideal.map ((affine K n).toLocallyRingedSpace.restrictStalkIso
        (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G)
          y).commRingCatIsoToRingEquiv ((modelIdeal K n G f).stalkIdeal y) =
      Ideal.span (Set.range fun j =>
        (affine K n).toLocallyRingedSpace.presheaf.germ G y.1 y.2 (f j)) := by
  unfold modelIdeal
  erw [IdealSheaf.stalkIdeal_ofGlobal, Ideal.map_span]
  exact congrArg Ideal.span ((Set.range_comp _ _).symm.trans
    (congrArg Set.range (funext fun j => restrictStalkIso_germ_toGlobal K n G y (f j))))

/-- The stalk of the local model at a point `w` of `V`, read in `𝒜_{Kⁿ,w}`:
`𝒪_{X,w} ≅ 𝒜_{Kⁿ,w}/(hs)`. -/
def stalkEquivQuotient (w : D.V) :
    (localModel K n G f).toLocallyRingedSpace.presheaf.stalk w.1 ≃+*
      (affine K n).toLocallyRingedSpace.presheaf.stalk (w.1.1.1 : Kn.{u} K n) ⧸
        Ideal.span (Set.range fun i =>
          (affine K n).toLocallyRingedSpace.presheaf.germ D.U w.1.1.1 (D.hWU w.2) (D.hs i)) :=
  (QuotientSpace.stalkEquiv (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f)
    w.1).trans <|
  (Ideal.quotientEquiv
    (QuotientSpace.stalkIdeal (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f)
      w.1.1)
    (Ideal.span (Set.range fun j =>
      (affine K n).toLocallyRingedSpace.presheaf.germ G w.1.1.1 (D.hU (D.hWU w.2)) (f j)))
    ((affine K n).toLocallyRingedSpace.restrictStalkIso
      (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat) G)
        w.1.1).commRingCatIsoToRingEquiv
    (map_restrictStalkIso_stalkIdeal (f := f) w.1.1).symm).trans
    (Ideal.quotEquivOfEq (D.hideal w.1.1.1 w.2))

/-- The algebraic heart of Hironaka's statement [Hir64, Ch. 0, §1, p. 121]: the stalks of `X|V`
are regular local rings of dimension `n − c`. -/
theorem isRegularLocalRing_stalk_restrict (w : D.V) :
    IsRegularLocalRing
        (((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.stalk w) ∧
      ringKrullDim (((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.stalk w) =
        ((n - c : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hreg, hdim⟩ := isRegularLocalRing_quotient_span_range_and_ringKrullDim K n w.1.1.1 _
    (D.germ_hs_mem_maximalIdeal w) (D.linearIndependent_dlin_germ_hs w)
  let e := ((localModel K n G f).toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding D.V)
    w).commRingCatIsoToRingEquiv.trans (D.stalkEquivQuotient w)
  exact ⟨@IsRegularLocalRing.of_ringEquiv _ _ hreg _ _ e.symm,
    (ringKrullDim_eq_of_ringEquiv e).trans (WithBot.eq_natCast_sub_of_add_natCast_eq hdim)⟩


/-! ### Injectivity of the stalk maps: the dimension argument -/

/-- A surjective stalk map of `ΨHom` is injective: its source `𝒪_{X|V, Ψ₀ v}` is a regular local
domain of dimension `n − c` (`isRegularLocalRing_stalk_restrict`), its target `𝒜_{K^{n−c}, v}` has
the same dimension, and a proper ideal of a Noetherian local domain with a quotient of full
dimension is zero (`Ideal.eq_bot_of_ringKrullDim_quotient_eq`,
`Hironaka/Algebra/Local/QuotientParameters.lean`). -/
theorem stalkMap_injective_of_surjective (v : D.G')
    (hsurj : Function.Surjective (D.ΨHom.stalkMap v).hom) :
    Function.Injective (D.ΨHom.stalkMap v).hom := by
  obtain ⟨hreg, hdim⟩ := D.isRegularLocalRing_stalk_restrict (D.Ψ₀ v)
  have hreg' : IsRegularLocalRing
      (((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.toPresheafedSpace.presheaf.stalk
        (D.ΨHom.base v)) := hreg
  have hdim' : ringKrullDim
      (((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.toPresheafedSpace.presheaf.stalk
        (D.ΨHom.base v)) = ((n - c : ℕ) : WithBot ℕ∞) := hdim
  have : Nontrivial
      ((analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.toPresheafedSpace.presheaf.stalk
        v) :=
    (isRegularLocalRing_stalk_analyticSpaceOfOpen K (n - c) D.G' v).toIsLocalRing.toNontrivial
  rw [RingHom.injective_iff_ker_eq_bot]
  have hle : RingHom.ker (D.ΨHom.stalkMap v).hom ≤ IsLocalRing.maximalIdeal _ :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  have hq : ringKrullDim (_ ⧸ RingHom.ker (D.ΨHom.stalkMap v).hom) =
      ringKrullDim ((analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf.stalk v) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)
  rw [ringKrullDim_stalk_analyticSpaceOfOpen K (n - c) D.G' v, ← hdim'] at hq
  exact Ideal.eq_bot_of_ringKrullDim_quotient_eq hle hq

/-! ### Surjectivity of the stalk maps: pulling germs back along `π_σ ∘ e` -/

/-- The projection `π : Kⁿ → K^{n−c}`, `y ↦ π_σ(e y)` (junk outside `e.source`). -/
def π (y : Kn.{u} K n) : Kn.{u} K (n - c) := ⟨projCompl D.σ (D.e y).down⟩

theorem contMDiff_proj :
    ContMDiff 𝓘(K, Kn.{u} K n) 𝓘(K, Kn.{u} K (n - c)) ω
      fun y : Kn.{u} K n => (⟨projCompl D.σ y.down⟩ : Kn.{u} K (n - c)) := by
  rw [contMDiff_iff_contDiff]
  exact ((ContinuousLinearEquiv.ulift : Kn.{u} K (n - c) ≃L[K] (Fin (n - c) → K)).symm.contDiff.comp
    (contDiff_projCompl D.σ)).comp
    (ContinuousLinearEquiv.ulift : Kn.{u} K n ≃L[K] (Fin n → K)).contDiff

/-- `π = π_σ ∘ e` is analytic on `e.source`. -/
theorem contMDiffOn_π : ContMDiffOn 𝓘(K, Kn.{u} K n) 𝓘(K, Kn.{u} K (n - c)) ω D.π D.e.source :=
  (D.contMDiff_proj.contMDiffOn (s := Set.univ)).comp
    (contMDiffOn_of_mem_maximalAtlas (n := ω) D.he) fun _ _ => Set.mem_univ _

theorem π_Θ {v : Kn.{u} K (n - c)} (hv : v ∈ D.G') : D.π (D.Θ v) = v := by
  unfold π
  rw [D.e_Θ hv]
  exact ULift.ext _ _ (projCompl_embedCompl D.σ v.down)

theorem Θ_mem_source {v : Kn.{u} K (n - c)} (hv : v ∈ D.G') : D.Θ v ∈ D.e.source :=
  D.e.map_target hv.1


/-- The open `Wg ⊆ Kⁿ` on which the pullback `g ∘ π` of a section `g` of `𝒜_{G'}` over `Ω₀` is
analytic: `e.source ∩ π⁻¹(Ω₀)`. -/
def pullOpen (Ω₀ : Opens D.G') : Opens (Kn.{u} K n) :=
  ⟨D.e.source ∩ D.π ⁻¹' (Subtype.val '' (Ω₀ : Set D.G')),
    D.contMDiffOn_π.continuousOn.isOpen_inter_preimage D.e.open_source
      (D.G'.isOpen.isOpenMap_subtype_val _ Ω₀.isOpen)⟩

theorem mem_pullOpen {Ω₀ : Opens D.G'} {y : Kn.{u} K n} :
    y ∈ D.pullOpen Ω₀ ↔ y ∈ D.e.source ∧ ∃ hy : D.π y ∈ D.G', (⟨D.π y, hy⟩ : D.G') ∈ Ω₀ := by
  change y ∈ D.e.source ∧ D.π y ∈ Subtype.val '' (Ω₀ : Set D.G') ↔ _
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨u, hu, huy⟩
    refine ⟨huy ▸ u.2, ?_⟩
    have : (⟨D.π y, huy ▸ u.2⟩ : D.G') = u := Subtype.ext huy.symm
    rw [this]
    exact hu
  · rintro ⟨hy, hΩ⟩
    exact ⟨⟨_, hy⟩, hΩ, rfl⟩

theorem mem_source_of_mem_pullOpen {Ω₀ : Opens D.G'} {y : Kn.{u} K n} (hy : y ∈ D.pullOpen Ω₀) :
    y ∈ D.e.source := (D.mem_pullOpen.mp hy).1

theorem π_mem_of_mem_pullOpen {Ω₀ : Opens D.G'} {y : Kn.{u} K n} (hy : y ∈ D.pullOpen Ω₀) :
    D.π y ∈ (Opens.isOpenEmbedding (X := (affine K (n - c)).toLocallyRingedSpace.toTopCat)
      D.G').isOpenMap.functor.obj Ω₀ :=
  (mem_functor_obj_iff (X := (affine K (n - c)).toLocallyRingedSpace.toTopCat) D.G' Ω₀ _).mpr
    (D.mem_pullOpen.mp hy).2

theorem Θ_mem_pullOpen {Ω₀ : Opens D.G'} (v : D.G') (hv : v ∈ Ω₀) : D.Θ v ∈ D.pullOpen Ω₀ :=
  D.mem_pullOpen.mpr ⟨D.Θ_mem_source v.2, by rw [D.π_Θ v.2]; exact ⟨v.2, hv⟩⟩

/-- The pullback `g ∘ π` as a section of `𝒜_{Kⁿ}` over `pullOpen Ω₀`. -/
def pullSection (Ω₀ : Opens D.G')
    (g : (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf.obj (op Ω₀)) :
    (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.obj (op (D.pullOpen Ω₀)) :=
  sectionOfContMDiffOn (extendSection K (Kn.{u} K (n - c)) g ∘ D.π) (D.pullOpen Ω₀)
    ((contMDiffOn_extendSection g).comp
      (D.contMDiffOn_π.mono fun _ hy => D.mem_source_of_mem_pullOpen hy)
      fun _ hy => D.π_mem_of_mem_pullOpen hy)

/-- The trace of `pullOpen Ω₀` on `G`. -/
def pullOpenG (Ω₀ : Opens D.G') : Opens (analyticSpaceOfOpen K n G) :=
  (Opens.map (Opens.inclusion' (X := (affine K n).toLocallyRingedSpace.toTopCat) G)).obj
    (D.pullOpen Ω₀)

theorem functor_pullOpenG_le (Ω₀ : Opens D.G') :
    (Opens.isOpenEmbedding (X := (affine K n).toLocallyRingedSpace.toTopCat)
      G).isOpenMap.functor.obj (D.pullOpenG Ω₀) ≤ D.pullOpen Ω₀ := by
  rintro y ⟨x, hx, rfl⟩
  exact hx

/-- The pullback as a section of `𝒜_G`. -/
def pullSectionG (Ω₀ : Opens D.G')
    (g : (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf.obj (op Ω₀)) :
    (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.obj (op (D.pullOpenG Ω₀)) :=
  (affine K n).toLocallyRingedSpace.presheaf.map (homOfLE (D.functor_pullOpenG_le Ω₀)).op
    (D.pullSection Ω₀ g)

/-- The germ family of the pullback on the support. -/
def pullFamily (Ω₀ : Opens D.G')
    (g : (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf.obj (op Ω₀)) :
    (localModel K n G f).toLocallyRingedSpace.presheaf.obj (op (QuotientSpace.preimage
      (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f) (D.pullOpenG Ω₀))) :=
  QuotientSpace.classFamily _ _ (D.pullOpenG Ω₀) (D.pullSectionG Ω₀ g)

/-- The open of `V` over `pullOpen Ω₀`. -/
def pullOpenV (Ω₀ : Opens D.G') : Opens ((localModel K n G f).restrictOpen D.V) :=
  (Opens.map (Opens.inclusion' (X := (localModel K n G f).toLocallyRingedSpace.toTopCat) D.V)).obj
    (QuotientSpace.preimage (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f)
      (D.pullOpenG Ω₀))

theorem mem_pullOpenV {Ω₀ : Opens D.G'} {w : D.V} : w ∈ D.pullOpenV Ω₀ ↔ w.1.1.1 ∈ D.pullOpen Ω₀ :=
  Iff.rfl

theorem functor_pullOpenV_le (Ω₀ : Opens D.G') :
    (Opens.isOpenEmbedding (X := (localModel K n G f).toLocallyRingedSpace.toTopCat)
      D.V).isOpenMap.functor.obj (D.pullOpenV Ω₀) ≤
      QuotientSpace.preimage (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f)
        (D.pullOpenG Ω₀) := by
  rintro y ⟨x, hx, rfl⟩
  exact hx

/-- The pullback germ family as a section of `X|V` over `pullOpenV Ω₀`. -/
def pullFamilyV (Ω₀ : Opens D.G')
    (g : (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf.obj (op Ω₀)) :
    ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.obj
      (op (D.pullOpenV Ω₀)) :=
  (localModel K n G f).toLocallyRingedSpace.presheaf.map (homOfLE (D.functor_pullOpenV_le Ω₀)).op
    (D.pullFamily Ω₀ g)


theorem mem_pullOpens_pullOpenV {Ω₀ : Opens D.G'} {v' : Kn.{u} K (n - c)}
    (h : v' ∈ D.pullOpens (D.pullOpenV Ω₀)) :
    (D.ptOf h).1.1.1 ∈ D.pullOpen Ω₀ :=
  D.mem_pullOpenV.mp (D.Ψ₀_mem_of_mem_pullOpens h)

/-- The evaluated pull-back family is the section `g` itself: `(g ∘ π) ∘ Θ = g`. -/
theorem secOf_pullFamilyV_apply (Ω₀ : Opens D.G')
    (g : (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf.obj (op Ω₀))
    (v' : D.pullOpens (D.pullOpenV Ω₀)) :
    D.secOf (D.pullOpenV Ω₀) (D.pullFamilyV Ω₀ g) v' =
      extendSection K (Kn.{u} K (n - c)) g v'.1 := by
  rw [D.secOf_apply]
  have hpG : (D.ptOf v'.2).1.1 ∈ D.pullOpenG Ω₀ := D.mem_pullOpens_pullOpenV v'.2
  change evalFiber G f _ (Ideal.Quotient.mk _
    ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ (D.pullOpenG Ω₀)
      (D.ptOf v'.2).1.1 hpG (D.pullSectionG Ω₀ g))) = _
  rw [evalFiber_mk, evalRestrict_germ]
  refine (extendSection_of_mem K (Kn.{u} K n) _ (Set.mem_image_of_mem _ hpG)).trans ?_
  change (extendSection K (Kn.{u} K (n - c)) g ∘ D.π) (D.Θ v'.1) = _
  rw [Function.comp_apply, D.π_Θ (D.mem_G'_of_mem_pullOpens v'.2)]

/-- Surjectivity of the stalk maps: every germ `g` at `v ∈ G'` is the image of the germ family of
`g ∘ π`. -/
theorem stalkMap_surjective (v : D.G') : Function.Surjective (D.ΨHom.stalkMap v).hom := by
  intro t
  obtain ⟨Ω₀, hvΩ₀, g, rfl⟩ :=
    (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.presheaf.exists_germ_eq t
  have hvΩ : D.Ψ₀ v ∈ D.pullOpenV Ω₀ := D.mem_pullOpenV.mpr (D.Θ_mem_pullOpen v hvΩ₀)
  refine ⟨((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.presheaf.germ
    (D.pullOpenV Ω₀) (D.Ψ₀ v) hvΩ (D.pullFamilyV Ω₀ g), ?_⟩
  refine (D.ΨHom_stalkMap_germ _ v hvΩ _).trans ?_
  refine TopCat.Presheaf.germ_ext _ ((Opens.map D.Ψtop).obj (D.pullOpenV Ω₀) ⊓ Ω₀)
    (Opens.mem_inf.mpr ⟨hvΩ, hvΩ₀⟩) (homOfLE inf_le_left) (homOfLE inf_le_right) ?_
  refine ContMDiffMap.ext fun v' => ?_
  obtain ⟨hG', hW'⟩ := (mem_functor_obj_iff
    (X := (affine K (n - c)).toLocallyRingedSpace.toTopCat) D.G' _ v'.1).mp v'.2
  obtain ⟨hΩ, hΩ₀⟩ := Opens.mem_inf.mp hW'
  have hv' : v'.1 ∈ D.pullOpens (D.pullOpenV Ω₀) := D.mem_pullOpens.mpr ⟨hG', hΩ⟩
  exact (D.secOf_pullFamilyV_apply Ω₀ g ⟨v'.1, hv'⟩).trans
    (extendSection_of_mem K (Kn.{u} K (n - c)) g ((mem_functor_obj_iff
      (X := (affine K (n - c)).toLocallyRingedSpace.toTopCat) D.G' Ω₀ v'.1).mpr ⟨hG', hΩ₀⟩))

/-! ### The `K`-isomorphism -/

theorem stalkMap_bijective (v : D.G') : Function.Bijective (D.ΨHom.stalkMap v).hom :=
  ⟨D.stalkMap_injective_of_surjective v (D.stalkMap_surjective v), D.stalkMap_surjective v⟩

theorem isLocalHom_stalkMap (v : D.G') : IsLocalHom (D.ΨHom.stalkMap v).hom where
  map_nonunit a ha := by
    let e := RingEquiv.ofBijective _ (D.stalkMap_bijective v)
    have : a = e.symm ((D.ΨHom.stalkMap v).hom a) := (e.symm_apply_apply a).symm
    rw [this]
    exact ha.map e.symm

/-- The morphism of locally ringed spaces `(G', 𝒜_{G'}) ⟶ X|V`. -/
def ΨLRS : (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace ⟶
    ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace :=
  ⟨D.ΨHom, D.isLocalHom_stalkMap⟩

/-- `Ψ` carries the constants to the constants: it is a `K`-morphism. -/
theorem ΨLRS_algebraMap :
    (LocallyRingedSpace.Γ.map D.ΨLRS.op).hom.comp
        ((localModel K n G f).restrictOpen D.V).algebraMap =
      (analyticSpaceOfOpen K (n - c) D.G').algebraMap := by
  refine RingHom.ext fun r => ContMDiffMap.ext fun v' => ?_
  change D.secOf ⊤ (((localModel K n G f).restrictOpen D.V).algebraMap r) v' = r
  refine (D.secOf_apply ⊤ _ v').trans ?_
  change evalFiber G f _ (Ideal.Quotient.mk _
    ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ ⊤ (D.ptOf (Ω := ⊤) v'.2).1.1
      (Opens.mem_top _) ((analyticSpaceOfOpen K n G).algebraMap r))) = r
  refine (evalFiber_mk G f _ _).trans ?_
  refine (evalRestrict_germ G _ (Opens.mem_top _) _).trans ?_
  refine (extendSection_of_mem K (Kn.{u} K n) (M := Kn.{u} K n) _
    ((mem_functor_obj_iff (X := (affine K n).toLocallyRingedSpace.toTopCat) G ⊤ _).mpr
      ⟨(D.ptOf (Ω := ⊤) v'.2).1.1.2, Opens.mem_top _⟩)).trans ?_
  rfl

/-- The `K`-morphism `(G', 𝒜_{G'}) ⟶ X|V`. -/
def Ψ : analyticSpaceOfOpen K (n - c) D.G' ⟶ (localModel K n G f).restrictOpen D.V :=
  ⟨D.ΨLRS, D.ΨLRS_algebraMap⟩

theorem isIso_Ψ : IsIso D.Ψ :=
  haveI : IsIso D.Ψ.1.1.base :=
    (TopCat.isoOfHomeo (X := (analyticSpaceOfOpen K (n - c) D.G').toLocallyRingedSpace.toTopCat)
      (Y := ((localModel K n G f).restrictOpen D.V).toLocallyRingedSpace.toTopCat)
      D.homeo).isIso_hom
  KLocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective D.Ψ fun v => D.stalkMap_bijective v

/-- The `K`-isomorphism `X|V ≅ (G', 𝒜_{G'})` [Hir64, Ch. 0, §1, p. 121]. -/
def kIso : KLocallyRingedSpace.KIso ((localModel K n G f).restrictOpen D.V)
    (analyticSpaceOfOpen K (n - c) D.G') :=
  haveI := D.isIso_Ψ
  (asIso D.Ψ).symm

end ModelChartData

/-- The implicit function theorem for a local model [Hir64, Ch. 0, §1, p. 121]: if at a point `z` of
the local model `X = V(f₁, …, f_k) ⊆ G ⊆ Kⁿ` the ideal `𝓘_z = (f₁, …, f_k)_z` of `𝒜_{Kⁿ,z}` is
generated by `c` germs `h₁, …, h_c` with linearly independent differentials at `z`, then a
neighbourhood `X|V` of `z` is `K`-isomorphic to `(G', 𝒜_{G'})` for an open `G' ⊆ Kⁿ⁻ᶜ`. -/
theorem exists_kIso_analyticSpaceOfOpen_of_span_germ_eq (z : localModel K n G f) {c : ℕ}
    (h : Fin c → (affine K n).toLocallyRingedSpace.presheaf.stalk z.1.1)
    (hgen : Ideal.span (Set.range fun i =>
        (affine K n).toLocallyRingedSpace.presheaf.germ G z.1.1 z.1.2 (f i)) =
      Ideal.span (Set.range h))
    (hind : LinearIndependent K (fun i => dlin K n z.1.1 (h i))) :
    ∃ (V : Opens (localModel K n G f)) (_ : z ∈ V) (G' : Opens (Kn.{u} K (n - c))),
      Nonempty (KLocallyRingedSpace.KIso ((localModel K n G f).restrictOpen V)
        (analyticSpaceOfOpen K (n - c) G')) := by
  obtain ⟨D⟩ := exists_modelChartData G f z h hgen hind
  exact ⟨D.V, D.z_mem_V, D.G', ⟨D.kIso⟩⟩






end AnalyticSpace
