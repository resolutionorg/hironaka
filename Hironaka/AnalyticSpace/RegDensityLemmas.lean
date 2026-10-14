/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Semicontinuity
public import Hironaka.AnalyticSpace.Jacobian
public import Mathlib.Analysis.Complex.Basic
import Hironaka.Analytic.Rueckert.Noetherian
import Hironaka.Analytic.Rueckert.Parameters
import Hironaka.AnalyticSpace.Glue
import Hironaka.AnalyticSpace.ModelSupport
import Hironaka.AnalyticSpace.RegularParameters
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# Local models near a point: zero sets, simple points, graph ideals

Bookkeeping for the density of the simple points of a reduced complex space
(`Hironaka/AnalyticSpace/RegDensity.lean`; [Fre17, II 5.13]): the generators `modelGens` of `(f)_z`
read in `Conv K n` at a point `z` of a local model and their zero set near `0`, which is the
translated point set of the model (`eventually_forall_evalSeries_modelGens_eq_zero_iff`, from the
Taylor homomorphism's specification `IsTaylorHom`; `mem_cosupport_modelIdeal_iff_extendSection` for
the model's points); the transport of regularity and reducedness of stalks along an open subspace
and a `K`-isomorphism in both directions, so that a point of the chart `X|U ≅ (localModel)|W` is
simple in `X` iff its image is simple in the model (`mem_reg_iff_localModel`); the graph ideal
`(X_j − T_j(X ∘ e))_{j ∉ range e}`, whose quotient is a regular local ring
(`isRegularLocalRing_quotient_graphIdeal`: `n − d` germs of the maximal ideal with independent
differentials, `isRegularLocalRing_quotient_span_range_and_ringKrullDim` of
`Hironaka/AnalyticSpace/RegularParameters.lean`), hence a domain — so the graph ideal is prime and
Rückert's Nullstellensatz identifies it with the radical model ideal at a graph point; and a
separating series for a minimal prime (in every other minimal prime, not in the given one), which
isolates one local irreducible component. Routine; used by `Hironaka/AnalyticSpace/RegDensity.lean`,
`Hironaka/AnalyticSpace/Nullstellensatz.lean`, `Hironaka/AnalyticSpace/CoverLemmas.lean`,
`Hironaka/AnalyticSpace/RegOpenImmersion.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/PieceModel.lean`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open Analytic Filter Topology
open scoped Manifold ContDiff
open MvPowerSeries

universe u

namespace AnalyticSpace

open KLocallyRingedSpace

variable {K : Type} [RCLike K] {n : ℕ}

/-- The Taylor isomorphism at `q`, coerced to series, is the Taylor homomorphism. -/
theorem coe_convAt (q : Kn.{u} K n) (s : (affine K n).toLocallyRingedSpace.presheaf.stalk q) :
    ((taylorAffine K n q s : Analytic.Conv K n) : MvPowerSeries (Fin n) K) = taylorAt K n q s := rfl

/-- The function of the Taylor series at `p` of the germ of a section `F` is `F` near `p`. -/
theorem eventually_evalSeries_convAt_germ (p : Kn.{u} K n) {U : Opens (Kn.{u} K n)} (hp : p ∈ U)
    (F : (affine K n).toLocallyRingedSpace.presheaf.obj (op U)) :
    ∀ᶠ y' in 𝓝 (0 : Fin n → K),
      evalSeries ((taylorAffine K n p ((affine K n).toLocallyRingedSpace.presheaf.germ U p hp F) :
        Analytic.Conv K n) : MvPowerSeries (Fin n) K) y' =
        extendSection K (Kn.{u} K n) F (ULift.up (p.down + y')) := by
  have h1 := (isTaylorHom_taylorHom (Kn.{u} K n) ContinuousLinearEquiv.ulift
    (chartAt (Kn.{u} K n) p) (mem_chart_source _ p) (IsManifold.chart_mem_maximalAtlas p)).2 U hp F
  have hc : Continuous fun y' : Fin n → K => p.down + y' := continuous_const.add continuous_id
  have ht : Tendsto (fun y' : Fin n → K => p.down + y') (𝓝 0) (𝓝 p.down) :=
    hc.tendsto' 0 p.down (add_zero _)
  filter_upwards [ht.eventually h1] with y' hy'
  rw [coe_convAt]
  change extendSection K (Kn.{u} K n) F (ULift.up (p.down + y')) = _ at hy'
  rw [hy', taylorAt_apply]
  change evalSeries _ y' = evalSeries _ (p.down + y' - p.down)
  rw [add_sub_cancel_left]
  rfl

variable (G : Opens (Kn.{u} K n)) {k : ℕ} (f : Fin k → AnalyticFun K n G)

/-- The generators of `(f)_z` read in `Conv K n`. -/
def modelGens (z : localModel K n G f) (j : Fin k) : Analytic.Conv K n :=
  taylorAffine K n z.1.1 ((affine K n).toLocallyRingedSpace.presheaf.germ G z.1.1 z.1.2 (f j))

theorem span_range_modelGens (z : localModel K n G f) :
    Ideal.span (Set.range (modelGens G f z)) = modelIdealAt G f z := by
  unfold modelIdealAt modelGens
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- The zero set of `(f)_z` near `0` is the translated point set of the model. -/
theorem eventually_forall_evalSeries_modelGens_eq_zero_iff (z : localModel K n G f) :
    ∀ᶠ y' in 𝓝 (0 : Fin n → K),
      ((∀ j, evalSeries (modelGens G f z j : MvPowerSeries (Fin n) K) y' = 0) ↔
        ∀ j, extendSection K (Kn.{u} K n) (f j) (ULift.up (z.1.1.down + y')) = 0) := by
  have h : ∀ᶠ y' in 𝓝 (0 : Fin n → K), ∀ j,
      evalSeries (modelGens G f z j : MvPowerSeries (Fin n) K) y' =
        extendSection K (Kn.{u} K n) (f j) (ULift.up (z.1.1.down + y')) :=
    eventually_all.mpr fun j => eventually_evalSeries_convAt_germ z.1.1 z.1.2 (f j)
  filter_upwards [h] with y' hy'
  simp only [hy']

/-- Membership of a point of `G` in the model: all equations vanish. -/
theorem mem_cosupport_modelIdeal_iff_extendSection (x : analyticSpaceOfOpen K n G) :
    x ∈ (modelIdeal K n G f).support ↔
      ∀ j, extendSection K (Kn.{u} K n) (f j) (x.1 : Kn.{u} K n) = 0 := by
  rw [mem_cosupport_modelIdeal_iff]
  refine forall_congr' fun j => ?_
  rw [extendSection_of_mem (M := Kn.{u} K n) K (Kn.{u} K n) (f j) (x := (x.1 : Kn.{u} K n)) x.2]
  rfl


variable {G} {f}

/-- Regularity of a stalk of `X|U` is regularity of the stalk of `X`. -/
theorem isRegularLocalRing_stalk_restrictOpen_iff (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (x : X.restrictOpen U) :
    IsRegularLocalRing ((X.restrictOpen U).toLocallyRingedSpace.presheaf.stalk x) ↔
      IsRegularLocalRing (X.toLocallyRingedSpace.presheaf.stalk x.1) := by
  constructor
  · intro h
    exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _
      (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding U)
        x).commRingCatIsoToRingEquiv
  · exact isRegularLocalRing_stalk_restrictOpen X U x

/-- Regularity of stalks is invariant under a `K`-isomorphism. -/
theorem isRegularLocalRing_stalk_kIso_iff {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (a : A) :
    IsRegularLocalRing (B.toLocallyRingedSpace.presheaf.stalk (e.hom.1.base a)) ↔
      IsRegularLocalRing (A.toLocallyRingedSpace.presheaf.stalk a) := by
  constructor
  · intro h
    exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _
      (asIso (e.hom.1.stalkMap a)).commRingCatIsoToRingEquiv
  · exact isRegularLocalRing_stalk_of_kIso' e a

/-- A point of the chart `X|U ≅ (localModel)|W` is simple in `X` iff its image is a simple point of
the local model. -/
theorem mem_reg_iff_localModel {X : AnalyticSpace.{u} K} {U : Opens X} {n k : ℕ}
    {G : Opens (Kn.{u} K n)} {f : Fin k → AnalyticFun K n G} {W : Opens (localModel K n G f)}
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen U) ((localModel K n G f).restrictOpen W))
    {y : X} (hy : y ∈ U) :
    y ∈ regularLocus X ↔ IsRegularLocalRing
      ((localModel K n G f).toLocallyRingedSpace.presheaf.stalk (e.hom.1.base ⟨y, hy⟩).1) := by
  change IsRegularLocalRing (X.toLocallyRingedSpace.presheaf.stalk y) ↔ _
  rw [← isRegularLocalRing_stalk_restrictOpen_iff X.toKLocallyRingedSpace U ⟨y, hy⟩,
    ← isRegularLocalRing_stalk_kIso_iff e ⟨y, hy⟩,
    isRegularLocalRing_stalk_restrictOpen_iff]


variable {d : ℕ}

/-- A series in the base coordinates has no linear term in a fibre coordinate. -/
theorem coeff_single_convEmbed_of_not_mem_range (e : Fin d ↪ Fin n) (T : Analytic.Conv ℂ d)
    {i : Fin n}
    (hi : i ∉ Set.range e) :
    coeff (Finsupp.single i 1) (convEmbed ℂ e T : MvPowerSeries (Fin n) ℂ) = 0 := by
  rw [coe_convEmbed]
  apply coeff_rename_eq_zero
  rintro ⟨μ, hμ⟩
  have hmem : i ∈ (Finsupp.mapDomain e μ).support := by
    rw [hμ]
    simp
  rw [Finsupp.mapDomain_support_of_injective e.injective] at hmem
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hmem
  exact hi ⟨k, hk⟩

theorem constantCoeff_convEmbed (e : Fin d ↪ Fin n) (T : Analytic.Conv ℂ d) :
    constantCoeff (convEmbed ℂ e T : MvPowerSeries (Fin n) ℂ) =
      constantCoeff (T : MvPowerSeries (Fin d) ℂ) := by
  rw [coe_convEmbed, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  have : (0 : Fin n →₀ ℕ) = Finsupp.embDomain e 0 := by simp
  rw [this, coeff_embDomain_rename]

/-- Membership in the maximal ideal of `𝒜_{ℂⁿ,q}`, read through the Taylor isomorphism. -/
theorem mem_maximalIdeal_stalk_iff_convAt (q : Kn.{0} ℂ n)
    (s : (affine ℂ n).toLocallyRingedSpace.presheaf.stalk q) :
    s ∈ IsLocalRing.maximalIdeal ((affine ℂ n).toLocallyRingedSpace.presheaf.stalk q) ↔
      constantCoeff ((taylorAffine ℂ n q s : Analytic.Conv ℂ n) : MvPowerSeries (Fin n) ℂ) = 0 := by
  rw [← mem_maximalIdeal_conv_iff, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, MulEquiv.isUnit_map]

/-- The differential of a germ at `q`, read through the Taylor isomorphism: the linear coefficients
of its series. -/
theorem dlin_eq_coeff_convAt (q : Kn.{0} ℂ n)
    (s : (affine ℂ n).toLocallyRingedSpace.presheaf.stalk q) (i : Fin n) :
    dlin ℂ n q s i =
      coeff (Finsupp.single i 1) ((taylorAffine ℂ n q s : Analytic.Conv ℂ n) : MvPowerSeries
          (Fin n) ℂ) :=
  rfl

/-- The quotient of `𝒪_n` by the graph ideal `(X_j − T_j(X ∘ e))_{j ∉ range e}`, `T_j(0) = 0`, is a
regular local ring (`n − d` germs of `𝔪` with independent differentials,
`isRegularLocalRing_quotient_span_range_and_ringKrullDim`). -/
theorem isRegularLocalRing_quotient_graphIdeal (e : Fin d ↪ Fin n) (T : Fin n → Analytic.Conv ℂ d)
    (hT0 : ∀ j, j ∉ Set.range e → constantCoeff (T j : MvPowerSeries (Fin d) ℂ) = 0) :
    IsRegularLocalRing (Analytic.Conv ℂ n ⧸ Ideal.span (Set.range fun j :
        {j : Fin n // j ∉ Set.range e} =>
      convX ℂ j - convEmbed ℂ e (T j))) := by
  classical
  let q : Kn.{0} ℂ n := ULift.up 0
  let ι := {j : Fin n // j ∉ Set.range e}
  let ε : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let g : ι → Analytic.Conv ℂ n := fun j => convX ℂ j - convEmbed ℂ e (T j)
  let h : Fin (Fintype.card ι) → (affine ℂ n).toLocallyRingedSpace.presheaf.stalk q :=
    fun a => (taylorAffine ℂ n q).symm (g (ε a))
  have hcoe : ∀ a, ((taylorAffine ℂ n q (h a) : Analytic.Conv ℂ n) : MvPowerSeries (Fin n) ℂ) =
      X (ε a).1 - rename e (T (ε a) : MvPowerSeries (Fin d) ℂ) := by
    intro a
    simp only [h, RingEquiv.apply_symm_apply, g, Subalgebra.coe_sub, coe_convX, coe_convEmbed]
  have hm : ∀ a,
      h a ∈ IsLocalRing.maximalIdeal ((affine ℂ n).toLocallyRingedSpace.presheaf.stalk q) := by
    intro a
    rw [mem_maximalIdeal_stalk_iff_convAt, hcoe, map_sub, constantCoeff_X, zero_sub, neg_eq_zero,
      ← coe_convEmbed, constantCoeff_convEmbed, hT0 _ (ε a).2]
  have hli : LinearIndependent ℂ fun a => dlin ℂ n q (h a) := by
    let proj : (Fin n → ℂ) →ₗ[ℂ] (ι → ℂ) :=
      { toFun := fun v i => v i.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine LinearIndependent.of_comp proj ?_
    have hcomp : (⇑proj ∘ fun a => dlin ℂ n q (h a)) = ⇑(Pi.basisFun ℂ ι) ∘ ⇑ε := by
      funext a i
      change dlin ℂ n q (h a) i.1 = (Pi.basisFun ℂ ι) (ε a) i
      rw [dlin_eq_coeff_convAt, hcoe, map_sub, ← coe_convEmbed,
        coeff_single_convEmbed_of_not_mem_range e _ i.2, sub_zero, coeff_X, Pi.basisFun_apply]
      by_cases hia : i = ε a
      · subst hia
        simp
      · have hne : Finsupp.single (i : Fin n) 1 ≠ Finsupp.single ((ε a : ι) : Fin n) 1 := by
          intro h'
          exact hia (Subtype.ext (Finsupp.single_left_injective one_ne_zero h'))
        rw [ite_eq_right hne, Pi.single_eq_of_ne hia]
    rw [hcomp]
    exact (Pi.basisFun ℂ ι).linearIndependent.comp ε ε.injective
  obtain ⟨hreg, -⟩ := isRegularLocalRing_quotient_span_range_and_ringKrullDim ℂ n q h hm hli
  have hJ :
      Ideal.span (Set.range g) = Ideal.map (taylorAffine ℂ n q) (Ideal.span (Set.range h)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    have : (⇑(taylorAffine ℂ n q) ∘ h) = g ∘ ε := by
      funext a
      simp [h]
    rw [this, ε.surjective.range_comp]
  exact @IsRegularLocalRing.of_ringEquiv _ _ hreg _ _
    (Ideal.quotientEquiv _ _ (taylorAffine ℂ n q) hJ)

section ModelPoints

variable {G : Opens (Kn.{u} K n)} {k : ℕ} {f : Fin k → AnalyticFun K n G}

/-- The stalk of the local model at `z` is `𝒪_n / (f)_z`. -/
def stalkEquivQuotientModelIdealAt (z : localModel K n G f) :
    (localModel K n G f).toLocallyRingedSpace.presheaf.stalk z ≃+* Analytic.Conv K n ⧸ modelIdealAt
        G f z :=
  (stalkEquivQuotientF z).trans (Ideal.quotientEquiv _ _ (taylorAffine K n z.1.1) rfl)

/-- A point of the chart is simple iff `𝒪_n/(f)_z` is regular at its image. -/
theorem mem_reg_iff_isRegularLocalRing_quotient {X : AnalyticSpace.{u} K} {U : Opens X}
    {W : Opens (localModel K n G f)}
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen U) ((localModel K n G f).restrictOpen W))
    {y : X} (hy : y ∈ U) :
    y ∈ regularLocus X ↔
      IsRegularLocalRing (Analytic.Conv K n ⧸ modelIdealAt G f (e.hom.1.base ⟨y, hy⟩).1) := by
  rw [mem_reg_iff_localModel e hy]
  constructor
  · intro h
    exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _ (stalkEquivQuotientModelIdealAt _)
  · intro h
    exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _ (stalkEquivQuotientModelIdealAt _).symm

/-- Reducedness of stalks passes to an open subspace and back. -/
theorem isReduced_stalk_restrictOpen_iff (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (x : X.restrictOpen U) :
    _root_.IsReduced ((X.restrictOpen U).toLocallyRingedSpace.presheaf.stalk x) ↔
      _root_.IsReduced (X.toLocallyRingedSpace.presheaf.stalk x.1) := by
  let φ := (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding U)
    x).commRingCatIsoToRingEquiv
  constructor
  · intro h
    exact @isReduced_of_injective _ _ _ _ _ _ _ φ.symm φ.symm.injective h
  · intro h
    exact @isReduced_of_injective _ _ _ _ _ _ _ φ φ.injective h

/-- Reducedness of stalks transports forward along a `K`-isomorphism. -/
theorem isReduced_stalk_of_kIso {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (a : A)
    (h : _root_.IsReduced (A.toLocallyRingedSpace.presheaf.stalk a)) :
    _root_.IsReduced (B.toLocallyRingedSpace.presheaf.stalk (e.hom.1.base a)) := by
  let φ := (asIso (e.hom.1.stalkMap a)).commRingCatIsoToRingEquiv
  exact @isReduced_of_injective _ _ _ _ _ _ _ φ φ.injective h

/-- On a reduced space, the ideal `(f)_z` of the model at the image of a point is radical. -/
theorem isRadical_modelIdealAt_of_isReduced {X : AnalyticSpace.{u} K} (hX : X.IsReduced)
    {U : Opens X} {W : Opens (localModel K n G f)}
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen U) ((localModel K n G f).restrictOpen W))
    {y : X} (hy : y ∈ U) : (modelIdealAt G f (e.hom.1.base ⟨y, hy⟩).1).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  have h2 : _root_.IsReduced ((X.toKLocallyRingedSpace.restrictOpen
      U).toLocallyRingedSpace.presheaf.stalk
      ⟨y, hy⟩) :=
    (isReduced_stalk_restrictOpen_iff X.toKLocallyRingedSpace U ⟨y, hy⟩).mpr (hX y)
  have h3 := isReduced_stalk_of_kIso e ⟨y, hy⟩ h2
  set z : localModel K n G f := (e.hom.1.base ⟨y, hy⟩).1 with hz
  have h4 : _root_.IsReduced ((localModel K n G f).toLocallyRingedSpace.presheaf.stalk z) :=
    (isReduced_stalk_restrictOpen_iff (localModel K n G f) W _).mp h3
  let φ := stalkEquivQuotientModelIdealAt z
  exact @isReduced_of_injective _ _ _ _ _ _ _ φ.symm φ.symm.injective h4

/-- Transport of regularity of a quotient along `σ`: `𝒪_n / comap σ J ≅ 𝒪_n / J`. -/
theorem isRegularLocalRing_quotient_comap_iff (σ : Analytic.Conv K n ≃ₐ[K] Analytic.Conv K n)
    (J : Ideal (Analytic.Conv K n)) :
    IsRegularLocalRing (Analytic.Conv K n ⧸ Ideal.comap σ J) ↔ IsRegularLocalRing
        (Analytic.Conv K n ⧸ J) := by
  have hmap : J = Ideal.map (σ.toRingEquiv : Analytic.Conv K n →+* Analytic.Conv K n)
      (Ideal.comap σ J) := by
    have h := Ideal.map_comap_of_surjective (σ.toRingEquiv : Analytic.Conv K n →+* Analytic.Conv K
        n)
      σ.surjective J
    exact h.symm
  constructor
  · intro h
    exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _ (Ideal.quotientEquiv _ _ σ.toRingEquiv hmap)
  · intro h
    exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _
      (Ideal.quotientEquiv _ _ σ.toRingEquiv hmap).symm


end ModelPoints

section Neighbourhoods

variable (G : Opens (Kn.{u} K n)) {k : ℕ} (f : Fin k → AnalyticFun K n G)

/-- Near a point `z` of the model, a point `z.1.1 + y'` of `Kⁿ` at which all equations vanish is a
point of the model. -/
theorem eventually_exists_localModel_pt (z : localModel K n G f) :
    ∀ᶠ y' in 𝓝 (0 : Fin n → K),
      (∀ j, evalSeries (modelGens G f z j : MvPowerSeries (Fin n) K) y' = 0) →
        ∃ z' : localModel K n G f, z'.1.1 = ULift.up (z.1.1.down + y') := by
  have hc : Continuous fun y' : Fin n → K => (ULift.up (z.1.1.down + y') : Kn.{u} K n) :=
    (ContinuousLinearEquiv.ulift : Kn.{u} K n ≃L[K] (Fin n → K)).symm.continuous.comp
      (continuous_const.add continuous_id)
  have hG : ∀ᶠ y' in 𝓝 (0 : Fin n → K), (ULift.up (z.1.1.down + y') : Kn.{u} K n) ∈ G := by
    have : Tendsto (fun y' : Fin n → K => (ULift.up (z.1.1.down + y') : Kn.{u} K n)) (𝓝 0)
        (𝓝 z.1.1) := hc.tendsto' 0 z.1.1 (ULift.ext _ _ (add_zero _))
    exact this.eventually (G.isOpen.mem_nhds z.1.2)
  filter_upwards [hG, eventually_forall_evalSeries_modelGens_eq_zero_iff G f z] with y' hyG hiff
  intro h0
  refine ⟨⟨⟨ULift.up (z.1.1.down + y'), hyG⟩, ?_⟩, rfl⟩
  exact (mem_cosupport_modelIdeal_iff_extendSection G f ⟨_, hyG⟩).mpr (hiff.mp h0)

/-- A neighbourhood of a point of `(localModel)|W` contains all points of the model over an open
of `Kⁿ` around the point. -/
theorem exists_mem_nhds_of_mem_nhds_localModel_restrict {W : Opens (localModel K n G f)}
    {z : localModel K n G f} (hz : z ∈ W)
    {N : Set ((localModel K n G f).restrictOpen W)}
    (hN : N ∈ 𝓝 (⟨z, hz⟩ : (localModel K n G f).restrictOpen W)) :
    ∃ O ∈ 𝓝 z.1.1, ∀ (z' : localModel K n G f) (hz' : z' ∈ W), z'.1.1 ∈ O →
      (⟨z', hz'⟩ : (localModel K n G f).restrictOpen W) ∈ N := by
  let g : (localModel K n G f).restrictOpen W → Kn.{u} K n := fun z' => z'.1.1.1
  have hind : Topology.IsInducing g :=
    Topology.IsInducing.subtypeVal.comp (Topology.IsInducing.subtypeVal.comp
      Topology.IsInducing.subtypeVal)
  let w : (localModel K n G f).restrictOpen W := ⟨z, hz⟩
  have hN' : N ∈ Filter.comap g (𝓝 (g w)) := by
    rw [← hind.nhds_eq_comap w]
    exact hN
  obtain ⟨O, hO, hsub⟩ := Filter.mem_comap.mp hN'
  exact ⟨O, hO, fun z' hz' hzO => hsub hzO⟩

/-- An open of the model containing `z` contains all points of the model over an open of `Kⁿ`
around `z.1.1`. -/
theorem exists_mem_nhds_of_mem_opens_localModel {W : Opens (localModel K n G f)}
    {z : localModel K n G f} (hz : z ∈ W) :
    ∃ O ∈ 𝓝 z.1.1, ∀ z' : localModel K n G f, z'.1.1 ∈ O → z' ∈ W := by
  let g : localModel K n G f → Kn.{u} K n := fun z' => z'.1.1
  have hind : Topology.IsInducing g :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hW : (W : Set (localModel K n G f)) ∈ 𝓝 z := W.isOpen.mem_nhds hz
  have hW' : (W : Set (localModel K n G f)) ∈ Filter.comap g (𝓝 (g z)) := by
    rw [← hind.nhds_eq_comap z]
    exact hW
  obtain ⟨O, hO, hsub⟩ := Filter.mem_comap.mp hW'
  exact ⟨O, hO, fun z' hzO => hsub hzO⟩


end Neighbourhoods

end AnalyticSpace

namespace Analytic

variable {n : ℕ}

/-- The other components are avoided: for `I` radical, `P` a minimal prime of `I` and `h₀` in every
other minimal prime, `F · h₀ ∈ I` for every `F ∈ P`. -/
theorem mul_mem_of_mem_minimalPrimes_of_forall_mem {I P : Ideal (Conv ℂ n)} (hI : I.IsRadical)
    (hP : P ∈ I.minimalPrimes) {h₀ : Conv ℂ n} (hh₀ : ∀ Q ∈ I.minimalPrimes, Q ≠ P → h₀ ∈ Q)
    {F : Conv ℂ n} (hF : F ∈ P) : F * h₀ ∈ I := by
  rw [← hI.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
  intro Q hQ
  by_cases hQP : Q = P
  · subst hQP
    exact Q.mul_mem_right _ hF
  · exact Q.mul_mem_left _ (hh₀ Q hQ hQP)

/-- A separating element for a minimal prime: `h₀` in every other minimal prime and not in `P`. -/
theorem exists_mem_forall_minimalPrimes_ne_of_mem_minimalPrimes {I P : Ideal (Conv ℂ n)}
    (hP : P ∈ I.minimalPrimes) :
    ∃ h₀ : Conv ℂ n, (∀ Q ∈ I.minimalPrimes, Q ≠ P → h₀ ∈ Q) ∧ h₀ ∉ P := by
  classical
  have hPp : P.IsPrime := hP.1.1
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (Conv ℂ n) I
  set s : Finset (Ideal (Conv ℂ n)) := hfin.toFinset.erase P with hs
  by_contra hcon
  have hle : s.inf id ≤ P := by
    intro h₀ hh₀
    by_contra hnot
    apply hcon
    refine ⟨h₀, fun Q hQ hQP => ?_, hnot⟩
    have hQs : Q ∈ s := Finset.mem_erase.mpr ⟨hQP, hfin.mem_toFinset.mpr hQ⟩
    exact (Finset.inf_le hQs : s.inf id ≤ id Q) hh₀
  obtain ⟨Q, hQs, hQP⟩ := hPp.inf_le'.mp hle
  have hQmin : Q ∈ I.minimalPrimes := hfin.mem_toFinset.mp (Finset.mem_of_mem_erase hQs)
  have hne : Q ≠ P := Finset.ne_of_mem_erase hQs
  exact hne (le_antisymm hQP (hP.2 hQmin.1 hQP))

end Analytic

end
