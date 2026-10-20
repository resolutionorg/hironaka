/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexify
public import Hironaka.AnalyticSpace.ClosedSubspace.Defs
public import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.Manifold.Sheaf.LocalRing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Complexifications of real-analytic spaces and the morphism `α_n`

Hironaka [Hir64, Ch. 0, §1, p. 120] identifies `ℝ` with a topological subfield of `ℂ`, hence `ℝⁿ`
with a topological subspace of `ℂⁿ`, and has the natural `ℂ`-isomorphism
`α_n : (ℝⁿ, 𝒜_{ℝⁿ} ⊗_ℝ ℂ) → (ℂⁿ, 𝒜_{ℂⁿ})|ℝⁿ`. A preanalytic complexification of `X` is a pair
`(Y, f)` of a preanalytic `ℂ`-space `Y` and a `ℂ`-morphism `f : X(ℂ) → Y` such that (1) `f(X)` is a
closed subset of `|Y|` and (2) `f` induces a `ℂ`-isomorphism of `X(ℂ)` onto `Y|f(X)`; an analytic
complexification is a preanalytic one with `Y` an analytic `ℂ`-space.

* `Complexification X`: Hironaka's analytic complexification of an analytic `ℝ`-space `X`, an
  analytic `ℂ`-space `Y` with a `ℂ`-morphism `f : X(ℂ) ⟶ Y` such that (1) `f(X)` is closed and
  (2) `f` is a homeomorphism onto `f(X)` whose stalk maps `𝒪_{Y,f(x)} → 𝒪_{X(ℂ),x}` are
  bijective — the stalkwise reading of "`f` induces a `ℂ`-isomorphism of `X(ℂ)` onto `Y|f(X)`"
  (`Y|f(X)` has the stalks `𝒪_{Y,f(x)}`, and a morphism of sheaves is an isomorphism iff it is so
  on stalks). Preanalytic `ℂ`-spaces are not defined in this library, so the preanalytic notion
  is not transcribed; `complexify` itself is defined for every `ℝ`-local-ringed space with real
  residue fields, which covers the preanalytic case. That every analytic `ℝ`-space has a
  complexification is the theorem of Bruhat and Whitney [Hir64, Ch. 0, §1, p. 120, footnote 7].
* `localModelSpace K n G f`: a local analytic `K`-space is an analytic `K`-space (clause (i) with
  the identity, Hausdorff and countable at infinity as a closed subset of an open of `Kⁿ`); `ℝⁿ`
  itself and every `V(f₁, …, f_k) ⊆ G` are analytic spaces this way (the example
  `V(x² + y²) ⊆ ℝ²` is `circleSpace` of `HironakaExamples/Space/CircleSpace.lean`).
* `Hom.restrictTo g U U' h : A|U ⟶ B|U'`, the restriction of a `K`-morphism to opens with
  `g(U) ⊆ U'`, the lift through the open immersion `B|U' ⟶ B`; `restrictOpenIncl : A|U ⟶ A|U'`
  for `U ≤ U'`; `IsLocalCoordination X U h`, "`(U, h)` is a local `Kⁿ`-coordination" as a
  predicate (the content of `LocalCoordination`).
* `realToComplex n : (ℝⁿ, 𝒜_{ℝⁿ} ⊗_ℝ ℂ) ⟶ (ℂⁿ, 𝒜_{ℂⁿ})`, Hironaka's `α_n` as a `ℂ`-morphism: the
  base map is the inclusion `ℝⁿ ⊆ ℂⁿ` (`realInclusion`), and a holomorphic function `F` on an
  open `V ⊆ ℂⁿ` is sent to `Re(F|ℝⁿ) + Im(F|ℝⁿ) · i` on `V ∩ ℝⁿ` (`realToComplexSheafHom`); the
  real and imaginary parts of a holomorphic function are real-analytic
  (`contMDiff_restrictScalars_opens`: restriction of scalars, `ContDiffAt.restrict_scalars`),
  and the stalk maps are local because a germ is a unit iff its value is nonzero on both sides.
* `AnalyticSpace.IsGeometric`: the geometric spaces of [BM97, Remarks 1.7 (2)], those whose
  simple locus is Zariski-dense.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

/-! ### Local analytic `K`-spaces are analytic `K`-spaces -/

section LocalModelSpace

variable (K : Type) [RCLike K]

/-- A local analytic `K`-space `(S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})` is an analytic `K`-space (Hironaka's
clause (i) with the identity as the local isomorphism; Hausdorff and countable at infinity as a
closed subset of the open `G ⊆ Kⁿ`, `locallyCompactSpace_localModel`). -/
def localModelSpace (n : ℕ) (G : Opens (Kn.{u} K n)) {k : ℕ} (f : Fin k → AnalyticFun K n G) :
    AnalyticSpace.{u} K where
  toKLocallyRingedSpace := localModel K n G f
  locallyModel x := ⟨⊤, Opens.mem_top x, n, k, G, f, ⊤, ⟨Iso.refl _⟩⟩
  t2 := by
    have : T2Space (analyticSpaceOfOpen K n G).toLocallyRingedSpace.toTopCat :=
      inferInstanceAs (T2Space G)
    exact inferInstanceAs (T2Space (modelIdeal K n G f).support)
  sigmaCompact :=
    @sigmaCompactSpace_of_locallyCompact_secondCountable _ _
      (locallyCompactSpace_localModel K n G f) (secondCountableTopology_localModel K n G f)

theorem localModelSpace_toKLocallyRingedSpace (n : ℕ) (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) :
    (localModelSpace K n G f).toKLocallyRingedSpace = localModel K n G f := rfl

end LocalModelSpace

/-! ### Restrictions of morphisms to opens; local coordinations as a predicate -/

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The restriction `g|U : A|U ⟶ B|U'` of a `K`-morphism to opens with `g(U) ⊆ U'`: the lift of
`A|U ⟶ A ⟶ B` through the open immersion `B|U' ⟶ B`. -/
def Hom.restrictTo {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) (U : Opens A) (U' : Opens B)
    (h : ∀ a ∈ U, Hom.toFun g a ∈ U') : A.restrictOpen U ⟶ B.restrictOpen U' :=
  have h₁ : LocallyRingedSpace.IsOpenImmersion (ofRestrict B U').1 := inferInstance
  have hr : Set.range (ofRestrict A U ≫ g).1.base ⊆ Set.range (ofRestrict B U').1.base := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨Hom.toFun g a.1, h a.1 a.2⟩, rfl⟩
  Hom.ofFac (ofRestrict A U ≫ g) (ofRestrict B U')
    (LocallyRingedSpace.IsOpenImmersion.lift (H := h₁) (ofRestrict B U').1
      (ofRestrict A U ≫ g).1 hr)
    (LocallyRingedSpace.IsOpenImmersion.lift_fac (H := h₁) _ _ _)

@[reassoc (attr := simp)]
theorem Hom.restrictTo_comp_ofRestrict {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) (U : Opens A)
    (U' : Opens B) (h : ∀ a ∈ U, Hom.toFun g a ∈ U') :
    Hom.restrictTo g U U' h ≫ ofRestrict B U' = ofRestrict A U ≫ g :=
  Hom.ext (by
    rw [Hom.comp_val, Hom.restrictTo, Hom.ofFac_val]
    exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _)

theorem Hom.toFun_restrictTo {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) (U : Opens A)
    (U' : Opens B) (h : ∀ a ∈ U, Hom.toFun g a ∈ U') (a : A.restrictOpen U) :
    (Hom.toFun (Hom.restrictTo g U U' h) a).1 = Hom.toFun g a.1 := by
  have := congrArg (fun φ => Hom.toFun φ a) (Hom.restrictTo_comp_ofRestrict g U U' h)
  exact this

/-- The inclusion `A|U ⟶ A|U'` of open subspaces, `U ≤ U'`. -/
def restrictOpenIncl (A : KLocallyRingedSpace.{u} K) {U U' : Opens A} (h : U ≤ U') :
    A.restrictOpen U ⟶ A.restrictOpen U' :=
  Hom.restrictTo (𝟙 A) U U' fun _ ha => h ha

/-- "`(U, h)` is a local `Kⁿ`-coordination of `X`" [Hir64, Ch. 0, §1, p. 120]:
`h : X|U ⟶ (Kⁿ, 𝒜_{Kⁿ})` induces a `K`-isomorphism of `X|U` onto (an open of) a local analytic
`K`-space in `(Kⁿ, 𝒜_{Kⁿ})` — the content of `LocalCoordination`, as a predicate on the pair. -/
def IsLocalCoordination (X : KLocallyRingedSpace.{u} K) (U : Opens X) {n : ℕ}
    (h : X.restrictOpen U ⟶ affine K n) : Prop :=
  ∃ (k : ℕ) (G : Opens (Kn.{u} K n)) (g : Fin k → AnalyticFun K n G)
    (W : Opens (localModel K n G g))
    (iso : KIso (X.restrictOpen U) ((localModel K n G g).restrictOpen W)),
    h = iso.hom ≫ ofRestrict _ W ≫ localModel.ι K n G g

end KLocallyRingedSpace

theorem LocalCoordination.isLocalCoordination {K : Type} [RCLike K]
    {X : AnalyticSpace.{u} K} {x : X} (c : X.LocalCoordination x) :
    KLocallyRingedSpace.IsLocalCoordination X.toKLocallyRingedSpace c.U c.h :=
  ⟨c.k, c.G, c.f, c.W, c.iso, c.h_eq⟩

/-! ### Complexifications -/

/-- An (analytic) complexification of an analytic `ℝ`-space `X` [Hir64, Ch. 0, §1, p. 120]: an
analytic `ℂ`-space `Y` and a `ℂ`-morphism `f : X(ℂ) ⟶ Y` such that (1) `f(X)` is closed in `|Y|`
and (2) `f` induces a `ℂ`-isomorphism of `X(ℂ)` onto `Y|f(X)` — read stalkwise: `f` is a
homeomorphism onto its image and every stalk map `𝒪_{Y,f(x)} → 𝒪_{X(ℂ),x}` is bijective. -/
structure Complexification (X : AnalyticSpace.{u} ℝ) where
  /-- The complex space `Y`. -/
  Y : AnalyticSpace.{u} ℂ
  /-- The `ℂ`-morphism `f : X(ℂ) ⟶ Y`. -/
  f : KLocallyRingedSpace.complexify X.toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace
  /-- Hironaka's (1): `f(X)` is closed in `|Y|`. -/
  isClosed_range : IsClosed (Set.range (KLocallyRingedSpace.Hom.toFun f))
  /-- Hironaka's (2), topological part: `f` is a homeomorphism onto `f(X)`. -/
  isEmbedding : Topology.IsEmbedding (KLocallyRingedSpace.Hom.toFun f)
  /-- Hironaka's (2), sheaf part: the stalk maps `𝒪_{Y,f(x)} → 𝒪_{X(ℂ),x}` are bijective. -/
  bijective_stalkMap : ∀ x, Function.Bijective (f.1.stalkMap x).hom

namespace Complexification

variable {X : AnalyticSpace.{u} ℝ} (C : Complexification X)

/-- (1) and (2) together: `f` is a closed embedding of the underlying spaces. -/
theorem isClosedEmbedding : Topology.IsClosedEmbedding (KLocallyRingedSpace.Hom.toFun C.f) :=
  ⟨C.isEmbedding, C.isClosed_range⟩

theorem injective_toFun : Function.Injective (KLocallyRingedSpace.Hom.toFun C.f) :=
  C.isEmbedding.injective

end Complexification

/-! ### Hironaka's `α_n : (ℝⁿ, 𝒜_{ℝⁿ} ⊗_ℝ ℂ) ⟶ (ℂⁿ, 𝒜_{ℂⁿ})` -/

namespace KLocallyRingedSpace

section RealToComplex

variable (n : ℕ)

/-- The inclusion `ℝⁿ ⊆ ℂⁿ` [Hir64, Ch. 0, §1, p. 120], as a continuous `ℝ`-linear map of the
universe-lifted spaces. -/
def realInclusion : Kn.{u} ℝ n →L[ℝ] Kn.{u} ℂ n :=
  ((ContinuousLinearEquiv.ulift.symm : (Fin n → ℂ) ≃L[ℝ] Kn.{u} ℂ n) :
      (Fin n → ℂ) →L[ℝ] Kn.{u} ℂ n) ∘L
    (ContinuousLinearMap.pi fun i : Fin n => Complex.ofRealCLM ∘L ContinuousLinearMap.proj i) ∘L
      ((ContinuousLinearEquiv.ulift : Kn.{u} ℝ n ≃L[ℝ] (Fin n → ℝ)) : Kn.{u} ℝ n →L[ℝ] (Fin n → ℝ))

theorem realInclusion_apply (p : Kn.{u} ℝ n) :
    realInclusion n p = ⟨fun i => (p.down i : ℂ)⟩ := rfl

theorem realInclusion_injective : Function.Injective (realInclusion n) := by
  intro p q h
  exact ULift.ext (funext fun i =>
    Complex.ofReal_injective (congrFun (congrArg ULift.down h) i))

/-- The inclusion `ℝⁿ ⊆ ℂⁿ` as a map of the underlying spaces of `(ℝⁿ, 𝒜_{ℝⁿ} ⊗_ℝ ℂ)` and
`(ℂⁿ, 𝒜_{ℂⁿ})`. -/
def realInclusionTop :
    (complexify (affine.{u} ℝ n)).toLocallyRingedSpace.carrier ⟶
      (affine.{u} ℂ n).toLocallyRingedSpace.carrier :=
  TopCat.ofHom ⟨realInclusion n, (realInclusion n).continuous⟩

/-- The `ω`-version of Mathlib's `ContMDiff.subtypeVal_comp_iff` (stated at `∞` at the pin): a map
into an open subset is `C^n` iff it is `C^n` into the ambient manifold. -/
theorem contMDiff_subtypeVal_comp_iff_opens {E E' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] {N : Type*} [TopologicalSpace N] [ChartedSpace E' N] {m : WithTop ℕ∞}
    {U : Opens N} (g : M → U) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') m (Subtype.val ∘ g) ↔ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') m g :=
  forall_congr' fun x => ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff g Set.univ x

/-- A holomorphic function on an open `V ⊆ ℂⁿ` is real-analytic on `V` viewed as an open of the
real vector space `ℂⁿ` (restriction of scalars). -/
theorem contMDiff_restrictScalars_opens {V : Opens (Kn.{u} ℂ n)} {F : V → ℂ}
    (hF : ContMDiff 𝓘(ℂ, Kn.{u} ℂ n) 𝓘(ℂ) ω F) : ContMDiff 𝓘(ℝ, Kn.{u} ℂ n) 𝓘(ℝ, ℂ) ω F := by
  have hF' : F = fun x : V => Function.extend Subtype.val F (0 : Kn.{u} ℂ n → ℂ) x :=
    funext fun x => (Subtype.val_injective.extend_apply F 0 x).symm
  rw [hF'] at hF ⊢
  intro x
  have h1 := contMDiffAt_subtype_iff.mp (hF x)
  have h2 : ContDiffAt ℂ ω (Function.extend Subtype.val F (0 : Kn.{u} ℂ n → ℂ)) x :=
    contMDiffAt_iff_contDiffAt.mp h1
  exact contMDiffAt_subtype_iff.mpr (contMDiffAt_iff_contDiffAt.mpr (h2.restrict_scalars ℝ))

/-- The trace `V ∩ ℝⁿ ⊆ ℝⁿ` of an open `V ⊆ ℂⁿ`, as an open of `ℝⁿ`. -/
def realPreimage (V : Opens (Kn.{u} ℂ n)) : Opens (Kn.{u} ℝ n) :=
  ⟨realInclusion n ⁻¹' V, V.isOpen.preimage (realInclusion n).continuous⟩

theorem mem_realPreimage {V : Opens (Kn.{u} ℂ n)} {p : Kn.{u} ℝ n} :
    p ∈ realPreimage n V ↔ realInclusion n p ∈ V := Iff.rfl

/-- The inclusion `ℝⁿ ⊆ ℂⁿ` restricted to the trace `V ∩ ℝⁿ` of an open `V ⊆ ℂⁿ`. -/
def realInclusionRestrict (V : Opens (Kn.{u} ℂ n)) : realPreimage n V → V :=
  fun p => ⟨realInclusion n p.1, p.2⟩

/-- The restriction of the inclusion to the trace of an open `V ⊆ ℂⁿ` is real-analytic. -/
theorem contMDiff_realInclusionRestrict (V : Opens (Kn.{u} ℂ n)) :
    ContMDiff 𝓘(ℝ, Kn.{u} ℝ n) 𝓘(ℝ, Kn.{u} ℂ n) ω (realInclusionRestrict n V) :=
  (contMDiff_subtypeVal_comp_iff_opens (realInclusionRestrict n V)).mp
    (by exact (realInclusion n).contMDiff.comp contMDiff_subtype_val)

/-- The real part of a holomorphic function on `V ⊆ ℂⁿ`, restricted to `V ∩ ℝⁿ`, is
real-analytic. -/
theorem contMDiff_re_restrict {V : Opens (Kn.{u} ℂ n)}
    (F : (affine.{u} ℂ n).toLocallyRingedSpace.presheaf.obj (op V)) :
    ContMDiff 𝓘(ℝ, Kn.{u} ℝ n) 𝓘(ℝ) ω
      (fun p : realPreimage n V => (F.1 (realInclusionRestrict n V p)).re) :=
  Complex.reCLM.contMDiff.comp
    ((contMDiff_restrictScalars_opens n F.2).comp (contMDiff_realInclusionRestrict n V))

/-- The imaginary part, likewise. -/
theorem contMDiff_im_restrict {V : Opens (Kn.{u} ℂ n)}
    (F : (affine.{u} ℂ n).toLocallyRingedSpace.presheaf.obj (op V)) :
    ContMDiff 𝓘(ℝ, Kn.{u} ℝ n) 𝓘(ℝ) ω
      (fun p : realPreimage n V => (F.1 (realInclusionRestrict n V p)).im) :=
  Complex.imCLM.contMDiff.comp
    ((contMDiff_restrictScalars_opens n F.2).comp (contMDiff_realInclusionRestrict n V))

/-- The sheaf map of `α_n`: a holomorphic function `F` on `V ⊆ ℂⁿ` goes to
`Re(F|ℝⁿ) + Im(F|ℝⁿ) · i` on `V ∩ ℝⁿ`. -/
def realToComplexSheafHom :
    (affine.{u} ℂ n).toLocallyRingedSpace.presheaf ⟶
      realInclusionTop n _* (complexify (affine.{u} ℝ n)).toLocallyRingedSpace.presheaf where
  app V := CommRingCat.ofHom
    { toFun := fun F =>
        (⟨⟨fun p => (F.1 (realInclusionRestrict n (unop V) p)).re, contMDiff_re_restrict n F⟩,
          ⟨fun p => (F.1 (realInclusionRestrict n (unop V) p)).im, contMDiff_im_restrict n F⟩⟩ :
          Complexified ((affine.{u} ℝ n).toLocallyRingedSpace.presheaf.obj
            (op ((Opens.map (realInclusionTop n)).obj (unop V)))))
      map_one' := rfl
      map_mul' := fun _ _ => by
        refine Complexified.ext (ContMDiffMap.ext fun p => ?_) (ContMDiffMap.ext fun p => ?_)
        · exact Complex.mul_re _ _
        · exact Complex.mul_im _ _
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality _ _ _ := rfl

/-- (Implementation.) `α_n` as a morphism of presheafed spaces. -/
def realToComplexAux :
    (complexify (affine.{u} ℝ n)).toPresheafedSpace ⟶ (affine.{u} ℂ n).toPresheafedSpace where
  base := realInclusionTop n
  c := realToComplexSheafHom n

theorem realToComplexAux_c_app_re {V : Opens (Kn.{u} ℂ n)}
    (F : (affine.{u} ℂ n).toLocallyRingedSpace.presheaf.obj (op V))
    (p : realPreimage n V) :
    (((realToComplexAux n).c.app (op V)) F).re.1 p = (F.1 (realInclusionRestrict n V p)).re := rfl

theorem realToComplexAux_c_app_im {V : Opens (Kn.{u} ℂ n)}
    (F : (affine.{u} ℂ n).toLocallyRingedSpace.presheaf.obj (op V))
    (p : realPreimage n V) :
    (((realToComplexAux n).c.app (op V)) F).im.1 p = (F.1 (realInclusionRestrict n V p)).im := rfl

/-- The stalk maps of `α_n` are local: a germ is a unit iff its value is nonzero, on both sides
(`contMDiffSheafCommRing.isUnit_stalk_iff`, `Complexified.isUnit_iff_isUnit_norm`), and
`|F(p)|² = Re(F(p))² + Im(F(p))²`. -/
theorem isLocalHom_stalkMap_realToComplexAux (p : Kn.{u} ℝ n) :
    IsLocalHom ((realToComplexAux n).stalkMap p).hom := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨V, hV, F, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (affine.{u} ℂ n).toLocallyRingedSpace.presheaf a
  have e := PresheafedSpace.stalkMap_germ_apply (realToComplexAux n) V p hV F
  rw [e] at ha
  have ha' := ha.map (stalkComplexifyEquiv (affine.{u} ℝ n).toLocallyRingedSpace.presheaf p)
  erw [stalkComplexifyEquiv_germ] at ha'
  rw [Complexified.isUnit_iff_isUnit_norm] at ha'
  have hn : Complexified.norm (Complexified.map
      ((affine.{u} ℝ n).toLocallyRingedSpace.presheaf.germ _ p hV).hom
        ((realToComplexAux n).c.app (op V) F)) =
      (affine.{u} ℝ n).toLocallyRingedSpace.presheaf.germ _ p hV
        (((realToComplexAux n).c.app (op V) F).re * ((realToComplexAux n).c.app (op V) F).re +
          ((realToComplexAux n).c.app (op V) F).im * ((realToComplexAux n).c.app (op V) F).im) := by
    rw [map_add, map_mul, map_mul]
    rfl
  rw [hn] at ha'
  change IsUnit ((contMDiffSheafCommRing 𝓘(ℝ, Kn.{u} ℝ n) 𝓘(ℝ) ω (Kn.{u} ℝ n) ℝ).presheaf.germ
    _ p hV _) at ha'
  rw [contMDiffSheafCommRing.isUnit_stalk_iff] at ha'
  erw [contMDiffSheafCommRing.eval_germ] at ha'
  change IsUnit ((contMDiffSheafCommRing 𝓘(ℂ, Kn.{u} ℂ n) 𝓘(ℂ) ω (Kn.{u} ℂ n) ℂ).presheaf.germ
    V _ hV F)
  rw [contMDiffSheafCommRing.isUnit_stalk_iff]
  erw [contMDiffSheafCommRing.eval_germ]
  intro h0
  apply ha'
  have h0' : F.1 (realInclusionRestrict n V ⟨p, hV⟩) = 0 := h0
  change (F.1 (realInclusionRestrict n V ⟨p, hV⟩)).re *
      (F.1 (realInclusionRestrict n V ⟨p, hV⟩)).re +
    (F.1 (realInclusionRestrict n V ⟨p, hV⟩)).im * (F.1 (realInclusionRestrict n V ⟨p, hV⟩)).im = 0
  rw [h0']
  simp

/-- The natural `ℂ`-morphism `α_n : (ℝⁿ, 𝒜_{ℝⁿ} ⊗_ℝ ℂ) ⟶ (ℂⁿ, 𝒜_{ℂⁿ})` [Hir64, Ch. 0, §1, p. 120],
the inclusion `ℝⁿ ⊆ ℂⁿ` with `F ↦ Re(F|ℝⁿ) + Im(F|ℝⁿ) · i` on sections. -/
def realToComplex : complexify (affine.{u} ℝ n) ⟶ affine.{u} ℂ n :=
  ⟨⟨realToComplexAux n, isLocalHom_stalkMap_realToComplexAux n⟩, rfl⟩

theorem toFun_realToComplex (p : Kn.{u} ℝ n) : Hom.toFun (realToComplex n) p = realInclusion n p :=
  rfl

end RealToComplex

end KLocallyRingedSpace

/-! ### Geometric spaces -/

/-- Bierstone and Milman's **geometric** analytic spaces [BM97, Remarks 1.7 (2)]: `X` is geometric
when its simple locus `X.regularLocus` is Zariski-dense in `|X|` — no closed analytic subspace other
than `X` itself contains all the simple points: every closed subspace `W` with
`X.regularLocus ⊆ |W|` has `|W| = |X|`. -/
def IsGeometric {K : Type} [RCLike K] (X : AnalyticSpace.{u} K) : Prop :=
  ∀ W : ClosedSubspace X, regularLocus X ⊆ _root_.Manifold.IdealSheaf.support W →
    _root_.Manifold.IdealSheaf.support W = Set.univ

end AnalyticSpace
