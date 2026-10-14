/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Modules.Defs
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Sections of a quasi-coherent sheaf over affine opens

For a quasi-coherent sheaf of modules `F` on a scheme `X` (Mathlib's `X.Modules` with
`IsQuasicoherent`):

* over a basic open `D(r)` of an affine open `V`, the restriction `Γ(F, V) → Γ(F, D(r))` is the
  localization at the powers of `r` [Sta, Tags 01I9 and 01IA]
  (`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_resₗ_basicOpen`). This is Mathlib's
  `isIso_fromTildeΓ_of_isQuasicoherent` (a quasi-coherent sheaf on `Spec R` is `M^~`) for the
  restriction of `F` along `Spec Γ(X, V) ≅ V`, read on `X`: the sections of the restriction are
  the sections of `F` (`Scheme.Modules.restrict_obj`), and the `Γ(X, V)`-action on them is the
  restriction of functions (`fromSpec_appIso_inv`);
* for affine opens `U ≤ V`, `Γ(F, U)` is the base change `Γ(X, U) ⊗_{Γ(X, V)} Γ(F, V)`
  [Sta, Tags 01I9 and 01IA] (`isBaseChange_resₗ`): both sides localize to `Γ(F, D(r))` at the
  basic opens `D(r) ⊆ U` of `V`, which cover `U`. Consequently the image of `Γ(F, V)` spans
  `Γ(F, U)` (`span_range_restrictionMap_eq_top`), and every semilinear map out of `Γ(F, V)` extends
  to a `Γ(X, U)`-linear map out of `Γ(F, U)` (`exists_extend_restrictionMap`): the hypotheses of the
  base change of the projective bundle of a module (`affineProjectiveBundle.isPullback_map`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The ring identity behind the restriction to an affine open: the `Γ(X, V)`-action on the
sections of `F.restrict hV.fromSpec` over `W` is the restriction. -/
theorem fromSpec_appIso_inv {V : X.Opens} (hV : IsAffineOpen V) (W : (Spec Γ(X, V)).Opens)
    (h : hV.fromSpec ''ᵁ W ≤ V) (r : Γ(X, V)) :
    (hV.fromSpec.appIso W).inv ((Spec Γ(X, V)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso Γ(X, V)).inv r)) = X.presheaf.map (homOfLE h).op r := by
  apply (ConcreteCategory.bijective_of_isIso (hV.fromSpec.appIso W).hom).1
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
    Scheme.Hom.appIso_hom, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Scheme.Hom.naturality_assoc, hV.fromSpec_app_self, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 3


/-- The restriction `Γ(F, V) → Γ(F, U)` as a `Γ(X, V)`-linear map, `Γ(F, U)` a `Γ(X, V)`-module
through the restriction of functions. -/
noncomputable def resₗ {U V : X.Opens} (h : U ≤ V) :
    letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
    Γ(F, V) →ₗ[Γ(X, V)] Γ(F, U) :=
  letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r x => F.val.map_smul (homOfLE h).op r x }

theorem resₗ_apply {U V : X.Opens} (h : U ≤ V) (x : Γ(F, V)) :
    F.resₗ h x = F.presheaf.map (homOfLE h).op x := rfl

omit F in
theorem fromSpec_image_top {V : X.Opens} (hV : IsAffineOpen V) : hV.fromSpec ''ᵁ ⊤ = V :=
  (Scheme.Hom.image_top_eq_opensRange _).trans hV.opensRange_fromSpec

/-- The sections of `F` over an affine open `V` are the global sections of the restriction of `F`
to `Spec Γ(X, V) ≅ V`, as `Γ(X, V)`-modules. -/
noncomputable def topSectionsEquiv {V : X.Opens} (hV : IsAffineOpen V) :
    Γ(F, V) ≃ₗ[Γ(X, V)] Γ(F.restrict hV.fromSpec, ⊤) :=
  LinearEquiv.ofBijective (M₂ := Γ(F.restrict hV.fromSpec, ⊤))
    { toFun := F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op
      map_add' := map_add _
      map_smul' := fun c x => by
        change F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op (c • x) =
          (hV.fromSpec.appIso ⊤).inv ((Spec Γ(X, V)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, V)).inv c)) •
              F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op x
        rw [fromSpec_appIso_inv hV ⊤ (fromSpec_image_top hV).le]
        exact F.val.map_smul (homOfLE (fromSpec_image_top hV).le).op c x }
    (by
      have : IsIso (homOfLE (fromSpec_image_top hV).le).op := by
        rw [show (homOfLE (fromSpec_image_top hV).le).op = (eqToHom (fromSpec_image_top hV)).op
          from rfl]
        infer_instance
      exact ConcreteCategory.bijective_of_isIso
        (F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op))

theorem topSectionsEquiv_apply {V : X.Opens} (hV : IsAffineOpen V) (x : Γ(F, V)) :
    F.topSectionsEquiv hV x = F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op x :=
  rfl

set_option linter.style.haveILetI false in
/-- The restriction to a basic open `D(r)` of an affine open `V` is a localization on `X` if and
only if it is one for the restriction of `F` to `Spec Γ(X, V) ≅ V`, the condition of Mathlib's
`isIso_fromTildeΓ_iff_isLocalizing`: the two restriction maps are identified by the restrictions
of `F` along `Spec Γ(X, V) ≅ V`, and the actions of `Γ(X, V)` by `fromSpec_appIso_inv`. -/
theorem isLocalizedModule_restrict_fromSpec_iff {V : X.Opens} (hV : IsAffineOpen V)
    (r : Γ(X, V)) :
    letI := Module.compHom Γ(F, X.basicOpen r)
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    IsLocalizedModule (Submonoid.powers r)
      ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map
        (PrimeSpectrum.basicOpen r : (Spec Γ(X, V)).Opens).leTop.op).hom ↔
      IsLocalizedModule (Submonoid.powers r) (F.resₗ (X.basicOpen_le r)) := by
  letI := Module.compHom Γ(F, X.basicOpen r)
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  set W : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen r with hW
  have h2 : hV.fromSpec ''ᵁ W = X.basicOpen r := hV.fromSpec_image_basicOpen r
  let e1 := (F.topSectionsEquiv hV).toLinearMap
  let e2 : Γ(F, X.basicOpen r) →ₗ[Γ(X, V)] Γ(F.restrict hV.fromSpec, W) :=
    { toFun := F.presheaf.map (homOfLE h2.le).op
      map_add' := map_add _
      map_smul' := fun c x => by
        change F.presheaf.map (homOfLE h2.le).op
            (X.presheaf.map (homOfLE (X.basicOpen_le r)).op c • x) =
          (hV.fromSpec.appIso W).inv ((Spec Γ(X, V)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, V)).inv c)) • F.presheaf.map (homOfLE h2.le).op x
        rw [fromSpec_appIso_inv hV _ (h2.le.trans (X.basicOpen_le r)),
          show X.presheaf.map (homOfLE (h2.le.trans (X.basicOpen_le r))).op c =
            X.presheaf.map (homOfLE h2.le).op
              (X.presheaf.map (homOfLE (X.basicOpen_le r)).op c) by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl]
        exact F.val.map_smul (homOfLE h2.le).op _ x }
  have he1 : Function.Bijective e1 := (F.topSectionsEquiv hV).bijective
  have he2 : Function.Bijective e2 := by
    have : IsIso (homOfLE h2.le).op := by
      rw [show (homOfLE h2.le).op = (eqToHom h2).op from rfl]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso (F.presheaf.map (homOfLE h2.le).op)
  have hcomm : e2 ∘ₗ F.resₗ (X.basicOpen_le r) =
      ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map W.leTop.op).hom ∘ₗ e1 := by
    ext x
    change F.presheaf.map (homOfLE h2.le).op (F.presheaf.map (homOfLE (X.basicOpen_le r)).op x) =
      F.presheaf.map _ (F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op x)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : IsLocalizedModule (Submonoid.powers r) (e2 ∘ₗ F.resₗ (X.basicOpen_le r)) := by
      rw [hcomm]
      exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r) e1 he1).mpr h
    exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r) e2 he2).mp h'
  · have h' : IsLocalizedModule (Submonoid.powers r)
        (((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map W.leTop.op).hom ∘ₗ e1) := by
      rw [← hcomm]
      exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r) e2 he2).mpr h
    exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r) e1 he1).mp h'

set_option linter.style.haveILetI false in
/-- **Sections of a quasi-coherent module over a basic open are a localization**: for an affine
open `V` and `r ∈ Γ(X, V)`, the restriction `Γ(F, V) → Γ(F, D(r))` is the localization at the
powers of `r` [Sta, Tags 01I9 and 01IA]. This is Mathlib's `isIso_fromTildeΓ_of_isQuasicoherent`
for the restriction of `F` to `Spec Γ(X, V) ≅ V`, read on `X`. -/
theorem isLocalizedModule_resₗ_basicOpen [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (r : Γ(X, V)) :
    letI := Module.compHom Γ(F, X.basicOpen r)
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    IsLocalizedModule (Submonoid.powers r) (F.resₗ (X.basicOpen_le r)) :=
  (F.isLocalizedModule_restrict_fromSpec_iff hV r).mp
    ((isIso_fromTildeΓ_iff_isLocalizing (F.restrict hV.fromSpec)).mp inferInstance r)

set_option linter.style.haveILetI false in
/-- `isLocalizedModule_resₗ_basicOpen` for an open given as equal to the basic open. -/
theorem isLocalizedModule_resₗ_of_eq_basicOpen [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (r : Γ(X, V)) {D : X.Opens} (hD : D = X.basicOpen r) (hle : D ≤ V) :
    letI := Module.compHom Γ(F, D) (X.presheaf.map (homOfLE hle).op).hom
    IsLocalizedModule (Submonoid.powers r) (F.resₗ hle) := by
  subst hD
  exact F.isLocalizedModule_resₗ_basicOpen hV r

set_option linter.style.haveILetI false in
omit F in
/-- `IsAffineOpen.isLocalization_basicOpen` for an open given as equal to the basic open. -/
theorem isLocalization_of_eq_basicOpen {V : X.Opens} (hV : IsAffineOpen V) (r : Γ(X, V))
    {D : X.Opens} (hD : D = X.basicOpen r) (hle : D ≤ V) :
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    IsLocalization.Away r Γ(X, D) := by
  subst hD
  exact hV.isLocalization_basicOpen r

set_option linter.style.haveILetI false in
/-- **The sections of a quasi-coherent module over nested affine opens** `U ≤ V`: `Γ(F, U)` is the
base change `Γ(X, U) ⊗_{Γ(X, V)} Γ(F, V)` [Sta, Tags 01I9 and 01IA]. Both sides are localizations of
`Γ(F, V)` at the basic opens `D(r) ⊆ U` of `V` (`isLocalizedModule_resₗ_basicOpen`, applied to `V`
and to `U`, where `D(r)` is the basic open of the restriction of `r`), and these cover `U`; a map of
modules that is bijective after localizing at a family generating the unit ideal is bijective
(Mathlib's `bijective_of_isLocalized_span`). -/
theorem isBaseChange_resₗ [F.IsQuasicoherent] {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : U ≤ V) :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
    letI : IsScalarTower Γ(X, V) Γ(X, U) Γ(F, U) := IsScalarTower.of_compHom _ _ _
    IsBaseChange Γ(X, U) (F.resₗ h) := by
  letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
  letI : IsScalarTower Γ(X, V) Γ(X, U) Γ(F, U) := IsScalarTower.of_compHom _ _ _
  -- The basic opens of `V` inside `U`, as basic opens of `U`.
  let s : Set Γ(X, U) :=
    {t | ∃ r : Γ(X, V), X.basicOpen r ≤ U ∧ X.presheaf.map (homOfLE h).op r = t}
  have hres (r : Γ(X, V)) (hr : X.basicOpen r ≤ U) :
      X.basicOpen (X.presheaf.map (homOfLE h).op r) = X.basicOpen r := by
    rw [Scheme.basicOpen_res, inf_eq_right.mpr hr]
  choose r hr hrt using fun t : s => t.2
  have hD (t : s) : X.basicOpen (t : Γ(X, U)) = X.basicOpen (r t) := by
    rw [← hrt t, hres _ (hr t)]
  have hspan : Ideal.span s = ⊤ := by
    refine (hU.iSup_basicOpen_eq_self_iff).mp (le_antisymm (iSup_le fun t => X.basicOpen_le _)
      fun x hxU => ?_)
    obtain ⟨r₀, hr₀U, hxr₀⟩ := hV.exists_basicOpen_le ⟨x, hxU⟩ (h hxU)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, r₀, hr₀U, rfl⟩, ?_⟩
    change x ∈ X.basicOpen (X.presheaf.map (homOfLE h).op r₀)
    rw [hres r₀ hr₀U]
    exact hxr₀
  -- The localizations: the sections over the basic opens.
  let P : s → Type u := fun t => Γ(F, X.basicOpen (t : Γ(X, U)))
  letI (t : s) : Module Γ(X, U) (P t) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le (t : Γ(X, U)))).op).hom
  let g (t : s) : Γ(F, U) →ₗ[Γ(X, U)] P t := F.resₗ (X.basicOpen_le (t : Γ(X, U)))
  have hg (t : s) : IsLocalizedModule.Away (t : Γ(X, U)) (g t) :=
    F.isLocalizedModule_resₗ_basicOpen hU t
  let Φ : Γ(X, U) ⊗[Γ(X, V)] Γ(F, V) →ₗ[Γ(X, U)] Γ(F, U) := (F.resₗ h).liftBaseChange Γ(X, U)
  have hf (t : s) : IsLocalizedModule.Away (t : Γ(X, U)) (g t ∘ₗ Φ) := by
    have hDV : X.basicOpen (t : Γ(X, U)) ≤ V := (X.basicOpen_le _).trans h
    -- `Γ(X, D)` as an algebra over `Γ(X, V)` and over `Γ(X, U)`.
    letI : Algebra Γ(X, V) Γ(X, X.basicOpen (t : Γ(X, U))) :=
      (X.presheaf.map (homOfLE hDV).op).hom.toAlgebra
    have hcomp (a : Γ(X, V)) : X.presheaf.map (homOfLE hDV).op a =
        X.presheaf.map (homOfLE (X.basicOpen_le (t : Γ(X, U)))).op
          (X.presheaf.map (homOfLE h).op a) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    haveI : IsScalarTower Γ(X, V) Γ(X, U) Γ(X, X.basicOpen (t : Γ(X, U))) :=
      IsScalarTower.of_algebraMap_eq hcomp
    letI : Module Γ(X, V) (P t) := Module.compHom _ (X.presheaf.map (homOfLE hDV).op).hom
    haveI : IsScalarTower Γ(X, V) Γ(X, U) (P t) :=
      ⟨fun a b x => by
        change X.presheaf.map (homOfLE (X.basicOpen_le (t : Γ(X, U)))).op
            (X.presheaf.map (homOfLE h).op a * b) • x =
          X.presheaf.map (homOfLE hDV).op a •
            (X.presheaf.map (homOfLE (X.basicOpen_le (t : Γ(X, U)))).op b • x)
        rw [map_mul, mul_smul, hcomp]⟩
    haveI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen (t : Γ(X, U))) (P t) :=
      IsScalarTower.of_compHom _ _ _
    haveI : IsScalarTower Γ(X, V) Γ(X, X.basicOpen (t : Γ(X, U))) (P t) :=
      IsScalarTower.of_compHom _ _ _
    haveI := hU.isLocalization_basicOpen (t : Γ(X, U))
    change IsLocalizedModule (Submonoid.powers (t : Γ(X, U))) (g t ∘ₗ Φ)
    rw [isLocalizedModule_iff_isBaseChange (Submonoid.powers (t : Γ(X, U)))
      Γ(X, X.basicOpen (t : Γ(X, U)))]
    refine IsBaseChange.of_comp (TensorProduct.isBaseChange Γ(X, V) Γ(F, V) Γ(X, U)) ?_
    have hV' := F.isLocalizedModule_resₗ_of_eq_basicOpen hV (r t) (hD t) hDV
    haveI := isLocalization_of_eq_basicOpen hV (r t) (hD t) hDV
    have hb := (isLocalizedModule_iff_isBaseChange (Submonoid.powers (r t))
      Γ(X, X.basicOpen (t : Γ(X, U))) (F.resₗ hDV)).mp hV'
    convert hb using 1
    ext x
    change F.presheaf.map (homOfLE (X.basicOpen_le (t : Γ(X, U)))).op
        ((1 : Γ(X, U)) • F.presheaf.map (homOfLE h).op x) = F.presheaf.map (homOfLE hDV).op x
    rw [one_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hbij : Function.Bijective Φ := by
    refine bijective_of_isLocalized_span s hspan P (fun t => g t ∘ₗ Φ) P g Φ fun t => ?_
    have : IsLocalizedModule.map (Submonoid.powers (t : Γ(X, U))) (g t ∘ₗ Φ) (g t) Φ =
        LinearMap.id :=
      IsLocalizedModule.linearMap_ext (Submonoid.powers (t : Γ(X, U))) (g t ∘ₗ Φ) (g t)
        (by rw [IsLocalizedModule.map_comp, LinearMap.id_comp])
    rw [this]
    exact Function.bijective_id
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ hbij) fun x => by
    simp [Φ, LinearMap.liftBaseChange_tmul]

set_option linter.style.haveILetI false in
/-- For affine opens `U ≤ V` of `X`, the restrictions of the sections of a quasi-coherent sheaf
over `V` span its sections over `U` (`isBaseChange_resₗ`). -/
theorem span_range_restrictionMap_eq_top [F.IsQuasicoherent] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    Submodule.span Γ(X, U) (Set.range (F.restrictionMap h)) = ⊤ := by
  letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
  letI : IsScalarTower Γ(X, V) Γ(X, U) Γ(F, U) := IsScalarTower.of_compHom _ _ _
  have hb := F.isBaseChange_resₗ hU hV h
  refine eq_top_iff.mpr fun n _ => hb.inductionOn n (fun x => ?_)
    (fun c n hn => Submodule.smul_mem _ c hn) (fun _ _ => add_mem)
  exact Submodule.subset_span ⟨x, rfl⟩

set_option linter.style.haveILetI false in
/-- For affine opens `U ≤ V` of `X`, every map out of the sections of a quasi-coherent sheaf over
`V`, semilinear along the restriction `Γ(X, V) → Γ(X, U)`, extends along the restriction to a
`Γ(X, U)`-linear map out of the sections over `U` (`isBaseChange_resₗ`). -/
theorem exists_extend_restrictionMap [F.IsQuasicoherent] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) (T : Type u) [AddCommGroup T]
    [Module Γ(X, U) T] (g : Γ(F, V) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] T) :
    ∃ g' : Γ(F, U) →ₗ[Γ(X, U)] T, ∀ x, g' (F.restrictionMap h x) = g x := by
  letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
  letI : IsScalarTower Γ(X, V) Γ(X, U) Γ(F, U) := IsScalarTower.of_compHom _ _ _
  letI := Module.compHom T (X.presheaf.map (homOfLE h).op).hom
  letI : IsScalarTower Γ(X, V) Γ(X, U) T := IsScalarTower.of_compHom _ _ _
  have hb := F.isBaseChange_resₗ hU hV h
  let gR : Γ(F, V) →ₗ[Γ(X, V)] T :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := g.map_smulₛₗ }
  exact ⟨hb.lift gR, fun x => hb.lift_eq gR x⟩

end AlgebraicGeometry.Scheme.Modules
