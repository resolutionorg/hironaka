/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.HomOfSectionsCompat
public import Hironaka.AnalyticSpace.Manifold.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# `K`-morphisms `(Kᵐ, 𝒜)|W ⟶ (Kⁿ, 𝒜)` from `n` analytic functions on `W`

The affine case of the existence of a morphism into `Kⁿ` with prescribed coordinate functions: `n`
analytic functions `a₁, …, aₙ` on an open `W ⊆ Kᵐ` define the `K`-morphism
`(W, 𝒜_W) ⟶ (Kⁿ, 𝒜_{Kⁿ})`, `w ↦ (a₁(w), …, aₙ(w))` — the morphism `ofManifoldHom` of the analytic
map `W → Kⁿ`, transported to the open subspace `(Kᵐ, 𝒜)|W` along `ofManifold_restrictOpen_iso`
(`Hironaka/AnalyticSpace/Manifold/Restrict.lean`). Its coordinate pullbacks are the `a_i`
(`pullbackΓ_homOfSectionsAffine_coordSection`): the germ of the pullback of `z_i` at `w` is computed
through the stalk maps of the two factors (`stalkMap_comp`), the transport being controlled by
`ofManifold_restrictOpen_iso_hom_comp` and the identification of the stalks of `(Kᵐ, 𝒜)|W` with
those of `𝒜` (`resIso`). Routine.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {m n : ℕ} (W : Opens (Kn.{u} K m))
  (a : Fin n → (affine.{u} K m).toLocallyRingedSpace.presheaf.obj (op W))

/-- The analytic map `W → Kⁿ` with components `a i`. -/
def affineMap : W → Kn.{u} K n := fun w => ⟨fun i => (a i).1 w⟩

theorem contMDiff_affineMap : ContMDiff 𝓘(K, Kn.{u} K m) 𝓘(K, Kn.{u} K n) ω (affineMap W a) := by
  have h1 : ContMDiff 𝓘(K, Kn.{u} K m) 𝓘(K, Fin n → K) ω (fun w : W => fun i => (a i).1 w) :=
    contMDiff_pi_module_iff.mpr fun i => (a i).2
  let e : (Fin n → K) →L[K] Kn.{u} K n :=
    (ContinuousLinearEquiv.ulift.symm : (Fin n → K) ≃L[K] Kn.{u} K n).toContinuousLinearMap
  exact e.contMDiff.comp h1

/-- The identification `(Kᵐ, 𝒜)|W ≅ Sp(W)` of the open subspace with the space of the manifold
`W`. -/
abbrev affineRestrictIso : (affine.{u} K m).restrictOpen W ≅ ofManifold K (Kn.{u} K m) W :=
  ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K m) (M := Kn.{u} K m) W

/-- The affine case: the `K`-morphism `(Kᵐ, 𝒜)|W ⟶ (Kⁿ, 𝒜)` with coordinate functions
`a₁, …, aₙ`. -/
def homOfSectionsAffine : (affine.{u} K m).restrictOpen W ⟶ affine.{u} K n :=
  (affineRestrictIso W).hom ≫
    ofManifoldHom (K := K) (E := Kn.{u} K m) (E' := Kn.{u} K n) (affineMap W a)
      (contMDiff_affineMap W a)

/-- The identification `(Kᵐ, 𝒜)|W ≅ Sp(W)` is the identity on points. -/
theorem affineRestrictIso_hom_base (w : (affine.{u} K m).restrictOpen W) :
    (affineRestrictIso W).hom.1.base w = w := by
  have h := congrArg (fun φ => Hom.toFun φ w)
    (ofManifold_restrictOpen_iso_hom_comp (K := K) (E := Kn.{u} K m) (M := Kn.{u} K m) W)
  exact Subtype.ext h

theorem toFun_homOfSectionsAffine (w : (affine.{u} K m).restrictOpen W) :
    Hom.toFun (homOfSectionsAffine W a) w = affineMap W a w := by
  change (ofManifoldHom (K := K) (affineMap W a) (contMDiff_affineMap W a)).1.base
    ((affineRestrictIso W).hom.1.base w) = _
  rw [affineRestrictIso_hom_base]
  rfl

/-- The analytic map `W → Kⁿ` as a `K`-morphism `Sp(W) ⟶ (Kⁿ, 𝒜)`. -/
abbrev affineMapHom : ofManifold K (Kn.{u} K m) W ⟶ affine.{u} K n :=
  ofManifoldHom (K := K) (E := Kn.{u} K m) (E' := Kn.{u} K n) (affineMap W a)
    (contMDiff_affineMap W a)

/-- The inclusion `W → Kᵐ` as a `K`-morphism `Sp(W) ⟶ (Kᵐ, 𝒜)`. -/
abbrev affineIncl : ofManifold K (Kn.{u} K m) W ⟶ affine.{u} K m :=
  ofManifoldHom (K := K) (E := Kn.{u} K m) (E' := Kn.{u} K m) (Subtype.val : W → Kn.{u} K m)
    contMDiff_subtype_val

theorem affineRestrictIso_hom_comp_affineIncl :
    (affineRestrictIso W).hom ≫ affineIncl W = ofRestrict (affine.{u} K m) W :=
  ofManifold_restrictOpen_iso_hom_comp (K := K) (E := Kn.{u} K m) (M := Kn.{u} K m) W

/-- The germ at `w` of the pullback of a coordinate function along `homOfSectionsAffine W a`,
seen in the stalk of `𝒜` at `w`, is the germ of `a i`. -/
theorem resIso_germ_pullbackΓ_homOfSectionsAffine_coord (w : (affine.{u} K m).restrictOpen W)
    (i : Fin n) :
    (resIso (affine.{u} K m) W w.2).hom
        (((affine.{u} K m).restrictOpen W).toLocallyRingedSpace.presheaf.germ ⊤ w trivial
          ((homOfSectionsAffine W a).pullbackΓ (coordSection K n i))) =
      (affine.{u} K m).toLocallyRingedSpace.presheaf.germ W w.1 w.2 (a i) := by
  set ρ := (affineRestrictIso W).hom with hρdef
  set ψ := affineMapHom W a with hψdef
  -- (A) the germ of the pullback is the stalk map on the coordinate germ
  have hA := AnalyticSpace.stalkMap_coordAt ((affine.{u} K m).restrictOpen W)
    (homOfSectionsAffine W a) w i
  rw [← hA]
  -- (B) the stalk map of the composite
  have hB : (homOfSectionsAffine W a).1.stalkMap w = ψ.1.stalkMap (ρ.1.base w) ≫ ρ.1.stalkMap w :=
    LocallyRingedSpace.stalkMap_comp ρ.1 ψ.1 w
  rw [hB]
  change (resIso (affine.{u} K m) W w.2).hom (ρ.1.stalkMap w (ψ.1.stalkMap (ρ.1.base w)
    (coordAt K n ((homOfSectionsAffine W a).1.base w) i))) = _
  -- (C) the `ofManifoldHom` factor on the coordinate germ: the germ of `a i ∘ (inclusion)` on `W`
  have hC := PresheafedSpace.stalkMap_germ_apply ψ.1.1 ⊤ (ρ.1.base w) (Opens.mem_top _)
    (coordSection K n i)
  change ψ.1.stalkMap (ρ.1.base w) ((affine.{u} K n).toLocallyRingedSpace.presheaf.germ ⊤
    (ψ.1.base (ρ.1.base w)) (Opens.mem_top _) (coordSection K n i)) =
    (ofManifold K (Kn.{u} K m) W).toLocallyRingedSpace.presheaf.germ _ (ρ.1.base w)
      (Opens.mem_top _) (ψ.1.c.app (op ⊤) (coordSection K n i)) at hC
  erw [hC]
  -- (D) rewrite that germ as the stalk map of the inclusion on the germ of `a i`
  have hD := PresheafedSpace.stalkMap_germ_apply (affineIncl W).1.1 W (ρ.1.base w)
    (ρ.1.base w).2 (a i)
  have hE : (ofManifold K (Kn.{u} K m) W).toLocallyRingedSpace.presheaf.germ _ (ρ.1.base w)
      (Opens.mem_top _) (ψ.1.c.app (op ⊤) (coordSection K n i)) =
      (ofManifold K (Kn.{u} K m) W).toLocallyRingedSpace.presheaf.germ _ (ρ.1.base w)
        (ρ.1.base w).2 ((affineIncl W).1.c.app (op W) (a i)) := by
    refine TopCat.Presheaf.germ_ext _ ⊤ (Opens.mem_top _)
      (homOfLE fun x _ => (Opens.mem_top (ψ.1.base x))) (homOfLE fun x _ => x.2) ?_
    rfl
  rw [hE]
  erw [← hD]
  -- (E) the composite `ρ ≫ incl` is the open immersion `(Kᵐ, 𝒜)|W ⟶ (Kᵐ, 𝒜)`
  have hF := congrArg (fun φ => φ.hom ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _
    (ρ.1.base w).2 (a i))) (LocallyRingedSpace.stalkMap_comp ρ.1 (affineIncl W).1 w)
  change (ρ.1 ≫ (affineIncl W).1).stalkMap w _ = ρ.1.stalkMap w ((affineIncl W).1.stalkMap
    (ρ.1.base w) ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ (ρ.1.base w).2 (a i)))
    at hF
  erw [← hF]
  have hEq : ρ.1 ≫ (affineIncl W).1 = (ofRestrict (affine.{u} K m) W).1 := by
    rw [← Hom.comp_val]
    exact congrArg Subtype.val (affineRestrictIso_hom_comp_affineIncl W)
  have hG := LocallyRingedSpace.stalkMap_congr_hom (ρ.1 ≫ (affineIncl W).1)
    (ofRestrict (affine.{u} K m) W).1 hEq w
  rw [hG]
  change (resIso (affine.{u} K m) W w.2).hom ((ofRestrict (affine.{u} K m) W).1.stalkMap w
    ((affine.{u} K m).toLocallyRingedSpace.presheaf.stalkSpecializes _
      ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ (ρ.1.base w).2 (a i)))) = _
  have hH := congrArg (fun φ => φ.hom (a i)) (TopCat.Presheaf.germ_stalkSpecializes
    (affine.{u} K m).toLocallyRingedSpace.presheaf (U := W) (ρ.1.base w).2
    (specializes_of_eq (congrArg (fun f => f.base w) hEq.symm)))
  change (affine.{u} K m).toLocallyRingedSpace.presheaf.stalkSpecializes _
    ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ (ρ.1.base w).2 (a i)) =
    (affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ _ (a i) at hH
  erw [hH]
  -- (F) the stalk map of the open immersion on the germ of `a i`, then back to `𝒜`
  have hI := PresheafedSpace.stalkMap_germ_apply (ofRestrict (affine.{u} K m) W).1.1 W w w.2 (a i)
  erw [hI]
  refine (resIso_hom_germ (affine.{u} K m) W w.2 _ w.2 _).trans ?_
  exact TopCat.Presheaf.germ_res_apply (affine.{u} K m).toLocallyRingedSpace.presheaf
    ((Opens.isOpenEmbedding W).isOpenMap.adjunction.counit.app W) w.1 _ (a i)

/-- The coordinate pullbacks of `homOfSectionsAffine W a` are the `a i` (restricted to the image
of `⊤`, which is `W`). -/
theorem pullbackΓ_homOfSectionsAffine_coordSection (i : Fin n) :
    (homOfSectionsAffine W a).pullbackΓ (coordSection K n i) =
      (affine.{u} K m).toLocallyRingedSpace.presheaf.map (homOfLE (imgOpens_top_le _ W)).op
        (a i) := by
  apply TopCat.Presheaf.section_ext ((affine.{u} K m).restrictOpen W).toLocallyRingedSpace.𝒪
  intro w hw
  apply (ConcreteCategory.bijective_of_isIso (resIso (affine.{u} K m) W w.2).hom).1
  refine (resIso_germ_pullbackΓ_homOfSectionsAffine_coord W a w i).trans ?_
  refine ((resIso_hom_germ (affine.{u} K m) W w.2 ⊤ hw _).trans ?_).symm
  exact TopCat.Presheaf.germ_res_apply (affine.{u} K m).toLocallyRingedSpace.presheaf
    (homOfLE (imgOpens_top_le _ W)) w.1 _ (a i)

end AnalyticSpace.KLocallyRingedSpace
