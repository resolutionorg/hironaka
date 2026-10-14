/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Defs
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The reduced closed subspace, as an ideal sheaf

Bierstone–Milman define the reduced space `X_red` corresponding to `X` using the coherent sheaf
of ideals `I_{X_red} = √I_X` [BM97, Remark 3.14]. For an ideal sheaf `J` of finite type on a sheaf
of rings, `radicalSubspace J` is the ideal sheaf whose stalks are the radicals `√J_x`, taken when
that stalk family has local generators (the coherence of the radical, Cartan's theorem on the
radical of a coherent ideal, provided by `hasLocalGenerators_radical_of_cartan`), the unit ideal
sheaf otherwise: the pattern of the weak transform and of `strictTransformSubspace`. It is the
reduction of a closed subspace at the level of ideal sheaves on a manifold, used to show that the
strict transform of a reduced subspace is reduced
(`Hironaka.Manifold.BlowUp.Transform.StrictSubspaceReduced`); for analytic spaces the
reduction is defined in `Hironaka/AnalyticSpace/`.

Boundary cases: for `J` with radical stalks (a reduced subspace), `radicalSubspace J` has the
same stalks as `J`, given the witness; for `J = ⊤`, the radical of `⊤` is `⊤`, and both branches
give `⊤`.
-/

@[expose] public section

open TopologicalSpace Opposite CategoryTheory

universe u

namespace Manifold

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} X}

open scoped Classical in
/-- **The reduced closed subspace** `X_red` of the closed subspace with ideal sheaf `J`
[BM97, Remark 3.14]: the ideal sheaf `√J` with the radicals `√J_x` as stalks, when that family has
local generators (Cartan's theorem on the radical of a coherent ideal), the unit ideal sheaf
otherwise. -/
noncomputable def IdealSheaf.radicalSubspace (J : IdealSheaf 𝒪) : IdealSheaf 𝒪 :=
  if hex : IdealSheaf.HasLocalGenerators (𝒪 := 𝒪) fun x => (J.stalkIdeal x).radical
  then IdealSheaf.ofStalks 𝒪 _ hex
  else ⊤

theorem IdealSheaf.stalkIdeal_radicalSubspace_of_hasLocalGenerators (J : IdealSheaf 𝒪)
    (hex : IdealSheaf.HasLocalGenerators (𝒪 := 𝒪) fun x => (J.stalkIdeal x).radical) (x : X) :
    (IdealSheaf.radicalSubspace J).stalkIdeal x = (J.stalkIdeal x).radical := by
  rw [IdealSheaf.radicalSubspace, dite_eq_left hex, IdealSheaf.stalkIdeal_ofStalks]

theorem IdealSheaf.radicalSubspace_of_not_hasLocalGenerators (J : IdealSheaf 𝒪)
    (hex : ¬ IdealSheaf.HasLocalGenerators (𝒪 := 𝒪) fun x => (J.stalkIdeal x).radical) :
    IdealSheaf.radicalSubspace J = ⊤ := by
  rw [IdealSheaf.radicalSubspace, dite_eq_right hex]

end Manifold
