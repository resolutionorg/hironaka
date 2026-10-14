/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Defs
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Total, strict and geometric strict transforms of closed subspaces

The transforms of a closed analytic subspace `X ⊆ M`, given by its ideal sheaf `I` of finite type,
under the blowing-up `π : M' → M` with centre the closed submanifold `Y` (`IsBlowUp ψ Y c π`),
exceptional divisor `F = π⁻¹(Y)` with ideal sheaf `I_F = hY.idealSheaf.pullback π h.contMDiff`,
following [BM97, §3, "The strict transform"] and [Hir64, Ch. 0, §5, p. 142].

* **The total transform** `σ⁻¹(X)`: the closed subspace of `M'` defined by
  `π⁻¹(I) = π^*I · 𝒪_{M'}`, the pull-back `I.pullback π h.contMDiff` along the blow-up (its
  points are the preimages of the points of `X`, `IdealSheaf.support_pullback`).
* **The strict transform** `X'` ([BM97, Proposition 3.13]; compare the controlled transform of a
marked ideal, [Wlo09, Definition 3.2.4, (3)]).
  Bierstone–Milman give two forms: the ideal generated at `a'` by the strict transforms
  `f' = y_exc^{-d}(f ∘ σ)` of the `f ∈ I_{σ(a')}`, and (Proposition 3.13) the saturation
  `⋃_k (I_{σ⁻¹(X)} : I_F^k)` with respect to the exceptional divisor. `strictTransformSubspace` is
  the saturation: the ideal sheaf whose stalks are
  `saturationStalk hY h I a' = ⨆ k, (π⁻¹(I)_{a'} : I_{F,a'}^k)`, taken by a classical choice when
  this stalk family has local generators (Bierstone–Milman's "`I_{X'}` is an ideal of finite type
  since `X` is locally Noetherian", proved in
  `Hironaka.Manifold.BlowUp.Transform.SaturationFiniteType`), the unit ideal sheaf otherwise,
  the pattern of the weak transform; in the first case its stalks are the saturations
  (`stalkIdeal_strictTransformSubspace_of_hasLocalGenerators`). The generated-by-strict-transforms
  form is `strictTransformElems`; that its span is contained in the saturation is immediate
  (`span_strictTransformElems_le_saturationStalk`, one direction of Proposition 3.13); the other
  direction is proved in `Hironaka.Manifold.BlowUp.Transform.StrictSubspaceProp313`.
* **The geometric strict transform** `X''` ([BM97, Remarks 1.7, (2)] and [BM97, Remark 3.15]):
  the smallest closed subspace of `σ⁻¹(X)` containing the set `|σ⁻¹(X)| ∖ |F|`; in ideal-sheaf
  terms the largest ideal sheaf `J ≥ π⁻¹(I)` whose cosupport contains that set
  (`geometricCandidates`; `geometricStrictTransform` is the greatest element, by a classical
  choice, the unit ideal sheaf if there is none). The total transform is a
  candidate, and the strict transform is one as soon as its stalks are the saturation
  (`strictTransform_mem_geometricCandidates_of_hasLocalGenerators`), which gives `X'' ⊆ X'`.

Conventions: ideal sheaves are ordered by inclusion of stalk ideals, so `X' ⊆ σ⁻¹(X)` reads
`π⁻¹(I) ≤ I_{X'}`; `⊤` is the empty subspace. The strict transform of the centre itself is empty
(the saturation of `I_F` is `⊤`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ}
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-! ### The strict transform -/

variable (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
  (I : IdealSheaf (structureSheaf 𝕜 E M))

theorem stalkIdeal_strictTransformSubspace_of_hasLocalGenerators
    (hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I))
    (a' : M') :
    (strictTransformSubspace hY h I).stalkIdeal a' = saturationStalk hY h I a' := by
  rw [strictTransformSubspace, dite_eq_left hex, IdealSheaf.stalkIdeal_ofStalks]

theorem strictTransformSubspace_of_not_hasLocalGenerators
    (hex : ¬ IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I)) :
    strictTransformSubspace hY h I = ⊤ := by
  rw [strictTransformSubspace, dite_eq_right hex]

/-- The total transform lies in its saturation (the term `k = 0`). -/
theorem totalTransform_stalkIdeal_le_saturationStalk (a' : M') :
    (I.pullback π h.contMDiff).stalkIdeal a' ≤ saturationStalk hY h I a' :=
  le_iSup_of_le 0 fun _ hg => Submodule.mem_colon.mpr fun p _ => Ideal.mul_mem_right p _ hg

/-- **`X' ⊆ σ⁻¹(X)`** — the strict transform contains the total transform's ideal
sheaf (unconditionally: if the saturation is not of finite type the chosen ideal sheaf is the
empty subspace). -/
theorem totalTransform_le_strictTransformSubspace :
    I.pullback π h.contMDiff ≤ strictTransformSubspace hY h I := by
  rw [IdealSheaf.le_def]
  intro a'
  by_cases hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I)
  · rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex]
    exact totalTransform_stalkIdeal_le_saturationStalk hY h I a'
  · rw [strictTransformSubspace_of_not_hasLocalGenerators hY h I hex, IdealSheaf.stalkIdeal_top]
    exact le_top

/-- **The strict transforms of the elements of `I`** at `a'`:
the germs `g = y_exc^{-d}(f ∘ σ)`, i.e. `y^d · g = σ^*(f)` for some `f ∈ I_{σ(a')}`, some
generator `y` of `I_{F,a'}` and some `d` (in the domain `𝒪_{M',a'}` the ideal they generate is
the one generated with the maximal `d = μ_{C,σ(a')}(f)`). -/
def strictTransformElems (a' : M') : Set ((structureSheaf 𝕜 E M').presheaf.stalk a') :=
  {g | ∃ f ∈ I.stalkIdeal (π a'), ∃ (y : (structureSheaf 𝕜 E M').presheaf.stalk a') (d : ℕ),
    Ideal.span {y} = (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' ∧
      y ^ d * g = germMap π h.contMDiff a' f}

/-- A strict transform
`g = y^{-d}(f ∘ σ)` lies in the saturation — `y^d g = σ^*(f) ∈ π⁻¹(I)_{a'}`. -/
theorem span_strictTransformElems_le_saturationStalk (a' : M') :
    Ideal.span (strictTransformElems hY h I a') ≤ saturationStalk hY h I a' := by
  refine Ideal.span_le.mpr ?_
  rintro g ⟨f, hf, y, d, hy, hyg⟩
  refine Submodule.mem_iSup_of_mem d (Submodule.mem_colon.mpr fun p hp => ?_)
  rw [SetLike.mem_coe, ← hy, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hp
  obtain ⟨b, rfl⟩ := hp
  have hmem : germMap π h.contMDiff a' f ∈ (I.pullback π h.contMDiff).stalkIdeal a' := by
    rw [IdealSheaf.stalkIdeal_pullback]
    exact Ideal.mem_map_of_mem _ hf
  rw [smul_eq_mul, show g * (b * y ^ d) = b * (y ^ d * g) by ring, hyg]
  exact Ideal.mul_mem_left _ b hmem

/-! ### The geometric strict transform -/

/-- The closed subspaces `Z ⊆ σ⁻¹(X)` whose set
of points contains `|σ⁻¹(X)| ∖ |F|` — as ideal sheaves, the `J ≥ π⁻¹(I)` with
`|σ⁻¹(X)| ∖ |F| ⊆ |J|`. -/
def geometricCandidates : Set (IdealSheaf (structureSheaf 𝕜 E M')) :=
  {J | I.pullback π h.contMDiff ≤ J ∧
    ∀ a' ∈ (I.pullback π h.contMDiff).support \
      (hY.idealSheaf.pullback π h.contMDiff).support, a' ∈ J.support}

open scoped Classical in
/-- **The geometric strict transform `X''`** —
the smallest closed subspace of `σ⁻¹(X)` containing the set `|σ⁻¹(X)| ∖ |F|`, i.e. the greatest
element of `geometricCandidates` (it exists by local Noetherianness), taken by
`Classical.choice`; the unit ideal sheaf if there is none. -/
def geometricStrictTransform : IdealSheaf (structureSheaf 𝕜 E M') :=
  if hex : ∃ J, IsGreatest (geometricCandidates hY h I) J then Classical.choose hex else ⊤

theorem isGreatest_geometricStrictTransform_of_exists
    (hex : ∃ J, IsGreatest (geometricCandidates hY h I) J) :
    IsGreatest (geometricCandidates hY h I) (geometricStrictTransform hY h I) := by
  rw [geometricStrictTransform, dite_eq_left hex]
  exact Classical.choose_spec hex

/-- The total transform is a candidate (`Z = σ⁻¹(X)`). -/
theorem totalTransform_mem_geometricCandidates :
    I.pullback π h.contMDiff ∈ geometricCandidates hY h I :=
  ⟨le_rfl, fun _ ha' => ha'.1⟩

/-- Off the exceptional divisor the saturation is the total transform's stalk (`I_{F,a'} = 𝒪`). -/
theorem saturationStalk_of_notMem_cosupport {a' : M'}
    (ha' : a' ∉ (hY.idealSheaf.pullback π h.contMDiff).support) :
    saturationStalk hY h I a' = (I.pullback π h.contMDiff).stalkIdeal a' := by
  have htop : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal a' = ⊤ :=
    not_not.mp (mt (IdealSheaf.mem_support _).mpr ha')
  refine le_antisymm (iSup_le fun k => ?_) (totalTransform_stalkIdeal_le_saturationStalk hY h I a')
  intro g hg
  rw [htop, Ideal.top_pow] at hg
  simpa using Submodule.mem_colon.mp hg 1 Submodule.mem_top

/-- The strict transform is a candidate as soon as its stalks are the saturation
(`X' ⊆ σ⁻¹(X)`, and off `F` the strict and total transforms agree). -/
theorem strictTransform_mem_geometricCandidates_of_hasLocalGenerators
    (hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I)) :
    strictTransformSubspace hY h I ∈ geometricCandidates hY h I := by
  refine ⟨totalTransform_le_strictTransformSubspace hY h I, fun a' ha' => ?_⟩
  rw [IdealSheaf.mem_support, stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex,
    saturationStalk_of_notMem_cosupport hY h I ha'.2]
  exact (IdealSheaf.mem_support _).mp ha'.1

/-- Given the two existence
facts (the finite type of the saturation and local Noetherianness): the strict transform's ideal
sheaf lies in the geometric strict transform's. -/
theorem strictTransform_le_geometricStrictTransform_of_exists
    (hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I))
    (hg : ∃ J, IsGreatest (geometricCandidates hY h I) J) :
    strictTransformSubspace hY h I ≤ geometricStrictTransform hY h I :=
  (isGreatest_geometricStrictTransform_of_exists hY h I hg).2
    (strictTransform_mem_geometricCandidates_of_hasLocalGenerators hY h I hex)

end Manifold

end
