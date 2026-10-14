/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.BlowUp.Transform.Defs
import Hironaka.Algebra.Local.PrimeProducts
import Hironaka.Algebra.Local.Regular
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Submanifold.Ideal
import Hironaka.Manifold.Submanifold.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# The subspace predicates on analytic manifolds: elementary facts

The elementary facts about the predicates of Hironaka's Definitions 1 and 2 on the ideal sheaves of
an analytic manifold — `IsInvertible`, `IsReduced`, `IsNonsingular`, `IsIrreducible`,
`HasOnlyNormalCrossingsWith`, `HasOnlyNormalCrossings`, `IsNormalCrossingsDivisor` — and the reduced
transform `IdealSheaf.reducedTransform`: the two branches of the reduced transform and its set of
points (`f⁻¹(E) ∪ f⁻¹(D)` on either branch, [Hir64, Main Theorem II'(N) (iii), p. 156]); the ideal
sheaf of a closed submanifold defines a non-singular subspace — its quotient stalks are the stalks
of the submanifold (`Hironaka/Manifold/Submanifold/Ideal.lean`), regular local rings
(`Hironaka/Manifold/Germ/StalkNoetherian.lean`) — hence the centre of every monoidal transformation
is non-singular (Bierstone–Milman's blowing-up has a closed submanifold as centre,
[BM88, Definition 4.1]); a non-singular subspace is reduced (a regular local ring is a domain, so
the stalks are prime); an irreducible subspace is nonempty; and the reduced transform is natural
along a square of analytic isomorphisms, the compatibility of the boundary with local isomorphisms
that the functoriality of the resolution needs.
-/

public section

open TopologicalSpace Filter Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {N N' : AnalyticManifold.{u} 𝕜 E}

/-! ### The reduced transform: the two branches and the set of points -/

section ReducedTransform

variable (f : AnalyticMap N' N) (D B : AnalyticManifold.IdealSheaf N)

/-- The reduced transform on the branch where the vanishing ideals of `f⁻¹(E) ∪ f⁻¹(D)` have local
generators is the ideal sheaf with those stalks. -/
theorem reducedTransform_eq_of_hasLocalGenerators
    (h : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N') fun x : N' =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑f ⁻¹' B.support ∪ ⇑f ⁻¹' D.support) x) :
    AnalyticManifold.IdealSheaf.reducedTransform f B D = IdealSheaf.ofStalks _ _ h :=
  dite_eq_left h

/-- The reduced transform on the other branch is the product `f^*E · f^*D`. -/
theorem reducedTransform_eq_mul_of_not
    (h : ¬ IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N') fun x : N' =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑f ⁻¹' B.support ∪ ⇑f ⁻¹' D.support) x) :
    AnalyticManifold.IdealSheaf.reducedTransform f B D =
      (B.pullback f f.contMDiff * D.pullback f f.contMDiff) :=
  dite_eq_right h

/-- On the first branch the stalks of the reduced transform are the vanishing ideals of
`f⁻¹(E) ∪ f⁻¹(D)`. -/
theorem reducedTransform_stalkIdeal_of_hasLocalGenerators
    (h : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N') fun x : N' =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑f ⁻¹' B.support ∪ ⇑f ⁻¹' D.support) x) (x : N') :
    (AnalyticManifold.IdealSheaf.reducedTransform f B D).stalkIdeal x =
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑f ⁻¹' B.support ∪ ⇑f ⁻¹' D.support) x := by
  rw [reducedTransform_eq_of_hasLocalGenerators f D B h, IdealSheaf.stalkIdeal_ofStalks]

/-- The set of points of `red(f⁻¹(E) ∪ f⁻¹(D))` is `f⁻¹(E) ∪ f⁻¹(D)`, on either branch of the
definition [Hir64, Main Theorem II'(N) (iii), p. 156]. -/
theorem reducedTransform_support :
    (AnalyticManifold.IdealSheaf.reducedTransform f B D).support =
      ⇑f ⁻¹' B.support ∪ ⇑f ⁻¹' D.support := by
  have hZ : IsClosed (⇑f ⁻¹' B.support ∪ ⇑f ⁻¹' D.support) :=
    (B.isClosed_support.preimage f.contMDiff.continuous).union
      (D.isClosed_support.preimage f.contMDiff.continuous)
  ext x
  rw [IdealSheaf.mem_support]
  by_cases h : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N') fun x : N' =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑f ⁻¹' B.support ∪ ⇑f ⁻¹' D.support) x
  · rw [reducedTransform_stalkIdeal_of_hasLocalGenerators f D B h]
    constructor
    · intro hne
      by_contra hx
      exact hne (vanishingStalk_eq_top_of_notMem_closure (by rwa [hZ.closure_eq]))
    · intro hx
      exact vanishingStalk_ne_top_of_mem_closure (by rwa [hZ.closure_eq])
  · rw [reducedTransform_eq_mul_of_not f D B h]
    rw [IdealSheaf.stalkIdeal_mul, Ideal.mul_ne_top_iff, ← IdealSheaf.mem_support,
      ← IdealSheaf.mem_support, IdealSheaf.support_pullback, IdealSheaf.support_pullback]
    exact Iff.rfl

end ReducedTransform

/-! ### Non-singular, reduced, irreducible -/

/-- An irreducible subspace is nonempty (Hironaka's "irreducible" includes nonempty,
[Hir64, Definition 2, p. 141]). -/
theorem _root_.AnalyticManifold.IdealSheaf.IsIrreducible.nonempty
    {J : AnalyticManifold.IdealSheaf N} (hJ : J.IsIrreducible) :
    J.support.Nonempty :=
  hJ.1

/-- A non-singular subspace is reduced: its stalks are prime off the unit ideal (a regular local
ring is a domain). -/
theorem IsNonsingular.isReduced {J : AnalyticManifold.IdealSheaf N} (hJ : J.IsNonsingular) :
    J.IsReduced := by
  intro x
  by_cases hx : x ∈ J.support
  · have h1 :
      IsRegularLocalRing (AnalyticManifold.IdealSheaf.stalkRing N x ⧸ J.stalkIdeal x) := hJ x hx
    have h2 : IsDomain (AnalyticManifold.IdealSheaf.stalkRing N x ⧸ J.stalkIdeal x) :=
        inferInstance
    exact ((Ideal.Quotient.isDomain_iff_prime _).mp h2).isRadical
  · have hx' : J.stalkIdeal x = ⊤ := by
      rw [IdealSheaf.mem_support, not_not] at hx
      exact hx
    rw [hx']
    exact fun r _ => Submodule.mem_top

variable {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- The ideal sheaf of a closed submanifold defines a non-singular subspace ([Hir64, p. 121]): its
quotient stalks `𝒪_{M,a}/𝓘_{Y,a} ≅ 𝒪_{Y,a}` are the stalks of the manifold `Y`, regular local
rings. -/
theorem isNonsingular_idealSheaf {Y : Set N} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c) :
    AnalyticManifold.IdealSheaf.IsNonsingular hY.idealSheaf := by
  intro x hx
  have hxY : x ∈ Y := by
    rwa [IsClosedSubmanifold.cosupport_idealSheaf] at hx
  rw [IsClosedSubmanifold.stalkIdeal_idealSheaf_of_mem hY hxY]
  let _i := hY.chartedSpace
  have _h := hY.isManifold'
  have e := RingHom.quotientKerEquivOfSurjective (hY.restrictStalk_surjective ⟨x, hxY⟩)
  have h3 : IsRegularLocalRing (hY.stalk ⟨x, hxY⟩) :=
    isRegularLocalRing_stalk (Fin (n - c) → 𝕜) (⟨x, hxY⟩ : Y)
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- The centre of a monoidal transformation is non-singular (Bierstone–Milman's blowing-up has a
closed analytic submanifold as centre, [BM88, Definition 4.1]). -/
theorem IsMonoidalTransformation.isNonsingular (f : AnalyticMap N' N)
    (D : AnalyticManifold.IdealSheaf N) (hf : f.IsMonoidalTransformation D) :
        D.IsNonsingular := by
  obtain ⟨m, ψ', c, hY, hD, -⟩ := hf
  convert isNonsingular_idealSheaf ψ' hY using 1
  exact IsIdealSheafOf.eq_idealSheaf hY hD


/-! ### Naturality of the reduced transform along a square of diffeomorphisms -/

section Naturality

variable {M₁ M₂ : AnalyticManifold.{u} 𝕜 E}
  (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁ M₂ ω)

/-- **The reduced transform is natural along a square of diffeomorphisms** `f₂ ∘ g' = g ∘ f₁`:
`g'^* red(f₂⁻¹E ∪ f₂⁻¹D) = red(f₁⁻¹ g^*E ∪ f₁⁻¹ g^*D)`, on either branch of the definition — the
closed sets correspond under `g'`, their vanishing ideals under the germ maps of `g'`, the
local-generator condition is invariant, and on the product branch the pullbacks compose (the
compatibility of the boundary with the pull-back of a blow-up sequence along a local isomorphism,
[Kol07, 30.1]). -/
theorem reducedTransform_pullback_of_comp_eq {N₁ N₂ : AnalyticManifold.{u} 𝕜 E}
    (f₁ : AnalyticMap N₁ M₁) (f₂ : AnalyticMap N₂ M₂)
    (g' : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N₁ N₂ ω) (hsq : ⇑f₂ ∘ ⇑g' = ⇑g ∘ ⇑f₁)
    (D B : AnalyticManifold.IdealSheaf M₂) :
    (AnalyticManifold.IdealSheaf.reducedTransform f₂ B D).pullback ⇑g' g'.contMDiff =
      AnalyticManifold.IdealSheaf.reducedTransform f₁ (B.pullback ⇑g g.contMDiff)
        (D.pullback ⇑g g.contMDiff) := by
  have e : ∀ x, g (f₁ x) = f₂ (g' x) := fun x => (congrFun hsq x).symm
  have hW : ⇑f₁ ⁻¹' IdealSheaf.support (B.pullback ⇑g g.contMDiff) ∪
      ⇑f₁ ⁻¹' IdealSheaf.support (D.pullback ⇑g g.contMDiff) =
      ⇑g' ⁻¹' (⇑f₂ ⁻¹' B.support ∪ ⇑f₂ ⁻¹' D.support) := by
    rw
        [show IdealSheaf.support (B.pullback ⇑g g.contMDiff) =
            ⇑g ⁻¹' B.support from
        IdealSheaf.support_pullback ⇑g g.contMDiff B,
      show IdealSheaf.support (D.pullback ⇑g g.contMDiff) =
          ⇑g ⁻¹' D.support from
        IdealSheaf.support_pullback ⇑g g.contMDiff D]
    ext x
    simp only [Set.mem_union, Set.mem_preimage, e]
  by_cases h₂ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N₂) fun x : N₂ =>
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑f₂ ⁻¹' B.support ∪ ⇑f₂ ⁻¹' D.support) x
  · have h₁ : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N₁) fun x : N₁ =>
        vanishingStalk (𝕜 := 𝕜) (E := E)
          (⇑f₁ ⁻¹' IdealSheaf.support (B.pullback ⇑g g.contMDiff) ∪
            ⇑f₁ ⁻¹' IdealSheaf.support (D.pullback ⇑g g.contMDiff)) x := by
      rw [hW]
      exact hasLocalGenerators_vanishingStalk_preimage_of g' _ h₂
    rw [reducedTransform_eq_of_hasLocalGenerators f₂ D B h₂,
      reducedTransform_eq_of_hasLocalGenerators f₁ _ _ h₁]
    refine IdealSheaf.ext fun x => ?_
    rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_ofStalks,
      IdealSheaf.stalkIdeal_ofStalks, hW, vanishingStalk_preimage_diffeomorph g' _ x]
  · have h₁ : ¬ IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E N₁) fun x : N₁ =>
        vanishingStalk (𝕜 := 𝕜) (E := E)
          (⇑f₁ ⁻¹' IdealSheaf.support (B.pullback ⇑g g.contMDiff) ∪
            ⇑f₁ ⁻¹' IdealSheaf.support (D.pullback ⇑g g.contMDiff)) x := by
      rw [hW]
      exact fun h => h₂ ((hasLocalGenerators_vanishingStalk_preimage_iff g' _).mp h)
    rw [reducedTransform_eq_mul_of_not f₂ D B h₂, reducedTransform_eq_mul_of_not f₁ _ _ h₁]
    change (B.pullback ⇑f₂ f₂.contMDiff * D.pullback ⇑f₂ f₂.contMDiff).pullback ⇑g' g'.contMDiff =
      (B.pullback ⇑g g.contMDiff).pullback ⇑f₁ f₁.contMDiff *
        (D.pullback ⇑g g.contMDiff).pullback ⇑f₁ f₁.contMDiff
    rw [IdealSheaf.pullback_mul, IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback,
      IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback,
      IdealSheaf.pullback_congr B (f₂.contMDiff.comp g'.contMDiff) (g.contMDiff.comp f₁.contMDiff)
        hsq,
      IdealSheaf.pullback_congr D (f₂.contMDiff.comp g'.contMDiff) (g.contMDiff.comp f₁.contMDiff)
        hsq]

end Naturality

end Manifold
