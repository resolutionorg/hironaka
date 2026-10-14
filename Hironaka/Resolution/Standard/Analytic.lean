/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Maps.Proper.Basic
public import Hironaka.Manifold.IdealSheaf.Principal
public import Hironaka.Manifold.MonomialAt.Defs
public import Hironaka.Manifold.AnalyticManifold.Model
import Hironaka.Manifold.Chart.Rechart
import Hironaka.Manifold.Germ.ChartTransport
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Jacobian.Bundled
import Hironaka.Manifold.Jacobian.Units
import Hironaka.Manifold.Snc.Monomial
import Hironaka.Resolution.Analytic.BM97.JacobianAssembly
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Local monomialization of a real-analytic function, in Mathlib's terms

The local monomialization of a real-analytic function [Ati70, Resolution Theorem], with the
Jacobian clause of [BM97, Theorem 1.10], stated with Mathlib's definitions alone
(`exists_proper_analytic_monomialization`): for `f` real-analytic on an open set `U ⊆ ℝⁿ` and not
identically zero near any point, a proper real-analytic map `π : M → U` from an analytic manifold,
an analytic isomorphism over `{f ≠ 0}`, such that in the chart of `M` at every point both `f ∘ π`
and the Jacobian determinant of `π` are units times monomials.

The proof applies the principalization theorem with the Jacobian clause [BM97, Theorem 1.10]
(`exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback` in the
namespace `AnalyticManifold`) to the principal ideal sheaf `(f)` on the manifold `U`
(`IdealSheaf.principal` of the section `analyticSection hf`):

* `(f)` is nonzero at every point, since `f` is not identically zero near any point
  (`isNonzeroEverywhere_principal_analyticSection`), and its support is the zero set of `f`
  (`compl_support_principal_analyticSection`), so the resolution `σ : M̃ → U` is proper and an
  analytic isomorphism over `{f ≠ 0}`;
* the pull-back `σ*(f)` is generated at every point by the germ of `f ∘ σ`, the Jacobian ideal by
  the germ of the Jacobian determinant of `σ` in any pair of charts
  (`exists_stalk_jacobianStalk_eq_span_of_charts`), and their product is a normal-crossings
  divisor; both generators divide its monomial generator, so near every point `q`, in one chart
  `c q` of the maximal atlas, `f ∘ σ` and the Jacobian determinant of `σ` in the chart `c q` are
  units times monomials (`IdealSheaf.IsNormalCrossingsDivisor.exists_chart_forall_le_span`);
* the manifold `M` is `ULift M̃` (in any universe) with the charts `c q` as its preferred charts
  (`Manifold.rechartedSpace`), so that both monomial forms hold in the chart of `M` at every point;
  `ULift.down : M → M̃` is an analytic isomorphism (`Manifold.rechartedDiffeomorph`), and
  `π = σ ∘ ULift.down`.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace Opposite
open scoped Manifold ContDiff

noncomputable section

universe u

open Manifold

namespace Hironaka.Resolution.Standard

variable {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- An analytic function `f` on the open set `U ⊆ ℝⁿ` as a global section of the sheaf of analytic
functions on the manifold `U`. -/
def analyticSection (hf : AnalyticOnNhd ℝ f U) :
    (structureSheaf ℝ (EuclideanSpace ℝ (Fin n))
      ((AnalyticManifold.of ℝ (EuclideanSpace ℝ (Fin n))).restrict U)).presheaf.obj (op ⊤) :=
  ⟨fun x => f x.1.1, by
    have h1 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω
        (fun x : ↥(⊤ : Opens ((AnalyticManifold.of ℝ (EuclideanSpace ℝ (Fin n))).restrict U)) =>
          (x.1.1 : EuclideanSpace ℝ (Fin n))) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ω f U :=
      contMDiffOn_iff_contDiffOn.mpr hf.contDiffOn_of_completeSpace
    exact h2.comp_contMDiff h1 fun x => x.1.2⟩

/-- The section `analyticSection hf` is `f` restricted to `U`. -/
theorem analyticSection_apply (hf : AnalyticOnNhd ℝ f U)
    (x : ↥(⊤ : Opens ((AnalyticManifold.of ℝ (EuclideanSpace ℝ (Fin n))).restrict U))) :
    analyticSection hf x = f x.1.1 := rfl

/-- The support of the ideal sheaf `(f)` on `U` is the zero set of `f`. -/
theorem compl_support_principal_analyticSection (hf : AnalyticOnNhd ℝ f U) :
    (IdealSheaf.principal (analyticSection hf)).supportᶜ =
      {x : ((AnalyticManifold.of ℝ (EuclideanSpace ℝ (Fin n))).restrict U) | f x.1 ≠ 0} := by
  ext x
  rw [mem_compl_iff, IdealSheaf.mem_support, Set.mem_ofPred_eq, not_not,
    IdealSheaf.stalkIdeal_principal_eq_top_iff, analyticSection_apply]

/-- The ideal sheaf `(f)` on `U` is nonzero at every point when `f` is not identically zero near
any point of `U`. -/
theorem isNonzeroEverywhere_principal_analyticSection (hf : AnalyticOnNhd ℝ f U)
    (hf₀ : ∀ x ∈ U, ∃ᶠ y in 𝓝 x, f y ≠ 0) :
    (IdealSheaf.principal (analyticSection hf)).IsNonzeroEverywhere := by
  intro x hbot
  rw [IdealSheaf.stalkIdeal_principal, Ideal.span_singleton_eq_bot] at hbot
  have h0 := congrArg (stalkToGerm 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω _ x) hbot
  rw [stalkToGerm_structureSheaf_germ, map_zero] at h0
  have hev : ∀ᶠ y in 𝓝 x, f y.1 = 0 := by
    have h1 : (extendSection ℝ (EuclideanSpace ℝ (Fin n)) (analyticSection hf) : _ → ℝ) =ᶠ[𝓝 x]
        0 :=
      Filter.Germ.coe_eq.mp (by simpa using h0)
    filter_upwards [h1] with y hy
    rwa [extendSection_of_mem _ _ _ (Opens.mem_top y)] at hy
  have hev' : ∀ᶠ z in 𝓝 x.1, f z = 0 := by
    rw [← map_nhds_subtype_coe_eq_nhds x.2 (U.isOpen.mem_nhds x.2), Filter.eventually_map]
    exact hev
  exact hf₀ x.1 x.2 (hev'.mono fun y hy => not_not.mpr hy)

end Hironaka.Resolution.Standard

open Hironaka.Resolution.Standard
open AnalyticManifold
  (exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback)

-- `TopCat.of.chartedSpace` (Mathlib's `Geometry/Manifold/Sheaf/Basic`, imported here but not by
-- `Challenge/Standard`) also solves `ChartedSpace ℝⁿ ℝⁿ`; off, the statement elaborates with
-- `chartedSpaceSelf`, as in the challenge file.
attribute [-instance] TopCat.of.chartedSpace in
/-- **Local monomialization of a real-analytic function** [Ati70, Resolution Theorem, p. 147].
Let `f` be real-analytic on an open set `U ⊆ ℝⁿ`, and not identically zero near any point of `U`.
There is a proper real-analytic map `π : M → U` from an `n`-dimensional real-analytic manifold `M`,
an analytic isomorphism over the points where `f` does not vanish, such that near every point `p`
of `M`, in the coordinates `y` of the chart of `M` at `p`, both `f ∘ π` and the Jacobian
determinant of `π` are monomials in `y` times analytic functions that do not vanish at `p`
(`IsMonomialAt`).

This is the form of resolution of singularities that analysis uses: the change of variables
`x = π(y)` turns an integral of a function of `f(x)` over `U` into a sum of integrals of functions
of monomials against monomial densities. [Atiyah][Ati70] uses it to divide distributions, [Bernstein
and Gelfand][BG69], independently, for the meromorphic continuation of $\int |P|^\lambda \varphi$,
and Watanabe for the asymptotics of Bayesian learning [Wat09, Theorem 2.3]. The theorem follows
from Bierstone and Milman's principalization with the Jacobian clause [BM97, Theorem 1.10], applied
to the ideal sheaf generated by `f`.

Relation to the source.
* **Strengthening.** Atiyah states the theorem near a point: for `f` analytic and not identically
  zero near `0 ∈ ℝⁿ`, his map is over some open neighbourhood of `0`. Here `π` is over the whole of
  `U`, for `f` not identically zero near any point of `U`, which is his hypothesis on a connected
  `U`. The monomial form of the Jacobian determinant is not in his theorem: it is Bierstone and
  Milman's clause [BM97, the sentence after Theorem 1.10]. His coordinates are centred at the point
  and the chart coordinates here need not be, which is no weaker: a coordinate that does not
  vanish at the point contributes a unit.
* **Gap.** Atiyah's standing convention that manifolds are connected [Ati70, footnote 2] is not
  asserted for `M`.

Source statement: [Ati70, Resolution Theorem, p. 147] -/
theorem exists_proper_analytic_monomialization {n : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hf₀ : ∀ x ∈ U, ∃ᶠ y in 𝓝 x, f y ≠ 0) :
    ∃ (M : Type u) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M)
      (π : M → U),
      -- `M` is an `n`-dimensional real-analytic manifold, Hausdorff and second countable
      IsManifold (𝓡 n) ω M ∧ T2Space M ∧ SecondCountableTopology M ∧
      -- `π` is real-analytic and proper
      ContMDiff (𝓡 n) (𝓡 n) ω π ∧
      IsProperMap π ∧
      -- `π` is an analytic isomorphism over the points where `f` does not vanish
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ω π (π ⁻¹' {x | f x ≠ 0}) ∧
      Set.BijOn π (π ⁻¹' {x | f x ≠ 0}) {x | f x ≠ 0} ∧
      -- near every point `p`, in the coordinates of the chart at `p`, `f ∘ π` and the Jacobian
      -- determinant of `π` are monomials up to a unit
      ∀ p : M,
        IsMonomialAt n (fun q => f (π q)) p ∧
        IsMonomialAt n (fun q =>
          (fderiv ℝ ((↑) ∘ π ∘ (extChartAt (𝓡 n) p).symm) (extChartAt (𝓡 n) p q)).det) p := by
  classical
  -- the ideal sheaf `(f)` on the manifold `U` and its resolution
  let X : AnalyticManifold.{0} ℝ (EuclideanSpace ℝ (Fin n)) :=
    (AnalyticManifold.of ℝ (EuclideanSpace ℝ (Fin n))).restrict U
  let t := analyticSection hf
  obtain ⟨F, hprop, -, -, hjac, hiso⟩ :=
    exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback X
      (IdealSheaf.principal t) (isNonzeroEverywhere_principal_analyticSection hf hf₀)
  set σ := F.map with hσ
  -- at every point, the pull-back of `(f)` is generated by the germ of `f ∘ σ`
  have hgen : ∀ q : F.space, ∃ s : AnalyticManifold.IdealSheaf.stalkRing F.space q,
      stalkToGerm 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω F.space q s =
        ((fun y => f (σ y).1 : F.space → ℝ) : (𝓝 q).Germ ℝ) ∧
      ((IdealSheaf.principal t).pullback σ σ.contMDiff).stalkIdeal q = Ideal.span {s} := by
    intro q
    let t₀ := (structureSheaf ℝ (EuclideanSpace ℝ (Fin n)) X).presheaf.germ ⊤ (σ q)
      (Opens.mem_top _) t
    refine ⟨germMap (⇑σ) σ.contMDiff q t₀, ?_, ?_⟩
    · rw [stalkToGerm_germMap, stalkToGerm_structureSheaf_germ, Filter.Germ.coe_compTendsto]
      congr 1
      funext y
      change extendSection ℝ (EuclideanSpace ℝ (Fin n)) t (σ y) = _
      rw [extendSection_of_mem ℝ (EuclideanSpace ℝ (Fin n)) t (Opens.mem_top _)]
      rfl
    · rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_principal, Ideal.map_span,
        Set.image_singleton]
  -- in one chart `c q` at every point, `f ∘ σ` and the Jacobian determinant of `σ` are units
  -- times monomials: both generators divide the generator of the normal-crossings divisor
  -- `J_σ · σ*(f)`
  have hmono : ∀ q : F.space, ∃ (c : OpenPartialHomeomorph F.space (EuclideanSpace ℝ (Fin n)))
      (α β : Fin n → ℕ) (u v : F.space → ℝ),
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω F.space ∧ q ∈ c.source ∧
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ω u q ∧ u q ≠ 0 ∧
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ω v q ∧ v q ≠ 0 ∧
      (∀ᶠ y in 𝓝 q, f (σ y).1 = u y * ∏ j, (EuclideanSpace.equiv (Fin n) ℝ) (c y) j ^ α j) ∧
      ∀ᶠ y in 𝓝 q, jacobianFun ℝ (⇑σ) (chartAt (EuclideanSpace ℝ (Fin n)) (σ q)) c y =
        v y * ∏ j, (EuclideanSpace.equiv (Fin n) ℝ) (c y) j ^ β j := by
    intro q
    obtain ⟨c, hc, hqc, H⟩ := hjac.exists_chart_forall_le_span (EuclideanSpace.equiv (Fin n) ℝ) q
    obtain ⟨s, hs, hJs⟩ := hgen q
    obtain ⟨sJ, hsJ, hJJ⟩ := exists_stalk_jacobianStalk_eq_span_of_charts σ.contMDiff
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ω) (σ q))
      hc hqc (mem_chart_source _ (σ q))
    obtain ⟨α, u, hu, hu0, hfu⟩ := H s _ (by
      rw [IdealSheaf.stalkIdeal_mul, ← hJs]
      exact Ideal.mul_le_right) hs
    obtain ⟨β, v, hv, hv0, hJv⟩ := H sJ _ (by
      rw [IdealSheaf.stalkIdeal_mul, jacobianIdeal_stalkIdeal, ← hJJ]
      exact Ideal.mul_le_left) hsJ
    exact ⟨c, α, β, u, v, hc, hqc, hu, hu0, hv, hv0, hfu, hJv⟩
  choose c α β u v hcm hcs hu hu0 hv hv0 hfu hJv using hmono
  -- re-chart `ULift F.space` by the charts `c q`
  let e : ULift.{u} F.space ≃ₜ F.space := Homeomorph.ulift
  let cs := rechartedSpace e c hcs
  have hman := isManifold_rechartedSpace e c hcs hcm
  let D := rechartedDiffeomorph e c hcs hcm
  have hD : ⇑D = e := rfl
  let S : Set X := {x | f x.1 ≠ 0}
  have hS : (IdealSheaf.principal t).supportᶜ = S := compl_support_principal_analyticSection hf
  refine ⟨ULift.{u} F.space, inferInstance, cs, fun q => σ (e q), hman, e.isEmbedding.t2Space,
    e.secondCountableTopology, ?_, ?_, ?_, ?_, ?_⟩
  · exact σ.contMDiff.comp D.contMDiff
  · exact hprop.comp e.isProperMap
  · rintro ⟨q, hq⟩
    have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        ω σ (e q) := hiso.1 ⟨e q, by rw [mem_preimage, hS]; exact hq⟩
    exact IsLocalDiffeomorphAt.comp (hf := D.isLocalDiffeomorph q) (hg := h1)
  · have h2 : Set.BijOn σ (σ ⁻¹' S) S := hS ▸ hiso.2
    have h3 : Set.BijOn e (e ⁻¹' (σ ⁻¹' S)) (σ ⁻¹' S) :=
      ⟨mapsTo_preimage _ _, e.injective.injOn, fun a ha => ⟨e.symm a, by simpa using ha, by simp⟩⟩
    exact h2.comp h3
  · intro p
    refine ⟨⟨α (e p), u (e p) ∘ e, (hu (e p)).comp p (D.contMDiff p), hu0 (e p), ?_⟩,
      ⟨β (e p), v (e p) ∘ e, (hv (e p)).comp p (D.contMDiff p), hv0 (e p), ?_⟩⟩
    · exact (e.continuous.tendsto p).eventually (hfu (e p))
    · exact (e.continuous.tendsto p).eventually (hJv (e p))
