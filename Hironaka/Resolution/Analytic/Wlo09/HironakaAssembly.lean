/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.FamilyExt
public import Hironaka.Manifold.Resolution.Defs
import Hironaka.Resolution.Analytic.ModelTransport.Family
import Hironaka.Resolution.Analytic.ModelTransport.SncFamily
import Hironaka.Resolution.Analytic.OrderReduction.Stage.Concrete
import Hironaka.Resolution.Analytic.Wlo09.HironakaClauses
import Hironaka.Resolution.Analytic.Wlo09.Monomial
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Hironaka's Main Theorem II″(N) on the model manifold

The conclusion of Hironaka's Main Theorem II′(N) [Hir64, p. 156], which II″(N) [Hir64, pp. 158–159]
asserts for real spaces, for a non-singular real or complex analytic manifold modelled on `𝕜ⁿ` with
a normal crossings divisor and a coherent sheaf of nonzero ideals, with its clauses (i)–(iv):
properness of the blow-down and, over every compact `K`, on the finite succession over `nhd K`, (i)
every centre is non-singular, (ii) the order of the weak transform of `𝓘|_{nhd K}` is a positive
constant on each centre, (iii) each boundary is a simple normal crossing family having simple normal
crossings with its centre (the `IsSncBoundaryWith` form of "only normal crossings with"), (iv) the
last boundary is a simple normal crossing family and the last weak transform is the unit ideal. It
is proved here for the glued blow-down of the resolution family `resolveFam bo T` along the
exhaustion of a manifold `M` modelled on `𝕜ⁿ`, stated on the extension-compatible family
`resolveFamExt bo T` (`Wlo09/FamilyExt.lean`). Kollár's form is [Kol07, Theorem 68] with [Kol07,
Remark 67]; Włodarczyk's is [Wlo09, Theorem 2.0.3 (1), (2), (4)] with the reduction of the maximal
order in [Wlo09, §6, Step 2a]. The theorem is the input of the main theorem
`exists_extensionCompatibleFamily_weakTransformSeq_eq_top` at the end of this file, which transports
it along the chart isomorphism of the boundary of an arbitrary real analytic manifold.

## The proof

`σ` is proper because over each piece of the exhaustion it is a finite composite of blow-ups and
properness is local on the target (`isProperMap_resolveFamExt_map`); over `nhd K` the succession
`seq K` is the value of `resolveFam` there, whose centres are closed submanifolds, hence
non-singular (clause (i), `FiniteSuccession.center_isNonsingular`); whose weak transforms of
`𝓘|_{nhd K}` have order exactly the round's mark along the centres ([Kol07, Remark 67] read
backwards, `Hironaka/Resolution/Analytic/Wlo09/HironakaClauses.lean`; clause (ii),
`resolveSeqOn_clause_ii`); whose boundaries are the ideal sheaves of the total transforms of the
simple normal crossing boundary family `T.F|_{nhd K}`, themselves simple normal crossing families
for the standard model and having simple normal crossings with the centre of their stage (clause
(3′) of [Kol07, Definition 66]; `isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt` fed by
`isOfOrderGe_zero_resolveSeqOn`, with `center_resolveSeqOn_hasSncWith` and the boundary identified
through `restrictTriple_F_idealSheaf`; clause (iii) and the first half of (iv), with the codimension
`codim i` of the centre); and whose last weak transform is the unit ideal (the last round at mark
`1`, `ord_lt`; the second half of (iv), `weakTransformSeq_last_resolveSeqOn_eq_top`).
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable (𝕜 : Type) [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : Manifold.AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)

/-- **Hironaka's Main Theorem II″(N) on the model manifold** ([Hir64, pp. 158–159], with the
clauses of Main Theorem II′(N), p. 156) for the glued blow-down of `resolveFam bo T`: properness
(`isProperMap_resolveFamExt_map`) and, over every compact `K`, clauses (i), (ii) and the second half
of (iv) by the per-open theorems of `Hironaka/Resolution/Analytic/Wlo09/HironakaClauses.lean` at
`nhd K`, and clause (iii) with the first half of (iv) by the boundary family of the value (the total
transform of `T.F|_{nhd K}` at each stage). Used by
`exists_extensionCompatibleFamily_weakTransformSeq_eq_top` (below) and, for the empty boundary, by
`exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback`
(`Hironaka/Resolution/Analytic/BM97/JacobianAssembly.lean`). Stated for `𝕜 = ℝ` or `ℂ`: at
`𝕜 = ℝ` it is II″(N) (pp. 158–159); at `𝕜 = ℂ` it is the compatible-family form of the
conclusion of II′(N) (p. 156), without Hironaka's assumption that `X` admit a projective morphism
to a complex Stein space. -/
theorem resolveFamExt_mainTheoremIIpp :
    IsProperMap (resolveFamExt bo T).map ∧
    ∀ K : Compacts M,
      (∀ i, IdealSheaf.IsNonsingular (((resolveFamExt bo T).seq K).center i)) ∧
      (∀ i, ∃ c : ℕ, 0 < c ∧
        ∀ y ∈ (((resolveFamExt bo T).seq K).center i).support,
          (((resolveFamExt bo T).seq K).weakTransformSeq
            (T.I.restrict ((resolveFamExt bo T).nhd K)) i.castSucc).ord y = c) ∧
      (∀ i, (((resolveFamExt bo T).seq K).boundarySeq
        (IdealSheaf.restrict T.F.idealSheaf ((resolveFamExt bo T).nhd K))
        i.castSucc).IsSncBoundaryWith (((resolveFamExt bo T).seq K).center i)) ∧
      (((resolveFamExt bo T).seq K).boundarySeq
        (IdealSheaf.restrict T.F.idealSheaf ((resolveFamExt bo T).nhd K))
        (Fin.last _)).IsSncBoundary ∧
      ((resolveFamExt bo T).seq K).weakTransformSeq
          (T.I.restrict ((resolveFamExt bo T).nhd K)) (Fin.last _) =
        (⊤ : ((resolveFamExt bo T).seq K).last.IdealSheaf) := by
  refine ⟨isProperMap_resolveFamExt_map bo T,
    fun K => ⟨fun i => FiniteSuccession.center_isNonsingular _ i,
      resolveSeqOn_clause_ii 𝕜 bo T _ _, fun i => ?_, ?_,
      weakTransformSeq_last_resolveSeqOn_eq_top bo T _ _⟩⟩
  · -- clause (iii): the boundary family at stage `i`
    have h := FiniteSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
      (S := (resolveFamExt bo T).seq K) (restrictTriple T _).isSnc i.castSucc
      (fun i' _ => (isOfOrderGe_zero_resolveSeqOn bo T _ _ i').1)
    refine ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), _,
      ((resolveFamExt bo T).seq K).codim i, h.1, ?_, center_resolveSeqOn_hasSncWith bo T _ _ i⟩
    rw [← restrictTriple_F_idealSheaf]
    exact h.2.symm
  · -- clause (iv-a): the boundary family at the last stage
    have h := FiniteSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
      (S := (resolveFamExt bo T).seq K) (restrictTriple T _).isSnc (Fin.last _)
      (fun i' _ => (isOfOrderGe_zero_resolveSeqOn bo T _ _ i').1)
    refine ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), _, h.1, ?_⟩
    rw [← restrictTriple_F_idealSheaf]
    exact h.2.symm

end Hironaka.Manifold

end

end

public section

universe u v

section Principalization

open TopologicalSpace

namespace AnalyticManifold

/-- **Hironaka's Main Theorem II″(N)** for real-analytic manifolds [Hir64, Main Theorem II″(N),
pp. 158–159], whose conclusion is that of Main Theorem II′(N), p. 156, in the compatible-family form
of Włodarczyk's locally finite principalization [Wlo09, Theorem 2.0.3 (1) and (4)]. Let `X` be a
real-analytic manifold, `E₀` an ideal sheaf on `X` with only normal crossings (`IsSncBoundary`), and
`J₀` an ideal sheaf on `X` with nonzero stalks. Then there is a proper analytic map `σ : X̃ → X`
which over an open neighbourhood `U_K` of every compact `K ⊆ X` splits, compatibly across compacts
(`ExtensionCompatibleFamily`), into a finite succession of monoidal transformations
`U_K = U_0 ← U_1 ← ⋯ ← U_r` with centres `D_i ⊆ U_i` such that, for every compact `K`,
* (i) every centre `D_i` is non-singular;
* (ii) the order of the weak transform `J_i` of `J₀|_{U_K}` is a positive constant along `D_i`
  (`FiniteSuccession.HasConstantPositiveOrderAlongCenters`);
* (iii) with `E_0 = E₀|_{U_K}` and `E_{i+1} = red(σ_{i+1}⁻¹(E_i) ∪ σ_{i+1}⁻¹(D_i))`, every `E_i` has
  only normal crossings with `D_i`, and, the first half of (iv), `E_r` has only normal crossings
  (`FiniteSuccession.HasSncBoundaries`);
* the second half of (iv): `J_r = 𝒪_{U_r}`, the unit ideal sheaf `⊤`.

The constant of (ii) may depend on `K` and `i`. Clause (i) holds for every finite succession
(`FiniteSuccession.center_isNonsingular`); it is kept as Hironaka's (i). For `J₀ = 𝒪_X` the weak
transforms are the unit ideal, of order `0` everywhere, so (ii) leaves every centre empty, and `σ`
is then an isomorphism.

Relation to the source.
* **Translation.** `F : ExtensionCompatibleFamily X` with `F.map` is the pair $(\tilde X, \sigma)$;
  `F.nhd K` is $U_K$ and `F.seq K` the finite succession over it;
  `(F.seq K).weakTransformSeq (J₀.restrict (F.nhd K)) i` is $J_i$ and
  `(F.seq K).boundarySeq (E₀.restrict (F.nhd K)) i` is $E_i$.
* **Interpretation.** Hironaka's "has only normal crossings" for the boundary is read on his global
  irreducible components [Hir64, Definition 2, p. 141], that is, as simple normal crossings in the
  sense of [Kol07, Definition 24] (`IsSncBoundary`, `IsSncBoundaryWith`).
* **Translation.** A real-analytic manifold, `X : AnalyticManifold ℝ E`, is Hironaka's non-singular
  analytic $\mathbb{R}$-space.
* **Interpretation.** Hironaka's "coherent sheaf of non-zero ideals" is read as a locally finitely
  generated ideal sheaf (`IdealSheaf X`, coherent by Oka's theorem) with nonzero stalks (`hJ₀`).
* **Gap.** Hironaka's succession is one locally finite succession
  $\{f_\lambda : X_{\lambda+1} \to X_\lambda\}$ of $X$ itself, indexed by a countable well-ordered
  set $\Lambda$ with maximal element $\gamma$ (projective limits at the elements without
  predecessor) [Hir64, p. 155], whose canonical modification $X_\gamma \to X$ he notes is proper (p.
  155, after Main Theorem I′(n)). Here it is replaced by a finite succession
  $U_0 \leftarrow \cdots \leftarrow U_r$ (`F.seq K`) over a neighbourhood $U_K$ (`F.nhd K`) of each
  compact $K$, compatible across compacts, and the proper map $\sigma$ (`F.map`). Restricting
  Hironaka's succession over $U_K$ gives such a family (by local finiteness only finitely many
  centres meet the preimage of $U_K$); the compatible family is not asserted to come from one
  succession of $X$. Włodarczyk's "locally finite" is the compatible-family form itself.
* **Gap.** Clause (i) asserts non-singularity only, and a centre may be empty or have several
  components. Hironaka's irreducibility of the centres is not asserted per compact: Włodarczyk's
  centres are disjoint unions of smooth centres [Wlo09, Definition 3.2.4], and the irreducible
  refinement of the succession over a smaller compact is in general not the restriction of the
  succession over a larger one, which [Wlo09, Theorem 2.0.3 (4)] requires.
* **Strengthening.** In clause (iii) `IsSncBoundaryWith` also asserts that $E_i$ has only normal
  crossings at every point, which Hironaka's "with $D_i$" [Hir64, Definition 2, p. 141] does not; he
  derives it from (iii) (the remark after Main Theorem II, p. 143), and it is [Wlo09, Theorem 2.0.3
  (2)].
* **Gap.** Hironaka's $X$ is any non-singular analytic $\mathbb{R}$-space; II″(N) does not fix its
  dimension (the "of dimension $N$" is in II′(N), p. 156). Here `X` has one model space `E`, so it
  is pure-dimensional; a non-singular space whose components have different dimensions is the
  disjoint union of its pure-dimensional open and closed parts, to each of which the theorem
  applies. No finite-dimensionality of `E` is assumed: the coordinates `E ≃ ℝⁿ` that `hE₀` provides
  make `E` finite-dimensional.
* **Restatement.** The reducedness and invertibility of `E₀`, which Hironaka assumes ("reduced
  analytic subspace everywhere of codimension one"), are not separate hypotheses: both follow from
  the family of smooth hypersurfaces with simple normal crossings that `hE₀` provides, whose reduced
  ideal sheaf is `E₀`.

Source statement: [Hir64, Main Theorem II″(N), pp. 158–159]

Source statement: [Wlo09, Theorem 2.0.3 (1) and (4)] -/
theorem exists_extensionCompatibleFamily_weakTransformSeq_eq_top {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (X : AnalyticManifold.{u} ℝ E)
    (E₀ : IdealSheaf X) (hE₀ : E₀.IsSncBoundary)
    (J₀ : IdealSheaf X) (hJ₀ : J₀.IsNonzeroEverywhere) :
    ∃ F : ExtensionCompatibleFamily X, IsProperMap F.map ∧
      ∀ K : Compacts X,
        -- (i)
        (∀ i, ((F.seq K).center i).IsNonsingular) ∧
        -- (ii)
        (F.seq K).HasConstantPositiveOrderAlongCenters (J₀.restrict (F.nhd K)) ∧
        -- (iii) and the first half of (iv)
        (F.seq K).HasSncBoundaries (E₀.restrict (F.nhd K)) ∧
        -- the second half of (iv)
        (F.seq K).weakTransformSeq (J₀.restrict (F.nhd K)) (Fin.last _) = ⊤ := by
  open Hironaka.Manifold Manifold in
  -- the snc hypersurface family of the boundary and its coordinates `ψ`, along which we transport
  obtain ⟨n, ψ, FE, hFE, rfl⟩ := hE₀
  -- the triple (ideal sheaf, boundary family) on the standard model `X.transport ψ`, named once
  obtain ⟨T, hTI, hTF⟩ : ∃ T : AnalyticTriple (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))
      (X.transport ψ), T.I = J₀.transport ψ ∧
        T.F = FE.comap ⇑(X.transportDiffeomorph ψ).symm :=
    ⟨{ I := J₀.transport ψ
       isNonzeroEverywhere := (IdealSheaf.isNonzeroEverywhere_pullbackDiffeomorph_iff _ _).mpr hJ₀
       F := FE.comap ⇑(X.transportDiffeomorph ψ).symm
       isSnc := (HypersurfaceFamily.isSnc_comap_diffeomorph_iff _ ψ _ FE).mpr hFE }, rfl, rfl⟩
  -- the order-reduction families: the tower of the blow-up sequence functors of Kollár's
  -- Theorems 103 (order reduction of an ideal sheaf) and 107 (of a marked ideal) at the identity
  -- transform data, named once
  obtain ⟨bo, -⟩ : ∃ bo : ∀ d : ℕ, BOanFam.{u} ℝ n d, bo = fun d =>
      BOanFamAllOf ℝ (theorem107FamStarOf ℝ (fun n m => BMO.monomialStep3Fam ℝ n m)
        (fun n => BMOmod.nonmonomialTransformIdentity_inhabitant
          (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)))
        (fun n => BMOmod.nonmonomialTransformIdentityMod_inhabitant
          (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)))) n d :=
    ⟨_, rfl⟩
  -- the boundary of the model triple is the transport of `E₀` along `ψ`
  have hB : T.F.idealSheaf = IdealSheaf.transport ψ FE.idealSheaf := by
    rw [hTF]
    exact HypersurfaceFamily.idealSheaf_comap_diffeomorph _ FE
  -- Main Theorem II″(N) on the model manifold
  obtain ⟨hprop, hK⟩ := resolveFamExt_mainTheoremIIpp ℝ bo T
  refine ⟨(resolveFamExt bo T).transportBack ψ,
    (ExtensionCompatibleFamily.isProperMap_map_transportBack_iff ψ _).mpr hprop, fun K => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hK K
  rw [hTI] at h2 h5
  rw [hB] at h3 h4
  -- clauses (i), (iii), (iv) read back through the transport of each predicate; clause (ii)
  -- below, through the identification of the stages
  refine ⟨fun i =>
      (ExtensionCompatibleFamily.isNonsingular_center_seq_transportBack_iff ψ _ K i).mpr (h1 i),
    fun i => ?_,
    ⟨fun i =>
      (ExtensionCompatibleFamily.isSncBoundaryWith_boundarySeq_center_seq_transportBack_iff
        ψ _ _ K i).mpr (h3 i),
    (ExtensionCompatibleFamily.isSncBoundary_boundarySeq_last_seq_transportBack_iff ψ _ _ K).mpr
      h4⟩,
    (ExtensionCompatibleFamily.weakTransformSeq_last_seq_transportBack_eq_unit_iff ψ _ J₀ K).mpr
      h5⟩
  -- clause (ii): the order along the centre, read back through the stage identification
  obtain ⟨c, hc, hy⟩ := h2 i
  exact ⟨c, hc, fun y hy' =>
    (ExtensionCompatibleFamily.ord_weakTransformSeq_seq_transportBack ψ _ J₀ K i.castSucc y).trans
      (hy _ (Eq.mp (congrArg (y ∈ ·)
        (ExtensionCompatibleFamily.support_center_seq_transportBack ψ _ K i)) hy'))⟩

end AnalyticManifold

end Principalization

end
