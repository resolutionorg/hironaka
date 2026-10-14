/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.FamilyExt
public import Hironaka.Manifold.Jacobian.Defs
public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Resolution.Analytic.Principalization.Assembly
import Hironaka.Resolution.Analytic.ModelTransport.Family
import Hironaka.Resolution.Analytic.OrderReduction.Stage.Concrete
import Hironaka.Resolution.Analytic.Wlo09.HironakaAssembly
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Jacobian.Bundled
import Hironaka.Resolution.Analytic.BM97.LedgerLimit
import Hironaka.Resolution.Analytic.BM97.LedgerSequence
import Hironaka.Resolution.Analytic.Functor.EndResultEmbeddingLemmas
import Hironaka.Resolution.Analytic.Functor.LimitGluing
import Hironaka.Resolution.Analytic.Principalization.JacobianMonomial
import Hironaka.Resolution.Analytic.Wlo09.Monomial
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The Jacobian clause on the glued blow-down

For the glued blow-down `σ : M̃ → M` of the resolution family `resolveFam bo T`, on the
extension-compatible family `resolveFamExt bo T` (`Wlo09/FamilyExt.lean`), the product of the
Jacobian ideal of `σ` with `σ⁻¹(𝓘)` is the ideal sheaf of a normal-crossings divisor
(`resolveFamExt_jacobianIdeal_mul_pullback_isNormalCrossingsDivisor`): the remark after
[BM97, Theorem 1.10], that if `J` is the ideal generated locally by the Jacobian determinant of
the composite of the blowings-up then `J · σ⁻¹(𝓘)` is a normal-crossings divisor. It is the input
of Bierstone–Milman's principalization theorem with the Jacobian clause, the main theorem
`exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback` at the end
of this file, which transports the clauses on the model, together with those of Main Theorem
II″(N) for the empty boundary (`resolveFamExt_mainTheoremIIpp`), to an arbitrary real-analytic
manifold.

* On a piece `U` (the relatively compact opens of the exhaustion,
  `resolveSeqOn_jacobianIdeal_mul_pullback_composite_isNormalCrossingsDivisor`): the Jacobian ideal
  of the composite blow-down of `resolveSeqOn bo T U hU` is a monomial in the exceptional family at
  every point (`jacobianLedger_composite_of_forall_hasSncWith`,
  `Hironaka/Resolution/Analytic/BM97/LedgerSequence.lean`, its hypothesis that the centres have
  simple normal crossings with the boundary being the corollary `center_resolveSeqOn_hasSncWith` of
  clause (3′) of the value) and the pull-back of `𝓘|_U` is a boundary monomial
  (`pullbackIsMonomialAtLast_resolveSeqOn`, `Hironaka/Resolution/Analytic/Wlo09/Monomial.lean`); the
  product of two monomials of one simple normal crossing family is a normal-crossings divisor
  (`isNormalCrossingsDivisor_jacobianIdeal_mul_of_forall_monomial`,
  `Principalization/JacobianMonomial.lean`).
* On `M̃` (`resolveFamExt_jacobianIdeal_mul_pullback_isNormalCrossingsDivisor`): every point is
  `ι_m q` (`toLimit_surjective`); the stalk of `J · σ⁻¹(𝓘)` at `ι_m q` is carried by the germ
  isomorphism of
  `ι_m` onto the piece's stalk (the Jacobian factor by
  `CompatibleFamily.jacobianStalk_limitBlowDown_toLimitMap`,
  `Hironaka/Resolution/Analytic/BM97/LedgerLimit.lean`; the pull-back factor by `pullback_comp` and
  `limitDesc_comp_toLimitMap`), and the normal-crossings form is transported back along the local
  diffeomorphism `ι_m` (`exists_monomial_of_comap_of_isLocalDiffeomorphAt`).
* `resolveFamExt_comap_map_isNormalCrossingsDivisor`: `σ⁻¹(𝓘)` alone is the ideal sheaf of a
  normal-crossings divisor ([Kol07, Theorem 35 (2)]; [Wlo09, Theorem 2.0.3 (3)];
  [BM97, Theorem 1.10]), the gluing tool
  `CompatibleFamily.isNormalCrossingsDivisor_comap_limitBlowDown` fed on each piece by
  `resolveSeqOn_comap_last_isNormalCrossingsDivisor`; this is the form the main theorems use.
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)

/-- On the piece: for the value `resolveSeqOn bo T U hU` of the resolution family on the relatively
compact open `U`, the Jacobian ideal of the composite blow-down times the pull-back of `𝓘|_U` is a
normal-crossings divisor (the remark after [BM97, Theorem 1.10]):
`isNormalCrossingsDivisor_jacobianIdeal_mul_of_forall_monomial` with the Jacobian ledger
`jacobianLedger_composite_of_forall_hasSncWith` (its simple-normal-crossings hypothesis on the
centres from `center_resolveSeqOn_hasSncWith`) and the boundary-monomial form of the pull-back,
`pullbackIsMonomialAtLast_resolveSeqOn`. -/
theorem resolveSeqOn_jacobianIdeal_mul_pullback_composite_isNormalCrossingsDivisor
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (AnalyticMap.jacobianIdeal (resolveSeqOn bo T U hU).toSuccession.composite *
        (restrictTriple T U).I.pullback _ (resolveSeqOn bo T U
        hU).toSuccession.composite.contMDiff).IsNormalCrossingsDivisor := by
  have hZ := isOfOrderGe_zero_resolveSeqOn bo T U hU
  have h3 : ∀ i : Fin (resolveSeqOn bo T U hU).toSuccession.length,
      ((resolveSeqOn bo T U hU).toSuccession.totalTransformSeqFrom (restrictTriple T U).F
        i.castSucc).HasSncWith (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((resolveSeqOn bo T U hU).toSuccession.center i).support
        ((resolveSeqOn bo T U hU).toSuccession.codim i) :=
    fun i =>
      (resolveSeqOn bo T U hU).toSuccession.hasSncWith_totalTransformSeqFrom_center_of_forall_lt
        (restrictTriple T U).isSnc i fun i' _ => (hZ i').1
  have hG : ((resolveSeqOn bo T U hU).toSuccession.totalTransformSeqFrom (restrictTriple T U).F
      (Fin.last _)).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) :=
    ((resolveSeqOn bo T U
      hU).toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
      (restrictTriple T U).isSnc (Fin.last _) fun i' _ => (hZ i').1).1
  have hled := Hironaka.Manifold.jacobianLedger_composite_of_forall_hasSncWith
    (resolveSeqOn bo T U hU) (restrictTriple T U).F (restrictTriple T U).isSnc h3
  have hT1 := pullbackIsMonomialAtLast_resolveSeqOn bo T U hU
  refine isNormalCrossingsDivisor_jacobianIdeal_mul_of_forall_monomial
    (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (resolveSeqOn bo T U hU).toSuccession.composite _
    hG _ ?_ hT1
  intro x
  obtain ⟨s, h, hs, -, hx⟩ := (hled x).2
  exact ⟨s, h, hs, hx⟩

/-- **The product of the Jacobian ideal of the glued blow-down `σ` with `σ⁻¹(𝓘)` is a
normal-crossings divisor** (the remark after [BM97, Theorem 1.10]): every point of `M̃` lies on a
piece (`toLimit_surjective`); the stalk of `J · σ⁻¹(𝓘)` at `ι_m q` is carried onto the piece's by
the germ isomorphism of `ι_m = toLimitMap m` (the Jacobian factor by
`CompatibleFamily.jacobianStalk_limitBlowDown_toLimitMap`, the pull-back factor by `pullback_comp`
and `limitDesc_comp_toLimitMap`), and the normal-crossings form is transported back along the
local diffeomorphism `ι_m` by `exists_monomial_of_comap_of_isLocalDiffeomorphAt`. Used by
`exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback` (below).
-/
theorem resolveFamExt_jacobianIdeal_mul_pullback_isNormalCrossingsDivisor :
    AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor
      (AnalyticMap.jacobianIdeal (resolveFamExt bo T).map *
        T.I.pullback _ (resolveFamExt bo T).map.contMDiff) := by
  set C := resolveFam bo T with hC
  set Kex := exhaustion M with hKex
  have hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h) :=
    fun _ _ hU₁ hU₂ h => C.isAnalyticOpenEmbedding_endResultEmbedding hU₁ hU₂ h
  have hcomp : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)
      (p : (C.seqOn U₁ hU₁).stage (Fin.last _)),
      (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
        M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p) :=
    fun _ _ hU₁ hU₂ h p => C.composite_endResultEmbedding hU₁ hU₂ h p
  change AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor (AnalyticMap.jacobianIdeal
      (C.limitBlowDown Kex hemb hcomp) * T.I.pullback _
      (C.limitBlowDown Kex hemb hcomp).contMDiff)
  intro p
  obtain ⟨m, q₀, rfl⟩ := (C.endResultChain Kex hemb).toLimit_surjective p
  -- every object is typed at `endResultOn`/`endResultLimit`, so that the point
  -- computations below are rewrites and congruences, never unfoldings
  obtain ⟨q, rfl⟩ : ∃ q : C.endResultOn Kex m, q = q₀ := ⟨q₀, rfl⟩
  set ι : AnalyticMap (C.endResultOn Kex m) (C.endResultLimit Kex hemb) :=
    (C.endResultChain Kex hemb).toLimitMap m with hι
  set U := relCompactOpen Kex m with hUdef
  have hU : IsCompact (closure (U : Set M)) := isCompact_closure_relCompactOpen Kex m
  -- the pull-back factor: `(𝓘.comap σ).comap ι_m = (𝓘|U).comap σ^{(m)}`
  have hσι : (C.limitBlowDown Kex hemb hcomp).comp ι = C.blowDownOn Kex m :=
    (C.endResultChain Kex hemb).limitDesc_comp_toLimitMap _ _ m
  have heq : (T.I.pullback _ (C.limitBlowDown Kex hemb hcomp).contMDiff).pullback ι ι.contMDiff =
      (restrictTriple T U).I.pullback _ (C.seqOn U hU).toSuccession.composite.contMDiff := by
    have h1 := AnalyticManifold.IdealSheaf.pullback_comp T.I (C.limitBlowDown Kex hemb hcomp) ι
    have h2 := AnalyticManifold.IdealSheaf.pullback_comp T.I (M.inclusion U)
      (C.seqOn U hU).toSuccession.composite
    rw [hσι] at h1
    exact h1.trans h2.symm
  -- the stalk of the product at `ι_m q`, carried to the piece by the germ isomorphism of `ι_m`
  set σ := C.limitBlowDown Kex hemb hcomp with hσ
  have hstalk : (((AnalyticMap.jacobianIdeal σ * T.I.pullback σ σ.contMDiff)).pullback ι
      ι.contMDiff).stalkIdeal q
      =
      (AnalyticMap.jacobianIdeal (C.seqOn U hU).toSuccession.composite *
          (restrictTriple T U).I.pullback _ (C.seqOn U
              hU).toSuccession.composite.contMDiff).stalkIdeal q :=
    calc (((AnalyticMap.jacobianIdeal σ * T.I.pullback σ σ.contMDiff)).pullback ι
        ι.contMDiff).stalkIdeal q
        = Ideal.map (germMap ⇑ι ι.contMDiff q)
            (((AnalyticMap.jacobianIdeal σ * T.I.pullback σ σ.contMDiff)).stalkIdeal (ι q)) :=
          IdealSheaf.stalkIdeal_pullback ⇑ι ι.contMDiff _ _
      _ = Ideal.map (germMap ⇑ι ι.contMDiff q)
            (jacobianStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ⇑σ (ι q) * (T.I.pullback σ
                σ.contMDiff).stalkIdeal (ι q)) :=
          congrArg (Ideal.map _)
            ((IdealSheaf.stalkIdeal_mul _ _ _).trans
              (congrArg (· * (T.I.pullback σ σ.contMDiff).stalkIdeal (ι q))
                  (jacobianIdeal_stalkIdeal _ _)))
      _ = Ideal.map (germMap ⇑ι ι.contMDiff q)
              (jacobianStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ⇑σ (ι q)) *
            Ideal.map (germMap ⇑ι ι.contMDiff q) ((T.I.pullback σ σ.contMDiff).stalkIdeal (ι q)) :=
          Ideal.map_mul _ _ _
      _ = (AnalyticMap.jacobianIdeal (C.seqOn U hU).toSuccession.composite *
          (restrictTriple T U).I.pullback _ (C.seqOn U
              hU).toSuccession.composite.contMDiff).stalkIdeal q := by
          have e1 : Ideal.map (germMap ⇑ι ι.contMDiff q)
              (jacobianStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ⇑σ (ι q)) =
              jacobianStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ⇑(C.seqOn U hU).toSuccession.composite q :=
            Hironaka.Manifold.CompatibleFamily.jacobianStalk_limitBlowDown_toLimitMap
              C Kex hemb hcomp m q
          have e2 : Ideal.map (germMap ⇑ι ι.contMDiff q) ((T.I.pullback σ σ.contMDiff).stalkIdeal
              (ι q)) =
              ((restrictTriple T U).I.pullback _ (C.seqOn U
                  hU).toSuccession.composite.contMDiff).stalkIdeal q :=
            (IdealSheaf.stalkIdeal_pullback ⇑ι ι.contMDiff _ _).symm.trans
              (congrArg
                  (fun J : AnalyticManifold.IdealSheaf (C.endResultOn Kex m) => J.stalkIdeal q)
                      heq)
          have e3 : (AnalyticMap.jacobianIdeal (C.seqOn U hU).toSuccession.composite *
              (restrictTriple T U).I.pullback _ (C.seqOn U
                  hU).toSuccession.composite.contMDiff).stalkIdeal q =
              jacobianStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) ⇑(C.seqOn U hU).toSuccession.composite q *
                ((restrictTriple T U).I.pullback _ (C.seqOn U
                    hU).toSuccession.composite.contMDiff).stalkIdeal q :=
            (IdealSheaf.stalkIdeal_mul _ _ _).trans
              (congrArg (· * ((restrictTriple T U).I.pullback _
                (C.seqOn U hU).toSuccession.composite.contMDiff).stalkIdeal q)
                (jacobianIdeal_stalkIdeal _ _))
          exact (congrArg₂ (· * ·) e1 e2).trans e3.symm
  -- the piece is a normal-crossings divisor (the piece theorem), transported along `ι_m`
  obtain ⟨k, z, α, hreg, hz⟩ :=
    resolveSeqOn_jacobianIdeal_mul_pullback_composite_isNormalCrossingsDivisor bo T U hU q
  exact exists_monomial_of_comap_of_isLocalDiffeomorphAt ι _
    ((C.endResultChain Kex hemb).isLocalDiffeomorph_toLimit m q) ⟨k, z, α, hreg, hstalk.trans hz⟩

/-- **`σ⁻¹(𝓘)` is the ideal sheaf of a normal-crossings divisor** ([Kol07, Theorem 35 (2)];
[Wlo09, Theorem 2.0.3 (3)]; [BM97, Theorem 1.10]): the gluing tool
`CompatibleFamily.isNormalCrossingsDivisor_comap_limitBlowDown` at `resolveFam bo T`, fed on each
piece by `resolveSeqOn_comap_last_isNormalCrossingsDivisor`. Used by
`exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback` (below).
-/
theorem resolveFamExt_comap_map_isNormalCrossingsDivisor :
    AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor (T.I.pullback _ (resolveFamExt bo
        T).map.contMDiff) :=
  CompatibleFamily.isNormalCrossingsDivisor_comap_limitBlowDown (resolveFam bo T) (exhaustion M)
    (fun _ _ hU₁ hU₂ h => (resolveFam bo T).isAnalyticOpenEmbedding_endResultEmbedding hU₁ hU₂ h)
    (fun _ _ hU₁ hU₂ h p => (resolveFam bo T).composite_endResultEmbedding hU₁ hU₂ h p)
    T.I fun _ => resolveSeqOn_comap_last_isNormalCrossingsDivisor bo T _ _

end Hironaka.Manifold

end

end

public section

universe u v

section Principalization

open TopologicalSpace

namespace AnalyticManifold

/-- **Real-analytic principalization with the Jacobian clause** [BM97, Theorem 1.10 and the
sentence following it], in the compatible-family form of [Wlo09, Theorem 2.0.3 (1), (2) and (4)].
Let `M` be a real-analytic manifold modelled on a finite-dimensional real vector space and `I` an
ideal sheaf on `M` with nonzero stalks. Then there is a proper analytic map `σ : M̃ → M` which over
an open neighbourhood `U_K` of every compact `K ⊆ M` splits, compatibly across compacts
(`ExtensionCompatibleFamily`), into a finite succession of monoidal transformations
`U_K = U_0 ← ⋯ ← U_r` with centres `D_i`, such that
* for every compact `K`: every centre `D_i` is smooth; the exceptional divisors `E_i`, the
  boundaries started at the empty boundary `E_0 = ⊤`, have simple normal crossings with the centres,
  and the last one `E_r` has simple normal crossings (`FiniteSuccession.HasSncBoundaries`); and the
  weak transform of `I|_{U_K}` on `U_r` is the unit ideal sheaf;
* the pull-back `σ*(I)` is a normal-crossings divisor (`IdealSheaf.IsNormalCrossingsDivisor`);
* the product of the Jacobian ideal of `σ` (`AnalyticMap.jacobianIdeal`: the ideal sheaf generated
  locally, in analytic coordinates, by the Jacobian determinant of `σ`) with `σ*(I)` is a
  normal-crossings divisor;
* `σ` is an analytic isomorphism over the complement of the support of `I`
  (`AnalyticMap.IsIsoOver`), the support being Kollár's cosupport `cosupp I`
  [Kol07, Theorem 21 (2)].

The clauses on the successions are stated over each compact; the normal-crossings, Jacobian and
isomorphism clauses, being local on `M̃`, are stated on `σ` itself. For `I = 𝒪_M` the support of
`I` is empty, so `σ` is an isomorphism by the last clause.

Relation to the source.
* **Translation.** `I.pullback F.map F.map.contMDiff` is Bierstone–Milman's
  $\sigma^{-1}(I) = \sigma^*(I) \cdot \mathcal{O}_{M_k}$, and
  `F.map.jacobianIdeal * I.pullback F.map F.map.contMDiff` their $\mathcal{J} \cdot \sigma^{-1}(I)$,
  $\mathcal{J}$ the ideal generated by the Jacobian determinant of $\sigma$;
  `(F.seq K).weakTransformSeq (I.restrict (F.nhd K)) (Fin.last _) = ⊤` is their
  $I_k = \mathcal{O}_{M_k}$; `(F.seq K).HasSncBoundaries ⊤` is the clause on the exceptional
  divisors $E_j$, `⊤` being the empty boundary; and `F.map.IsIsoOver I.supportᶜ` says that
  $\sigma$ is an isomorphism over the complement of the support of $I$.
* **Interpretation.** Bierstone–Milman's "smooth $\mathrm{inv}_I$-admissible centres" are read as
  smooth centres having simple normal crossings with the exceptional divisor accumulated so far; the
  invariant $\mathrm{inv}_I$ does not appear in the statement.
* **Correction.** The hypothesis that `I` has nonzero stalks (`hI`) is tacit in the source: without
  it $\sigma^*(I)$ could not be a divisor. Kollár's principalization states it explicitly, for an
  ideal sheaf "not zero on any irreducible component" [Kol07, Theorem 35].
* **Strengthening.** Bierstone–Milman's finite sequence of blow-ups, for a quasi-compact $|M|$, is
  here a finite succession over a neighbourhood of every compact, compatible across compacts: for a
  manifold that is not quasi-compact the finite sequence is replaced by a locally finite one, by
  analogy with the remark after [BM97, Theorem 1.6], which is made for Theorem 1.6 only. For a
  compact `M` the family contains one finite succession over `M`.
* **Strengthening.** That the last exceptional divisor $E_r$ has simple normal crossings (in
  `HasSncBoundaries`) is not a clause of [BM97, Theorem 1.10]: it is their remark that admissibility
  "guarantees that $E_{i+1}$ is a collection of smooth hypersurfaces having only normal crossings"
  [BM97, after (1.2)], and [Wlo09, Theorem 2.0.3 (2)] at $i = r$.
* **Strengthening.** The clause that $\sigma$ is an isomorphism over the complement of the support
  of $I$ (`F.map.IsIsoOver I.supportᶜ`) is not in [BM97, Theorem 1.10] or [Wlo09, Theorem 2.0.3]; it
  is [Wlo09, Lemma 4.0.3], cf. [Kol07, Theorem 35 (3)].

Source statement: [BM97, Theorem 1.10]

Source statement: [Wlo09, Theorem 2.0.3] (compatible-family form) -/
theorem exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : AnalyticManifold.{u} ℝ E) (I : IdealSheaf M) (hI : I.IsNonzeroEverywhere) :
    ∃ F : ExtensionCompatibleFamily M, IsProperMap F.map ∧
      (∀ K : Compacts M,
        -- smooth centres
        (∀ i, ((F.seq K).center i).IsNonsingular) ∧
        -- the exceptional divisors: the boundaries started at the empty boundary `⊤`
        (F.seq K).HasSncBoundaries ⊤ ∧
        -- the weak transform of `I` becomes the unit ideal sheaf
        (F.seq K).weakTransformSeq (I.restrict (F.nhd K)) (Fin.last _) = ⊤) ∧
      -- `σ*(I)` is a normal-crossings divisor
      IdealSheaf.IsNormalCrossingsDivisor (I.pullback F.map F.map.contMDiff) ∧
      -- the Jacobian clause
      (F.map.jacobianIdeal * I.pullback F.map F.map.contMDiff).IsNormalCrossingsDivisor ∧
      -- `σ` is an isomorphism off the support of `I`
      F.map.IsIsoOver I.supportᶜ := by
  open Hironaka.Manifold Manifold in
  -- the standard model of `E` and the transport of `I` to it
  set n : ℕ := Module.finrank ℝ E with hn
  set ψ : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
    with hψ
  -- the order-reduction families: the tower of the blow-up sequence functors of Kollár's
  -- Theorems 103 and 107 at the identity transform data
  set bo : ∀ d : ℕ, BOanFam.{u} ℝ n d := fun d =>
    BOanFamAllOf ℝ (theorem107FamStarOf ℝ (fun n m => BMO.monomialStep3Fam ℝ n m)
      (fun n => BMOmod.nonmonomialTransformIdentity_inhabitant
        (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)))
      (fun n => BMOmod.nonmonomialTransformIdentityMod_inhabitant
        (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)))) n d with hbo
  set T : AnalyticTriple (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)) (M.transport ψ) :=
    ⟨I.transport ψ, (IdealSheaf.isNonzeroEverywhere_pullbackDiffeomorph_iff _ _).mpr hI,
      HypersurfaceFamily.empty _,
      HypersurfaceFamily.isSnc_empty (ψ := ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))⟩ with hT
  -- the extension-compatible family of the algorithm on the model, with its glued blow-down
  set F₀ : ExtensionCompatibleFamily (M.transport ψ) := resolveFamExt bo T with hF₀
  -- the boundary `E_0 = ∅` on the model: the unit ideal is the reduced ideal sheaf of the empty
  -- family
  have hunit : ((⊤ : M.IdealSheaf)).transport ψ = T.F.idealSheaf :=
    (IdealSheaf.pullbackDiffeomorph_top _).trans
      (HypersurfaceFamily.idealSheaf_empty (ψ := ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))).symm
  -- Main Theorem II″(N) on the model, for the empty boundary
  obtain ⟨-, hK⟩ := resolveFamExt_mainTheoremIIpp ℝ bo T
  refine ⟨F₀.transportBack ψ, (F₀.isProperMap_map_transportBack_iff ψ).mpr
    (isProperMap_resolveFamExt_map bo T), fun K => ?_, ?_, ?_, ?_⟩
  · -- the clauses on the succession over `K`: clauses (i), (iii) and (iv) of Main Theorem II″(N)
    -- on the model, read back through the transport of each predicate
    obtain ⟨h1, -, h3, h4, h5⟩ := hK K
    rw [← hunit] at h3 h4
    have hu : ((⊤ : M.IdealSheaf)).restrict ((F₀.transportBack ψ).nhd K) =
        (⊤ : (M.restrict ((F₀.transportBack ψ).nhd K)).IdealSheaf) :=
      IdealSheaf.pullback_top _ _
    rw [← hu]
    exact ⟨fun i => (F₀.isNonsingular_center_seq_transportBack_iff ψ K i).mpr (h1 i),
      ⟨fun i => (F₀.isSncBoundaryWith_boundarySeq_center_seq_transportBack_iff ψ ⊤ K i).mpr
          (h3 i),
        (F₀.isSncBoundary_boundarySeq_last_seq_transportBack_iff ψ ⊤ K).mpr h4⟩,
      (F₀.weakTransformSeq_last_seq_transportBack_eq_unit_iff ψ I K).mpr h5⟩
  · -- `σ*(I)` is a normal-crossings divisor
    exact (F₀.isNormalCrossingsDivisor_comap_map_transportBack_iff ψ I).mpr
      (resolveFamExt_comap_map_isNormalCrossingsDivisor bo T)
  · -- the Jacobian clause
    exact (F₀.isNormalCrossingsDivisor_jacobianIdeal_mul_pullback_map_transportBack_iff ψ I).mpr
      (resolveFamExt_jacobianIdeal_mul_pullback_isNormalCrossingsDivisor bo T)
  · -- `σ` is an isomorphism off the support of `I`
    exact (F₀.isAnalyticIsoOver_map_transportBack_iff ψ I).mpr
      (isAnalyticIsoOver_resolveFamExt_map bo T)

end AnalyticManifold

end Principalization

end
