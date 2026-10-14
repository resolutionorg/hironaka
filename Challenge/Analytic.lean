/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Resolution.Defs
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
public import Hironaka.Manifold.Jacobian.Defs
public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Manifold.Snc.Defs
public import Mathlib.Analysis.Complex.Basic

/-!
# Resolution of singularities: the analytic main theorems

## Conventions

A *real-analytic manifold* is an `AnalyticManifold ℝ E`: a Hausdorff, second-countable space with
charts in the real normed space `E` (its *model space*) and analytic chart changes. It is a
pure-dimensional non-singular analytic `ℝ`-space in Hironaka's sense [Hir64, Ch. 0, §1,
pp. 120–121]; Hironaka's non-singular spaces may have components of different dimensions. An
`AnalyticManifold 𝕜 E` over `𝕜 = ℝ` or `𝕜 = ℂ` (`RCLike 𝕜`) is defined in the same way. An
*ideal sheaf* `IdealSheaf X` is a locally finitely generated ideal sheaf of the sheaf of analytic
functions (Hironaka's coherent sheaf of ideals); `J.IsNonzeroEverywhere` says that every stalk
`J_x` is nonzero, and closed analytic subspaces (centres, boundaries) are given by their ideal
sheaves, the support `J.support` being the zero locus of `J`. `J.restrict U` is the restriction
of `J` to the open set `U`, `J.pullback f _` the pull-back `f*(J)` of `J` along the analytic map
`f`, and `⊤` the unit ideal sheaf `𝒪`.

A *finite succession of monoidal transformations* `U_0 ← U_1 ← ⋯ ← U_r` (`FiniteSuccession`) has
centres `D_i ⊆ U_i` (`S.center i`) that are closed submanifolds, empty ones admitted, and each map
`σ_{i+1} : U_{i+1} → U_i` is the blowing-up of `U_i` along `D_i`. The *weak transform* `J_i` of an
ideal sheaf `J` (`S.weakTransformSeq J i`) is defined by `J_0 = J` and `J_{i+1}` the pull-back of
`J_i` divided by the largest power of the ideal sheaf of the exceptional divisor that divides it;
its order `J.ord y` at a point is the largest `ν` with `J_y ⊆ 𝔪_y^ν`. The *boundaries* `E_i`
(`S.boundarySeq B i`) are defined by `E_0 = B` and `E_{i+1} = red(σ_{i+1}⁻¹(E_i) ∪ σ_{i+1}⁻¹(D_i))`;
started at the empty boundary `E_0 = ⊤`, they are the exceptional divisors of the succession. The
*strict transforms* `Y_i` of a closed subspace `Y` with ideal sheaf `I`
(`S.strictTransformSubspaceSeq I i`) are defined by `Y_0 = Y` and `Y_{i+1}` the strict transform of
`Y_i` under `σ_{i+1}`: the saturation `⋃_k (σ_{i+1}^* I_{Y_i} : I_F^k)` of the pull-back of its
ideal sheaf by the ideal sheaf `I_F` of the exceptional divisor `F = σ_{i+1}⁻¹(D_i)`.
An ideal sheaf `B` *has only normal crossings* (`IsSncBoundary`) when it is the reduced ideal sheaf
of a locally finite family of closed smooth hypersurfaces with simple normal crossings, and *only
normal crossings with* `D` (`IsSncBoundaryWith`) when moreover the family has simple normal
crossings with `D`: Hironaka's normal crossings [Hir64, Definition 2, p. 141] read, as he writes
it, on the global irreducible components, which is simple normal crossings
[Kol07, Definition 24; Wlo09, Definition 3.2.4]. The coordinates `E ≃ 𝕜ⁿ` and the codimension of
the centre are existential inside the two predicates, which are defined in the same way over
`𝕜 = ℝ` or `𝕜 = ℂ`.

Włodarczyk's *locally finite* principalization [Wlo09, Theorem 2.0.3 (1) and (4)] is an
`ExtensionCompatibleFamily X`: an analytic manifold `X̃` over the field of `X` (`ℝ` or `ℂ`) with
an analytic map `σ : X̃ → X` (`F.map`), and for every compact `K ⊆ X` an open neighbourhood
`U_K ⊇ K` (`F.nhd K`), growing with `K`, and a finite succession `F.seq K` over `U_K` whose last
stage `U_r` is identified with `σ⁻¹(U_K)` by an analytic isomorphism over `U_K`, so that `σ`
restricted to `σ⁻¹(U_K)` is the composite of the blow-ups; for `K ⊆ K'` the succession over
`U_{K'}`, restricted to `U_K`, is an extension of the succession over `U_K`: the same blow-ups
with isomorphisms interspersed [Wlo09, Definition 3.2.6]. That the identifications
`U_r ≅ σ⁻¹(U_K)` agree across compacts is a theorem
(`ExtensionCompatibleFamily.toSpace_comp_restrictStageIncl_eq`), not a field.
`AnalyticMap.IsIsoOver f U` says that `f` is a local analytic diffeomorphism on `f⁻¹(U)` and a
bijection from `f⁻¹(U)` onto `U`; an analytic map `g` is a *local analytic isomorphism* when
`IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g` (every point has an open neighbourhood mapped by `g`
analytically isomorphically onto an open set).

A *`K`-analytic space* (`AnalyticSpace K`, `K = ℝ` or `K = ℂ`) is a `K`-locally ringed space every
point of which has an open neighbourhood isomorphic to an open subspace of a local model
`(S(𝓘), (𝒜/𝓘)|_{S(𝓘)})`, the zero set `S(𝓘)` of finitely many analytic functions on an open subset
of `Kⁿ` with the quotient structure sheaf, and which is Hausdorff and countable at infinity
(Kollár's "separable"). The *simple locus* `X.regularLocus` is the set of points whose local ring
`𝒪_{X,x}` is regular (Kollár's smooth locus `X^{ns}`), `X.singularLocus` is its complement, and `X`
is *non-singular* (`IsNonsingular`) when its simple locus is all of `X`. A morphism `f : Y ⟶ X` is
an isomorphism over `U ⊆ X` (`Hom.IsIsoOver`) when its restriction `f⁻¹(U) → U` is an isomorphism;
the restriction over a set that is not open is the morphism itself, which the theorems never use,
since `X.regularLocus` is open. `X.restrictSet U` is the open subspace on an open `U`, and
`f.restrictSet U : Y|_{f⁻¹ U} ⟶ X|_U` the restriction of `f`; composition is written in
diagrammatic order, `f ≫ g`. A simple normal crossing divisor of a `K`-analytic space `R` is a
closed subspace `E : R.ClosedSubspace` which is the reduced divisor of a locally finite family of
closed smooth hypersurfaces with simple normal crossings ([Kol07, Definition 24], read at the level
of stalks; `ClosedSubspace.IsSncBoundary`), and `E.support` is its set of points.
-/

public section

universe u v

/-! ### Principalization -/

section Principalization

open TopologicalSpace

namespace AnalyticManifold

/-! #### The conditions of Hironaka's Main Theorem II″(N) and of Bierstone–Milman's theorem -/

/-- The boundaries `E_i` of a finite succession of monoidal transformations started at `B` have only
normal crossings with the centres, and the last one has only normal crossings [Hir64, Main Theorem
II′(N) (iii) and the first half of (iv)]. -/
example {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : AnalyticManifold.{u} ℝ E}
    (S : FiniteSuccession M) (B : IdealSheaf M) :
    S.HasSncBoundaries B ↔
      -- every boundary `E_i` has only normal crossings with the centre `D_i`
      (∀ i : Fin S.length, (S.boundarySeq B i.castSucc).IsSncBoundaryWith (S.center i)) ∧
      -- the last boundary `E_r` has only normal crossings
      (S.boundarySeq B (Fin.last S.length)).IsSncBoundary :=
  FiniteSuccession.hasSncBoundaries_iff S B

/-- An ideal sheaf `B` has only normal crossings when, for some linear coordinates `E ≃ ℝⁿ`, it is
the reduced ideal sheaf of a locally finite family of closed smooth hypersurfaces with a simple
normal crossings chart at every point [Hir64, Definition 2, p. 141; Kol07, Definition 24]. -/
example {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : AnalyticManifold.{u} ℝ E}
    (B : IdealSheaf M) :
    B.IsSncBoundary ↔
      ∃ (n : ℕ) (ψ : E ≃L[ℝ] (Fin n → ℝ)) (G : Manifold.HypersurfaceFamily M),
        -- the family `G` has simple normal crossings at every point
        G.IsSnc ψ ∧
        -- and `B` is its reduced ideal sheaf
        G.idealSheaf = B :=
  Iff.rfl

/-- An ideal sheaf `B` has only normal crossings with `D` when it is the reduced ideal sheaf of a
family of closed smooth hypersurfaces with simple normal crossings at every point which, at every
point of `D`, has simple normal crossings with `D`, the points of `D` forming a closed submanifold
of codimension `c` [Hir64, Definition 2, p. 141; Kol07, Definition 24 (4)]. So it asserts normal
crossings of `B` at every point, and with `D` at the points of `D`. -/
example {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : AnalyticManifold.{u} ℝ E}
    (B D : IdealSheaf M) :
    B.IsSncBoundaryWith D ↔
      ∃ (n : ℕ) (ψ : E ≃L[ℝ] (Fin n → ℝ)) (G : Manifold.HypersurfaceFamily M) (c : ℕ),
        -- the family `G` has simple normal crossings at every point
        G.IsSnc ψ ∧
        -- `B` is its reduced ideal sheaf
        G.idealSheaf = B ∧
        -- and at every point of `D` it has simple normal crossings with `D`
        G.HasSncWith ψ D.support c :=
  Iff.rfl

/-- The order of the weak transform `J_i` of `J` is a positive constant along every centre `D_i`
[Hir64, Main Theorem II′(N) (ii)]. -/
example {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : AnalyticManifold.{u} ℝ E}
    (S : FiniteSuccession M) (J : IdealSheaf M) :
    S.HasConstantPositiveOrderAlongCenters J ↔ ∀ i : Fin S.length, ∃ c : ℕ, 0 < c ∧
      ∀ y ∈ (S.center i).support, (S.weakTransformSeq J i.castSucc).ord y = c :=
  Iff.rfl

/-- An ideal sheaf is a normal-crossings divisor when it is principal, generated at every point by
a monomial in a regular system of parameters [BM97, Theorem 1.10]. -/
example {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : AnalyticManifold.{u} ℝ E}
    (J : IdealSheaf M) :
    J.IsNormalCrossingsDivisor ↔ ∀ x : M,
      ∃ (n : ℕ) (z : Fin n → IdealSheaf.stalkRing M x) (α : Fin n → ℕ),
        -- `z` is a regular system of parameters of the stalk `𝒪_{M,x}`
        IsLocalRing.IsRegularSystemOfParameters z ∧
        -- and the stalk `J_x` is generated by the monomial `∏ z_i^{α_i}`
        J.stalkIdeal x = Ideal.span {∏ i, z i ^ α i} :=
  Iff.rfl

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
        (F.seq K).weakTransformSeq (J₀.restrict (F.nhd K)) (Fin.last _) = ⊤ :=
  sorry

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
      F.map.IsIsoOver I.supportᶜ :=
  sorry

/-! #### The conditions of Włodarczyk's principalization -/

/-- `J = I_Y · I_Ẽ` with `Ẽ`, near every point, an effective combination of the hypersurfaces of
a simple normal crossings family whose reduced ideal sheaf is `B`: at every point `x` the stalk
`J_x` is the product of `(I_Y)_x` with a monomial in the vanishing ideals of hypersurfaces of the
family through `x` [Wlo09, Theorem 2.0.2 (6)]. For `Y = ⊤`, the ideal sheaf of the empty subspace,
it says that `J` is near every point the ideal of an effective combination of the hypersurfaces
[Wlo09, Theorem 2.0.3 (3)]. -/
example {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : AnalyticManifold.{u} 𝕜 E} (J Y B : IdealSheaf M) :
    J.IsMulBoundaryMonomial Y B ↔
      ∃ (n : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (G : Manifold.HypersurfaceFamily M),
        -- `B` is the reduced ideal sheaf of the simple normal crossings family `G`
        G.IsSnc ψ ∧ G.idealSheaf = B ∧
        -- at every point `x`, `J_x = (I_Y)_x · ∏_{j ∈ s} (I_{G^j})_x ^ {α_j}`, `G^j ∋ x`
        ∀ x, ∃ (s : Finset G.ι) (α : G.ι → ℕ), (∀ j ∈ s, x ∈ G.hyp j) ∧
          J.stalkIdeal x = Y.stalkIdeal x * ∏ j ∈ s, Manifold.vanishingStalk (G.hyp j) x ^ α j :=
  Iff.rfl

open scoped Manifold ContDiff in
/-- A morphism `f : R → S` of finite successions over `φ : N → M`, from a succession `R` over an
open `U'` of `N` to a succession `S` over an open `U` of `M`, consists of an index `j_k = f.blk k`
of a stage of `R` for every stage `S_k` and analytic maps `f.map k : R_{j_k} → S_k`; the index
runs from `0` to the last stage of `R` in steps of `0` or `1`, and the maps lie over `φ` (read in
`M` through the inclusions `M.inclusion U` and `N.inclusion U'` of the opens, `S.stageMap k` being
the composite of the first `k` blow-downs) and are compatible with the blow-downs (`R.stageMapLE h`
is the composite of the blow-downs of `R` between two stages). -/
example {𝕜 : Type} [RCLike 𝕜] {E E' : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
    {N : AnalyticManifold.{u} 𝕜 E'} {U : Opens M} {U' : Opens N}
    {R : FiniteSuccession (N.restrict U')} {S : FiniteSuccession (M.restrict U)}
    {φ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯} (f : R.Hom S φ) :
    -- the index `j_k = f.blk k` runs from `0` to the last stage of `R` in steps of `0` or `1`
    f.blk 0 = 0 ∧ f.blk (Fin.last _) = Fin.last _ ∧
    (∀ k : Fin S.length,
      (f.blk k.succ : ℕ) = f.blk k.castSucc ∨ (f.blk k.succ : ℕ) = f.blk k.castSucc + 1) ∧
    -- the maps `f.map k : R_{j_k} → S_k` lie over `φ`
    (∀ k p, M.inclusion U (S.stageMap k (f.map k p)) =
      φ (N.inclusion U' (R.stageMap (f.blk k) p))) ∧
    -- and are compatible with the blow-downs
    ∀ (k : Fin S.length) (hle : f.blk k.castSucc ≤ f.blk k.succ) (p : R.stage (f.blk k.succ)),
      S.map k (f.map k.succ p) = f.map k.castSucc (R.stageMapLE hle p) :=
  ⟨f.blk_zero, f.blk_last, f.blk_succ, f.stageMap_map, f.map_map⟩

open scoped Manifold ContDiff in
/-- `R`, a finite succession over an open `U'` of `N`, is the pull-back of the finite succession `S`
over an open `U` of `M` along `g : N → M`, up to blow-ups with empty centre: the induced sequence
`g^*(S)`, of the fibre products `N ×_M S_k`, is an extension of `R` [Wlo09, Theorem 3.5.1 (2);
Proposition 3.4.1; Definition 3.2.6]. There is a morphism `f : R → S` over `g` whose maps are local
analytic isomorphisms; at a step that raises the index, the centre of `R` (`R.centerAt`, the centre
indexed by its stage) is the pull-back of the centre of `S`, and at a step that does not, the
pulled-back centre is empty. -/
example {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M N : AnalyticManifold.{u} 𝕜 E} {U : Opens M} {U' : Opens N}
    (R : FiniteSuccession (N.restrict U')) (S : FiniteSuccession (M.restrict U))
    (g : AnalyticMap N M) :
    R.IsPullbackUpToEmptyAlong S g ↔
      ∃ f : R.Hom S g,
        -- every `f.map k : R_{j_k} → S_k` is a local analytic isomorphism
        (∀ k, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (f.map k)) ∧
        -- at a step raising the index, the centre of `R` is the pull-back of the centre of `S`
        (∀ (k : Fin S.length) (ha : (f.blk k.castSucc : ℕ) < R.length),
          (f.blk k.succ : ℕ) = f.blk k.castSucc + 1 →
            R.centerAt (f.blk k.castSucc) ha =
              (S.center k).pullback (f.map k.castSucc) (f.map k.castSucc).contMDiff) ∧
        -- at any other step, the pulled-back centre is empty
        (∀ k : Fin S.length, (f.blk k.succ : ℕ) = f.blk k.castSucc →
          ((S.center k).pullback (f.map k.castSucc) (f.map k.castSucc).contMDiff).support = ∅) :=
  Iff.rfl

/-- The compatible family `F'` over `N` is the pull-back of the compatible family `F` over `M` along
`g : N → M` when, over every pair of compacts whose neighbourhoods correspond under `g`, the
succession of `F'` is the pull-back of the succession of `F`, up to blow-ups with empty centre. -/
example {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M N : AnalyticManifold.{u} 𝕜 E} (F' : ExtensionCompatibleFamily N)
    (F : ExtensionCompatibleFamily M) (g : AnalyticMap N M) :
    F'.IsPullbackAlong F g ↔
      ∀ (K' : Compacts N) (K : Compacts M),
        -- `g(U_{K'}) ⊆ U_K`
        ⇑g '' (F'.nhd K' : Set N) ⊆ F.nhd K →
          -- the succession of `F'` over `U_{K'}` is the pull-back of that of `F` over `U_K`
          (F'.seq K').IsPullbackUpToEmptyAlong (F.seq K) g :=
  Iff.rfl

/-- The compatible family `F` is a locally finite principalization of the ideal sheaf `I`, with
`prin_I = F.map` and, over the neighbourhood `U_K` of a compact `K`, the succession
`F.seq K : U_K = U_0 ← ⋯ ← U_r` with composite `σ_K` and exceptional divisors `E_i` (the boundaries
started at the empty boundary `⊤`) [Wlo09, Theorem 2.0.3 (1)–(3)], `prin_I` being moreover an
isomorphism off the support of `I` [Wlo09, Lemma 4.0.3; Kol07, Theorem 35 (3)]. -/
example {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : AnalyticManifold.{u} 𝕜 E} (I : IdealSheaf M) (F : ExtensionCompatibleFamily M) :
    I.IsLocallyFinitelyPrincipalizedBy F ↔
      -- `prin_I` is proper
      IsProperMap F.map ∧
      -- every neighbourhood `U_K` has compact closure
      (∀ K : Compacts M, IsCompact (closure (F.nhd K : Set M))) ∧
      -- (1) the centres `C_i` are smooth
      (∀ (K : Compacts M) (i : Fin (F.seq K).length), ((F.seq K).center i).IsNonsingular) ∧
      -- (2) every `E_i` has simple normal crossings with `C_i`, and `E_r` has simple normal
      -- crossings
      (∀ K : Compacts M, (F.seq K).HasSncBoundaries ⊤) ∧
      -- (3) `σ_K^*(I|_{U_K})` is near every point the ideal of a combination of the components of
      -- `E_r`
      (∀ K : Compacts M, IdealSheaf.IsMulBoundaryMonomial
        ((I.restrict (F.nhd K)).pullback (F.seq K).composite (F.seq K).composite.contMDiff) ⊤
        ((F.seq K).boundarySeq ⊤ (Fin.last (F.seq K).length))) ∧
      -- (3) on `M̃`: `prin_I^*(I)` is a normal-crossings divisor
      IdealSheaf.IsNormalCrossingsDivisor (I.pullback F.map F.map.contMDiff) ∧
      -- `prin_I` is an isomorphism off the support of `I`
      F.map.IsIsoOver I.supportᶜ :=
  IdealSheaf.isLocallyFinitelyPrincipalizedBy_iff I F

open scoped Manifold ContDiff in
/-- The succession `S` over an open `U` of `M` is the push-forward of the succession `R` over an
open `U'` of `N` along the closed embedding `τ : N → M`, up to blow-ups whose centres lie outside
the part over `τ(U')` (Kollár's `j_* B` [Kol07, Definition 30.3], for `τ(U') ⊆ U`). There is a
morphism `f : R → S` over `τ` whose maps are embeddings with image closed in the part of `S_k` over
`τ(U')`; at a step raising the index the centre of `R` is the preimage of the centre of `S`, at any
other step `f.map k` misses the centre, and every centre point over `τ(U')` lies in the image of
`f.map k`. -/
example {𝕜 : Type} [RCLike 𝕜] {E E' : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
    {N : AnalyticManifold.{u} 𝕜 E'} {U : Opens M} {U' : Opens N}
    (S : FiniteSuccession (M.restrict U)) (R : FiniteSuccession (N.restrict U'))
    (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) :
    S.IsPushforwardUpToEmptyAlong R τ ↔
      ∃ f : R.Hom S τ,
        -- every `f.map k : R_{j_k} → S_k` is an embedding
        (∀ k, Topology.IsEmbedding (f.map k)) ∧
        -- whose image is closed in the part of `S_k` over `τ(U')`
        (∀ k (q : S.stage k), q ∈ closure (Set.range (f.map k)) →
          M.inclusion U (S.stageMap k q) ∈ ⇑τ '' (U' : Set N) → q ∈ Set.range (f.map k)) ∧
        -- at a step raising the index, the centre of `R` is the preimage of the centre of `S`
        (∀ (k : Fin S.length) (ha : (f.blk k.castSucc : ℕ) < R.length),
          (f.blk k.succ : ℕ) = f.blk k.castSucc + 1 →
            ⇑(f.map k.castSucc) ⁻¹' (S.center k).support =
              (R.centerAt (f.blk k.castSucc) ha).support) ∧
        -- at any other step, `f.map k` misses the centre
        (∀ k : Fin S.length, (f.blk k.succ : ℕ) = f.blk k.castSucc →
          ⇑(f.map k.castSucc) ⁻¹' (S.center k).support = ∅) ∧
        -- every centre point over `τ(U')` lies in the image of `f.map k`
        (∀ (k : Fin S.length) (q : S.stage k.castSucc), q ∈ (S.center k).support →
          M.inclusion U (S.stageMap k.castSucc q) ∈ ⇑τ '' (U' : Set N) →
            q ∈ Set.range (f.map k.castSucc)) :=
  Iff.rfl

open scoped Manifold ContDiff in
/-- The compatible family `F` over `M` is the push-forward of the compatible family `F'` over `N`
along `τ : N → M` when, over every pair of compacts whose neighbourhoods correspond under `τ`, the
succession of `F` is the push-forward of the succession of `F'`, up to blow-ups whose centres lie
outside the part over the image of the smaller neighbourhood. -/
example {𝕜 : Type} [RCLike 𝕜] {E E' : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
    {N : AnalyticManifold.{u} 𝕜 E'} (F : ExtensionCompatibleFamily M)
    (F' : ExtensionCompatibleFamily N) (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) :
    F.IsPushforwardAlong F' τ ↔
      ∀ (K' : Compacts N) (K : Compacts M),
        -- `τ(U_{K'}) ⊆ U_K`
        ⇑τ '' (F'.nhd K' : Set N) ⊆ F.nhd K →
          -- the succession of `F` over `U_K` is the push-forward of that of `F'` over `U_{K'}`
          (F.seq K).IsPushforwardUpToEmptyAlong (F'.seq K') τ :=
  Iff.rfl

/-- A pair `(M, I)`, the input of the functorial principalization, is an analytic manifold `M` over
`𝕜` on a finite-dimensional model space `E` with an ideal sheaf `I` on `M` with nonzero stalks
(Kollár's triple with an empty boundary). -/
example {𝕜 : Type} [RCLike 𝕜] (T : IdealSheafPair.{u, v} 𝕜) :
    -- the model space is finite-dimensional
    FiniteDimensional 𝕜 T.E ∧
    -- the ideal sheaf has nonzero stalks
    T.I.IsNonzeroEverywhere :=
  ⟨T.finiteDimensional, T.isNonzeroEverywhere⟩

/-- A compatible family assignment on the pairs is a compatible family of finite successions of
blow-ups of the manifold of every pair. -/
example {𝕜 : Type} [RCLike 𝕜] (P : CompatibleFamilyAssignment (IdealSheafPair.{u, v} 𝕜))
    (T : IdealSheafPair.{u, v} 𝕜) : ExtensionCompatibleFamily T.M :=
  P T

open scoped Manifold ContDiff in
/-- The pull-back of the pair `(M, I)` along a local analytic isomorphism `g : N → M` of manifolds
modelled on `E` is the pair `(N, g^*I)`. -/
example {𝕜 : Type} [RCLike 𝕜] (T : IdealSheafPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E}
    (g : AnalyticMap N T.M) (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g) :
    (T.pullback g hg).M = N ∧ (T.pullback g hg).I = T.I.pullback g g.contMDiff :=
  ⟨rfl, rfl⟩

open scoped Manifold ContDiff in
/-- The ideal sheaf `I` on `M` is the push-forward of the ideal sheaf `J` on `N` along `τ : N → M`
when `τ` is a closed embedding of analytic manifolds (an analytic embedding, Mathlib's
`IsSmoothEmbedding` at `ω`: an analytic immersion which is a homeomorphism onto its image, with
closed image; Kollár's "closed embedding of smooth schemes"), the ideal of its image is contained in
`I`
(at every point, the germs vanishing on `τ(N)` lie in the stalk of `I`), and `J = τ^*I`
(Kollár's `𝒪_X/I_X = j_*(𝒪_Y/I_Y)` [Kol07, 34.3]). -/
example {𝕜 : Type} [RCLike 𝕜] {E E' : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
    {N : AnalyticManifold.{u} 𝕜 E'} (I : IdealSheaf M) (J : IdealSheaf N)
    (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) :
    I.IsPushforwardAlong J τ ↔
      -- `τ` is an analytic immersion and a homeomorphism onto its image
      Manifold.IsSmoothEmbedding 𝓘(𝕜, E') 𝓘(𝕜, E) ω τ ∧
      -- with closed image
      IsClosed (Set.range τ) ∧
      -- the ideal of its image lies in `I`
      (∀ x, Manifold.vanishingStalk (𝕜 := 𝕜) (E := E) (Set.range τ) x ≤ I.stalkIdeal x) ∧
      -- `J = τ^*I`
      J = I.pullback τ τ.contMDiff :=
  ⟨fun h => ⟨h.isSmoothEmbedding, h.isClosed_range, h.vanishingStalk_le, h.pullback_eq⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

open scoped Manifold ContDiff in
/-- A compatible family assignment `P` on the pairs commutes with local analytic isomorphisms when,
for a local analytic isomorphism `g : N → M` of manifolds modelled on one space and the pair
`(N, g^*I)`, the family `P(N, g^*I)` is the pull-back of `P(M, I)` along `g`, and there is a
unique continuous map `g̃` from the space of `P(N, g^*I)` to the space of `P(M, I)` over `g`, a
local analytic isomorphism bijective between the fibres over `y` and over `g y` (the last sentence
of [Wlo09, Theorem 2.0.3], read as [Wlo09, Theorem 3.5.1 (2)] and as the natural lifting of
[Wlo09, Theorem 2.0.1 (3)]). -/
example {𝕜 : Type} [RCLike 𝕜] (P : CompatibleFamilyAssignment (IdealSheafPair.{u, v} 𝕜)) :
    IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms P ↔
      -- `P(N, g^*I)` is the pull-back of `P(M, I)` along `g`
      (∀ (T : IdealSheafPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E} (g : AnalyticMap N T.M)
        (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g),
        (P (T.pullback g hg)).IsPullbackAlong (P T) g) ∧
      -- the lift `g̃ : Ñ → M̃`
      ∀ (T : IdealSheafPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E} (g : AnalyticMap N T.M)
        (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g),
        ∃ g' : AnalyticMap (P (T.pullback g hg)).space (P T).space,
          -- `g̃` is over `g`
          (∀ q, (P T).map (g' q) = g ((P (T.pullback g hg)).map q)) ∧
          -- `g̃` is a local analytic isomorphism
          IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g' ∧
          -- `g̃` maps the fibre over `y` bijectively onto the fibre over `g y`
          (∀ y : N, Set.BijOn g' ((P (T.pullback g hg)).map ⁻¹' {y}) ((P T).map ⁻¹' {g y})) ∧
          -- `g̃` is the only continuous map over `g`
          ∀ φ : (P (T.pullback g hg)).space → (P T).space, Continuous φ →
            (∀ q, (P T).map (φ q) = g ((P (T.pullback g hg)).map q)) → φ = g' :=
  ⟨fun h => ⟨h.isPullbackAlong, h.exists_lift⟩, fun h => ⟨h.1, h.2⟩⟩

open scoped Manifold ContDiff in
/-- A compatible family assignment `P` on the pairs commutes with closed embeddings when, for pairs
`(M, I)` and `(N, J)` and a closed embedding of analytic manifolds `τ : N → M` along which `I` is
the push-forward of `J`, the family `P(M, I)` is the push-forward of `P(N, J)` along `τ` (the last
sentence of [Wlo09, Theorem 2.0.3], read as [Kol07, Theorem 35 (5)] and [Kol07, 34.3]). -/
example {𝕜 : Type} [RCLike 𝕜] (P : CompatibleFamilyAssignment (IdealSheafPair.{u, v} 𝕜)) :
    IdealSheafPair.CommutesWithClosedEmbeddings P ↔
      ∀ (T T' : IdealSheafPair.{u, v} 𝕜) (τ : C^ω⟮𝓘(𝕜, T'.E), T'.M; 𝓘(𝕜, T.E), T.M⟯),
        -- `I` is the push-forward of `J` along the closed embedding `τ`
        T.I.IsPushforwardAlong T'.I τ →
          -- `P(M, I)` is the push-forward of `P(N, J)` along `τ`
          (P T).IsPushforwardAlong (P T') τ :=
  Iff.rfl

/-- **Włodarczyk's functorial locally finite principalization** [Wlo09, Theorem 2.0.3], over
`𝕜 = ℝ` or `𝕜 = ℂ`, the analytic counterpart of Kollár's functorial principalization
[Kol07, Theorem 35] for an empty boundary. There is a compatible family assignment `P` on the
pairs `(M, I)` of an analytic manifold `M` over `𝕜`, modelled on a finite-dimensional space, and an
ideal sheaf `I` on `M` with nonzero stalks (`CompatibleFamilyAssignment (IdealSheafPair 𝕜)`) —
to each pair an analytic map `prin_I : M̃ → M` which over an open neighbourhood `U_K` of every
compact `K ⊆ M` splits, compatibly across compacts, into a finite succession of blow-ups
`U_K = U_0 ← U_1 ← ⋯ ← U_r` with smooth centres `C_i ⊆ U_i` and composite `σ_K : U_r → U_K` —
such that
* every value `P(M, I)` is a locally finite principalization of `I`
  (`IdealSheaf.IsLocallyFinitelyPrincipalizedBy`): with exceptional divisors `E_i` (the boundaries
  started at the empty boundary `⊤`), `prin_I` is proper and every `U_K` has compact closure;
  (1) every centre `C_i` is smooth; (2) every `E_i` has simple normal crossings with `C_i`, and
  `E_r` has simple normal crossings (`FiniteSuccession.HasSncBoundaries`); (3) the total transform
  `σ_K^*(I|_{U_K})` is, near every point, the ideal of an effective combination of the components of
  `E_r` through it (`IdealSheaf.IsMulBoundaryMonomial`, with the unit ideal `⊤` as its first
  factor), and the total transform `prin_I^*(I)` on `M̃` is a normal-crossings divisor
  (`IdealSheaf.IsNormalCrossingsDivisor`); and `prin_I` is an isomorphism over the complement of
  the support of `I` (`AnalyticMap.IsIsoOver`);
* `P` commutes with local analytic isomorphisms
  (`IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms`): for a local analytic isomorphism
  `g : N → M` of manifolds modelled on one space and the pair `(N, g^*I)`
  (`IdealSheafPair.pullback`), over every pair of compacts `K' ⊆ N`, `K ⊆ M` with
  `g(U_{K'}) ⊆ U_K` the succession of `P(N, g^*I)` over `U_{K'}` is the pull-back along `g` of the
  succession of `P(M, I)` over `U_K`, up to blow-ups with empty centre
  (`FiniteSuccession.IsPullbackUpToEmptyAlong`; [Wlo09, Theorem 3.5.1 (2)]); and there is a unique
  continuous map `g̃ : Ñ → M̃` over `g` between the spaces of `P(N, g^*I)` and `P(M, I)`, which is
  analytic, a local analytic isomorphism, and maps every fibre of `prin_{g^*I}` bijectively onto
  the fibre of `prin_I` over the image point, so that `Ñ` is the fibre product `N ×_M M̃`;
* `P` commutes with closed embeddings (`IdealSheafPair.CommutesWithClosedEmbeddings`): for pairs
  `(M, I)` and `(N, J)` and a closed embedding of analytic manifolds `τ : N → M`
  (an analytic embedding with closed image) along which `I` is the push-forward of `J` — the ideal
  of the closed submanifold `τ(N)` lies in `I`, and `J = τ^*I` (`IdealSheaf.IsPushforwardAlong`) —
  and compacts `K' ⊆ N`, `K ⊆ M` with `τ(U_{K'}) ⊆ U_K`, the succession of `P(M, I)` over `U_K` is
  the push-forward along `τ` of the succession of `P(N, J)` over `U_{K'}`, up to blow-ups whose
  centres lie outside the part over `τ(U_{K'})` (`FiniteSuccession.IsPushforwardUpToEmptyAlong`;
  [Kol07, 34.3]).

Włodarczyk's (4), that the factorization over a larger compact restricts to the factorization over
a smaller one, is the compatibility of the family: the succession over `K ⊆ K'`, restricted to
`U_K`, is an extension of the succession over `K`, the same blow-ups with isomorphisms interspersed
(`ExtensionCompatibleFamily.isExtensionOf_restrict`; [Wlo09, Definition 3.2.6]). Centres of
codimension one are admitted, as in [Wlo09, Remark (1) after Theorem 2.0.3]: the blow-up of such a
centre is an isomorphism, and the centre becomes a component of the exceptional divisor.

Relation to the source.
* **Translation.** `P` is Włodarczyk's principalization as a rule on all pairs $(M, I)$, the
  morphism $\mathrm{prin}$ of his last sentence: for the pair `T = (M, I)`, `P T` is the compatible
  family of $\mathrm{prin}_I \colon \tilde M \to M$, and
  `T.I.IsLocallyFinitelyPrincipalizedBy (P T)` is his "there exists a locally finite
  principalization of $I$", with clauses (1)–(3).
* **Correction.** The hypothesis that $I$ has nonzero stalks (the field `isNonzeroEverywhere` of
  the pair) is tacit in the source: otherwise the total transform $\sigma^{r*}(I)$ could not be the
  ideal of a divisor. Kollár states it explicitly, for an ideal sheaf "not zero on any irreducible
  component" [Kol07, Theorem 35]. The ideal sheaves with a zero stalk are not inputs, so nothing is
  asserted of them.
* **Interpretation.** In Włodarczyk's clause (3), the total transform $\sigma^{r*}(I)$ "is the ideal
  of a simple normal crossing divisor $\tilde E_U$ which is a locally finite combination of the
  irreducible components of the divisor $E_{U_r}$": the exponents of $\tilde E_U$ are read at each
  point, $\tilde E_U$ near a point being a combination of the components of $E_{U_r}$ through it.
* **Interpretation.** Włodarczyk's sheaf of ideals $\tilde I$ on $\tilde M$, which none of his
  clauses mentions, is read as the total transform $\mathrm{prin}_I^*(I)$; it is asserted to be a
  normal-crossings divisor (`IdealSheaf.IsNormalCrossingsDivisor`), the form of clause (3) that is
  local on $\tilde M$.
* **Translation.** "Embeddings of ambient varieties" in the last sentence is read as Kollár's
  commutation with closed embeddings [Kol07, Theorem 35 (5)], in the form of [Kol07, 34.3] for an
  empty boundary: $B(X, I_X) = j_* B(Y, I_Y)$ for a closed embedding $j$ of smooth varieties with
  $\mathcal{O}_X / I_X = j_*(\mathcal{O}_Y / I_Y)$, here `I.IsPushforwardAlong J τ` with the
  closed embedding `τ` (an analytic embedding with closed image), whose image is a closed
  submanifold: the ideal of the image (`vanishingStalk`) lies in `I`, and `J = τ^*I`. This is
  Włodarczyk's $I = \tau_*(J) \cdot \mathcal{O}_M$ [Wlo09, Remark (3) after Theorem 2.0.3], whose
  canonical resolution has the centres $\tau(C_i)$ of that of $J$ [Wlo09, Theorem 3.5.1 (3)]. The
  proof follows Kollár's derivation from his Claim 71.2 [Kol07, 72], the commutation of the marked
  order reduction with closed embeddings, through [Kol07, Theorem 107 (3)] and
  [Kol07, Theorem 103 (3)] at the mark `1`, the value of `P`.
* **Restatement.** The commutation with closed embeddings is stated over every pair of compact
  sets, as the push-forward of a succession up to blow-ups whose centres lie outside the part over
  $\tau(U_{K'})$ (`FiniteSuccession.IsPushforwardUpToEmptyAlong`): the succession of `P(M, I)` over
  $U_K$ also blows up centres over $U_K \setminus \tau(U_{K'})$, which the succession over $U_{K'}$
  does not see. The strict transforms of $\tau(N)$ are not formed: the relation is stated through
  embeddings of the stages, over $\tau$, with closed images containing every centre point over
  $\tau(U_{K'})$ and along which the centres pull back.
* **Restatement.** The commutation with local analytic isomorphisms is stated in two forms: over
  every pair of compact sets, as the relation between two successions of
  [Wlo09, Theorem 3.5.1 (2)], and globally, as the lift of $g \colon N \to M$ to a local analytic
  isomorphism $\tilde g \colon \tilde N \to \tilde M$ over $g$ identifying $\tilde N$ with the fibre
  product $N \times_M \tilde M$, the "natural lifting" of [Wlo09, Theorem 2.0.1 (3)]; the fibre
  product is stated pointwise, as the bijection of $\tilde g$ between the fibres over corresponding
  points.
* **Interpretation.** The exact equality for a surjective local analytic isomorphism
  [Wlo09, Theorem 3.5.1 (1)] has no counterpart per pair of compact sets: for $g$ the identity and
  compacts $K' \subsetneq K$ with a centre of the succession over $U_K$ lying over
  $U_K \setminus U_{K'}$, the succession induced over $U_{K'}$ has an empty centre which the
  succession over $U_{K'}$ omits. Its global content is read as: for surjective $g$ the lift
  $\tilde g$ is a surjective local analytic isomorphism identifying $\tilde N$ with
  $N \times_M \tilde M$.
* **Interpretation.** Włodarczyk's analytic manifold is read as pure-dimensional: the local analytic
  isomorphisms relate manifolds modelled on one space, and a closed embedding relates manifolds
  modelled on two, so the pairs carry their model space and `P` is one assignment over all
  finite-dimensional model spaces over $\mathbb{K}$.
* **Strengthening.** Every neighbourhood $U_K$ has compact closure, which the source does not ask.
  It makes the commutations apply, for a local analytic isomorphism or a closed embedding
  $g \colon N \to M$, to every compact set $K'$ of $N$: the closure $K$ of $g(U_{K'})$ is compact,
  and $g(U_{K'}) \subseteq K \subseteq U_K$.
* **Strengthening.** The clause that $\mathrm{prin}_I$ is an isomorphism over the complement of the
  support of $I$ is not in [Wlo09, Theorem 2.0.3]; it is [Wlo09, Lemma 4.0.3] and, for an empty
  boundary, [Kol07, Theorem 35 (3)].
* **Strengthening.** Each centre has a single codimension, and empty centres are admitted (their
  blow-ups are isomorphisms).
* **Gap.** Compared with Kollár's functorial principalization [Kol07, Theorem 35]
  (`AlgebraicGeometry.exists_functorial_principalization`): the inputs are pairs $(M, I)$, Kollár's
  triples with an empty boundary; the values are compatible families over the compact sets rather
  than single blow-up sequences, as Kollár's passage to analytic spaces provides them [Kol07, 44];
  the commutation with smooth morphisms [Kol07, 34.1] is asserted, in Włodarczyk's form, for local
  analytic isomorphisms only, the smooth morphisms of relative dimension zero; and the commutation
  with change of fields [Kol07, 34.2] has no counterpart.

Source statement: [Wlo09, Theorem 2.0.3, p. 35]

Source statement: [Kol07, Theorem 35] (analytic manifolds, empty boundary; item 44) -/
theorem exists_functorial_principalization (𝕜 : Type) [RCLike 𝕜] :
    ∃ P : CompatibleFamilyAssignment (IdealSheafPair.{u, v} 𝕜),
      -- (1)–(3)
      (∀ T : IdealSheafPair.{u, v} 𝕜, T.I.IsLocallyFinitelyPrincipalizedBy (P T)) ∧
      -- last sentence, 3.5.1 (2) and 2.0.1 (3)
      IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms P ∧
      -- last sentence, 34.3 with `E = ∅`
      IdealSheafPair.CommutesWithClosedEmbeddings P :=
  sorry

end AnalyticManifold

end Principalization

/-! ### Embedded desingularization -/

section EmbeddedDesingularization

open TopologicalSpace

namespace AnalyticManifold

/-! #### The conditions of Włodarczyk's embedded desingularization -/

/-- The closed analytic subspace defined by `J` is reduced: every stalk `J_x` is a radical
ideal. -/
example {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : AnalyticManifold.{u} 𝕜 E} (J : IdealSheaf M) :
    J.IsReduced ↔ ∀ x : M, (J.stalkIdeal x).IsRadical :=
  Iff.rfl

/-- The simple locus `Reg(Y)` of the closed analytic subspace `Y` with ideal sheaf `J`, the set of
points where `Y` is smooth: the points at which the local ring `𝒪_{M,x}/J_x` of `Y` is regular
[Wlo09, Theorem 2.0.2 (2)]. A point off `Y` is not in it, the zero ring not being local. -/
example {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : AnalyticManifold.{u} 𝕜 E} (J : IdealSheaf M) (x : M) :
    x ∈ J.regularLocus ↔ IsRegularLocalRing (IdealSheaf.stalkRing M x ⧸ J.stalkIdeal x) :=
  Iff.rfl

/-- `B` is the reduced ideal sheaf of a simple normal crossings family of hypersurfaces with which
the closed subspace `Y` has simple normal crossings transversally: at every point of `Y` a chart
adapted to `Y`, of the codimension of `Y` at that point, is a simple normal crossings chart of the
family, and the coordinates cutting out `Y` are distinct from those of the hypersurfaces through
the point [Wlo09, Theorem 2.0.2 (3)]. -/
example {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : AnalyticManifold.{u} 𝕜 E} (B Y : IdealSheaf M) :
    B.IsSncBoundaryTransversalTo Y ↔
      ∃ (n : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (G : Manifold.HypersurfaceFamily M),
        -- `B` is the reduced ideal sheaf of the simple normal crossings family `G`
        G.IsSnc ψ ∧ G.idealSheaf = B ∧
        -- at every point `a` of `Y`, a chart adapted to `Y` is an snc chart of `G` at `a`
        ∀ a ∈ Y.support, ∃ (c : ℕ) (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n)
          (cidx : {j // a ∈ G.hyp j} → Fin n),
          Manifold.IsAdaptedChart ψ Y.support φ σ ∧ G.IsSncChartAt ψ φ a cidx ∧
          -- and no hypersurface through `a` is cut out by a coordinate of `Y`
          ∀ j, cidx j ∉ Set.range σ :=
  Iff.rfl

/-- A finite succession `S : M = U_0 ← U_1 ← ⋯ ← U_r`, with composite `σ`, desingularizes the
closed subspace `Y` with ideal sheaf `I` when, with exceptional divisors `E_i` (the boundaries
started at the empty boundary `⊤`) and strict transforms `Y_i` of `Y`, `Ỹ = Y_r`: its centres
are smooth, every `E_i` has simple normal crossings with the centre `C_i` and `E_r` has simple
normal crossings, no point of a centre lies over a point where `Y` is smooth, the support of `E_r`
is the preimage of the singular locus of `Y`, `Ỹ` is smooth and has simple normal crossings with
`E_r`, and `σ^*(I_Y) = I_Ỹ · I_Ẽ` with `Ẽ` a combination of the components of `E_r`
[Wlo09, Theorem 2.0.2 (1)–(3), (6)]. -/
example {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : AnalyticManifold.{u} 𝕜 E} (I : IdealSheaf M) (S : FiniteSuccession M) :
    I.IsDesingularizedBy S ↔
      -- the centres `C_i` are smooth
      (∀ i, (S.center i).IsNonsingular) ∧
      -- (1) every `E_i` has simple normal crossings with `C_i`, and `E_r` has simple normal
      -- crossings
      S.HasSncBoundaries ⊤ ∧
      -- (2) no point of a centre lies over a point of `Reg(Y)`
      (∀ i : Fin S.length, ∀ x ∈ (S.center i).support,
        S.stageMap i.castSucc x ∉ I.regularLocus) ∧
      -- the support of `E_r` is the preimage of `Sing(Y) = Y ∖ Reg(Y)`
      (S.boundarySeq ⊤ (Fin.last S.length)).support =
        S.composite ⁻¹' (I.support \ I.regularLocus) ∧
      -- (3) `Ỹ = Y_r` is smooth
      (S.strictTransformSubspaceSeq I (Fin.last S.length)).IsNonsingular ∧
      -- (3) and has simple normal crossings with `E_r`, transversally
      (S.boundarySeq ⊤ (Fin.last S.length)).IsSncBoundaryTransversalTo
        (S.strictTransformSubspaceSeq I (Fin.last S.length)) ∧
      -- (6) `σ^*(I_Y) = I_Ỹ · I_Ẽ`
      IdealSheaf.IsMulBoundaryMonomial (I.pullback S.composite S.composite.contMDiff)
        (S.strictTransformSubspaceSeq I (Fin.last S.length))
        (S.boundarySeq ⊤ (Fin.last S.length)) :=
  IdealSheaf.isDesingularizedBy_iff I S

/-- The compatible family `F` is a locally finite embedded desingularization of the closed
subspace `Y` with ideal sheaf `I`, with `res_{Y,M} = F.map` and, over the neighbourhood `U_K` of a
compact `K`, the succession `F.seq K : U_K = U_0 ← ⋯ ← U_r` [Wlo09, Theorem 2.0.2]: `res_{Y,M}` is
proper, it is an isomorphism off the singular locus `Sing(Y) = Y ∖ Reg(Y)`, every `F.seq K`
desingularizes `Y ∩ U_K` (clauses (1)–(3) and (6)), has no empty centre and has every centre of
codimension at least two or of codimension one inside the exceptional divisor of its stage, and
`M̃` carries an exceptional divisor `E` and a strict transform `Ỹ` which, read on the last stage
`U_r` of `F.seq K` through the identification `U_r ≅ res_{Y,M}⁻¹(U_K)`, are `E_r` and `Y_r` for
every compact `K`: `E` is the reduced ideal sheaf of a simple normal crossings family of
hypersurfaces, with which `Ỹ` has simple normal crossings, transversally, and
`res_{Y,M}^*(I_Y) = I_Ỹ · I_Ẽ` with `Ẽ` near every point an effective combination of the
components of `E`. -/
example {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : AnalyticManifold.{u} 𝕜 E} (I : IdealSheaf M) (F : ExtensionCompatibleFamily M) :
    I.IsLocallyFinitelyDesingularizedBy F ↔
      -- `res_{Y,M}` is proper
      IsProperMap F.map ∧
      -- and an isomorphism off the singular locus `Sing Y` of `Y`
      F.map.IsIsoOver (I.support \ I.regularLocus)ᶜ ∧
      -- (∗) over a neighbourhood of every compact, with (1)–(3) and (6)
      (∀ K : Compacts M, (I.restrict (F.nhd K)).IsDesingularizedBy (F.seq K)) ∧
      -- no centre is empty
      (∀ (K : Compacts M) (i : Fin (F.seq K).length), (F.seq K).center i ≠ ⊤) ∧
      -- every centre has codimension at least two, or has codimension one and lies in the
      -- exceptional divisor of its stage
      (∀ (K : Compacts M) (i : Fin (F.seq K).length), 2 ≤ (F.seq K).codim i ∨
        (F.seq K).codim i = 1 ∧ ∀ x, ((F.seq K).boundarySeq ⊤ i.castSucc).stalkIdeal x ≤
          ((F.seq K).center i).stalkIdeal x) ∧
      -- the divisor `E` and the strict transform `Ỹ` (here `Y`) on `M̃`
      ∃ D Y : IdealSheaf F.space,
        -- over every compact, `E` and `Ỹ` are `E_r` and `Y_r`
        (∀ K : Compacts M,
          D.pullback (F.toSpace K) (F.toSpace K).contMDiff =
              (F.seq K).boundarySeq ⊤ (Fin.last (F.seq K).length) ∧
            Y.pullback (F.toSpace K) (F.toSpace K).contMDiff =
              (F.seq K).strictTransformSubspaceSeq (I.restrict (F.nhd K))
                (Fin.last (F.seq K).length)) ∧
        -- (1), (3) `E` is a simple normal crossings divisor on `M̃`, with which `Ỹ` has simple
        -- normal crossings, transversally
        D.IsSncBoundaryTransversalTo Y ∧
        -- (6) `res_{Y,M}^*(I_Y) = I_Ỹ · I_Ẽ`
        IdealSheaf.IsMulBoundaryMonomial (I.pullback F.map F.map.contMDiff) Y D :=
  IdealSheaf.isLocallyFinitelyDesingularizedBy_iff I F

/-- An embedded pair `(M, Y)`, the input of the embedded desingularization, is an analytic manifold
`M` over `𝕜` on a finite-dimensional model space `E` with a reduced closed analytic subspace
`Y ⊆ M`, given by its ideal sheaf. -/
example {𝕜 : Type} [RCLike 𝕜] (T : EmbeddedPair.{u, v} 𝕜) :
    -- the model space is finite-dimensional
    FiniteDimensional 𝕜 T.E ∧
    -- the subspace is reduced
    T.Y.IsReduced :=
  ⟨T.finiteDimensional, T.isReduced⟩

open scoped Manifold ContDiff in
/-- The pull-back of the embedded pair `(M, Y)` along a local analytic isomorphism `g : N → M` of
manifolds modelled on `E` is the embedded pair `(N, g^{-1}(Y))`. -/
example {𝕜 : Type} [RCLike 𝕜] (T : EmbeddedPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E}
    (g : AnalyticMap N T.M) (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g) :
    (T.pullback g hg).M = N ∧ (T.pullback g hg).Y = T.Y.pullback g g.contMDiff :=
  ⟨rfl, rfl⟩

open scoped Manifold ContDiff in
/-- A compatible family assignment `R` on the embedded pairs commutes with local analytic
isomorphisms when, for a local analytic isomorphism `g : N → M` of manifolds modelled on one space
and the embedded pair `(N, g^{-1}(Y))`, the family `R(N, g^{-1}(Y))` is the pull-back of `R(M, Y)`
along `g` (the first half of [Wlo09, Theorem 2.0.2 (4)], read as [Wlo09, Theorem 3.5.1 (2)]). -/
example {𝕜 : Type} [RCLike 𝕜] (R : CompatibleFamilyAssignment (EmbeddedPair.{u, v} 𝕜)) :
    EmbeddedPair.CommutesWithLocalAnalyticIsomorphisms R ↔
      ∀ (T : EmbeddedPair.{u, v} 𝕜) {N : AnalyticManifold.{u} 𝕜 T.E} (g : AnalyticMap N T.M)
        -- `g` is a local analytic isomorphism
        (hg : IsLocalDiffeomorph 𝓘(𝕜, T.E) 𝓘(𝕜, T.E) ω g),
          -- `R(N, g^{-1}(Y))` is the pull-back of `R(M, Y)` along `g`
          (R (T.pullback g hg)).IsPullbackAlong (R T) g :=
  Iff.rfl

open scoped Manifold ContDiff in
/-- A compatible family assignment `R` on the embedded pairs commutes with closed embeddings of
ambient manifolds when, for embedded pairs `(M, Y)` and `(N, Y')` and a closed embedding of
analytic manifolds `τ : N → M` along which the ideal sheaf of `Y` is the push-forward of that of
`Y'`, such that no connected component of `N` lies in `Y'`, the family `R(M, Y)` is the
push-forward of `R(N, Y')` along `τ` (the second half of [Wlo09, Theorem 2.0.2 (4)], read as
[Kol07, 34.3]). -/
example {𝕜 : Type} [RCLike 𝕜] (R : CompatibleFamilyAssignment (EmbeddedPair.{u, v} 𝕜)) :
    EmbeddedPair.CommutesWithClosedEmbeddings R ↔
      ∀ (T T' : EmbeddedPair.{u, v} 𝕜) (τ : C^ω⟮𝓘(𝕜, T'.E), T'.M; 𝓘(𝕜, T.E), T.M⟯),
        -- `I_Y` is the push-forward of `I_{Y'}` along the closed embedding `τ`
        T.Y.IsPushforwardAlong T'.Y τ →
        -- no connected component of `N` lies in `Y'`
        T'.Y.IsNonzeroEverywhere →
          -- `R(M, Y)` is the push-forward of `R(N, Y')` along `τ`
          (R T).IsPushforwardAlong (R T') τ :=
  Iff.rfl

/-- **Włodarczyk's locally finite embedded desingularization** [Wlo09, Theorem 2.0.2], over
`𝕜 = ℝ` or `𝕜 = ℂ`, with its commutation with local analytic isomorphisms and with closed
embeddings of ambient manifolds. There is a compatible family assignment `R` on the embedded pairs
`(M, Y)` of an analytic manifold `M` over `𝕜`, modelled on a finite-dimensional space, and a
reduced closed analytic subspace `Y ⊆ M` with ideal sheaf `I_Y`
(`CompatibleFamilyAssignment (EmbeddedPair 𝕜)`) — to each pair an analytic map `res_{Y,M} : M̃ → M`
which over an open neighbourhood `U_K` of every compact `K ⊆ M` splits, compatibly across
compacts, into a finite succession of blow-ups `U_K = U_0 ← U_1 ← ⋯ ← U_r` with smooth closed
centres `C_i ⊆ U_i` and composite `σ_K : U_r → U_K` — such that
* every value `R(M, Y)` is a locally finite embedded desingularization of `Y`
  (`IdealSheaf.IsLocallyFinitelyDesingularizedBy`): `res_{Y,M}` is proper and an isomorphism off
  the singular locus `Sing(Y) = Y ∖ Reg(Y)`; over every compact the succession satisfies (1)–(3)
  and (6) (`IdealSheaf.IsDesingularizedBy`), has no empty centre, and has every centre of
  codimension at least two or of codimension one inside the exceptional divisor of its stage; and
  `M̃` carries a divisor `E` and a strict transform `Ỹ` restricting to `E_r` and `Y_r` over every
  compact, with (1), (3) and (6) on `M̃`;
* (4) `R` commutes with local analytic isomorphisms
  (`EmbeddedPair.CommutesWithLocalAnalyticIsomorphisms`): for a local analytic isomorphism
  `g : N → M` of manifolds modelled on one space and compacts `K' ⊆ N`, `K ⊆ M` with
  `g(U_{K'}) ⊆ U_K`, the succession of `R(N, g^{-1}(Y))` (`EmbeddedPair.pullback`) over `U_{K'}`
  is the pull-back along `g` of the succession of `R(M, Y)` over `U_K`, up to blow-ups with empty
  centre (`FiniteSuccession.IsPullbackUpToEmptyAlong`; [Wlo09, Theorem 3.5.1 (2)]);
* (4) `R` commutes with closed embeddings of ambient manifolds
  (`EmbeddedPair.CommutesWithClosedEmbeddings`): for a closed embedding of analytic manifolds
  `τ : N → M` (an analytic embedding with closed image) along which `I_Y` is the push-forward of
  `I_{Y'}` (`IdealSheaf.IsPushforwardAlong`: `τ(N)` contains `Y`, and `Y' = τ^{-1}(Y)`), no
  connected component of `N` lying in `Y'`, and compacts `K' ⊆ N`, `K ⊆ M` with
  `τ(U_{K'}) ⊆ U_K`, the succession of `R(M, Y)` over `U_K` is the push-forward along `τ` of that
  of `R(N, Y')` over `U_{K'}`, up to blow-ups whose centres lie outside the part over `τ(U_{K'})`
  (`FiniteSuccession.IsPushforwardUpToEmptyAlong`; [Kol07, 34.3]).

Włodarczyk's (5), that the factorization over a larger compact restricts to the factorization over
a smaller one, is the compatibility of the family: the succession over `K ⊆ K'`, restricted to
`U_K`, is an extension of that over `K` (`ExtensionCompatibleFamily.isExtensionOf_restrict`;
[Wlo09, Definition 3.2.6]).

Relation to the source.
* **Translation.** `R` is Włodarczyk's embedded desingularization as a rule on all pairs $(M, Y)$,
  the morphism $\mathrm{res}$ of his clause (4): `T.Y.IsLocallyFinitelyDesingularizedBy (R T)` is
  his conclusion for the embedded pair `T = (M, Y)`, with `(R T).map` his $\mathrm{res}_{Y,M}$.
  `I.regularLocus` is his $\operatorname{Reg}(Y)$, the points at which the local ring
  $\mathcal{O}_{M,x}/I_x$ of $Y$ is regular, and
  `((R T).seq K).strictTransformSubspaceSeq (I.restrict ((R T).nhd K)) i` is $Y_i$.
* **Restatement.** Włodarczyk's divisor $E$ and strict transform $\tilde Y$ on $\tilde M$ are the
  `E` and `Y` of `exists_divisor_strictTransform`: on the last stage
  $U_r \cong \mathrm{res}_{Y,M}^{-1}(U_K)$ over every compact (`(R T).toSpace K`) they are $E_r$
  and $Y_r$, and his clauses (1), (3) and (6) are asserted on $\tilde M$ and on every $U_r$. The
  support identity $|E| = \mathrm{res}_{Y,M}^{-1}(\operatorname{Sing} Y)$ and the smoothness of
  $\tilde Y$ are stated on every $U_r$ only, from which they follow on $\tilde M$
  (`IdealSheaf.IsGloballyDesingularizedBy.support_eq`,
  `IdealSheaf.IsGloballyDesingularizedBy.isNonsingular`).
* **Strengthening.** That $\mathrm{res}_{Y,M}$ is an isomorphism over
  $M \setminus \operatorname{Sing}(Y)$, whose preimage is, over each $U_K$, the complement of the
  simple normal crossings divisor $E_r$, hence dense, says more than Włodarczyk's "bimeromorphic".
  Over $\operatorname{Reg}(Y)$ it follows from his clause (2); over $M \setminus Y$ it is not in
  Theorem 2.0.2 but holds for his construction, an initial segment of the principalization of
  $I_Y$, which is an isomorphism over $M \setminus V(I_Y)$ [Wlo09, Lemma 4.0.3].
* **Interpretation.** His "the support of the divisor $E$ is the exceptional locus of
  $\mathrm{res}_{Y,M}$" is read as $|E_r| = \sigma_K^{-1}(\operatorname{Sing} Y)$ for every
  compact $K$.
* **Interpretation.** Clauses (3) and (6) are read at each point: "has only simple normal crossings
  with the exceptional divisor $E_r$", said of $\tilde Y$, with the codimension of $\tilde Y$ read
  at each point and transversally (`IsSncBoundaryTransversalTo`); in
  $\sigma^*(I_Y) = I_{\tilde Y} I_{\tilde E}$, $\tilde E$ near a point is a combination of the
  components of $E_r$ through it, rather than "a locally finite combination of the irreducible
  components of the divisor $E_{U_r}$".
* **Correction.** The hypothesis that $Y$ is reduced (`isReduced`) is tacit in the source:
  Włodarczyk's $Y$ is "an analytic subspace", but the algebraic original of clause (6) assumes "a
  reduced closed subscheme" [Wlo05, Theorem 4.7.1], and his conclusion fails for the double line
  $Y = V(x^2) \subset \mathbb{K}^2$. His centres have codimension at least two
  [Wlo09, Remark (2) after Theorem 2.0.3], so their images in $\mathbb{K}^2$ form a closed
  discrete set $P$, $\sigma$ is an isomorphism over $\mathbb{K}^2 \setminus P$, and no component
  of $E_r$ meets the preimage $\tilde p$ of a point $p$ of the line off $P$. By (6),
  $I_{\tilde Y, \tilde p} = (x^2)$: either $\tilde Y$ has the non-regular local ring
  $\mathcal{O}/(x^2)$, against (3), or, read as reduced, $I_{\tilde Y} = (x)$ and (6) fails. The
  same argument, with images of dimension at most $\dim M - 2$, applies whenever $Y$ is
  generically non-reduced along a component of dimension $\dim M - 1$. Blowing up the line
  itself, a formal codimension-one blow-up of his Remark (1), would satisfy (3) and (6) with
  $\tilde Y = \emptyset$, but this is excluded by his Remark (2) and by "the support of the
  divisor $E$ is the exceptional locus".
* **Gap.** Non-reduced subspaces with no generically non-reduced component of dimension
  $\dim M - 1$ are not covered: those with embedded components, such as
  $V(x^2, xy) \subset \mathbb{K}^2$, and those generically non-reduced only along components of
  codimension at least two, such as $V(x^2, y) \subset \mathbb{K}^3$. The counterexample does
  not apply to them.
* **Interpretation.** Włodarczyk's manifold `M` is read as pure-dimensional: local analytic
  isomorphisms relate manifolds modelled on one space and closed embeddings manifolds modelled on
  two, so the embedded pairs carry their model space and `R` is one assignment over all
  finite-dimensional model spaces.
* **Strengthening.** The factorization is indexed by the compacts `K` of `M`, not only by
  Włodarczyk's compact sets $Z \subset Y$, with $K \subseteq U_K$ made explicit.
* **Gap.** The commutation with local analytic isomorphisms is stated over every pair of compact
  sets only. The lift of $g \colon N \to M$ to a map $\tilde N \to \tilde M$ identifying
  $\tilde N$ with $N \times_M \tilde M$, which the principalization theorem states, is not stated
  here, and with it the global content of the exact equality for a surjective $g$
  [Wlo09, Theorem 3.5.1 (1)], which has no counterpart per pair of compact sets.
* **Translation.** "Embeddings of ambient varieties" in clause (4) is read as Kollár's commutation
  with closed embeddings [Kol07, 34.3] over every pair of compact sets, as the last sentence of
  [Wlo09, Theorem 2.0.3] is, the stages of the succession over $N$ embedding over $\tau$ into
  those of the succession over $M$.
* **Restatement.** That clause is asserted when no connected component of $N$ lies in $Y$,
  Kollár's "$0 \neq I_Y$": on such a component the embedded desingularization of $Y \subseteq N$
  is trivial, while that of $Y \subseteq M$ may blow up centres on it where other components of
  $Y$ meet it.
* **Strengthening.** Each centre has a single codimension.
* **Translation.** That no centre is empty is the first half of Włodarczyk's Remark (2) after
  Theorem 2.0.3, in the empty blow-up convention of [Kol07, 32]. The codimension clause reads its
  second half, centres of codimension at least two, with his Remark (1), that the blow-up of a
  centre of codimension one is an isomorphism making it a component of the exceptional divisor: a
  centre of codimension one lies in the exceptional divisor already. No centre has codimension
  zero, since the centres lie over $\operatorname{Sing}(Y)$, which for a reduced $Y$ contains no
  smooth hypersurface germ, and no open set.
* **Gap.** Centres of codimension one are not removed from the successions. Deleting their steps
  would leave $\mathrm{res}_{Y,M}$, the exceptional divisors and the strict transforms unchanged
  (the equation of such a centre is a nonzerodivisor modulo the strict transform at that stage),
  but a centre of codimension one of a submanifold $N$ of positive codimension pushes forward to
  a centre of codimension at least two of $M$, so the deletion is incompatible with the
  commutation with closed embeddings in its push-forward form. Włodarczyk notes that such blow-ups
  "may occur for some marked ideals induced on subvarieties of ambient varieties" and "determine
  blow-ups of ambient varieties which are not isomorphisms" [Wlo09, Remark after Lemma 5.3.7].

Source statement: [Wlo09, Theorem 2.0.2] -/
theorem exists_embeddedDesingularization (𝕜 : Type) [RCLike 𝕜] :
    ∃ R : CompatibleFamilyAssignment (EmbeddedPair.{u, v} 𝕜),
      -- (1)–(3), (6), with `res_{Y,M}` proper and bimeromorphic, `E` and `Ỹ` on `M̃`
      (∀ T : EmbeddedPair.{u, v} 𝕜, T.Y.IsLocallyFinitelyDesingularizedBy (R T)) ∧
      -- (4), 3.5.1 (2)
      EmbeddedPair.CommutesWithLocalAnalyticIsomorphisms R ∧
      -- (4), 34.3
      EmbeddedPair.CommutesWithClosedEmbeddings R :=
  sorry

end AnalyticManifold

end EmbeddedDesingularization

/-! ### Resolution -/

section Resolution

open scoped CategoryTheory
open CategoryTheory (IsIso)

namespace AnalyticSpace

/-! #### The conditions of Kollár's Theorem 45 -/

/-- A morphism `π : R → X` of analytic spaces is a resolution when `R` is non-singular, `π` is
proper, and `π` is bimeromorphic (Kollár: birational [Kol07, (2)]; [Wlo09, Theorem 2.0.1]), read
onto its image: an isomorphism over an open subset of `X` whose preimage is dense in `R`. -/
example {K : Type} [RCLike K] {X R : AnalyticSpace.{u} K} (π : R ⟶ X) :
    π.IsResolution ↔
      -- `R` is non-singular
      R.IsNonsingular ∧
      -- `π` is proper
      IsProperMap π ∧
      -- `π` is an isomorphism over an open set whose preimage is dense
      ∃ U : Set X, IsOpen U ∧ π.IsIsoOver U ∧ Dense (π ⁻¹' U) :=
  Hom.isResolution_iff π

/-- A morphism `π : R → X` of analytic spaces is a strong resolution when it is a resolution,
changes nothing over the simple locus of `X`, and turns the singular locus into a simple normal
crossing divisor [Kol07, (3)]; these are clauses (1)–(3) of Theorem 45. -/
example {K : Type} [RCLike K] {X R : AnalyticSpace.{u} K} (π : R ⟶ X) :
    π.IsStrongResolution ↔
      -- (1) a resolution
      π.IsResolution ∧
      -- (2) an isomorphism over the simple locus `X^{ns}`
      π.IsIsoOver X.regularLocus ∧
      -- (3) `π⁻¹(Sing X)` is the support of a simple normal crossing divisor
      ∃ E : R.ClosedSubspace, E.IsSncBoundary ∧ E.support = π ⁻¹' X.singularLocus :=
  Hom.isStrongResolution_iff π

/-- A morphism `φ : X' → X` of analytic spaces is a local analytic isomorphism when every point of
`X'` has an open neighbourhood `U'` mapped by `φ` isomorphically onto an open subspace `X|_V`
[Wlo09, Theorem 2.0.1 (3)]. -/
example {K : Type} [RCLike K] {X' X : AnalyticSpace.{u} K} (φ : X' ⟶ X) :
    φ.IsLocalIso ↔
      ∀ x' : X', ∃ (U' : Set X') (V : Set X), IsOpen U' ∧ IsOpen V ∧ x' ∈ U' ∧
        -- an isomorphism `χ : X'|_{U'} ≅ X|_V` with `χ ≫ (X|_V → X) = (X'|_{U'} → X') ≫ φ`
        ∃ χ : X'.restrictSet U' ⟶ X.restrictSet V, IsIso χ ∧
          χ ≫ KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X V) =
            KLocallyRingedSpace.ofRestrict X'.toKLocallyRingedSpace (openOf X' U') ≫ φ :=
  Iff.rfl

/-- A morphism `f : Y → X` of analytic spaces is locally a finite composite of ambient blow-ups when
over every open `U ⊆ X` with compact closure the restriction of `f` to `f⁻¹(U)` is the composite of
a finite sequence of blow-ups with smooth centres of an ambient manifold, restricted to strict
transforms (`f.AmbientBlowUpFactorization U`) [Kol07, Theorem 45 (4), Warning 23];
[Wlo09, Theorem 2.0.2]. -/
example {K : Type} [RCLike K] {X Y : AnalyticSpace.{u} K} (f : Y ⟶ X) :
    f.IsLocallyFiniteAmbientBlowUpComposite ↔
      ∀ U : Set X, IsOpen U → IsCompact (closure U) → Nonempty (f.AmbientBlowUpFactorization U) :=
  Iff.rfl

/-- An input of the resolution theorem is a reduced `K`-analytic space. -/
example {K : Type} [RCLike K] (X : ReducedSpace.{u} K) : X.obj.IsReduced :=
  X.property

/-- A resolution assignment on the inputs gives every input `X` a `K`-analytic space `R(X)` and a
morphism `Π_X : R(X) → X` to its underlying space. -/
example {K : Type} [RCLike K]
    (R : ResolutionAssignment (ReducedSpace.{u} K)) (X : ReducedSpace.{u} K) :
    R.space X ⟶ X.obj :=
  R.map X

/-- A morphism `π : R → X` of analytic spaces is a strong resolution onto the closure of the simple
locus when it is a strong resolution (clauses (1)–(3) of Theorem 45, with properness and
bimeromorphy) whose image is the closure of the simple locus of `X`. -/
example {K : Type} [RCLike K] {X R : AnalyticSpace.{u} K} (π : R ⟶ X) :
    π.IsStrongResolutionOntoClosureRegularLocus ↔
      -- (1)–(3)
      π.IsStrongResolution ∧
      -- the image of `π` is the closure of the simple locus
      Set.range π = closure X.regularLocus :=
  Hom.isStrongResolutionOntoClosureRegularLocus_iff π

/-- A resolution assignment `R` on the inputs lifts local analytic isomorphisms when every
isomorphism `φ : X|_U → Y|_V` between open subspaces of two inputs lifts to exactly one morphism
`R(X)|_{Π_X⁻¹ U} → R(Y)|_{Π_Y⁻¹ V}` over `φ`, an isomorphism, and every local analytic isomorphism
`φ : X' → X` between inputs lifts to exactly one morphism `R(X') → R(X)` over `φ`, a local analytic
isomorphism. -/
example {K : Type} [RCLike K] (R : ResolutionAssignment (ReducedSpace.{u} K)) :
    R.LiftsLocalIsomorphisms ↔
      -- (5) a unique lift of every isomorphism between open subspaces of two inputs
      (∀ (X Y : ReducedSpace.{u} K) (U : Set X.obj) (V : Set Y.obj), IsOpen U → IsOpen V →
        ∀ φ : X.obj.restrictSet U ⟶ Y.obj.restrictSet V, IsIso φ →
          ∃ ψ : (R.space X).restrictSet (R.map X ⁻¹' U) ⟶
              (R.space Y).restrictSet (R.map Y ⁻¹' V),
            -- an isomorphism, and the only morphism over `φ`
            IsIso ψ ∧
              ∀ ψ', ψ' ≫ (R.map Y).restrictSet V = (R.map X).restrictSet U ≫ φ ↔ ψ' = ψ) ∧
      -- (5′) a unique lift of every local analytic isomorphism between inputs
      ∀ (X' X : ReducedSpace.{u} K) (φ : X'.obj ⟶ X.obj), φ.IsLocalIso →
        -- a local analytic isomorphism, and the only morphism over `φ`
        ∃ ψ : R.space X' ⟶ R.space X, ψ.IsLocalIso ∧ ∀ ψ', ψ' ≫ R.map X = R.map X' ≫ φ ↔ ψ' = ψ :=
  ⟨fun h => ⟨h.exists_lift_of_isIso, h.exists_lift_of_isLocalIso⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Resolution of analytic spaces** [Kol07, Theorem 45]; [Wlo09, Theorem 2.0.1], over `K = ℝ` or
`K = ℂ`. There is a resolution assignment `X ↦ (Π_X : R(X) → X)` on the reduced `K`-analytic
spaces (`ResolutionAssignment (ReducedSpace K)`) such that
* every `Π_X` is a strong resolution of `X` onto the closure of its simple locus
  (`Hom.IsStrongResolutionOntoClosureRegularLocus`): `Π_X` is proper and bimeromorphic onto its
  image, (1) `R(X)` is non-singular, (2) `Π_X` is an isomorphism over the simple locus
  `X.regularLocus`, (3) `Π_X⁻¹(X.singularLocus)` is the support of a simple normal crossing
  divisor of `R(X)`, and the image of `Π_X` is the closure of `X.regularLocus` (in neither source;
  see the relation to the source below);
* (4) over every relatively compact open subset of `X` the morphism `Π_X` is the composite of a
  finite sequence of blow-ups of smooth centres of an ambient manifold, restricted to strict
  transforms (`Hom.IsLocallyFiniteAmbientBlowUpComposite`);
* (5) `R` lifts local analytic isomorphisms (`ResolutionAssignment.LiftsLocalIsomorphisms`): every
  isomorphism between open subspaces of two inputs lifts to exactly one morphism between their
  preimages in the resolutions over it, an isomorphism; and every local analytic isomorphism
  `φ : X' → X` between inputs (`Hom.IsLocalIso`: locally an isomorphism onto an open subspace,
  injective or not) lifts to exactly one morphism `R(X') → R(X)` over it, itself a local analytic
  isomorphism ([Wlo09, Theorem 2.0.1 (3)]). Over every open on which `φ` is injective, the lift of
  `φ` restricts to the lift of the isomorphism of open subspaces
  (`ResolutionAssignment.LiftsLocalIsomorphisms.lift_restrict`).

Kollár's (4), "`Π_X` is projective over any compact subset of `X`", is split between the properness
of `Hom.IsResolution` and the factorization clause, whose ambient manifold is the disjoint union of
finitely many opens of `Kⁿ`, one per piece of a finite open cover of the relatively compact open,
with the identification with `Π_X` given piecewise. The non-singularity of `R(X)` is repeated by
(3), since `ClosedSubspace.IsSncBoundary` asks for a regular system of parameters at every point of
`R(X)`.

Relation to the source.
* **Translation.** `R.space X` and `R.map X` are Kollár's $R(X)$ and $\Pi_X$ for the input `X`,
  whose underlying space is `X.obj`; `X.regularLocus` is the set of simple points (his $X^{ns}$)
  and `X.singularLocus` its complement; clause (3) is a closed subspace `E` with `E.IsSncBoundary`
  and `E.support` equal to $\Pi_X^{-1}(\operatorname{Sing} X)$. Composition `≫` is in diagrammatic
  order: in (5), `ψ ≫ (R.map Y).restrictSet V = (R.map X).restrictSet U ≫ φ` is
  $\Pi_Y|_V \circ \psi = \varphi \circ \Pi_X|_U$, and `ψ ≫ R.map X = R.map X' ≫ φ` is
  $\Pi_X \circ \psi = \varphi \circ \Pi_{X'}$.
* **Interpretation.** Kollár's resolution is birational and Włodarczyk's bimeromorphic. Here $\Pi_X$
  is bimeromorphic onto its image: an isomorphism over an open set whose preimage is dense.
* **Gap.** Kollár states the theorem for any locally compact field $K$ of characteristic zero; here
  `K = ℝ` or `K = ℂ` (`RCLike K`).
* **Gap.** Kollár states the theorem for every separable $K$-analytic space. His notion of
  resolution [Kol07, (2), (3)] is stated for varieties, and his proofs are for reduced spaces,
  extended to reducible ones [Kol07, Theorem 36, proof; Proposition 37]. Here the inputs are the
  reduced spaces (`ReducedSpace`); a non-reduced $X$ is resolved through its reduction, by
  $\Pi_{X_{\mathrm{red}}}$ followed by the closed immersion $X_{\mathrm{red}} \to X$.
* **Gap.** Kollár's clause (4), "$\Pi_X$ is projective over any compact subset of $X$", is replaced
  by properness together with the ambient blow-up factorization over relatively compact opens
  [Kol07, Warning 23]; [Wlo09, Theorem 2.0.2, (∗)].
* **Strengthening.** Over $\mathbb{R}$ the simple locus of a reduced space need not be dense [Hir64,
  Introduction]: the subspace $x^2 + y^2 = 0$ of $\mathbb{R}^2$ is reduced and has support the
  origin and no simple point (in `HironakaExamples`: `Hironaka.Space.circleSpace_isReduced`,
  `Hironaka.Manifold.circleIdeal_cosupport_eq_singleton` and
  `Hironaka.Manifold.circleIdeal_regSet_eq_empty`). So $\Pi_X$ need not be surjective; its image is
  the closure of the simple locus, a clause printed in neither source.
* **Gap.** Kollár's clause (5), "$R$ commutes with smooth $K$-morphisms", is replaced by the unique
  lifting of isomorphisms between open subspaces and of local analytic isomorphisms, the smooth
  morphisms of relative dimension zero, Kollár's étale morphisms. Since the lifts are unique, they
  respect identities and composition, so $R$ is functorial for the étale morphisms between inputs.
  Smooth morphisms of positive relative dimension are not lifted, and the isomorphism
  $R(Y) \cong Y \times_X R(X)$ is not stated.
* **Strengthening.** Włodarczyk's clause (3) lifts every local analytic isomorphism
  $\varphi \colon Y' \to Y$ to a natural local analytic isomorphism
  $\tilde\varphi \colon \tilde Y' \to \tilde Y$. Here the lift is the only morphism
  $R(Y') \to R(Y)$ over $\varphi$, and a local analytic isomorphism; the lift of an isomorphism
  between open subspaces is likewise the only morphism over it, so the lift of $\varphi$ restricts,
  over every open on which $\varphi$ is injective, to the lift of the isomorphism of open
  subspaces, and the naturality follows from the uniqueness. The lift is glued from those lifts
  over the opens on which $\varphi$ is injective, and the uniqueness rests on the rigidity of
  morphisms out of a non-singular space: two morphisms that agree on a dense open subspace
  agree.

Source statement: [Kol07, Theorem 45]

Source statement: [Wlo09, Theorem 2.0.1] -/
theorem exists_functorial_resolution (K : Type) [RCLike K] :
    ∃ R : ResolutionAssignment (ReducedSpace.{u} K),
      (∀ X : ReducedSpace.{u} K,
        -- (1)–(3), and the image of `Π_X` is the closure of the simple locus
        (R.map X).IsStrongResolutionOntoClosureRegularLocus ∧
        -- (4)
        (R.map X).IsLocallyFiniteAmbientBlowUpComposite) ∧
      -- (5), and 2.0.1 (3)
      R.LiftsLocalIsomorphisms :=
  sorry

/-- **Resolution of a reduced complex-analytic space** [Kol07, Theorem 45 (1)–(4)];
[Wlo09, Theorem 2.0.1], for `K = ℂ`. Let `X` be a reduced complex-analytic space. Then there is a
morphism `π : R → X` such that
* `π` is a strong resolution of `X` (`Hom.IsStrongResolution`): `π` is proper and bimeromorphic onto
  its image, and (1) `R` is non-singular; (2) `π` is an isomorphism over the simple locus
  `X.regularLocus`; (3) `π⁻¹(X.singularLocus)` is the support of a simple normal crossing divisor
  of `R`;
* (4) over every relatively compact open subset of `X`, `π` is the composite of a finite sequence
  of blow-ups of smooth centres of an ambient manifold, restricted to strict transforms
  (`Hom.IsLocallyFiniteAmbientBlowUpComposite`);
* `π` is surjective.

Relation to the source.
* **Gap.** The statement is not printed in this form: it is [Kol07, Theorem 45 (1)–(4)] and [Wlo09,
  Theorem 2.0.1 (1)–(2)] for `K = ℂ` and a single space, without the functoriality of Kollár's (5)
  and Włodarczyk's (3).
* **Gap.** As in `AnalyticSpace.exists_functorial_resolution`: Kollár's Theorem 45 concerns every
  separable complex space and here `X` is reduced, and Kollár's "projective over any compact subset"
  is replaced by properness together with the ambient blow-up factorization over relatively compact
  opens.
* **Strengthening.** Surjectivity is not a printed clause. It is what Włodarczyk's "proper
  bimeromorphic" gives for a reduced complex space, whose simple locus is dense [Hir64,
  Introduction].

Source statement: [Kol07, Theorem 45 (1)–(4)]

Source statement: [Wlo09, Theorem 2.0.1] (surjectivity from the density of the simple locus over
ℂ) -/
theorem exists_surjective_resolution_of_isReduced (X : AnalyticSpace.{u} ℂ) (hX : X.IsReduced) :
    ∃ (R : AnalyticSpace.{u} ℂ) (π : R ⟶ X),
      -- (1)–(3)
      π.IsStrongResolution ∧
      -- (4)
      π.IsLocallyFiniteAmbientBlowUpComposite ∧
      -- `π` is onto
      Function.Surjective π :=
  sorry

end AnalyticSpace

end Resolution
