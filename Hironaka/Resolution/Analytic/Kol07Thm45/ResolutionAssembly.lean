/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/

module

public import Hironaka.Resolution.Analytic.Functor.EmbeddedDesingFam
public import Hironaka.AnalyticSpace.Resolution.Defs
public import Mathlib.Analysis.Complex.Basic
import Hironaka.AnalyticSpace.RegPoints
import Hironaka.AnalyticSpace.SncBoundaryChart
import Hironaka.AnalyticSpace.SncDivisorSetLocal
import Hironaka.Manifold.FiniteSuccession.Restrict.LiftRegDense
import Hironaka.Resolution.Analytic.Wlo09.Concrete
import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientFactorization
import Hironaka.Resolution.Analytic.Kol07Thm45.GluingProperties
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalIsoLift
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionClauses
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionFunctorial
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionIsoReg
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionSnc
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionSncGlobal
import Hironaka.Resolution.Analytic.Kol07Thm45.StrongResolutionOfIsoOver
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Resolution of analytic spaces from an embedded desingularization family

The assembly of the resolution of analytic spaces. Given a family functor `bed : BEDanFamStar K`
that is an embedded desingularization (`hbed : bed.IsEmbeddedDesing`,
`Functor/EmbeddedDesingFam.lean`: the exceptional divisors have simple normal crossings, the centres
lie over the non-simple points, the final strict transform is smooth and meets the exceptional
divisors with simple normal crossings, the total transform of the ideal factors accordingly, and
the functor commutes with local isomorphisms; the commutation with closed embeddings is the field
`closedEmbedding` of `BEDanFamStar`), the local resolutions of the pieces of a reduced analytic
space `X` — a piece is an open `X|V` embedded as a closed subspace of an open `G ⊆ 𝕜ⁿ`, resolved
by running `bed` on `(G, 𝓘_{X|V}, ∅)` (`PieceEmbedding.lean`) — glue to a resolution
`Π_X : R(X) → X` (`Resolution.lean`), and the glued space has the properties that the main
theorem `exists_functorial_resolution` asks of a `ResolutionAssignment`. This is Kollár's
construction of the resolution functor from the embedded one — the proof of [Kol07, Theorem 36],
carried to analytic spaces by [Kol07, 44] and stated as [Kol07, Theorem 45] — with the gluing over
the disjoint union of a cover [Kol07, Proposition 37, proof] and the independence of the embedding
[Kol07, Theorem 36, proof]; in Włodarczyk's form, the passage from the canonical embedded
desingularization to the canonical resolution of an analytic space [Wlo09, §4, (3)⇒(4)] and its
gluing over an exhaustion [Wlo09, §4.3].

The one hypothesis the gluing theorems carry beyond `hbed`, the independence of the local
resolution from the embedding (`LocalResolutionIndependentOn X bed`), is discharged here by
`localResolution_independent_local` (`LocalResolutionShear.lean`), Kollár's comparison of two
embeddings through the shear of [Kol07, Lemma 39]. The main theorem `exists_functorial_resolution`
instantiates `analyticSpace_resolution_of_isEmbeddedDesing` at the concrete family
`concreteBEDanFamStar` (`Hironaka/Resolution/Analytic/Wlo09/Concrete.lean`).

* `analyticSpace_resolution_of_isEmbeddedDesing`: the assignment `X ↦ (Π_X : R(X) → X)` with the
  clauses of the main theorem — non-singularity (`ResolutionClauses.lean`), the isomorphism over
  `X.regularLocus` (`ResolutionIsoReg.lean`), the simple normal crossings boundary with support
  `Π_X⁻¹(X.singularLocus)` (`ResolutionSncGlobal.lean`), properness (`ResolutionClauses.lean`), the
  locally finite ambient blow-up composite (`AmbientFactorization.lean`), the range
  `closure X.regularLocus` (`ResolutionSnc.lean`) and the functoriality for isomorphisms of open
  subspaces, with the uniqueness of the lift (`ResolutionFunctorial.lean`).
* The lifting of local analytic isomorphisms (`ResolutionAssignment.LiftsLocalIsomorphisms`,
  [Wlo09, Theorem 2.0.1 (3)]) is derived from the lifting of isomorphisms of open subspaces by
  gluing, for every assignment whose values are strong resolutions
  (`ResolutionAssignment.liftsLocalIsomorphismsOn_of_liftsIsomorphismsOfOpenSubspacesOn`,
  `LocalIsoLift.lean`).
* `AnalyticSpace.Hom.isStrongResolution_of_isIsoOver_regularLocus`
  (`StrongResolutionOfIsoOver.lean`): the bimeromorphy field of `Hom.IsResolution` follows from the
  isomorphism over the simple locus and the simple normal crossings divisor over the singular
  locus, so the clauses above make `Π_X` a strong resolution.
* The main theorems, at the end of the file: `AnalyticSpace.exists_functorial_resolution`
  ([Kol07, Theorem 45]; [Wlo09, Theorem 2.0.1]) and its specialization to `K = ℂ`,
  `AnalyticSpace.exists_surjective_resolution_of_isReduced`, where the image clause becomes
  surjectivity by the density of the simple locus of a reduced complex space
  (`Manifold.dense_reg_of_isReduced_complex`,
  `Hironaka/Manifold/FiniteSuccession/Restrict/LiftRegDense.lean`).
-/

public section

universe u

open scoped Manifold ContDiff CategoryTheory
open CategoryTheory (IsIso)
open TopologicalSpace AnalyticSpace Hironaka.Manifold

namespace Hironaka

variable (K : Type) [RCLike K]


/-- **The resolution of analytic spaces from an embedded desingularization family**: for any
`bed` with `hbed`, a `ResolutionAssignment` `X ↦ (Π_X : R(X) → X)` satisfying, for every reduced
`X`, the clauses of `exists_functorial_resolution` (non-singularity, the isomorphism over the simple
locus, the simple normal crossings divisor, properness, the ambient blow-up factorization, the
image, the unique lifting of isomorphisms); instantiated at `concreteBEDanFamStar` in the proof of
that theorem. -/
theorem analyticSpace_resolution_of_isEmbeddedDesing (bed : BEDanFamStar.{u} K)
    (hbed : bed.IsEmbeddedDesing) :
    ∃ R : AnalyticSpace.ResolutionAssignment (AnalyticSpace.{u} K), ∀ X : AnalyticSpace.{u} K,
        X.IsReduced →
      (R.space X).IsNonsingular ∧
      (R.map X).IsIsoOver (regularLocus X) ∧
      (∃ E : ClosedSubspace (R.space X), E.IsSncBoundary ∧
        E.support = (R.map X) ⁻¹' singularLocus X) ∧
      IsProperMap (R.map X) ∧ (R.map X).IsLocallyFiniteAmbientBlowUpComposite ∧
      Set.range (R.map X) = closure (regularLocus X) ∧
      ∀ (Y : AnalyticSpace.{u} K), Y.IsReduced → ∀ (U : Set X) (V : Set Y),
          IsOpen U → IsOpen V →
        ∀ φ : X.restrictSet U ⟶ Y.restrictSet V, IsIso φ →
          ∃! ψ : (R.space X).restrictSet ((R.map X) ⁻¹' U) ⟶
              (R.space Y).restrictSet ((R.map Y) ⁻¹' V),
            IsIso ψ ∧ ψ ≫ (R.map Y).restrictSet V = (R.map X).restrictSet U ≫ φ :=
  ⟨⟨bed.resolution, bed.resolutionMap⟩, fun X hX =>
    ⟨BEDanFamStar.resolution_isNonsingular_of_independent X hX bed hbed
        (Manifold.localResolutionIndependentOn_of_isEmbeddedDesing K X bed hbed),
      BEDanFamStar.resolutionMap_isIsoOver_reg_of_independent X hX bed hbed
        (Manifold.localResolutionIndependentOn_of_isEmbeddedDesing K X bed hbed),
      BEDanFamStar.resolution_exists_isSncBoundary_preimage_sing_of_independent X hX bed hbed
        (Manifold.localResolutionIndependentOn_of_isEmbeddedDesing K X bed hbed),
      BEDanFamStar.isProperMap_resolutionMap X bed,
      BEDanFamStar.isLocallyFiniteAmbientBlowUpComposite_resolutionMap_of_independent bed X hX hbed
        (Manifold.localResolutionIndependentOn_of_isEmbeddedDesing K X bed hbed),
      BEDanFamStar.range_resolutionMap_eq_closure_reg_of_independent X hX bed hbed
        (Manifold.localResolutionIndependentOn_of_isEmbeddedDesing K X bed hbed),
      fun Y hY U V hU hV φ hφ => by
        obtain ⟨ψ, hψ, hc⟩ := BEDanFamStar.resolution_functorial_of_independent X hX bed hbed
          (Manifold.localResolutionIndependentOn_of_isEmbeddedDesing K X bed hbed) Y hY
          (Manifold.localResolutionIndependentOn_of_isEmbeddedDesing K Y bed hbed) U V hU hV φ hφ
        exact ⟨ψ, ⟨hψ, hc⟩, fun ψ' ⟨hψ', hc'⟩ => (BEDanFamStar.resolution_lift_unique bed hbed hX
          (Manifold.localResolutionIndependentOn_of_isEmbeddedDesing K X bed hbed) U V hU φ hφ
          ψ ψ' hψ hψ' hc hc').symm⟩⟩⟩

end Hironaka

end

public section

universe u v

section Resolution

open scoped CategoryTheory

namespace AnalyticSpace

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
      R.LiftsLocalIsomorphisms := by
  obtain ⟨R, hR⟩ := Hironaka.analyticSpace_resolution_of_isEmbeddedDesing K
    (Hironaka.concreteBEDanFamStar K) (Hironaka.concreteBEDanFamStar_isEmbeddedDesing K)
  have hres : ∀ X : AnalyticSpace.{u} K, X.IsReduced → (R.map X).IsStrongResolution :=
    fun X hX => by
      obtain ⟨h1, h2, h3, h4, -⟩ := hR X hX
      exact Hom.isStrongResolution_of_isIsoOver_regularLocus h1 h4 h2 h3
  refine ⟨⟨fun X => R.space X.obj, fun X => R.map X.obj⟩, fun X =>
    ⟨⟨hres X.obj X.property, (hR X.obj X.property).2.2.2.2.2.1⟩,
      (hR X.obj X.property).2.2.2.2.1⟩,
    ResolutionAssignment.liftsLocalIsomorphisms_of_existsUnique_lift
      (fun X Y => (hR X.obj X.property).2.2.2.2.2.2 Y.obj Y.property)
      fun X => hres X.obj X.property⟩

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
      Function.Surjective π := by
  obtain ⟨R, hR, -⟩ := exists_functorial_resolution.{u} ℂ
  let X' : ReducedSpace.{u} ℂ := ⟨X, hX⟩
  refine ⟨R.space X', R.map X', (hR X').1.toIsStrongResolution, (hR X').2, ?_⟩
  -- the image `closure X.regularLocus` is everything: the simple locus is dense over `ℂ`
  rw [← Set.range_eq_univ, (hR X').1.range_eq]
  exact dense_iff_closure_eq.mp (Manifold.dense_reg_of_isReduced_complex X hX)

end AnalyticSpace

end Resolution
