/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.EmbeddedDesingGlobal
public import Hironaka.Resolution.Analytic.Wlo09.EmbeddedDesingPushforward
public import Hironaka.Manifold.Resolution.Defs
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.PullbackUpToEmpty
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionShear
import Hironaka.Resolution.Analytic.ModelTransport.Family

/-!
# Włodarczyk's locally finite embedded desingularization

The analytic embedded desingularization of a reduced closed subspace `Y` of an analytic manifold
`M` over `𝕜 = ℝ` or `ℂ` [Wlo09, Theorem 2.0.2], as one extension-compatible family over `M`,
with its exceptional divisor and strict transform on the glued space and its commutation with
local analytic isomorphisms and with closed embeddings of ambient manifolds (his clause (4)): the
main theorem `AnalyticManifold.exists_embeddedDesingularization` at the end of this file.

On the standard model `𝕜ⁿ` the family is `embeddedDesingFam`
(`Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingModel.lean`): the concrete embedded
desingularization functor `concreteBEDanFamStar` at the triple `(M, 𝓘_Y, ∅)` of `𝓘_Y` made the
unit ideal on the connected components of `M` where it vanishes, glued along the exhaustion of
`M`; its blow-down is proper and an isomorphism off `Sing(Y)`, over every compact the succession
desingularizes `Y` (`isDesingularizedBy_embeddedDesingFam`), and it commutes with local analytic
isomorphisms over every pair of compacts (`isPullbackUpToEmptyAlong_embeddedDesingFam`). Its
exceptional divisor `E` and strict transform `Ỹ` on the glued space are the glued objects of
`Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingGlobal.lean`
(`isGloballyDesingularizedBy_embeddedDesingFam`), and altogether the family is a locally finite
embedded desingularization of `Y` (`isLocallyFinitelyDesingularizedBy_embeddedDesingFam`).

On an arbitrary model `E` the assignment `embeddedDesingAssignment 𝕜 E` reads the value on the
re-modelled manifold back along `E ≃ 𝕜ⁿ` (`ExtensionCompatibleFamily.transportBack`), with the
clauses (`isAnalyticIsoOver_compl_sing_map_transportBack_iff`,
`isDesingularizedBy_seq_transportBack`, `isGloballyDesingularizedBy_transportBack`,
`Hironaka/Resolution/Analytic/ModelTransport/Family.lean`) and the pull-back relation along the
re-modelled local isomorphism (`IsPullbackUpToEmptyAlong.transportAlong`), as the functorial
principalization does (`Hironaka/Resolution/Analytic/Wlo09/FunctorialPrincipalization.lean`).
The commutation with closed embeddings of ambient manifolds
(`commutesWithClosedEmbeddings_embeddedDesingAssignment`) likewise carries the push-forward
relation on the standard models (`isPushforwardUpToEmptyAlong_embeddedDesingFam`,
`Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingPushforward.lean`) back along the
identifications of the two models (`IsPushforwardUpToEmptyAlong.transportAlong`), the embedding
re-modelled between them (`transportBetween`).
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u v

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### The assignment on an arbitrary model -/

section Assignment

variable (𝕜 : Type) [RCLike 𝕜]

/-- **Włodarczyk's embedded desingularization as an assignment on the embedded pairs** `(M, Y)`:
the embedded desingularization of the re-modelled ideal sheaf on the re-modelled manifold
(standard model `𝕜ⁿ`, `n = dim E`, `embeddedDesingFam`), read back on the manifold
(`transportBack`). -/
def embeddedDesingAssignment : CompatibleFamilyAssignment (EmbeddedPair.{u, v} 𝕜) :=
  fun T =>
    (embeddedDesingFam (T.M.transport (modelEquiv 𝕜 T.E)) (T.Y.transport (modelEquiv 𝕜 T.E))
      ((IdealSheaf.isReduced_pullbackDiffeomorph_iff _ _).mpr T.isReduced)).transportBack
      (modelEquiv 𝕜 T.E)

variable {𝕜}

/-- **Every value of the assignment is a locally finite embedded desingularization**: the family
on the standard model (`isLocallyFinitelyDesingularizedBy_embeddedDesingFam`) carried back by the
transport lemmas (`isProperMap_map_transportBack_iff`,
`isAnalyticIsoOver_compl_sing_map_transportBack_iff`, `isDesingularizedBy_seq_transportBack`,
`center_ne_top_seq_transportBack`, `boundarySeq_le_center_of_codim_le_one_seq_transportBack`
through `FiniteSuccession.two_le_codim_or_boundarySeq_le_center_iff`,
`isGloballyDesingularizedBy_transportBack`). -/
theorem isLocallyFinitelyDesingularizedBy_embeddedDesingAssignment (T : EmbeddedPair.{u, v} 𝕜) :
    T.Y.IsLocallyFinitelyDesingularizedBy (embeddedDesingAssignment 𝕜 T) := by
  dsimp only [embeddedDesingAssignment]
  set ψ := modelEquiv 𝕜 T.E
  have hI' : (T.Y.transport ψ).IsReduced :=
    (IdealSheaf.isReduced_pullbackDiffeomorph_iff _ _).mpr T.isReduced
  set F₀ : ExtensionCompatibleFamily (T.M.transport ψ) :=
    embeddedDesingFam (T.M.transport ψ) (T.Y.transport ψ) hI' with hF₀
  have h := isLocallyFinitelyDesingularizedBy_embeddedDesingFam (T.M.transport ψ) (T.Y.transport ψ)
    hI'
  obtain ⟨E₁, Y₁, hEY⟩ := h.exists_isGloballyDesingularizedBy
  exact ⟨(F₀.isProperMap_map_transportBack_iff ψ).mpr h.isProperMap,
    (F₀.isAnalyticIsoOver_compl_sing_map_transportBack_iff ψ T.Y).mpr h.isIsoOver_compl_sing,
    fun K => F₀.isDesingularizedBy_seq_transportBack ψ T.Y K (h.isDesingularizedBy_seq K),
    fun K => F₀.center_ne_top_seq_transportBack ψ K (h.center_ne_top K),
    fun K i => (FiniteSuccession.two_le_codim_or_boundarySeq_le_center_iff _ i
      (F₀.center_ne_top_seq_transportBack ψ K (h.center_ne_top K) i)).mpr
        (F₀.boundarySeq_le_center_of_codim_le_one_seq_transportBack ψ K
          (fun j => (FiniteSuccession.two_le_codim_or_boundarySeq_le_center_iff _ j
            (h.center_ne_top K j)).mp (h.two_le_codim_or_boundarySeq_le_center K j)) i),
    ⟨_, _, IdealSheaf.isGloballyDesingularizedBy_iff_and.mp
      (F₀.isGloballyDesingularizedBy_transportBack ψ T.Y hEY)⟩⟩

/-- **The assignment commutes with local analytic isomorphisms**: on the standard model the
re-modelled map is a local analytic isomorphism along which the re-modelled ideal sheaves pull
back (`isLocalDiffeomorph_transport`, `IdealSheaf.transport_pullback`), where the embedded
desingularization commutes with it (`isPullbackUpToEmptyAlong_embeddedDesingFam`); the pull-back
predicate carries back to `E` (`IsPullbackUpToEmptyAlong.transportAlong`). -/
theorem commutesWithLocalAnalyticIsomorphisms_embeddedDesingAssignment :
    EmbeddedPair.CommutesWithLocalAnalyticIsomorphisms (embeddedDesingAssignment.{u, v} 𝕜) := by
  intro T N g hg K' K hK
  dsimp only [embeddedDesingAssignment] at hK ⊢
  exact FiniteSuccession.IsPullbackUpToEmptyAlong.transportAlong (modelEquiv 𝕜 T.E) g
    (AnalyticMap.transport (modelEquiv 𝕜 T.E) g) (fun _ => rfl)
    (isPullbackUpToEmptyAlong_embeddedDesingFam _ _ _ (AnalyticMap.transport (modelEquiv 𝕜 T.E) g)
      (AnalyticMap.isLocalDiffeomorph_transport (modelEquiv 𝕜 T.E) hg) _ _
      (IdealSheaf.transport_pullback (modelEquiv 𝕜 T.E) g T.Y) K' K hK)

end Assignment

/-! ### The commutation with closed embeddings of ambient manifolds -/

section ClosedEmbeddings

variable {𝕜 : Type} [RCLike 𝕜]

/-- **The assignment commutes with closed embeddings of ambient manifolds**
(`EmbeddedPair.CommutesWithClosedEmbeddings`, the second half of [Wlo09, Theorem 2.0.2 (4)] read
as [Kol07, 34.3] over the compact sets): for a closed embedding of analytic manifolds `τ : N → M`
along which `𝓘_Y` is the push-forward of `𝓘_{Y'}`, the re-modelled map `transportBetween` is a
closed embedding of the re-modelled manifolds with image a closed submanifold of the same
codimension, along which the re-modelled ideal sheaves pull back and the containment of the ideal
sheaf of the image carries over (`Hironaka/Resolution/Analytic/Wlo09/ClosedEmbedding.lean`). For a
nonempty `N` the embedding identifies the re-modelled `N` with the bundled submanifold
(`IsClosedAnalyticEmbedding.toDiffeomorph`), and the push-forward relation holds on the standard
models (`isPushforwardUpToEmptyAlong_embeddedDesingFam_of_diffeomorph`); for an empty `N` both
successions are empty (`isPushforwardUpToEmptyAlong_embeddedDesingFam_of_isEmpty`). The relation
carries back to `E` and `E'` (`IsPushforwardUpToEmptyAlong.transportAlong`). -/
theorem commutesWithClosedEmbeddings_embeddedDesingAssignment :
    EmbeddedPair.CommutesWithClosedEmbeddings (embeddedDesingAssignment.{u, v} 𝕜) := by
  intro T T' τ hτ hJ K' K hK
  obtain ⟨n, s, ψ, hS, hle⟩ := hτ.exists_isClosedSubmanifold_stalkIdeal_le
  have hemb := hτ.isClosedAnalyticEmbedding
  have hJI := hτ.pullback_eq
  -- the data on the standard models
  have hI' : (T.Y.transport (modelEquiv 𝕜 T.E)).IsReduced :=
    (IdealSheaf.isReduced_pullbackDiffeomorph_iff _ _).mpr T.isReduced
  have hJ' : (T'.Y.transport (modelEquiv 𝕜 T'.E)).IsNonzeroEverywhere :=
    (IdealSheaf.isNonzeroEverywhere_pullbackDiffeomorph_iff _ _).mpr hJ
  have hST : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (Module.finrank 𝕜 T.E) → 𝕜))
      (Set.range (transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) τ)) s :=
    (AnalyticManifold.IsClosedSubmanifold.range_transportBetween (modelEquiv 𝕜 T.E)
      (modelEquiv 𝕜 T'.E) hS).congr_chart _
  have hleT := stalkIdeal_idealSheaf_range_transportBetween_le (modelEquiv 𝕜 T.E)
    (modelEquiv 𝕜 T'.E) hS hST T.Y hle
  have hJIT : T'.Y.transport (modelEquiv 𝕜 T'.E) =
      (T.Y.transport (modelEquiv 𝕜 T.E)).pullback
        (transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) τ)
        (transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) τ).contMDiff := by
    rw [hJI]
    exact IdealSheaf.transport_pullback_transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) T.Y
  dsimp only [embeddedDesingAssignment] at hK ⊢
  refine FiniteSuccession.IsPushforwardUpToEmptyAlong.transportAlong (modelEquiv 𝕜 T.E)
    (modelEquiv 𝕜 T'.E) τ (transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) τ)
    (fun _ => rfl) ?_
  rcases isEmpty_or_nonempty T'.M with hN | hN
  · -- an empty `N`: both successions are empty
    have : IsEmpty (T'.M.transport (modelEquiv 𝕜 T'.E)) := hN
    exact isPushforwardUpToEmptyAlong_embeddedDesingFam_of_isEmpty _ _ hI' _ hST hleT _
      (fun K' i => center_ne_top_seq_embeddedDesingFam _ _ _ K' i) K' K
  · -- a nonempty `N`: identified with the bundled submanifold of the image
    have : Nonempty (T'.M.transport (modelEquiv 𝕜 T'.E)) := hN
    have hτT := hemb.transportBetween (modelEquiv 𝕜 T.E) (modelEquiv 𝕜 T'.E) hS
    exact isPushforwardUpToEmptyAlong_embeddedDesingFam_of_diffeomorph _ _ hI' _ hST
      (hτT.toDiffeomorph hST) (hτT.coe_toDiffeomorph_apply hST) hleT _ hJ' hJIT
      ((IdealSheaf.isReduced_pullbackDiffeomorph_iff _ _).mpr T'.isReduced) K' K hK

end ClosedEmbeddings

end Hironaka.Manifold

end

end

public section

universe u v

section EmbeddedDesingularization

open TopologicalSpace

namespace AnalyticManifold

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
  ⟨Hironaka.Manifold.embeddedDesingAssignment 𝕜,
    Hironaka.Manifold.isLocallyFinitelyDesingularizedBy_embeddedDesingAssignment,
    Hironaka.Manifold.commutesWithLocalAnalyticIsomorphisms_embeddedDesingAssignment,
    Hironaka.Manifold.commutesWithClosedEmbeddings_embeddedDesingAssignment⟩

end AnalyticManifold

end EmbeddedDesingularization
