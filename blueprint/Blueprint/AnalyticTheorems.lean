import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import Blueprint.Spaces
import Hironaka.Resolution.Analytic.Wlo09.HironakaAssembly
import Hironaka.Resolution.Analytic.BM97.JacobianAssembly
import Hironaka.Resolution.Analytic.Wlo09.FunctorialPrincipalization
import Hironaka.Resolution.Analytic.Wlo09.EmbeddedDesingularization
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionAssembly

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Set Filter Topology TopologicalSpace
open AnalyticManifold Manifold AnalyticSpace
open scoped CategoryTheory

set_option verso.blueprint.autoDeps true
-- Infer from directly referenced declarations only, as before v4.34; walking through unassociated
-- helpers would traverse Mathlib.
set_option verso.blueprint.autoDeps.expandUntagged false

#doc (Manual) "Analytic manifolds and analytic spaces" =>
%%%
tag := "ch-analytic"
file := "analytic-theorems"
%%%

The theorems of this chapter are the analytic resolution theorems of the library: Hironaka's
principalization on a real-analytic manifold, Bierstone–Milman's principalization with the Jacobian
condition, Włodarczyk's functorial principalization on a real- or complex-analytic manifold,
Włodarczyk's embedded desingularization of a closed subspace of a real- or complex-analytic
manifold, the resolution of real- and complex-analytic spaces, and its form for a single reduced
complex space.

On a manifold that is not compact no finite succession of blow-ups can be expected to resolve
everything, and Hironaka states his global analytic theorems I′(n), II′(N), I″(n) and II″(N) for
locally finite successions indexed by a countable well-ordered set. The library uses instead the
form of Włodarczyk's locally finite principalization {cite Wlo09}[Theorem 2.0.3]: a proper analytic
map $`\sigma \colon \tilde M \to M` which, over an open neighbourhood $`U_K` of every compact
$`K \subseteq M`, is a finite succession of blow-ups, the successions for different compacts being
compatible ({bpref "def:compatible_family"}[]). Over a compact manifold, $`K = M` gives one finite
succession.

The objects of the manifold statements are analytic manifolds ({bpref "def:analytic_manifold"}[]),
locally finitely generated ideal sheaves of analytic functions ({bpref "def:ideal_sheaf_vocab"}[]),
finite successions of monoidal transformations with their weak transforms, boundaries and strict
transforms ({bpref "def:finite_succession"}[], {bpref "def:succession_transforms"}[]), and simple
normal crossings boundaries ({bpref "def:snc_boundary"}[]), described in the part on analytic
geometry. The section of each theorem states, before the theorem, the properties it asserts; a
property asserted by several theorems is stated at the first of them in this chapter.

# Main Theorem II″(N), compatible-family form
%%%
tag := "sec-mt2pp"
%%%

Main Theorem II″(N) principalizes an ideal sheaf on a real-analytic manifold over every compact
subset. Its conditions on boundaries and orders are used again by Bierstone–Milman's
principalization and by Włodarczyk's theorems.

*Hironaka's conditions on boundaries and orders.*

::::definition "def:manifold_hironaka_conditions" (lean := "AnalyticManifold.FiniteSuccession.HasSncBoundaries, AnalyticManifold.FiniteSuccession.HasConstantPositiveOrderAlongCenters")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II′(N), p. 156]", href := "https://doi.org/10.2307/1970486" }
%%%
Hironaka's conditions on boundaries and orders, for a finite succession `S` of an analytic manifold
$`M` with centres $`C_i`; they are the analytic forms of those of the algebraic theorems
({bpref "def:hironaka_conditions"}[], {bpref "def:constant_order"}[]):

- `S.HasSncBoundaries B`: the boundaries $`E_i` started at $`B`
  ({bpref "def:succession_transforms"}[]) have simple normal crossings with the centres, and the
  last one has simple normal crossings ({bpref "def:snc_boundary"}[]) {cite Hir64}[Main Theorem II′(N)
  (iii) and the first half of (iv)]; {cite Wlo09}[Theorem 2.0.3 (2)]. Started at the unit ideal `⊤`,
  the empty boundary, the $`E_i` are the exceptional divisors;
- `S.HasConstantPositiveOrderAlongCenters J`: for every $`i` the order of the weak transform $`J_i`
  is a positive constant along $`C_i` {cite Hir64}[Main Theorem II′(N) (ii)].
::::

::::theorem "thm:mt2pp" (lean := "AnalyticManifold.exists_extensionCompatibleFamily_weakTransformSeq_eq_top")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II″(N), pp. 158–159]", href := "https://doi.org/10.2307/1970486" }
%%%
Let $`X` be a real-analytic manifold, $`E_0` an ideal sheaf with only normal crossings (the reduced
divisor of a simple normal crossings family of smooth hypersurfaces of $`X`), and $`J_0` an ideal
sheaf with nonzero stalks. Then there are a real-analytic manifold $`\tilde X` and a proper
analytic map $`\sigma \colon \tilde X \to X` which, over an open neighbourhood $`U_K` of every
compact $`K \subseteq X` and compatibly across compacts, is a finite succession of monoidal
transformations $`U_K = U_0 \leftarrow U_1 \leftarrow \cdots \leftarrow U_r` with centres
$`D_i`, such that for every compact $`K`:

1. every centre $`D_i` is non-singular;
2. the order of the weak transform $`J_i` of $`J_0|_{U_K}` is a positive constant along $`D_i`;
3. the boundary $`E_i` ($`E_0|_{U_K}` and then
   $`E_{i+1} = \mathrm{red}(\sigma_{i+1}^{-1}(E_i) \cup \sigma_{i+1}^{-1}(D_i))`) has only normal
   crossings with $`D_i`;
4. $`E_r` has only normal crossings and $`J_r = \mathcal{O}_{U_r}`.

The conclusion is that of Hironaka's Main Theorem II′(N) (p. 156). This is the real-analytic
counterpart of Main Theorem II(N) ({bpref "thm:mt2n"}[]): principalize a nonzero ideal sheaf by
blowing up non-singular centres along which the order of the weak transform is a positive
constant, keeping the boundary in simple normal crossings. The constant of (2) may depend on $`K`
and $`i`. For $`J_0 = \mathcal{O}_X` condition (2) leaves every centre empty, and $`\sigma` is
then an isomorphism.

Condition (2) is {decl}`HasConstantPositiveOrderAlongCenters` and condition (3) with the first half
of (4) {decl}`HasSncBoundaries` ({bpref "def:manifold_hironaka_conditions"}[]).
::::

:::proof "thm:mt2pp"
The hypothesis `hE₀` provides coordinates $`E \cong \mathbb{R}^n` and a simple normal crossings
hypersurface family whose reduced ideal sheaf is $`E_0`. Transporting $`X`, $`J_0` and the family
along the coordinates gives a triple on the standard model, to which the order-reduction
algorithm is applied: the real-analytic form of the blow-up sequence functors of
{cite Kol07}[Theorem 103] and, for marked ideals, {cite Kol07}[Theorem 107], assembled functorially over
the exhaustion of the manifold by compacts. This yields a compatible family with proper blow-down
satisfying the conditions on the model, and each condition is carried back along the coordinates.
:::

# Real-analytic principalization with the Jacobian condition
%%%
tag := "sec-bm"
%%%

::::theorem "thm:bm" (lean := "AnalyticManifold.exists_extensionCompatibleFamily_isNormalCrossingsDivisor_jacobianIdeal_mul_pullback")
%%%
paperIdentity := some { label := "[BM97, Theorem 1.10]", href := "https://arxiv.org/abs/alg-geom/9508005" }
%%%
Let $`M` be a real-analytic manifold modelled on a finite-dimensional space and $`I` an ideal sheaf
with nonzero stalks. Then there is a proper analytic map $`\sigma \colon \tilde M \to M` which,
over a neighbourhood $`U_K` of every compact $`K` and compatibly across compacts, is a finite
succession of blow-ups $`U_K = U_0 \leftarrow \cdots \leftarrow U_r` with non-singular centres,
such that

- for every compact $`K`, the exceptional divisors $`E_i` (the boundaries started at the empty
  boundary) have simple normal crossings with the centres, the last one $`E_r` has simple normal
  crossings, and the weak transform of $`I|_{U_K}` on $`U_r` is the unit ideal;
- the pull-back $`\sigma^* I` is a normal-crossings divisor;
- the product of the Jacobian ideal of $`\sigma` with $`\sigma^* I` is a normal-crossings divisor;
- $`\sigma` is an analytic isomorphism over the complement of the support of $`I`.

The Jacobian condition is what the change of variables in an integral needs: in local coordinates on
$`\tilde M` both $`I \circ \sigma` and the Jacobian determinant of $`\sigma` are monomials times
units. The conditions on the successions are stated over each compact; the normal-crossings,
Jacobian and isomorphism conditions, being local on $`\tilde M`, are stated on $`\sigma` itself. For
$`I = \mathcal{O}_M` the support of $`I` is empty, so $`\sigma` is an isomorphism.

The condition on the exceptional divisors is `HasSncBoundaries ⊤`
({bpref "def:manifold_hironaka_conditions"}[]). The additional vocabulary is the Jacobian ideal,
analytic isomorphisms over a set and normal-crossings divisors ({bpref "def:jacobian"}[],
{bpref "def:snc_boundary"}[]).
::::

:::proof "thm:bm"
As for {bpref "thm:mt2pp"}[]: the model space is identified with $`\mathbb{R}^n`, $`I` is
transported to the model, where it forms a triple with the empty boundary family, and the
order-reduction algorithm yields a compatible family whose blow-down is proper, whose successions
satisfy the conditions of Main Theorem II″(N) for the empty boundary, and whose last weak transform
is the unit ideal. The normal-crossings, Jacobian and isomorphism conditions are proved for that
family and carried back along the identification.
:::

# Functorial principalization on analytic manifolds
%%%
tag := "sec-wlo09-principalization"
%%%

Włodarczyk's functorial principalization assigns a compatible family of finite successions
({bpref "def:compatible_family"}[]) to every ideal sheaf on every manifold, modelled on any
finite-dimensional space, by one rule. It asserts of each value that it is a locally finite
principalization, and of the rule that it commutes with local analytic isomorphisms, over the
compact sets and globally (every local analytic isomorphism lifts to the spaces of the values), and
with closed embeddings of analytic manifolds, over the compact sets.

*Locally finite principalization.*

::::definition "def:locally_finite_principalization" (lean := "AnalyticManifold.IdealSheaf.IsLocallyFinitelyPrincipalizedBy")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.3 (1)–(3)]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
`I.IsLocallyFinitelyPrincipalizedBy F`, for an ideal sheaf $`I` on $`M` and a compatible family $`F`
with map $`\mathrm{prin}_I`, says that $`F` is a locally finite principalization of $`I` in
Włodarczyk's sense. Write `F.seq K` for the succession over the neighbourhood $`U_K` of a compact
$`K`, with composite $`\sigma_K` and exceptional divisors $`E_i`. Then $`\mathrm{prin}_I` is proper;
every $`U_K` has compact closure; the centres are smooth; `(F.seq K).HasSncBoundaries ⊤`
({bpref "def:manifold_hironaka_conditions"}[]); the total transform $`\sigma_K^*(I|_{U_K})` is near
every point the ideal of an effective combination of the components of $`E_r`
({decl}`IsMulBoundaryMonomial` with the unit ideal as its first factor,
{bpref "def:embedded_snc"}[]); the total transform $`\mathrm{prin}_I^*(I)` is a normal-crossings
divisor; and $`\mathrm{prin}_I` is an isomorphism off the support of $`I` {cite Wlo09}[Theorem 2.0.3
(1)–(3); Lemma 4.0.3]. It is the analogue on manifolds of {decl}`Triple.IsPrincipalizedBy` on
schemes ({bpref "def:principalized_by"}[]), with properness and the compact closures of the $`U_K`
added and each condition stated over every compact.
::::

*The inputs: pairs of a manifold and an ideal sheaf.*

::::definition "def:ideal_sheaf_pair" (lean := "AnalyticManifold.IdealSheafPair, AnalyticManifold.IdealSheafPair.pullback")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.3; Kol07, Notation 64]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
A *pair* $`(M, I)` is an analytic manifold $`M` over $`\mathbb{K}`, modelled on a
finite-dimensional space $`E`, with an ideal sheaf $`I` on $`M` with nonzero stalks: the input of
Włodarczyk's principalization, Kollár's triple $`(X, I, \emptyset)` with an empty boundary
({bpref "def:triple"}[]). The model space is part of the input, so that one assignment covers the
manifolds of every dimension. `T.pullback g hg` is the pair $`(N, g^* I)` over a local analytic
isomorphism $`g \colon N \to M` of manifolds modelled on one space, the source of the morphism of
pairs over $`g` {cite Wlo09}[Theorem 3.5.1].
::::

*Compatible family assignments.*

::::definition "def:compatible_family_assignment" (lean := "AnalyticManifold.HasUnderlyingManifold, AnalyticManifold.CompatibleFamilyAssignment, AnalyticManifold.IdealSheafPair.hasUnderlyingManifold")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.3; Kol07, Definition 31]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
A type $`C` of inputs *has underlying manifolds* when every input has an underlying analytic
manifold over $`\mathbb{K}` on a finite-dimensional model space ({decl}`HasUnderlyingManifold`, the
counterpart of {decl}`HasUnderlyingScheme`, {bpref "def:functors"}[]); the pairs
are such a type. A *compatible family assignment* on $`C` ({decl}`CompatibleFamilyAssignment`) is a
compatible family of finite successions of blow-ups ({bpref "def:compatible_family"}[]) of the
underlying manifold of every input: Włodarczyk's $`\mathrm{prin}` and $`\mathrm{res}` as rules on
all pairs, the counterpart on manifolds of a blow-up sequence functor {cite Kol07}[Definition 31].
Its properties are the clauses of the functorial theorems.
::::

*The push-forward of an ideal sheaf along a closed embedding.*

::::definition "def:pushforward_along" (lean := "AnalyticManifold.IdealSheaf.IsPushforwardAlong")
%%%
paperIdentity := some { label := "[Kol07, 34.3]", href := "https://arxiv.org/abs/math/0508332" }
%%%
`I.IsPushforwardAlong J τ`, for ideal sheaves $`I` on $`M` and $`J` on $`N` and an analytic map
$`\tau \colon N \to M` between analytic manifolds modelled on $`E'` and on $`E`: $`\tau` is a
closed embedding of analytic manifolds, that is an analytic embedding (Mathlib's
`IsSmoothEmbedding` at $`\omega`: an analytic immersion, of the form $`u \mapsto (u, 0)` in
suitable charts near every point, which is a homeomorphism onto its image) with closed image; the
ideal of its image is contained in $`I` (at every point, the vanishing ideal of $`\tau(N)`,
{bpref "def:vanishing"}[], lies in the stalk of $`I`); and $`J = \tau^* I`. So $`N` carries the
analytic structure induced on the closed subset $`\tau(N)` (every analytic map with values in
$`\tau(N)` factors analytically through $`\tau`; for a finite-dimensional model of $`M`,
$`\tau(N)` is a closed submanifold, {bpref "def:submanifold"}[]), and the closed subspace of $`I`
lies in $`\tau(N)` and is the image of the closed subspace of $`J`: Kollár's "closed embedding of
smooth schemes" and his hypothesis $`\mathcal{O}_X / I_X = j_*(\mathcal{O}_Y / I_Y)` on the ideal
sheaves in his commutation with closed embeddings, for an empty boundary; the embedding of
Włodarczyk's "embeddings of ambient varieties".
::::

*Commuting with local analytic isomorphisms.*

::::definition "def:commutes_local_iso" (lean := "AnalyticManifold.IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.3, p. 35; Theorem 3.5.1 (2); Theorem 2.0.1 (3)]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
`IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms P`, for a compatible family assignment
$`P` on the pairs: the last sentence of {cite Wlo09}[Theorem 2.0.3] for local analytic isomorphisms,
in two forms. Over every pair of compact sets: for a local analytic isomorphism
$`g \colon N \to M` of manifolds modelled on one space, the pair $`(N, g^* I)` and compacts
$`K' \subseteq N`, $`K \subseteq M` with $`g(U_{K'}) \subseteq U_K`, the succession of
$`P(N, g^* I)` over $`U_{K'}` is the pull-back along $`g` of the succession of $`P(M, I)` over
$`U_K`, up to blow-ups with empty centre ({bpref "def:pullback_up_to_empty"}[]), the form of
{cite Wlo09}[Theorem 3.5.1 (2)]. Globally: writing $`\mathrm{prin}_I \colon \tilde M \to M` and
$`\mathrm{prin}_J \colon \tilde N \to N` for the maps of $`P(M, I)` and $`P(N, J)`, $`J = g^* I`,
there is an analytic map $`\tilde g \colon \tilde N \to \tilde M` with
$`\mathrm{prin}_I \circ \tilde g = g \circ \mathrm{prin}_J` which is a local analytic
isomorphism, maps the fibre of $`\mathrm{prin}_J` over every point $`y` bijectively onto the fibre
of $`\mathrm{prin}_I` over $`g(y)`, and is the only continuous map $`\tilde N \to \tilde M` over
$`g`: the "natural lifting" of {cite Wlo09}[Theorem 2.0.1 (3)], whose fibre bijection is the
identification of $`\tilde N` with the fibre product $`N \times_M \tilde M` stated pointwise, and
whose uniqueness makes the lift of a composite the composite of the lifts. The two forms are
bundled as the two conditions of Kollár's 34.1 are in {decl}`CommutesWithSmoothMorphisms`
({bpref "def:commutes_smooth"}[]).
::::

*Commuting with closed embeddings.*

::::definition "def:commutes_closed_analytic" (lean := "AnalyticManifold.IdealSheafPair.CommutesWithClosedEmbeddings")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.3, p. 35; Kol07, Theorem 35 (5), 34.3]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
`IdealSheafPair.CommutesWithClosedEmbeddings P`, for a compatible family assignment $`P` on the
pairs: for pairs $`(M, I)` and $`(N, J)` and a closed embedding of analytic manifolds
$`\tau \colon N \to M` along which $`I` is the push-forward of $`J`
({bpref "def:pushforward_along"}[]), and compacts $`K' \subseteq N`, $`K \subseteq M` with
$`\tau(U_{K'}) \subseteq U_K`, the succession of $`P(M, I)` over $`U_K` is the push-forward along
$`\tau` of the succession of $`P(N, J)` over $`U_{K'}`, up to blow-ups whose centres lie outside
the part over $`\tau(U_{K'})` ({bpref "def:pushforward_up_to_empty"}[]). This is the rest of the
last sentence of {cite Wlo09}[Theorem 2.0.3], "commutes with … embeddings of ambient varieties", read
as Kollár's commutation with closed embeddings {cite Kol07}[Theorem 35 (5)] in the form of
{cite Kol07}[34.3], $`B(X, I_X, E) = j_* B(Y, I_Y, E|_Y)` for an empty $`E`, over every pair of
compact sets; the counterpart on manifolds of {decl}`CommutesWithClosedEmbeddingsOfEmptyBoundary`
({bpref "def:commutes_closed_embeddings"}[]).
::::

::::theorem "thm:wlo09_principalization" (lean := "AnalyticManifold.exists_functorial_principalization")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.3, p. 35]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
Let $`\mathbb{K}` be $`\mathbb{R}` or $`\mathbb{C}`. There is a compatible family assignment $`P`
on the pairs $`(M, I)` of an analytic manifold $`M` over $`\mathbb{K}`, modelled on a
finite-dimensional space, and an ideal sheaf $`I` on $`M` with nonzero stalks
({bpref "def:ideal_sheaf_pair"}[], {bpref "def:compatible_family_assignment"}[]) — to each pair a
map $`\mathrm{prin}_I \colon \tilde M \to M` which over an open neighbourhood $`U_K` of every
compact $`K \subseteq M` is, compatibly across compacts, a finite succession of blow-ups
$`U_K = U_0 \leftarrow U_1 \leftarrow \cdots \leftarrow U_r` with composite $`\sigma_K` —
such that:

- every value $`P(M, I)` is a locally finite principalization of $`I`
  ({bpref "def:locally_finite_principalization"}[]): with exceptional divisors $`E_i`,
  $`\mathrm{prin}_I` is proper, every $`U_K` has compact closure, and (1) the centres are smooth;
  (2) every $`E_i` has simple normal crossings with the centre at its stage, and $`E_r` has simple
  normal crossings; (3) the total transform $`\sigma_K^*(I|_{U_K})` is near every point the ideal
  of an effective combination of the components of $`E_r`, and the total transform
  $`\mathrm{prin}_I^*(I)` is a normal-crossings divisor; moreover $`\mathrm{prin}_I` is an
  isomorphism off the support of $`I`;
- $`P` commutes with local analytic isomorphisms ({bpref "def:commutes_local_iso"}[]): for a
  local analytic isomorphism $`g \colon N \to M` of manifolds modelled on one space and the pair
  $`(N, g^* I)`, over compacts $`K' \subseteq N`, $`K \subseteq M` with $`g(U_{K'}) \subseteq U_K`
  the succession of $`P(N, g^* I)` over $`U_{K'}` is the pull-back along $`g` of the succession of
  $`P(M, I)` over $`U_K`, up to blow-ups with empty centre; and there is a unique continuous map
  $`\tilde g \colon \tilde N \to \tilde M` over $`g` between the spaces of $`P(N, g^* I)` and
  $`P(M, I)`, a local analytic isomorphism mapping every fibre of $`\mathrm{prin}_{g^*I}`
  bijectively onto the fibre of $`\mathrm{prin}_I` over the image point, so that
  $`\tilde N = N \times_M \tilde M`;
- $`P` commutes with closed embeddings ({bpref "def:commutes_closed_analytic"}[]): for pairs
  $`(M, I)` and $`(N, J)` and a closed embedding of analytic manifolds $`\tau \colon N \to M`
  along which $`I` is the push-forward of $`J` ({bpref "def:pushforward_along"}[]), and compacts
  $`K' \subseteq N`, $`K \subseteq M` with $`\tau(U_{K'}) \subseteq U_K`, the succession of
  $`P(M, I)` over $`U_K` is the push-forward along $`\tau` of the succession of $`P(N, J)` over
  $`U_{K'}`, up to blow-ups whose centres lie outside the part over $`\tau(U_{K'})`.

Włodarczyk's (4), that the factorization over a larger compact restricts to the factorization over
a smaller one, is the compatibility of the family. This is the analytic counterpart of Kollár's
functorial principalization ({bpref "thm:principalization"}[]) for an empty boundary: the
principalization is chosen for all pairs at once, by one rule, compatibly with local analytic
isomorphisms and with closed embeddings. The three properties are
{decl}`IdealSheaf.IsLocallyFinitelyPrincipalizedBy`,
{decl}`IdealSheafPair.CommutesWithLocalAnalyticIsomorphisms` and
{decl}`IdealSheafPair.CommutesWithClosedEmbeddings`, the second through the pull-back of a
succession up to empty blow-ups ({bpref "def:pullback_up_to_empty"}[]) and the third through the
push-forward along a closed embedding ({bpref "def:pushforward_up_to_empty"}[]).
::::

:::proof "thm:wlo09_principalization"
The model space is identified with $`\mathbb{K}^n`. On a manifold modelled on $`\mathbb{K}^n` the
value at $`I` is Kollár's order reduction of the marked ideal $`(M, I, \emptyset, 1)`
{cite Kol07}[72], over $`\mathbb{R}` or $`\mathbb{C}` alike: the marked family of the concrete
order-reduction tower at the mark $`1` ({cite Kol07}[Theorem 107], the three-step construction of
{cite Kol07}[111]), over the relatively compact opens, glued along the exhaustion of the manifold.
Over every relatively compact open its value is a smooth blow-up sequence of order at least $`1`
for $`(I, \emptyset)` whose marked transform has order less than $`1` at the end; so its
exceptional divisors are simple normal crossings families having simple normal crossings with the
centres, which gives (1) and (2), the total transform of $`I` is Kollár's monomial in the final
exceptional divisor {cite Kol07}[72], which gives (3), and the centres lie over the support of $`I`,
which gives the isomorphism off the support. The marked family commutes with local analytic
isomorphisms {cite Kol07}[Theorem 107 (2)]: the value of $`g^* I` over a relatively compact open of
$`N` is the pull-back of the value of $`I` over its image with the empty blow-ups erased, and by the
compatibility of the family the pull-back up to empty blow-ups of the value over any larger
relatively compact open. On a manifold modelled on $`E` the value is the value on the re-modelled
manifold carried back along the identification, with every condition and the pull-back relation;
the assignment on the pairs reads this construction at the model space, the manifold and the
ideal sheaf of each pair.
The lift $`\tilde g` is glued from the pull-back relation: over the neighbourhood $`U_{K'}` of a
compact of $`N`, the compact closure of $`g(U_{K'})` lies in some $`U_K`, the relation supplies a
local analytic isomorphism between the last stages over $`g`, bijective on the fibres, and through
the identifications of the last stages with the preimages of $`U_{K'}` and $`U_K` it is a map from
a piece of $`\tilde N` to $`\tilde M` over $`g`; two such maps agree on an overlap, because a map
over $`g` is determined on the dense set over which the composite blow-down of $`U_K` is injective
and $`\tilde M` is Hausdorff, so the pieces glue, and the same argument gives the uniqueness.

The commutation with closed embeddings is Kollár's Claim 71.2 {cite Kol07}[72]: the marked family at
the mark $`1` in dimension $`n` commutes with closed embeddings of empty divisor through the marked
family in dimension $`n - s`. For a hypersurface this is {cite Kol07}[Theorem 107 (3)] at the mark
$`1`, which the three-step construction satisfies because an ideal containing the ideal of a
hypersurface has order at most $`1`, so that its marked order reduction at the mark $`1` is a single
round of the order reduction of {cite Kol07}[Theorem 103], whose commutation with closed embeddings
is {cite Kol07}[Theorem 103 (3)]; the general codimension follows along a flag of hypersurfaces
{cite Kol07}[108]. On the standard models a closed embedding $`\tau \colon N \to M` identifies $`N`
with the bundled closed submanifold $`\tau(N)`, by the universal property of the embedding, which
fixes the dimension of $`N`; the value over $`U_K` is the push-forward of the value over the trace
of $`U_K` on $`\tau(N)`, the value over $`U_{K'}` is the pull-back up to empty blow-ups of that
value through the identification, and the embeddings of the relation are the inclusions of the
stages of the push-forward after the lifts of the pull-back, which are bijective on the fibres over
$`U_{K'}`. The relation is carried back from the re-modelled manifolds along the identifications of
the two models.
:::

# Embedded desingularization of analytic spaces
%%%
tag := "sec-wlo09-embedded"
%%%

Włodarczyk's embedded desingularization of a closed subspace of a manifold is stated, like his
principalization, over every compact subset, and as an assignment on all pairs of a manifold and a
closed subspace. It asserts that the succession over every compact desingularizes the subspace,
and that the assignment commutes with local analytic isomorphisms.

*Embedded desingularization of a subspace.*

::::definition "def:manifold_desingularized_by" (lean := "AnalyticManifold.IdealSheaf.IsDesingularizedBy")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.2]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
For a finite succession `S` of an analytic manifold $`M` with centres $`C_i`, and the closed
subspace $`Y` with ideal sheaf $`I`, `I.IsDesingularizedBy S` says, with composite $`\sigma`,
exceptional divisors $`E_i` and strict transforms $`Y_i`, $`\tilde Y = Y_r`: the centres are smooth;
`S.HasSncBoundaries ⊤` ({bpref "def:manifold_hironaka_conditions"}[]); no point of a centre lies
over a point of $`\operatorname{Reg}(Y)`; the support of $`E_r` is the preimage of
$`\operatorname{Sing}(Y) = Y \setminus \operatorname{Reg}(Y)`; $`\tilde Y` is smooth and
{decl}`IsSncBoundaryTransversalTo` holds for $`E_r` and $`\tilde Y`; and
$`\sigma^*(I_Y) = I_{\tilde Y} \cdot I_{\tilde E}` ({decl}`IsMulBoundaryMonomial`,
{bpref "def:embedded_snc"}[]) {cite Wlo09}[Theorem 2.0.2 (1)–(3), (6)]. It is the analogue on manifolds
of {decl}`EmbeddedPair.IsDesingularizedBy` on schemes ({bpref "def:desingularized_by"}[]).
::::

*Locally finite embedded desingularization.*

::::definition "def:locally_finite_embedded_desingularization" (lean := "AnalyticManifold.IdealSheaf.IsLocallyFinitelyDesingularizedBy")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.2]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
`I.IsLocallyFinitelyDesingularizedBy F`, for the ideal sheaf $`I` of a closed subspace $`Y` of
$`M` and a compatible family $`F` with map $`\mathrm{res}_{Y,M}`, says that $`F` is a locally
finite embedded desingularization of $`Y` in Włodarczyk's sense: $`\mathrm{res}_{Y,M}` is proper,
it is an isomorphism over the complement of the singular locus
$`\operatorname{Sing}(Y) = Y \setminus \operatorname{Reg}(Y)`, and for every compact $`K` the
succession `F.seq K` over the neighbourhood $`U_K` desingularizes $`Y \cap U_K`
(`I.IsDesingularizedBy`, {bpref "def:manifold_desingularized_by"}[]), has no empty centre and has
every centre of codimension at least two, or of codimension one inside the exceptional divisor of
its stage, and $`\tilde M` carries an exceptional divisor $`E` and a strict transform $`\tilde Y`
gluing the last exceptional divisors and strict transforms of the successions: over every compact
$`K`, read on the last stage $`U_r` of `F.seq K` through its identification `F.toSpace K` with
$`\mathrm{res}_{Y,M}^{-1}(U_K)`, $`E` is $`E_r` and $`\tilde Y` the strict transform $`Y_r` of
$`Y \cap U_K` ({bpref "def:succession_transforms"}[]). Then $`E` is the reduced ideal sheaf of a
simple normal crossings family of hypersurfaces, with which $`\tilde Y` has simple normal
crossings, transversally ({bpref "def:embedded_snc"}[]), and
$`\mathrm{res}_{Y,M}^*(I_Y) = I_{\tilde Y} \cdot I_{\tilde E}` with $`\tilde E` near every point
an effective combination of the components of $`E`. His clause (5) is the compatibility of the
family ({bpref "def:compatible_family"}[]).
::::

*The inputs: embedded pairs.*

::::definition "def:embedded_pair_manifold" (lean := "AnalyticManifold.EmbeddedPair, AnalyticManifold.EmbeddedPair.pullback, AnalyticManifold.EmbeddedPair.hasUnderlyingManifold")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.2]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
An *embedded pair* $`(M, Y)` is an analytic manifold $`M` over $`\mathbb{K}`, modelled on a
finite-dimensional space, with a reduced closed analytic subspace $`Y \subseteq M`, given by its
ideal sheaf: the input of Włodarczyk's embedded desingularization, the counterpart on manifolds of
the algebraic embedded pair ({bpref "def:embedded_pair"}[]), with the model space part of the
input as for {bpref "def:ideal_sheaf_pair"}[]; the embedded pairs have underlying manifolds
({bpref "def:compatible_family_assignment"}[]). `T.pullback g hg` is the embedded pair
$`(N, g^{-1}(Y))` over a local analytic isomorphism $`g \colon N \to M` of manifolds modelled on
one space; its subspace is reduced since the germ maps of $`g` are ring isomorphisms.
::::

*Commuting with local analytic isomorphisms.*

::::definition "def:commutes_local_iso_on" (lean := "AnalyticManifold.EmbeddedPair.CommutesWithLocalAnalyticIsomorphisms")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.2 (4); Theorem 3.5.1 (2)]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
`EmbeddedPair.CommutesWithLocalAnalyticIsomorphisms R`, for a compatible family assignment $`R`
on the embedded pairs: for a local analytic isomorphism $`g \colon N \to M` of manifolds modelled
on one space, the embedded pair $`(N, g^{-1}(Y))` and compacts $`K' \subseteq N`,
$`K \subseteq M` with $`g(U_{K'}) \subseteq U_K`, the succession of $`R(N, g^{-1}(Y))` over
$`U_{K'}` is the pull-back along $`g` of the succession of $`R(M, Y)` over $`U_K`, up to blow-ups
with empty centre ({bpref "def:pullback_up_to_empty"}[]): the first half of
{cite Wlo09}[Theorem 2.0.2 (4)], read as {cite Wlo09}[Theorem 3.5.1 (2)], the per-compact form of
{bpref "def:commutes_local_iso"}[] (the lift of the local isomorphism is not stated for the
embedded desingularization).
::::

*Commuting with closed embeddings of ambient manifolds.*

::::definition "def:commutes_closed_embeddings_on" (lean := "AnalyticManifold.EmbeddedPair.CommutesWithClosedEmbeddings")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.2 (4); Kol07, 34.3]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
`EmbeddedPair.CommutesWithClosedEmbeddings R`, for a compatible family assignment $`R` on the
embedded pairs: for embedded pairs $`(M, Y)` and $`(N, Y')` and a closed embedding of analytic
manifolds $`\tau \colon N \to M` along which the ideal sheaf of $`Y` is the push-forward of that
of $`Y'` ({bpref "def:pushforward_along"}[]: $`\tau(N)` a closed submanifold containing $`Y`,
and $`Y' = \tau^{-1}(Y)`), such that no connected component of $`N` lies in $`Y'` (the ideal
sheaf of $`Y'` has nonzero stalks, Kollár's $`0 \neq I_Y`), and compacts $`K' \subseteq N`,
$`K \subseteq M` with $`\tau(U_{K'}) \subseteq U_K`, the succession of $`R(M, Y)` over $`U_K` is
the push-forward along $`\tau` of the succession of $`R(N, Y')` over $`U_{K'}`, up to blow-ups
whose centres lie outside the part over $`\tau(U_{K'})`
({bpref "def:pushforward_up_to_empty"}[]): the second half of {cite Wlo09}[Theorem 2.0.2 (4)],
"embeddings of ambient varieties", read as {cite Kol07}[34.3] as {bpref "def:commutes_closed_analytic"}[]
reads the last sentence of Theorem 2.0.3.
::::

::::theorem "thm:wlo09_embedded" (lean := "AnalyticManifold.exists_embeddedDesingularization")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.2]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
Let $`\mathbb{K}` be $`\mathbb{R}` or $`\mathbb{C}`. There is a compatible family assignment $`R`
on the embedded pairs $`(M, Y)` of an analytic manifold $`M` over $`\mathbb{K}`, modelled on a
finite-dimensional space, and a reduced closed analytic subspace $`Y \subseteq M` with ideal sheaf
$`I_Y` ({bpref "def:embedded_pair_manifold"}[], {bpref "def:compatible_family_assignment"}[]) —
to each pair a map $`\mathrm{res}_{Y,M} \colon \tilde M \to M` which over an open neighbourhood
$`U_K` of every compact $`K \subseteq M` is, compatibly across compacts, a finite succession of
blow-ups $`U_K = U_0 \leftarrow U_1 \leftarrow \cdots \leftarrow U_r` with smooth closed centres
$`C_i` and composite $`\sigma_K \colon U_r \to U_K` — such that:

- every value $`R(M, Y)` is a locally finite embedded desingularization of $`Y`
  ({bpref "def:locally_finite_embedded_desingularization"}[]): $`\mathrm{res}_{Y,M}` is proper
  and an isomorphism over the complement of the singular locus
  $`\operatorname{Sing}(Y) = Y \setminus \operatorname{Reg}(Y)`, and for every compact $`K`, with
  exceptional divisors $`E_i` (the boundaries started at the empty boundary), strict transforms
  $`Y_i` of $`Y \cap U_K` and $`\tilde Y = Y_r`: every centre $`C_i` is smooth; (1) every $`E_i`
  has simple normal crossings with $`C_i`, and $`E_r` has simple normal crossings; (2) no point of
  a centre $`C_i` lies over a point of $`\operatorname{Reg}(Y)`; the support of $`E_r` is the
  preimage $`\sigma_K^{-1}(\operatorname{Sing} Y)`; (3) $`\tilde Y` is smooth and has simple
  normal crossings with $`E_r`, no component of $`E_r` containing $`\tilde Y` near a point;
  (6) $`\sigma_K^*(I_Y) = I_{\tilde Y} \cdot I_{\tilde E}`, with $`\tilde E` near every point
  an effective combination of the components of $`E_r`; and $`\tilde M` carries an exceptional
  divisor $`E` and a strict transform $`\tilde Y`: $`E` is the reduced ideal sheaf of a simple
  normal crossings family of hypersurfaces, with which $`\tilde Y` has simple normal crossings,
  transversally, $`\mathrm{res}_{Y,M}^*(I_Y) = I_{\tilde Y} \cdot I_{\tilde E}`
  with $`\tilde E` near every point an effective combination of the components of $`E`, and over
  every compact $`K`, read on $`U_r \cong \mathrm{res}_{Y,M}^{-1}(U_K)`, $`E` is $`E_r` and
  $`\tilde Y` is $`Y_r`; no centre of any succession is empty, and every centre has codimension
  at least two, or has codimension one and lies in the exceptional divisor of its stage;
- (4) $`R` commutes with local analytic isomorphisms ({bpref "def:commutes_local_iso_on"}[]): for
  a local analytic isomorphism $`g \colon N \to M` of manifolds modelled on one space, the
  embedded pair $`(N, g^{-1}(Y))` and compacts $`K' \subseteq N`, $`K \subseteq M` with
  $`g(U_{K'}) \subseteq U_K`, the succession of $`R(N, g^{-1}(Y))` over $`U_{K'}` is the pull-back
  along $`g` of the succession of $`R(M, Y)` over $`U_K`, up to blow-ups with empty centre;
- (4) $`R` commutes with closed embeddings of ambient manifolds
  ({bpref "def:commutes_closed_embeddings_on"}[]): for embedded pairs $`(M, Y)` and $`(N, Y')`
  and a closed embedding of analytic manifolds $`\tau \colon N \to M` along which $`I_Y` is the
  push-forward of $`I_{Y'}` ($`\tau(N)` a closed submanifold containing $`Y`, and
  $`Y' = \tau^{-1}(Y)`), such that no connected component of $`N` lies in $`Y'`, and compacts
  $`K' \subseteq N`, $`K \subseteq M` with $`\tau(U_{K'}) \subseteq U_K`, the succession of
  $`R(M, Y)` over $`U_K` is the push-forward along $`\tau` of the succession of $`R(N, Y')` over
  $`U_{K'}`, up to blow-ups whose centres lie outside the part over $`\tau(U_{K'})`.

Włodarczyk's (5), that the factorization over a larger compact restricts to the factorization over
a smaller one, is the compatibility of the family: the succession over $`K \subseteq K'`,
restricted to $`U_K`, is an extension of the succession over $`K` {cite Wlo09}[Definition 3.2.6].
This is the analytic counterpart of Włodarczyk's algebraic embedded desingularization
({bpref "thm:embedded"}[]), in the locally finite form of {bpref "thm:mt2pp"}[], chosen for all
embedded pairs at once, by one rule, compatibly with local analytic isomorphisms and with closed
embeddings of ambient manifolds.

The three properties are {decl}`IdealSheaf.IsLocallyFinitelyDesingularizedBy`
({bpref "def:locally_finite_embedded_desingularization"}[]), whose conditions on the successions
are {decl}`IdealSheaf.IsDesingularizedBy` ({bpref "def:manifold_desingularized_by"}[]), built on
the strict transforms of a closed subspace ({bpref "def:succession_transforms"}[]), the simple
locus $`\operatorname{Reg}(Y)` and reducedness ({bpref "def:ideal_sheaf_vocab"}[]), and the
transversal simple normal crossings and monomial factorization predicates
({bpref "def:embedded_snc"}[]), in which it also states its conditions on the exceptional divisor
and the strict transform on $`\tilde M`;
{decl}`EmbeddedPair.CommutesWithLocalAnalyticIsomorphisms`
({bpref "def:commutes_local_iso_on"}[]), through the pull-back of a succession up to empty
blow-ups ({bpref "def:pullback_up_to_empty"}[]); and
{decl}`EmbeddedPair.CommutesWithClosedEmbeddings` ({bpref "def:commutes_closed_embeddings_on"}[]),
through the push-forward along a closed embedding ({bpref "def:pushforward_up_to_empty"}[]).
::::

:::proof "thm:wlo09_embedded"
The model space is identified with $`\mathbb{K}^n` and $`I` is transported to the model, where,
made the unit ideal on the connected components of $`M` on which it vanishes (a union of
components, by the identity theorem), it forms a triple with the empty boundary family. Włodarczyk's modification of the resolution
algorithm for the marked ideal $`(M, I, \emptyset, 1)` (the proof of {cite Wlo09}[Theorem 7.4.1]: the
algorithm is stopped as soon as the controlled transform is the ideal of a smooth hypersurface of
maximal contact), run on the real- or complex-analytic form of the blow-up sequence functors of
{cite Kol07}[Theorem 103] and {cite Kol07}[Theorem 107], gives an embedded desingularization functor over
the relatively compact opens of the model, which is glued along the exhaustion of the manifold to
a compatible family with a proper blow-down. Its centres lie over $`Y` by the order condition of the
algorithm, hence over $`\operatorname{Sing}(Y)` by (2), so the blow-down is an isomorphism over the
complement of $`\operatorname{Sing}(Y)`; and the support of $`E_r` is the preimage of
$`\operatorname{Sing}(Y)`, because off $`E_r` the composite blow-down is an isomorphism near the
point, carrying the smooth $`\tilde Y` onto $`Y`. Over the components where $`I` vanishes nothing
is blown up, the strict transform is the component itself and the exceptional divisor is empty,
so every condition holds for $`I` as it does for the modified ideal sheaf. The exceptional
families of the pieces glue to a locally finite simple normal crossings family on the glued
space, each member born on the piece where it first appears and continued along the embeddings of
the pieces, which carry exceptional families to exceptional families; $`E` is its reduced ideal
sheaf, and $`\tilde Y` is the saturation of the total transform $`\mathrm{res}_{Y,M}^*(I)` by $`E`,
which on each piece is the last strict transform {cite BM97}[Proposition 3.13], the strict transform
being, at a point of the last stage, the saturation of the total transform by the exceptional
ideal: near a point of $`\tilde Y` the exceptional ideal is a product of coordinates and the ideal
of $`\tilde Y` a prime generated by coordinates not among them, so the saturation changes
nothing. The conditions on $`E` and $`\tilde Y` are read on the pieces through the inclusions,
which are local analytic isomorphisms. The functor commutes with local analytic isomorphisms
{cite Kol07}[34.1]: the value of $`g^* I` over a relatively compact
open is the pull-back of the value of $`I` over its image with the empty blow-ups erased, and by
the compatibility of the family the pull-back up to empty blow-ups of the value over any larger
relatively compact open. The commutation with closed embeddings of ambient manifolds is that of
the functor over the relatively compact opens, through the functor of the lower dimension at the
restriction of $`I` to the submanifold, which is reduced when $`I` is and contains the ideal of the
submanifold: on the standard models the embedding identifies $`N` with the bundled submanifold,
the value over $`U_K` is the push-forward of the value over the trace of $`U_K` on $`\tau(N)`, and
the value over $`U_{K'}` is the pull-back up to empty blow-ups of that value through the
identification, as for the principalization; the modification of $`I` on its zero components is
invisible along $`\tau(N)`, since $`J` has nonzero stalks. Each condition and the two relations
are carried back along the identifications of the models. A centre of codimension at most one
lies over $`\operatorname{Sing}(Y)` and has simple normal crossings with the exceptional divisor
of its stage; off that divisor the composite blow-down is a local isomorphism and would carry
the centre, a smooth hypersurface or an open set, into $`\operatorname{Sing}(Y)`, which contains
neither: the singular locus of a reduced subspace contains no smooth hypersurface germ, since the
stalk of the ideal sheaf at a point of such a germ would lie in every power of its equation,
hence vanish by Krull's intersection theorem; so the centre lies in the exceptional divisor and
has codimension one.
:::

# Resolution of analytic spaces
%%%
tag := "sec-spaces"
%%%

The resolution of analytic spaces is a resolution assignment
({bpref "def:resolution_assignment"}[]), a morphism $`\Pi_X \colon R(X) \to X` for every analytic
space $`X`, here on the reduced spaces. It asserts of the values that they are strong resolutions
onto the closure of the simple locus and locally composites of blow-ups of an ambient manifold, and
of the assignment that it lifts isomorphisms between open subspaces of inputs and local analytic
isomorphisms between inputs. The resolution of a single reduced complex space asserts
the first two properties again.

*Strong resolutions of analytic spaces.*

::::definition "def:space_resolution" (lean := "AnalyticSpace.Hom.IsResolution, AnalyticSpace.Hom.IsStrongResolution, AnalyticSpace.Hom.IsStrongResolutionOntoClosureRegularLocus")
%%%
paperIdentity := some { label := "[Kol07, (2) and (3)]", href := "https://arxiv.org/abs/math/0508332" }
%%%
For a morphism $`\pi \colon R \to X` of $`K`-analytic spaces:

- `π.IsResolution`: $`R` is non-singular, $`\pi` is proper, and $`\pi` is bimeromorphic
  (Kollár: birational {cite Kol07}[(2)]; {cite Wlo09}[Theorem 2.0.1]), read onto its image: an
  isomorphism over an open subset $`U \subseteq X` whose preimage is dense in $`R`. Kollár asks
  for $`\pi` projective; only the properness that projectivity implies is recorded. The density is
  asked of the preimage and not of $`U`: over $`\mathbb{R}` the simple locus of a reduced space
  need not be dense, and then no resolution is an isomorphism over a dense open subset of $`X`.
- `π.IsStrongResolution` {cite Kol07}[(3)], conditions (1)–(3) of Kollár's Theorem 45: a resolution
  that is an isomorphism over the simple locus `X.regularLocus` and such that
  $`\pi^{-1}(\operatorname{Sing} X)` is the support of a closed subspace `E` with
  `E.IsSncBoundary` ({bpref "def:closed_subspace"}[]).
- `π.IsStrongResolutionOntoClosureRegularLocus`: a strong resolution whose image is the closure
  of the simple locus of $`X`, conditions (1)–(3) of Theorem 45 with the image clause. Over
  $`\mathbb{C}` the simple locus of a reduced space is dense and the clause is the surjectivity of
  $`\pi`; over $`\mathbb{R}` it need not be dense, and $`\pi` misses the part of $`X` away from the
  closure of the simple points.
::::

*Local factorization through ambient blow-ups.*

::::definition "def:ambient_factorization" (lean := "ChartedSpace.sigma, ChartedSpace.sigmaOfNonempty, AnalyticManifold.sigmaOpens, AnalyticManifold.IdealSheaf.toAnalyticSpace, AnalyticManifold.IdealSheaf.toAnalyticSpaceι, AnalyticManifold.IdealSheaf.overPiece, AnalyticSpace.Hom.AmbientBlowUpFactorization, AnalyticSpace.Hom.IsLocallyFiniteAmbientBlowUpComposite")
%%%
paperIdentity := some { label := "[Kol07, Theorem 45 (4)]", href := "https://arxiv.org/abs/math/0508332" }
%%%
Condition (4) of the resolution theorem describes $`\Pi_X` locally as a composite of blow-ups of an
ambient manifold restricted to strict transforms. The ambient is a disjoint union
$`A = \bigsqcup_i G_i` of countably many open subsets of $`K^n`
({decl}`AnalyticManifold.sigmaOpens`, built on the charted space structure of a disjoint union,
{decl}`ChartedSpace.sigma`, {decl}`ChartedSpace.sigmaOfNonempty`). An ideal sheaf $`J` on $`A` cuts
out the closed subspace $`\operatorname{Sp}(A)/J` ({decl}`IdealSheaf.toAnalyticSpace`, with its
morphism {decl}`toAnalyticSpaceι`), and {decl}`overPiece` is its part over $`G_i`.

An ambient blow-up factorization `f.AmbientBlowUpFactorization U` of $`f \colon Y \to X` over an
open $`U` ({decl}`Hom.AmbientBlowUpFactorization`) consists of finitely many open subspaces $`U_i`
covering $`U`, closed embeddings of the $`X|_{U_i}` into open subsets $`G_i \subseteq K^n`, a
finite succession of blow-ups of the ambient $`A` with smooth centres, the strict transforms of
$`\bigsqcup X|_{U_i}`, the last one a closed submanifold, and isomorphisms over each $`U_i`
identifying $`f^{-1}(U_i) \to U_i` with the restricted composite {cite Kol07}[Warning 23];
{cite Wlo09}[Theorem 2.0.2]. `f.IsLocallyFiniteAmbientBlowUpComposite` asks for such a factorization
over every relatively compact open $`U \subseteq X`.
::::

*Lifting local analytic isomorphisms.*

::::definition "def:lifts_local_isomorphisms" (lean := "AnalyticSpace.Hom.IsLocalIso, AnalyticSpace.ResolutionAssignment.LiftsLocalIsomorphisms")
%%%
paperIdentity := some { label := "[Kol07, Theorem 45 (5); Wlo09, Theorem 2.0.1 (3)]", href := "https://arxiv.org/abs/math/0508332" }
%%%
A morphism $`\varphi \colon X' \to X` of analytic spaces is a *local analytic isomorphism*
({decl}`Hom.IsLocalIso`) when every point of $`X'` has an open neighbourhood $`U'` which $`\varphi`
maps isomorphically onto an open subspace $`X|_V`: open immersions, isomorphisms, covering maps and
the morphism $`\coprod U_i \to X` from the disjoint union of an open cover, injective or not. A
morphism $`\psi \colon A \to B` is *the only morphism over* $`\varphi \colon X \to Y`, along
$`p \colon A \to X` and $`q \colon B \to Y`, when the morphisms $`\psi'` with
$`q \circ \psi' = \varphi \circ p` are exactly $`\psi`. A resolution assignment $`R` on inputs $`C` ({bpref "def:resolution_assignment"}[])
*lifts local analytic isomorphisms* (`R.LiftsLocalIsomorphisms`) in two forms: every isomorphism
$`\varphi \colon X|_U \to Y|_V` between open subspaces of two inputs lifts to exactly one morphism
$`\psi \colon R(X)|_{\Pi_X^{-1} U} \to R(Y)|_{\Pi_Y^{-1} V}` over $`\varphi`, an isomorphism; and
every local analytic isomorphism $`\varphi \colon X' \to X` between inputs lifts to exactly one
morphism $`\psi \colon R(X') \to R(X)` with $`\Pi_X \circ \psi = \varphi \circ \Pi_{X'}`, a local
analytic isomorphism. Over every open $`U'` which $`\varphi` maps isomorphically onto an open
subspace, the lift of $`\varphi` restricts to the lift of that isomorphism, since the restriction
lies over it and the lift of the first form is the only morphism over it. Because the lifts are
unique, they
respect identities and composition: $`R` is a functor on the groupoid of isomorphisms between open
subspaces of inputs and on the local analytic isomorphisms between inputs. The first form stands
for condition (5) of Kollár's Theorem 45, "$`R` commutes with smooth $`K`-morphisms", for the étale
morphisms that are injective, and the second is {cite Wlo09}[Theorem 2.0.1 (3)] and the case of étale
morphisms of Kollár's (5); the two are bundled as the two conditions of Kollár's 34.1 are in
{decl}`CommutesWithSmoothMorphisms` ({bpref "def:commutes_smooth"}[]). Smooth morphisms that are not
étale are not lifted. For strong resolutions, the second form follows from the first by gluing the
local lifts over the opens on which $`\varphi` is injective, the gluing being compatible on the
overlaps because a morphism out of a non-singular space is determined on a dense open subset.
::::

*The inputs: reduced spaces.*

::::definition "def:reduced_space" (lean := "AnalyticSpace.ReducedSpace")
%%%
paperIdentity := some { label := "[Kol07, Theorem 45]", href := "https://arxiv.org/abs/math/0508332" }
%%%
The reduced $`K`-analytic spaces, as a full subcategory of the $`K`-analytic spaces
({decl}`ReducedSpace`, the counterpart of {bpref "def:inputs_36"}[]), are the inputs of the
resolution of analytic spaces. Kollár states the theorem for every separable analytic space; his
notion of resolution is stated for varieties, and his proofs are for reduced spaces, extended to
reducible ones. A non-reduced space $`X` is resolved through its reduction: the resolution of
$`X_{\mathrm{red}}` followed by the closed immersion $`X_{\mathrm{red}} \to X`.
::::

::::theorem "thm:spaces" (lean := "AnalyticSpace.exists_functorial_resolution")
%%%
paperIdentity := some { label := "[Kol07, Theorem 45]", href := "https://arxiv.org/abs/math/0508332" }
%%%
For $`K = \mathbb{R}` or $`\mathbb{C}` there is a resolution assignment
$`X \mapsto (\Pi_X \colon R(X) \to X)` on the reduced $`K`-analytic spaces
({bpref "def:reduced_space"}[], {bpref "def:resolution_assignment"}[]) such that for every input
$`X`:

1. $`R(X)` is non-singular;
2. $`\Pi_X` is an isomorphism over the simple points of $`X`;
3. $`\Pi_X^{-1}(\operatorname{Sing} X)` is the support of a simple normal crossings divisor;
4. $`\Pi_X` is proper and bimeromorphic onto its image, and the image of $`\Pi_X` is the closure
   of the simple points; over every relatively compact open subset of $`X`, $`\Pi_X` is a finite
   composite of blow-ups of smooth centres of an ambient manifold restricted to strict transforms;
5. every analytic isomorphism between open subspaces of two inputs lifts to exactly one morphism
   of the resolutions over it, an isomorphism, and every local analytic isomorphism
   $`\varphi \colon X' \to X` between inputs lifts to exactly one morphism $`R(X') \to R(X)` over
   it, itself a local analytic isomorphism, which restricts over every open on which $`\varphi` is
   injective to the lift of the isomorphism of open subspaces.

This is resolution of singularities for analytic spaces, functorial for local analytic
isomorphisms: the lifts are unique, so they respect identities and composition, and the resolution
is local on the space. Kollár's condition (5) asks more, the commutation with all smooth morphisms;
the lifting of local analytic isomorphisms is its case of étale morphisms and is
{cite Wlo09}[Theorem 2.0.1 (3)]. Conditions (1)–(3), with properness, bimeromorphy and the image
clause, are {decl}`Hom.IsStrongResolutionOntoClosureRegularLocus`
({bpref "def:space_resolution"}[]), condition (4) is
{decl}`Hom.IsLocallyFiniteAmbientBlowUpComposite` ({bpref "def:ambient_factorization"}[]), and
condition 5 is
{decl}`ResolutionAssignment.LiftsLocalIsomorphisms` ({bpref "def:lifts_local_isomorphisms"}[]).
The bimeromorphy follows from (2) and (3): the preimage of the simple locus is the complement of
the support of a simple normal crossings divisor, hence dense.

Analytic spaces, their morphisms, simple points and closed subspaces are in the chapter
{ref "ch-spaces"}[Analytic spaces]: {bpref "def:analytic_space"}[], {bpref "def:restrict_space"}[],
{bpref "def:closed_subspace"}[], {bpref "def:resolution_assignment"}[].
::::

:::proof "thm:spaces"
An embedded desingularization functor for closed subspaces of manifolds (the order-reduction
algorithm applied to the ideal of the subspace in every dimension, functorial under local analytic
isomorphisms and compatible with closed embeddings of the ambient manifolds) is applied to local
embeddings of the reduced space into manifolds. The resolutions of the pieces are independent of
the embedding chosen and glue over the exhaustion of the space by relatively compact opens to
$`R(X)`; the conditions are read off the properties of the functor, the lifting of condition (5)
from its functoriality. The lift of an isomorphism between open subspaces is the only morphism over
it, because two morphisms out of a non-singular open part of $`R(X)` over the same morphism agree
over the simple locus, where the resolutions are isomorphisms, a dense open subset. The lifting of
local analytic isomorphisms follows: the lifts over the opens on which $`\varphi` is injective
agree on the overlaps by the same rigidity, and glue.
:::

# Resolution of a reduced complex-analytic space
%%%
tag := "sec-spaces-complex"
%%%

::::theorem "thm:spaces_complex" (lean := "AnalyticSpace.exists_surjective_resolution_of_isReduced")
%%%
paperIdentity := some { label := "[Kol07, Theorem 45 (1)–(4)], over ℂ", href := "https://arxiv.org/abs/math/0508332" }
%%%
Let $`X` be a reduced complex-analytic space. Then there is a morphism $`\pi \colon R \to X` such
that

1. $`R` is non-singular;
2. $`\pi` is an isomorphism over the simple points of $`X`;
3. $`\pi^{-1}(\operatorname{Sing} X)` is the support of a simple normal crossings divisor;
4. $`\pi` is proper and bimeromorphic onto its image and, over every relatively compact open subset
   of $`X`, a finite composite of blow-ups of smooth centres of an ambient manifold restricted to
   strict transforms;
5. $`\pi` is surjective.

This is resolution of singularities for a single reduced complex space, without the functoriality
of the resolution of analytic spaces ({bpref "thm:spaces"}[]). Conditions (1)–(3), with properness
and bimeromorphy, are {decl}`Hom.IsStrongResolution` ({bpref "def:space_resolution"}[]), and (4) is
{decl}`Hom.IsLocallyFiniteAmbientBlowUpComposite` ({bpref "def:ambient_factorization"}[]).
::::

:::proof "thm:spaces_complex"
The specialization of {bpref "thm:spaces"}[] to $`K = \mathbb{C}`: its conditions (1)–(4) are
taken as they stand, its condition on the image, $`\operatorname{range} \pi = \overline{X^{ns}}`,
becomes surjectivity because the simple locus of a reduced complex space is dense, and the lifting
condition (5) is dropped.
:::
