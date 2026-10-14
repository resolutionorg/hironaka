import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import Blueprint.SchemeVocabulary
import Hironaka.Manifold.Snc.Defs
import Hironaka.Manifold.Jacobian.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Set Filter Topology TopologicalSpace
open AnalyticManifold Manifold

set_option verso.blueprint.autoDeps true
-- Infer from directly referenced declarations only, as before v4.34; walking through unassociated
-- helpers would traverse Mathlib.
set_option verso.blueprint.autoDeps.expandUntagged false

#doc (Manual) "Ideal sheaves, submanifolds and blow-ups" =>
%%%
tag := "ch-manifolds"
file := "manifolds"
%%%

The analytic theorems are written in a vocabulary collected in the namespace `AnalyticManifold`,
built on an infrastructure in the namespace `Manifold`: the sheaf of analytic functions on a
manifold and its germs, locally finitely generated ideal sheaves, closed submanifolds and blow-ups
with smooth centre in the sense of Bierstone–Milman {cite BM88}[Definition 4.1], simple normal
crossings families of hypersurfaces, and the Jacobian ideal. The field is `𝕜` (`ℝ` for the main
theorems, `ℝ` or `ℂ` where `RCLike 𝕜` suffices) and the model space a normed space `E`.

# Analytic manifolds and maps

::::definition "def:analytic_manifold" (lean := "AnalyticManifold, AnalyticManifold.carrier, AnalyticManifold.top, AnalyticManifold.charted, AnalyticManifold.manifold, AnalyticManifold.t2, AnalyticManifold.secondCountable, AnalyticManifold.instCoeSortType, AnalyticMap, AnalyticManifold.restrict, AnalyticManifold.inclusion")
%%%
paperIdentity := some { label := "[Hir64, pp. 119–121]", href := "https://doi.org/10.2307/1970486" }
%%%
An `AnalyticManifold 𝕜 E` is a bundled analytic manifold modelled on `E`: a type of points
({decl}`carrier`) with a topology ({decl}`top`), a charted-space structure ({decl}`charted`) with
analytic chart changes ({decl}`manifold`, Mathlib's {decl}`IsManifold` at smoothness $`\omega`),
Hausdorff ({decl}`t2`) and second countable ({decl}`secondCountable`), without boundary; the
coercion {decl}`instCoeSortType` lets `M` stand for its type of points. For `E` finite-dimensional
this is a pure-dimensional non-singular analytic $`\mathbb{K}`-space in Hironaka's sense; his
non-singular spaces may have components of different dimensions.

An `AnalyticMap M N` is a bundled analytic map (Mathlib's `C^ω` maps). An open subset $`U` of $`M`
is again an analytic manifold, `M.restrict U`, with the inclusion `M.inclusion U`; this is how
Włodarczyk's neighbourhoods $`U_K` of compact sets become manifolds.
::::

# The sheaf of analytic functions and germs

::::definition "def:structure_sheaf" (lean := "Manifold.contMDiffLocalPredicate, Manifold.contMDiffSheaf, Manifold.contMDiffPresheafCommRing, Manifold.instCommRingObjOppositeOpensCarrierOfPresheafContMDiffSheaf, Manifold.contMDiffSheafCommRing, Manifold.structureSheaf, Manifold.constSection, Manifold.constHom, Manifold.chartSection, Manifold.coord, Manifold.contMDiffSheaf.coeFun, Manifold.contMDiffSheafCommRing.coeFun, Manifold.structureSheaf.coeFun")
%%%
paperIdentity := some { label := "[BM97, (0.3)]", href := "https://arxiv.org/abs/alg-geom/9508005" }
%%%
The *structure sheaf* `structureSheaf 𝕜 E M` is the sheaf of commutative rings
$`U \mapsto \{f \colon U \to \mathbb{K} \text{ analytic}\}`, the sheaf of regular functions of an
analytic manifold. It is built from the sheaf of $`C^n` functions to a $`C^n` ring
({decl}`contMDiffLocalPredicate`, {decl}`contMDiffSheaf`, {decl}`contMDiffPresheafCommRing` with its
ring instance, {decl}`contMDiffSheafCommRing`) at $`n = \omega`; a section is a function on its open
set (the coercions `coeFun` of the three sheaves). Its stalks are local rings, as the order of an
ideal sheaf at a point requires ({bpref "def:ideal_sheaf_general"}[]). The constants give its
$`\mathbb{K}`-algebra structure ({decl}`constSection`, {decl}`constHom`), and a chart $`\varphi`
with linear coordinates $`\psi` gives coordinate functions $`\psi_i \circ \varphi` as sections
({decl}`chartSection`) and as germs ({decl}`coord`).
::::

::::definition "def:germs" (lean := "Manifold.extendBy0, Manifold.germAt, Manifold.stalkToGermCocone, Manifold.stalkToGermHom, Manifold.stalkToGerm, Manifold.germCompRingHom")
The stalk of the structure sheaf at $`a` is identified with a subring of the ring of function germs
at $`a`: a section over a neighbourhood of $`a`, extended by zero ({decl}`extendBy0`), has a germ
({decl}`germAt`); these form a cocone over the neighbourhoods ({decl}`stalkToGermCocone`), whence
the ring map from the stalk to germs ({decl}`stalkToGermHom`, {decl}`stalkToGerm`), which is
injective. Composition of germs with a map tending to the base point is a ring map
({decl}`germCompRingHom`); it underlies the stalk maps of analytic maps ({bpref "def:pullback"}[]).
::::

# Ideal sheaves

::::definition "def:ideal_sheaf_general" (lean := "Manifold.IdealSheaf, Manifold.IdealSheaf.carrier, Manifold.IdealSheaf.res_mem, Manifold.stalkIdealOf, Manifold.IdealSheaf.stalkIdeal, Manifold.IdealSheaf.HasLocalGenerators, Manifold.IdealSheaf.ofStalks, Manifold.IdealSheaf.instTop, Manifold.IdealSheaf.instBot, Manifold.IdealSheaf.instMul, Manifold.IdealSheaf.support, Manifold.IdealSheaf.IsNonzeroEverywhere, Manifold.IdealSheaf.ord")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II″(N), p. 158]", href :=
    "https://doi.org/10.2307/1970486" }
%%%
For a sheaf of commutative rings $`\mathcal{O}` on a space $`X`, `Manifold.IdealSheaf 𝒪` is a
*locally finitely generated ideal sheaf*: ideals of sections over every open set ({decl}`carrier`),
closed under restriction ({decl}`res_mem`), satisfying the sheaf condition, whose stalk ideals
({decl}`stalkIdealOf`, {decl}`stalkIdeal`) are generated near every point by finitely many sections
({decl}`HasLocalGenerators`). This is Hironaka's "coherent sheaf of ideals", with "coherent" read as
locally finitely generated.

An ideal sheaf can be given by its stalks: {decl}`ofStalks` builds it from a family of stalk ideals
with local generators. The unit ideal `⊤`, the zero ideal `⊥` and products `J * J'` are built this
way (`hasLocalGenerators_top`, `_bot`, `_mul` and the instances {decl}`instTop`, {decl}`instBot`,
{decl}`instMul`). The support $`V(J) = \{a : J_a \ne \mathcal{O}_a\}` ({decl}`support`, Kollár's
cosupport) is the set of points of the closed subspace defined by $`J`; {decl}`IsNonzeroEverywhere`
asks every stalk to be nonzero; and `J.ord a` is the order
$`\nu_a(J) = \max\{p : J_a \subseteq \mathfrak m_a^p\}`, the order {decl}`IsLocalRing.ord` of the
stalk ideal ({bpref "def:order"}[]).
::::

::::definition "def:pullback" (lean := "Manifold.IdealSheaf.pullback, Manifold.germMapOn, Manifold.germMap, Manifold.stalkGermComp, Manifold.stalkEquivRange")
%%%
paperIdentity := some { label := "[BM97, Theorem 1.10]", href :=
    "https://arxiv.org/abs/alg-geom/9508005" }
%%%
The *pull-back* $`\varphi^* J` of an ideal sheaf along an analytic map is the ideal sheaf generated
by the $`f \circ \varphi`, $`f` a section of $`J`: Hironaka's total transform, Bierstone–Milman's
$`\sigma^{-1}(I)`. It is built stalkwise: the stalk map of $`\varphi` at $`b`,
$`s \mapsto s \circ \varphi` ({decl}`germMapOn`, {decl}`germMap`), is defined through germ
composition ({decl}`stalkGermComp`, with `stalkGermComp_mem_range`, {decl}`stalkEquivRange`,
`tendsto_of_contMDiffOn_of_eq`), and the images of local generators are local generators
(`hasLocalGenerators_pullback`).
::::

::::definition "def:ideal_sheaf_vocab" (lean := "AnalyticManifold.IdealSheaf, AnalyticManifold.IdealSheaf.stalkRing, Manifold.IdealSheaf.pullback, AnalyticManifold.IdealSheaf.restrict, AnalyticManifold.IdealSheaf.IsNonsingular, AnalyticManifold.IdealSheaf.IsReduced, AnalyticManifold.IdealSheaf.regularLocus")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II″(N), p. 158]", href :=
    "https://doi.org/10.2307/1970486" }
%%%
The statements use the names of `AnalyticManifold`: `IdealSheaf M` is a locally finitely generated
ideal sheaf of the structure sheaf of $`M`, whose stalk rings are `stalkRing M x`. Closed analytic
subspaces (centres, boundaries) are given by their ideal sheaves. The operations are the inverse
image $`f^{-1}(J) \cdot \mathcal{O}_M` along an analytic map (`J.pullback f f.contMDiff`) and the
    restriction
$`J|_U` to an open set (`J.restrict U`); the unit ideal sheaf $`\mathcal{O}_M` (`⊤`), products,
the set of points `J.support` (the cosupport) and Hironaka's order $`\nu(J_x)` (`J.ord x`) are
those of the general ideal sheaves ({bpref "def:ideal_sheaf_general"}[]). The predicates are:

- {decl}`IsNonzeroEverywhere` (of the general ideal sheaves): every stalk is nonzero, Hironaka's
  "sheaf of non-zero ideals";
- {decl}`IsNonsingular`: every point of the subspace is simple, $`\mathcal{O}_{M,x}/J_x` regular;
  vacuous on the empty subspace;
- {decl}`IsReduced`: the subspace is reduced, every stalk $`J_x` a radical ideal.

`J.regularLocus` is the set of simple points of the subspace, the points at which
$`\mathcal{O}_{M,x}/J_x` is a regular local ring: Włodarczyk's $`\operatorname{Reg}(Y)`
{cite Wlo09}[Theorem 2.0.2 (2)]. A point off the subspace is not in it, the zero ring not being local,
and `J.IsNonsingular` holds exactly when the support lies in the simple locus.

Hironaka's "reduced" and "everywhere of codimension one" for the boundary are not hypotheses of
Main Theorem II″(N): they follow from the simple normal crossings hypothesis {decl}`IsSncBoundary`
({bpref "def:snc_boundary"}[], {bpref "thm:mt2pp"}[]). {decl}`IsReduced` is the hypothesis on the
embedded subspace of Włodarczyk's embedded desingularization ({bpref "thm:wlo09_embedded"}[]).
::::

::::definition "def:vanishing" (lean := "Manifold.Germ.VanishesOn, Manifold.vanishingGermIdeal, Manifold.vanishingStalk")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II′(N) (iii), p. 156]", href :=
    "https://doi.org/10.2307/1970486" }
%%%
A function germ at $`x` *vanishes on* $`Z` if some representative is zero on $`Z` near $`x`
({decl}`Germ.VanishesOn`); such germs form an ideal ({decl}`vanishingGermIdeal`), and its trace on
the stalk of the structure sheaf is the *vanishing ideal* `vanishingStalk Z x`. These are the stalks
of Hironaka's reduced structure $`\mathrm{red}` on a closed set, used for boundaries
({bpref "def:manifold_transforms"}[], {bpref "def:snc_boundary"}[]).
::::

# Closed submanifolds and blow-ups

::::definition "def:submanifold" (lean := "Manifold.IsAdaptedChart, Manifold.IsClosedSubmanifold, Manifold.IsIdealSheafOf, Manifold.IsClosedSubmanifold.idealSheaf")
Fix linear coordinates $`\psi \colon E \cong \mathbb{K}^n`. A chart $`\varphi` is *adapted* to $`Y`
({decl}`IsAdaptedChart`) if on its source $`Y` is a coordinate subspace $`\{z_\sigma = 0\}` of the
coordinates $`\psi \circ \varphi`. A *closed submanifold* of codimension $`c`
(`IsClosedSubmanifold ψ Y c`) is a closed set with an adapted chart at each of its points. Its ideal
sheaf is specified by {decl}`IsIdealSheafOf` (cosupport $`Y`, stalks at the points of $`Y` spanned
by the adapted coordinates) and chosen by {decl}`IsClosedSubmanifold.idealSheaf` (the unit ideal
sheaf if none exists; existence and uniqueness are lemmas of the library).
::::

::::definition "def:manifold_blowup" (lean := "Manifold.blowUpChartMap, Manifold.IsBlowUpChart, Manifold.IsBlowUp, Manifold.IsBlowUp.contMDiff, AnalyticMap.IsMonoidalTransformation")
Blow-ups of manifolds are characterized rather than constructed, following Bierstone–Milman's
definition of blowing up {cite BM88}[Definition 4.1]. `IsBlowUp ψ Y c π` says that $`\pi \colon M' \to
    M`
is the blowing-up of $`M` with centre the closed submanifold $`Y`: $`M'` is an analytic manifold,
$`\pi` is proper and analytic ({decl}`IsBlowUp.contMDiff`), (1) $`\pi` is an analytic isomorphism
$`M' \setminus \pi^{-1}(Y) \to M \setminus Y`, and (2) over every adapted chart of $`Y` the
standard blow-up charts exist and cover $`\pi^{-1}(U)`. A blow-up chart of index $`i`
({decl}`IsBlowUpChart`) is a chart $`\Phi` of $`M'` in which $`\pi` reads as the model map
`blowUpChartMap σ i`: the $`i`-th coordinate of the block is the scaling variable and the other
block coordinates are ratios multiplied by it. The ideal of the exceptional divisor,
$`I_F = \pi^* I_Y`, is the pull-back `hY.idealSheaf.pullback π h.contMDiff` along the blow-up.

`AnalyticMap.IsMonoidalTransformation f D` is the form used in the statements: for some
coordinates and codimension, the cosupport of $`D` is a closed submanifold, $`D` is its ideal
sheaf, and $`f` is a blowing-up with that centre. The coordinates are existential inside the
predicate, so the statements carry no model isomorphism.
::::

::::definition "def:manifold_transforms" (lean := "Manifold.IdealSheaf.ordAlongIdeal, Manifold.IdealSheaf.genericOrdAlong, Manifold.IdealSheaf.IsDivExceptional, AnalyticManifold.IdealSheaf.weakTransform, AnalyticManifold.IdealSheaf.reducedTransform, Manifold.saturationStalk, Manifold.strictTransformSubspace")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §5, p. 142]", href :=
    "https://doi.org/10.2307/1970486" }
%%%
Transforms of an ideal sheaf along a blow-up of manifolds:

- the total transform $`\pi^{-1}(I) = \pi^* I \cdot \mathcal{O}_{M'}` (`IdealSheaf.totalTransform`);
- the order of $`J` along a centre, $`\nu_{D,a}(J) = \sup\{p : J_a \subseteq D_a^p\}`
  ({decl}`ordAlongIdeal`, {cite BM97}[§3]), and its generic value along the connected component of the
  centre through $`a` ({decl}`genericOrdAlong`);
- {decl}`IsDivExceptional`: $`J'` is the quotient of the total transform by the exceptional ideal to
  the generic order, stalkwise a colon ideal;
- `weakTransform f J D` ({decl}`AnalyticManifold.IdealSheaf.weakTransform`): Hironaka's weak
  transform, the ideal sheaf with that property, chosen when it exists (Hironaka shows that it does
  along a monoidal transformation) and the unit ideal otherwise;
- `reducedTransform f E D`: Hironaka's $`\mathrm{red}(f^{-1}(E) \cup f^{-1}(D))`,
  the reduced subspace on that set through vanishing ideals ({bpref "def:vanishing"}[]), when
  these have local generators (as they do in the main theorems), and the product
  $`f^*E \cdot f^*D` otherwise, which has the same points;
- the strict transform of a closed subspace, stalkwise the saturation of the total transform by
  the exceptional ideal ({decl}`saturationStalk`, {decl}`strictTransformSubspace`).

The exponent of the weak transform may vary along the centre: it is the generic order along each
connected component.
::::

# Simple normal crossings boundaries

::::definition "def:snc_boundary" (lean := "Manifold.HypersurfaceFamily, Manifold.HypersurfaceFamily.ι, Manifold.HypersurfaceFamily.hyp, Manifold.HypersurfaceFamily.support, Manifold.HypersurfaceFamily.IsSncChartAt, Manifold.HypersurfaceFamily.IsSnc, Manifold.HypersurfaceFamily.HasSncWith, Manifold.HypersurfaceFamily.idealSheaf, AnalyticManifold.IdealSheaf.IsSncBoundary, AnalyticManifold.IdealSheaf.IsSncBoundaryWith, AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor")
%%%
paperIdentity := some { label := "[Kol07, Definition 24]", href :=
    "https://arxiv.org/abs/math/0508332" }
%%%
A `HypersurfaceFamily M` is an ordered countable family of subsets `hyp j` of $`M` (indexed by `ι`),
the components $`E^j` of a divisor $`E = \sum E^j`, with support $`\bigcup_j E^j`. It is a *simple
normal crossings divisor* ({decl}`IsSnc`) if every component is a closed smooth hypersurface, the
family is locally finite, and every point has an snc chart ({decl}`IsSncChartAt`): a chart in which
each component through the point is its own coordinate hyperplane. {decl}`HasSncWith` adds a closed
submanifold $`Y` cut out by some of the coordinates of such charts. {decl}`idealSheaf` is the
reduced ideal sheaf of the divisor, through the vanishing ideals of its support.

The statements use two predicates on an ideal sheaf $`B`:

- `IsSncBoundary B`: $`B` is the reduced ideal sheaf of a simple normal crossings hypersurface
  family, for some coordinates;
- `IsSncBoundaryWith B D`: moreover the family has simple normal crossings with the closed
  subspace $`D` {cite Kol07}[Definition 24 (4)]; {cite Wlo09}[Definition 3.2.4 (2)].

{decl}`IsNormalCrossingsDivisor` is Bierstone–Milman's normal-crossings divisor: a principal ideal
sheaf generated at every point by a monomial $`\prod z_i^{\alpha_i}` in a regular system of
parameters ({bpref "def:regular_system"}[]) {cite BM97}[Theorem 1.10].
::::

::::definition "def:embedded_snc" (lean := "AnalyticManifold.IdealSheaf.IsSncBoundaryTransversalTo, AnalyticManifold.IdealSheaf.IsMulBoundaryMonomial")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 2.0.2 (3), (6)]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
Two predicates of Włodarczyk's embedded desingularization ({bpref "thm:wlo09_embedded"}[]), for
ideal sheaves $`B`, $`Y` and $`J`:

- `B.IsSncBoundaryTransversalTo Y`: $`B` is the reduced ideal sheaf of a simple normal crossings
  hypersurface family $`G` with which the closed subspace $`Y` has simple normal crossings
  transversally: at every point $`a` of $`Y` there is a chart adapted to $`Y`, of the codimension of
  $`Y` at $`a`, which is an snc chart of $`G` at $`a`, and the coordinates cutting out $`Y` are
  distinct from those of the hypersurfaces through $`a`. Unlike {decl}`IsSncBoundaryWith`, the
  codimension may vary from point to point, as it does for the strict transform of a subspace that
  is not equidimensional; and no component through $`a` may contain $`Y` near $`a`, which Kollár's
  Definition 24 (4) allows. This is the reading of "$`\tilde Y` has only simple normal crossings
  with the exceptional divisor $`E_r`" {cite Wlo09}[Theorem 2.0.2 (3)].
- `J.IsMulBoundaryMonomial Y B`: $`J = I_Y \cdot I_{\tilde E}` for a divisor $`\tilde E` that is,
  near every point, an effective combination of the hypersurfaces of a simple normal crossings
  family whose reduced ideal sheaf is $`B`: at every point $`x` the stalk $`J_x` is the product of
  $`(I_Y)_x` with a monomial in the vanishing ideals of hypersurfaces of the family through $`x`
  ({bpref "def:vanishing"}[]), the exponents read at $`x` {cite Wlo09}[Theorem 2.0.2 (6)].
::::

# The Jacobian ideal and analytic isomorphisms

::::definition "def:jacobian" (lean := "Manifold.jacobianFun, Manifold.jacobianStalk, AnalyticMap.jacobianIdeal, AnalyticMap.IsIsoOver")
%%%
paperIdentity := some { label := "[BM97, Theorem 1.10]", href :=
    "https://arxiv.org/abs/alg-geom/9508005" }
%%%
`jacobianFun 𝕜 f χ φ' y` is the Jacobian determinant $`\det D(\chi \circ f \circ \varphi'^{-1})` of
$`f` in the charts $`\chi` (target) and $`\varphi'` (source). `jacobianStalk f a'` is the ideal
of $`\mathcal{O}_{N,a'}` generated by its germ in the standard charts, and
`AnalyticMap.jacobianIdeal f` is the ideal sheaf with these stalks: the ideal generated locally, in
any analytic coordinates, by the Jacobian determinant, independent of the coordinates since a
change of charts multiplies the determinant by a unit.

`AnalyticMap.IsIsoOver f U`: $`f` restricts to an analytic isomorphism $`f^{-1}(U) \to U`,
that is, a local diffeomorphism on $`f^{-1}(U)` and a bijection onto $`U` (condition (1) of
{cite BM88}[Definition 4.1], off the centre).
::::
