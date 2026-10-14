import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import Blueprint.Successions
import Hironaka.AnalyticSpace.Resolution.Defs

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

#doc (Manual) "Analytic spaces" =>
%%%
tag := "ch-spaces"
file := "analytic-spaces"
%%%

The resolution of analytic spaces ({bpref "thm:spaces"}[], {bpref "thm:spaces_complex"}[]) is
stated for $`K`-analytic spaces in
Hironaka's sense {cite Hir64}[Ch. 0, §1], $`K = \mathbb{R}` or $`\mathbb{C}` (`RCLike K`): locally ringed
spaces locally isomorphic to the zero set of finitely many analytic functions with the quotient
structure sheaf. The library builds them from Mathlib's locally ringed spaces in the namespace
`AnalyticSpace`, where the theorems are also stated, so that their names are those of this
chapter.

# K-local-ringed spaces

::::definition "def:k_space" (lean := "AnalyticSpace.KLocallyRingedSpace, AnalyticSpace.KLocallyRingedSpace.toLocallyRingedSpace, AnalyticSpace.KLocallyRingedSpace.algebraMap, AnalyticSpace.KLocallyRingedSpace.Hom, AnalyticSpace.KLocallyRingedSpace.Hom.toFun, AnalyticSpace.KLocallyRingedSpace.instCategory, AnalyticSpace.KLocallyRingedSpace.KIso, AnalyticSpace.KLocallyRingedSpace.restrictOpen, AnalyticSpace.KLocallyRingedSpace.ofRestrict, AnalyticSpace.KLocallyRingedSpace.Hom.ofFac, AnalyticSpace.KLocallyRingedSpace.instCoeSortType")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §1, p. 119]", href := "https://doi.org/10.2307/1970486" }
%%%
A `KLocallyRingedSpace K` is a locally ringed space ({decl}`toLocallyRingedSpace`) with a structural
ring homomorphism `algebraMap : K →+* Γ(X, 𝒪_X)`, the ring form of a morphism to
$`\operatorname{Spec} K`. Its morphisms ({decl}`Hom`, with underlying map {decl}`Hom.toFun`) are the
morphisms of locally ringed spaces commuting with the structural homomorphisms, forming the category
$`\mathfrak{R}/K` ({decl}`instCategory`) with isomorphisms {decl}`KIso`. An open subset gives the
open subspace $`X|_U` ({decl}`restrictOpen`) with its open immersion ({decl}`ofRestrict`), and a
factorization of a $`K`-morphism through another is a $`K`-morphism ({decl}`Hom.ofFac`). The
coercion {decl}`instCoeSortType` lets `X` stand for its type of points.
::::

::::definition "def:manifold_space" (lean := "AnalyticSpace.KLocallyRingedSpace.ofManifold, AnalyticSpace.KLocallyRingedSpace.ofManifoldBase, AnalyticSpace.KLocallyRingedSpace.ofManifoldSheafHom, AnalyticSpace.KLocallyRingedSpace.ofManifoldHomAux, AnalyticSpace.KLocallyRingedSpace.ofManifoldHom, AnalyticSpace.toSpace, AnalyticSpace.toSpaceHom")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §1, pp. 119–120]", href := "https://doi.org/10.2307/1970486" }
%%%
An analytic manifold $`M` is a $`K`-local-ringed space $`(M, \mathcal{O}_M)` with the sheaf of
analytic functions ({decl}`KLocallyRingedSpace.ofManifold`); an analytic map induces a $`K`-morphism
by precomposition ({decl}`ofManifoldBase`, {decl}`ofManifoldSheafHom`, {decl}`ofManifoldHomAux`,
{decl}`ofManifoldHom`). With Hironaka's axioms verified, $`M` is an analytic space
$`\operatorname{Sp}(M)` ({decl}`toSpace`) and an analytic map a morphism $`\operatorname{Sp}(f)`
({decl}`toSpaceHom`).
::::

# Local models and quotients

::::definition "def:local_model" (lean := "AnalyticSpace.Kn, AnalyticSpace.AnalyticFun, AnalyticSpace.affine, AnalyticSpace.analyticSpaceOfOpen, AnalyticSpace.toGlobal, Manifold.IdealSheaf.ofGlobal, AnalyticSpace.modelIdeal, AnalyticSpace.localModel")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §1]", href := "https://doi.org/10.2307/1970486" }
%%%
The local models: `Kn K n` is $`K^n` (placed in the universe of the construction),
`AnalyticFun K n G` the analytic functions on an open $`G \subseteq K^n`, `affine K n` the
$`K`-local-ringed space $`(K^n, \mathcal{A}_{K^n})` and `analyticSpaceOfOpen K n G` its open
subspace $`(G, \mathcal{A}_G)`, into whose global sections analytic functions map by
{decl}`toGlobal`. Finitely many analytic functions $`f_1, \dots, f_k` on $`G` generate an ideal
sheaf ({decl}`IdealSheaf.ofGlobal`, {decl}`modelIdeal`), and the *local analytic space*
`localModel K n G f` is the quotient
$`(S(\mathcal{I}), (\mathcal{A}_G/\mathcal{I})|_{S(\mathcal{I})})` by it.
::::

::::definition "def:quotient" (lean := "AnalyticSpace.QuotientSpace.support, AnalyticSpace.QuotientSpace.fiber, AnalyticSpace.QuotientSpace.preimage, AnalyticSpace.QuotientSpace.stalkIdeal, AnalyticSpace.QuotientSpace.prelocalPred, AnalyticSpace.QuotientSpace.localPred, AnalyticSpace.QuotientSpace.sheafTypes, AnalyticSpace.QuotientSpace.instCommRingObjOppositeOpensCarrierSupportPresheafSheafTypes, AnalyticSpace.QuotientSpace.sectionsSubring, AnalyticSpace.QuotientSpace.presheafCommRing, AnalyticSpace.QuotientSpace.classFamily, AnalyticSpace.QuotientSpace.classHom, AnalyticSpace.QuotientSpace.ιTop, AnalyticSpace.QuotientSpace.ιHom, AnalyticSpace.QuotientSpace.quotientSpace, AnalyticSpace.QuotientSpace.ι, AnalyticSpace.KLocallyRingedSpace.quotient, AnalyticSpace.KLocallyRingedSpace.quotientι")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §1]", href := "https://doi.org/10.2307/1970486" }
%%%
The quotient of a locally ringed space $`X` by an ideal sheaf $`\mathcal{J}` of finite type is the
locally ringed space $`(S(\mathcal{J}), (\mathcal{O}_X/\mathcal{J})|_{S(\mathcal{J})})`
({decl}`QuotientSpace.quotientSpace`) {cite Hir64}[Ch. 0, §1]; {cite BM97}[§3]. Its points are the support
$`S(\mathcal{J}) = \{z : \mathcal{J}_z \ne \mathcal{O}_{X,z}\}` ({decl}`support`, with
{decl}`preimage` of opens), and its sections over an open set are the families of classes in the
fibres $`\mathcal{O}_{X,z}/\mathcal{J}_z` ({decl}`fiber`, {decl}`stalkIdeal`) that are locally the
classes of one ambient section ({decl}`prelocalPred`, {decl}`localPred`). These form a sheaf of
rings ({decl}`sheafTypes` with its ring instance, {decl}`sectionsSubring`, {decl}`presheafCommRing`,
`sheafCommRing`). The canonical morphism into $`X` sends an ambient section to its family of classes
({decl}`classFamily`, {decl}`classHom`, {decl}`ιTop`, {decl}`ιHom`) and has local stalk maps
(`isLocalHom_stalkMap`), giving the closed embedding {decl}`QuotientSpace.ι`. With the induced
$`K`-structure this is {decl}`KLocallyRingedSpace.quotient` and {decl}`quotientι`.
::::

# Analytic spaces and their morphisms

::::definition "def:analytic_space" (lean := "AnalyticSpace, AnalyticSpace.toKLocallyRingedSpace, AnalyticSpace.Hom, AnalyticSpace.instCategory, AnalyticSpace.Hom.toFun, AnalyticSpace.instCoeSortType, AnalyticSpace.instCoeFunHomForallCarrierCarrierCommRingCat, AnalyticSpace.IsReduced, AnalyticSpace.regularLocus, AnalyticSpace.singularLocus, AnalyticSpace.IsNonsingular")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §1, p. 120]", href := "https://doi.org/10.2307/1970486" }
%%%
An *analytic $`K`-space* (`AnalyticSpace K`) is a $`K`-local-ringed space
({decl}`toKLocallyRingedSpace`) every point of which has a neighbourhood $`K`-isomorphic to an open
subspace of a local model, and which is Hausdorff and countable at infinity (Kollár's "separable").
The analytic spaces form the full subcategory $`An/K` ({decl}`instCategory`): a morphism `f : X ⟶ Y`
is a $`K`-morphism of the underlying $`K`-local-ringed spaces ({decl}`Hom`, a named type so that dot
notation works on morphisms), and composition is the category's `≫`, in diagrammatic order. A space
has a type of points (the coercion {decl}`instCoeSortType`), a morphism has an underlying map
({decl}`Hom.toFun`, the coercion `⇑f` given by the instance `instCoeFunHom…`), and an isomorphism
of analytic spaces is an isomorphism in $`An/K` (`IsIso f`). A space is *reduced*
({decl}`IsReduced`) if every stalk is reduced. Its simple points ({decl}`regularLocus`) are those
whose local ring is regular, the singular locus ({decl}`singularLocus`) is their complement, and
$`X` is *non-singular* ({decl}`IsNonsingular`) if every point is simple.
::::

::::definition "def:restrict_space" (lean := "AnalyticSpace.openOf, AnalyticSpace.restrictOpen, AnalyticSpace.restrictSet, AnalyticSpace.Hom.restrictSet, AnalyticSpace.Hom.IsIsoOver")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §1, p. 120]", href := "https://doi.org/10.2307/1970486" }
%%%
An open subspace of an analytic space is an analytic space ({decl}`restrictOpen`). The statements
restrict along arbitrary sets: `restrictSet X U` is $`X|_U` when $`U` is open and $`X` itself
otherwise (through {decl}`openOf`), which keeps restriction of morphisms total. The restriction
$`f|_{f^{-1}(V)} \colon X|_{f^{-1}(V)} \to Y|_V` of a morphism ({decl}`Hom.restrictSet`) is the lift
of $`f` through the open immersion of $`Y|_V`, possible because $`f` maps $`f^{-1}(V)` into $`V`
(`range_toFun_ofRestrict_comp_subset`). `f.IsIsoOver V`, "$`f` restricts to an isomorphism
$`f^{-1}(V) \to V`", is `IsIso (f.restrictSet V)`.
::::

::::definition "def:closed_subspace" (lean := "AnalyticSpace.ClosedSubspace, AnalyticSpace.ClosedSubspace.IsSncBoundaryWith, AnalyticSpace.ClosedSubspace.IsSncBoundary, AnalyticSpace.closedSubspace, AnalyticSpace.closedSubspaceι")
%%%
paperIdentity := some { label := "[Kol07, Definition 24]", href := "https://arxiv.org/abs/math/0508332" }
%%%
A closed analytic subspace of $`X` (`AnalyticSpace.ClosedSubspace X`) is given by its ideal sheaf of
finite type, a {decl}`Manifold.IdealSheaf` of the structure sheaf, with support
$`S(\mathcal{I}) = \{x : \mathcal{I}_x \ne \mathcal{O}_{X,x}\}`
({decl Manifold.IdealSheaf.support}`support`, {bpref "def:ideal_sheaf_general"}[]). The quotient by
it is again an analytic space ({decl}`AnalyticSpace.closedSubspace`, by `quotient_locallyModel`),
with its canonical morphism into $`X` ({decl}`closedSubspaceι`).

`E.IsSncBoundaryWith D` is Kollár's Definition 24 on an analytic space, at the level of stalks and
on global components: there is a locally finite family of closed subspaces such that at every
point some regular system of parameters cuts out each component through the point by one member,
distinct components by distinct members, $`E` by the product of those members, and, at points of
$`D`, $`D` by some of the members. `E.IsSncBoundary` is the case $`D = X`: $`E` is the reduced
divisor of a simple normal crossings family.
::::

# Resolution assignments

::::definition "def:resolution_assignment" (lean := "AnalyticSpace.HasUnderlyingSpace, AnalyticSpace.hasUnderlyingSpaceSelf, AnalyticSpace.FullSubcategory.hasUnderlyingSpace, AnalyticSpace.ResolutionAssignment, AnalyticSpace.ResolutionAssignment.space, AnalyticSpace.ResolutionAssignment.map")
%%%
paperIdentity := some { label := "[Kol07, Theorem 45]", href := "https://arxiv.org/abs/math/0508332" }
%%%
A type $`C` of inputs *has underlying spaces* ({decl}`HasUnderlyingSpace`) when every input has an
underlying $`K`-analytic space: the spaces themselves, and the full subcategories of the spaces of
a class. A `ResolutionAssignment C` assigns to every input $`X` a space $`R(X)` ({decl}`space`) and
a morphism $`\Pi_X \colon R(X) \to X` ({decl}`map`) to its underlying space: Kollár's resolution
functor $`R \colon X \mapsto (\Pi_X \colon R(X) \to X)`. It carries no conditions; the properties
that the resolution of analytic spaces asserts of it are stated with that theorem
({bpref "thm:spaces"}[]), whose inputs are the reduced spaces; the constructions behind it produce
assignments on all spaces.
::::
