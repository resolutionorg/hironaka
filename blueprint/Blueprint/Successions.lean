import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import Blueprint.Manifolds
import Blueprint.Conventions
import Hironaka.Manifold.Resolution.Defs
import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Set Filter Topology TopologicalSpace
open AnalyticManifold Manifold

set_option verso.blueprint.autoDeps true
-- Infer from directly referenced declarations only, as before v4.34; walking through unassociated
-- helpers would traverse Mathlib.
set_option verso.blueprint.autoDeps.expandUntagged false

#doc (Manual) "Finite successions, compatible families and pull-backs" =>
%%%
tag := "ch-successions"
file := "successions"
%%%

This chapter describes the successions of blow-ups of analytic manifolds, the compatible families
over the compact subsets of a manifold in which the three principalization theorems and the
embedded desingularization are stated ({bpref "thm:mt2pp"}[], {bpref "thm:bm"}[],
{bpref "thm:wlo09_principalization"}[], {bpref "thm:wlo09_embedded"}[]), and the pull-back of a
succession along a local analytic isomorphism. What those theorems assert of their successions is
stated with each theorem ({ref "ch-analytic"}[Analytic manifolds and analytic spaces]). The
declarations are in the namespace `AnalyticManifold`.

# Finite successions of monoidal transformations

::::definition "def:finite_succession" (lean := "AnalyticManifold.finStages, AnalyticManifold.FiniteSuccession, AnalyticManifold.FiniteSuccession.length, AnalyticManifold.FiniteSuccession.later, AnalyticManifold.FiniteSuccession.center, AnalyticManifold.FiniteSuccession.map, AnalyticManifold.FiniteSuccession.isMonoidal, AnalyticManifold.FiniteSuccession.stage, AnalyticManifold.FiniteSuccession.stageMapAux, AnalyticManifold.FiniteSuccession.stageMap, AnalyticManifold.FiniteSuccession.last, AnalyticManifold.FiniteSuccession.composite")
%%%
paperIdentity := some { label := "[Hir64, p. 155]", href := "https://doi.org/10.2307/1970486" }
%%%
A `FiniteSuccession M` is Włodarczyk's finite sequence of blow-ups with smooth centres {cite Wlo09}[Theorem 2.0.3 (1)], Hironaka's succession of monoidal transformations for the finite well-ordered
index set $`\{0 < 1 < \cdots < r\}`. It is given as a structure: a length $`r` ({decl}`length`),
later stages $`U_1, \dots, U_r` ({decl}`later`; the stages `stage i` are $`U_0 = M` followed by
these, {decl}`finStages`), centres $`C_i` on $`U_i` given by ideal sheaves ({decl}`center`), and
analytic maps $`\sigma_{i+1} \colon U_{i+1} \to U_i` ({decl}`map`), each the monoidal transformation
of $`U_i` with centre $`C_i` (the field {decl}`isMonoidal`, {bpref "def:manifold_blowup"}[]). The
composites $`\sigma^i \colon U_i \to M` are `stageMap i` (by recursion, {decl}`stageMapAux`), the
end result is {decl}`last` and the whole composite {decl}`composite`.

Empty centres are admitted: a monoidal transformation with empty centre is an isomorphism,
Włodarczyk's "isomorphisms" in {cite Wlo09}[Definitions 3.2.5, 3.2.6]. Unlike the scheme-theoretic
{decl}`BlowUpSequence`, which constructs each blow-up, a {decl}`FiniteSuccession` takes the blown-up
manifolds as data together with the property that each map is the blow-up.
::::

::::definition "def:succession_chart_data" (lean := "AnalyticManifold.FiniteSuccession.dimAt, AnalyticManifold.FiniteSuccession.chartAt, AnalyticManifold.FiniteSuccession.codim")
The monoidal transformation property of each step is existential in coordinates and codimension;
`dimAt i`, `chartAt i` and `codim i` choose witnesses (the dimension $`n` of the model, linear
coordinates $`E \cong \mathbb{K}^n` and the codimension of the centre). With them each step is a
blow-up in the sense of Bierstone–Milman (`isBlowUp_map`) with centre a closed submanifold
(`isClosedSubmanifold_center`).
::::

::::definition "def:succession_transforms" (lean := "AnalyticManifold.FiniteSuccession.weakTransformSeqAux, AnalyticManifold.FiniteSuccession.weakTransformSeq, AnalyticManifold.FiniteSuccession.boundarySeqAux, AnalyticManifold.FiniteSuccession.boundarySeq, AnalyticManifold.FiniteSuccession.strictTransformSubspaceSeqAux, AnalyticManifold.FiniteSuccession.strictTransformSubspaceSeq")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II′(N) (ii), (iii), p. 156]", href := "https://doi.org/10.2307/1970486" }
%%%
Along a finite succession, by recursion on the stage:

- `S.weakTransformSeq J i` is the weak transform $`J_i`: $`J_0 = J` and $`J_{i+1}` the weak
  transform of $`J_i` by $`\sigma_{i+1}` ({bpref "def:manifold_transforms"}[]);
- `S.boundarySeq E i` is the boundary $`E_i`: $`E_0 = E` and
  $`E_{i+1} = \mathrm{red}(\sigma_{i+1}^{-1}(E_i) \cup \sigma_{i+1}^{-1}(C_i))`;
- `S.strictTransformSubspaceSeq J i` is the strict transform $`Y_i` of the closed subspace $`Y`
  with ideal sheaf $`J`: $`Y_0 = Y` and $`Y_{i+1}` the strict transform of $`Y_i` under
  $`\sigma_{i+1}`, the saturation of its total transform by the exceptional divisor
  ({bpref "def:manifold_transforms"}[]); Kollár's restricted sequence {cite Kol07}[Definition 30.2].

Each is defined through an auxiliary recursion on a natural number with a proof that it is a stage
({decl}`weakTransformSeqAux`, {decl}`boundarySeqAux`, {decl}`strictTransformSubspaceSeqAux`).

Starting the boundary from the unit ideal (the empty divisor) gives the accumulated exceptional
divisor, as in the Jacobian principalization ({bpref "thm:bm"}[]).
::::

# Restriction, extension and compatible families

::::definition "def:restrict_extension" (lean := "AnalyticManifold.FiniteSuccession.restrict, AnalyticManifold.FiniteSuccession.restrictStageOpens, AnalyticManifold.FiniteSuccession.restrictOpensLater, AnalyticManifold.FiniteSuccession.restrictOpensMapAux, AnalyticManifold.FiniteSuccession.restrictOpensIncl, AnalyticManifold.FiniteSuccession.restrictOpensCenterAux, AnalyticManifold.FiniteSuccession.IsExtensionOf, AnalyticManifold.FiniteSuccession.stageMapLE, AnalyticManifold.FiniteSuccession.centerAt")
The restriction of an ideal sheaf to an open subset, $`J|_U`, is `J.restrict U`
({bpref "def:ideal_sheaf_vocab"}[]). The restriction of a finite succession over an open $`U_2` to
an open $`U_1 \subseteq U_2` ({decl}`FiniteSuccession.restrict`) has the preimages of $`U_1` as
stages and the restricted centres, possibly empty: a blow-up restricted to an open subset is the
blow-up of the open subset with the restricted centre. Its parts are the traces of $`U_1` on the
stages ({decl}`restrictStageOpens`, {decl}`restrictOpensLater`), the restricted maps
({decl}`restrictOpensMapAux`, the first composed with the inclusion {decl}`restrictOpensIncl` of
$`U_1` into $`U_2`) and the restricted centres ({decl}`restrictOpensCenterAux`).

`T.IsExtensionOf S` is Włodarczyk's extension of a sequence of blow-ups {cite Wlo09}[Definition 3.2.6]:
$`T` consists of the blow-ups of $`S`, at increasing indices $`j_1 < \cdots < j_m`, with
isomorphisms (blow-ups with empty centre) in between, the stages identified over $`M` compatibly
with the maps and the centres; it is stated with the composites between two stages
({decl}`stageMapLE`) and the centres indexed by their stage ({decl}`centerAt`). "The definition of
extension arises naturally when we pass to open subsets of the considered ambient manifold" (loc.
cit.).
::::

::::definition "def:compatible_family" (lean := "AnalyticManifold.ExtensionCompatibleFamily, AnalyticManifold.ExtensionCompatibleFamily.space, AnalyticManifold.ExtensionCompatibleFamily.map, AnalyticManifold.ExtensionCompatibleFamily.nhd, AnalyticManifold.ExtensionCompatibleFamily.seq")
An `ExtensionCompatibleFamily M` is the compatible-family form of a locally finite principalization:
a manifold $`\tilde M` ({decl}`space`) with an analytic map $`\tilde M \to M` ({decl}`map`,
Włodarczyk's $`\mathrm{prin}_I`, Hironaka's canonical modification $`X_\gamma \to X`), and for every
compact $`K \subseteq M`

- an open neighbourhood $`U_K` of $`K` (`nhd K`), monotone in $`K`;
- a finite succession `seq K` over $`U_K` whose end result is identified with
  $`\mathrm{map}^{-1}(U_K)` over $`U_K`, so that the map restricted there is the composite of the
  blow-ups;

such that for $`K_1 \subseteq K_2` the restriction of `seq K₂` to $`U_{K_1}` is an extension of
`seq K₁`. Properness of the map is not part of the definition; the main theorems assert it.
::::

# Morphisms of successions

::::definition "def:succession_hom" (lean := "AnalyticManifold.FiniteSuccession.Hom")
For an analytic map $`\varphi \colon N \to M` between manifolds on possibly different model
spaces, a finite succession $`R` over an open $`U' \subseteq N` and a finite succession $`S` over
an open $`U \subseteq M`, a morphism `R.Hom S φ` from $`R` to $`S` over $`\varphi` consists of an
index $`j_k` of a stage of $`R` for every stage $`S_k`, running from $`0` to the last stage of
$`R` in steps of $`0` or $`1`, and analytic maps $`f_k \colon R_{j_k} \to S_k` which lie over
$`\varphi` and commute with the blow-downs (through the composites between two stages,
{decl}`stageMapLE`, {bpref "def:restrict_extension"}[]). The pull-back and the push-forward of
successions below are such morphisms with conditions on the maps and on the centres.
::::

# Pull-back along a local analytic isomorphism

::::definition "def:pullback_up_to_empty" (lean := "AnalyticManifold.FiniteSuccession.IsPullbackUpToEmptyAlong, AnalyticManifold.ExtensionCompatibleFamily.IsPullbackAlong")
%%%
paperIdentity := some { label := "[Wlo09, Theorem 3.5.1 (2)]", href := "https://gokovagt.org/proceedings/2008/ggt08-wlodarczyk.pdf" }
%%%
For an analytic map $`g \colon N \to M`, a finite succession $`R` over an open $`U' \subseteq N` and
a finite succession $`S` over an open $`U \subseteq M`, `R.IsPullbackUpToEmptyAlong S g` says that
$`R` is the pull-back of $`S` along $`g`, up to blow-ups with empty centre: there is a morphism
from $`R` to $`S` over $`g` ({bpref "def:succession_hom"}[]) whose maps
$`f_k \colon R_{j_k} \to S_k` are local analytic isomorphisms, such that at a step that raises
the index the centre of $`R` is the pull-back of the centre of $`S` ({decl}`centerAt`,
{bpref "def:restrict_extension"}[]), and at a step that does not, the pulled-back centre is empty.

The pull-back of a blowing-up along a local analytic isomorphism is the blowing-up of the
pulled-back centre, so the stages of $`R` are the fibre products $`N \times_M S_k` with the steps
of empty pulled-back centre (isomorphisms) left out.

For compatible families ({bpref "def:compatible_family"}[]) $`F'` over $`N` and $`F` over $`M`,
`F'.IsPullbackAlong F g` ({decl}`ExtensionCompatibleFamily.IsPullbackAlong`) says that for
compacts $`K' \subseteq N`, $`K \subseteq M` with $`g(U_{K'}) \subseteq U_K` the succession of
$`F'` over $`U_{K'}` is the pull-back along $`g` of the succession of $`F` over $`U_K`, up to
blow-ups with empty centre. This is the form in which the commutation of principalization with
local analytic isomorphisms is stated ({bpref "def:commutes_local_iso"}[]).
::::

# Push-forward along a closed embedding

::::definition "def:pushforward_up_to_empty" (lean := "AnalyticManifold.FiniteSuccession.IsPushforwardUpToEmptyAlong, AnalyticManifold.ExtensionCompatibleFamily.IsPushforwardAlong")
%%%
paperIdentity := some { label := "[Kol07, Definition 30.3; 34.3]", href := "https://arxiv.org/abs/math/0508332" }
%%%
For an analytic map $`\tau \colon N \to M` between manifolds on possibly different model spaces, a
finite succession $`S` over an open $`U \subseteq M` and a finite succession $`R` over an open
$`U' \subseteq N` with $`\tau(U') \subseteq U`, `S.IsPushforwardUpToEmptyAlong R τ` says that $`S`
is the push-forward of $`R` along $`\tau`, up to blow-ups whose centres lie outside the part over
$`\tau(U')`: there is a morphism from $`R` to $`S` over $`\tau` ({bpref "def:succession_hom"}[])
whose maps $`f_k \colon R_{j_k} \to S_k` are embeddings with image closed in the part of $`S_k`
over $`\tau(U')`, such that at a step that raises the index the centre of $`R` is the preimage
under $`f_k` of the centre of $`S`, at a step that does not, $`f_k` misses the centre, and every
point of a centre of $`S` over $`\tau(U')` lies in the image of $`f_k`.

Kollár's push-forward $`j_* B` of a blow-up sequence of a closed submanifold {cite Kol07}[Definition
30.3] has centres $`Z_i^X = (j_i)_*(Z_i^S)`, with $`j_i \colon S_i \to X_i` the inclusions of
the strict transforms. Here the strict transforms are not formed: the images of the $`f_k` are the
strict transforms of $`\tau(U')`, and $`S` is the push-forward of $`R` with blow-ups whose centres
lie away from $`\tau(U')` interspersed, the blow-ups of the sequence over the trace of $`U` on
$`\tau(N)` that the sequence over the smaller open $`U'` omits.

For compatible families $`F` over $`M` and $`F'` over $`N`, `F.IsPushforwardAlong F' τ`
({decl}`ExtensionCompatibleFamily.IsPushforwardAlong`) says that for compacts $`K' \subseteq N`,
$`K \subseteq M` with $`\tau(U_{K'}) \subseteq U_K` the succession of $`F` over $`U_K` is the
push-forward along $`\tau` of the succession of $`F'` over $`U_{K'}`, up to blow-ups whose centres
lie outside the part over $`\tau(U_{K'})`. This is the form in which the commutation of
principalization with closed embeddings is stated ({bpref "def:commutes_closed_analytic"}[]).
::::
