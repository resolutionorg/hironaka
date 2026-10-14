import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import Blueprint.ConjunctionChains
import Hironaka.Scheme.Resolution.Defs
import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal
open CategoryTheory AlgebraicGeometry Scheme Scheme.IdealSheafData

set_option verso.blueprint.autoDeps true
-- Infer from directly referenced declarations only, as before v4.34; walking through unassociated
-- helpers would traverse Mathlib.
set_option verso.blueprint.autoDeps.expandUntagged false

#doc (Manual) "Conventions and sources" =>
%%%
tag := "ch-conventions"
file := "conventions"
%%%

This appendix collects the matters that concern every page: a dictionary from the classical
notions to their names in Mathlib and the library, the typing conventions of the statements, the
names of the declarations, and the sources cited. How to read a node, with its boxes on the relation to the source, is explained in
the introduction ({ref "intro-reading"}[How to read a node]).

# Dictionary
%%%
tag := "conv-dictionary"
%%%

The statements use the standard notions of scheme theory {cite Sta}[] under their names in Mathlib or
in the library. Each line gives a classical notion, its Lean name, and the node of the library's
definition where there is one.

- *Scheme; morphism; composite; identity; isomorphism*: {decl}`Scheme`, `X ⟶ Y`, `f ≫ g` (first `f`,
  then `g`), `𝟙 X`, `IsIso f`.
- *Spectrum of a ring; the point $`\operatorname{Spec} k`*: `Spec R` for `R : CommRingCat`;
  `Spec (.of k)`.
- *Open subsets; affine opens; functions on an open $`U`; stalk at $`x`*: `X.Opens`,
  `X.affineOpens`, `Γ(X, U)`, `X.presheaf.stalk x`.
- *The part of $`f \colon X \to Y` over an open $`U \subseteq Y`*: `f ∣_ U : f ⁻¹ᵁ U ⟶ U`, as in
  the weak form of Main Theorem I ({bpref "thm:mt1_weak"}[]).
- *Algebraic $`k`-scheme (separated and of finite type over $`k`)*: `X : AlgScheme k`, with
  scheme `X.left` and structure morphism `X.left ↘ Spec (.of k)` ({ref "conv-schemes"}[Algebraic k-schemes],
  {bpref "def:alg_scheme"}[], {bpref "def:finite_type"}[]).
- *Closed subscheme, given by its ideal sheaf; its support; inverse image along $`h`*:
  `I : X.IdealSheafData`, `I.support`, `I.comap h` ({ref "conv-ideals"}[below]).
- *Stalk $`I_x` and order $`\nu(I_x)` of an ideal sheaf*: `I.stalkIdeal x`, `I.ord x`
  ({bpref "def:stalk_ideal"}[], {bpref "def:order"}[]).
- *Reduced; irreducible components; integral (a variety, when of finite type over $`k`)*:
  `IsReduced X`, `irreducibleComponents X`, `IsIntegral X`.
- *Simple point (regular local ring); non-singular scheme; singular locus*: `X.IsRegularAt x`,
  `IsRegular X`, `X.singularLocus` ({bpref "def:is_regular"}[]).
- *Regular system of parameters, the local coordinates at a point*:
  {decl}`IsLocalRing.IsRegularSystemOfParameters` ({bpref "def:regular_system"}[]).
- *Smooth morphism, of relative dimension $`d`; smooth locus $`X^{ns}` of $`X` over $`k`*:
  `Smooth f`, `SmoothOfRelativeDimension d f`, `(X.left ↘ Spec (.of k)).smoothLocus`. Over a field
  of characteristic zero a scheme of finite type is smooth over $`k` exactly at its simple points
  ({bpref "def:is_regular"}[]).
- *Cartesian square, $`P = X \times_S Y`; base change along a field extension $`\sigma`*:
  {decl}`IsPullback`; a cartesian square over `Spec σ` ({bpref "def:change_of_fields"}[]).
- *Effective Cartier divisor*: the subscheme of an invertible ideal sheaf, `I.IsInvertible`
  ({bpref "def:invertible"}[]).
- *Blow-up, or monoidal transformation, with centre $`D`; exceptional divisor*: `D.blowUp`,
  `D.blowUpπ`, `D.exceptionalDivisor` ({bpref "def:blowup_construction"}[],
  {bpref "def:exceptional_divisor"}[]).
- *Quasi-coherent sheaf of modules, of finite type; projective bundle $`\mathbf{P}(\mathcal{E})`;
  projective morphism*: `E : X.Modules` with `E.IsQuasicoherent` and `SheafOfModules.IsFiniteType E`,
  `E.projectiveBundle`, `IsProjective f` ({bpref "def:projective_bundle"}[],
  {bpref "def:projective"}[]).
- *Finite succession of blow-ups*: `BlowUpSequence X` ({bpref "def:blowup_sequence"}[]).
- *Normal crossings (Hironaka); simple normal crossings divisor (Kollár)*:
  {decl}`IsSncBoundaryWith`, {decl}`IsSncBoundary` ({bpref "def:normal_crossings"}[]);
  {decl}`DivisorFamily` and {decl}`DivisorFamily.IsSnc` ({bpref "def:divisor_family"}[],
  {bpref "def:snc"}[]).
- *Analytic manifold; coherent sheaf of ideals; blow-up of a manifold; analytic space*:
  `AnalyticManifold 𝕜 E`, {decl}`Manifold.IdealSheaf`, {decl}`Manifold.IsBlowUp`, `AnalyticSpace K`
  ({bpref "def:analytic_manifold"}[], {bpref "def:ideal_sheaf_general"}[],
  {bpref "def:manifold_blowup"}[], {bpref "def:analytic_space"}[]).

# Ideal sheaves and closed subschemes
%%%
tag := "conv-ideals"
%%%

Closed subschemes, centres and boundaries are given by their ideal sheaves: Mathlib's
`X.IdealSheafData` on a scheme ({ref "ch-scheme-vocab"}[Algebraic k-schemes, singularities and
normal crossings]), a locally finitely generated ideal sheaf of the sheaf of analytic functions on a
manifold or an analytic space ({ref "ch-manifolds"}[Analytic manifolds]). Ideal sheaves are ordered
by inclusion, so a larger ideal sheaf is a smaller subscheme: the unit ideal sheaf `⊤` is the empty
subscheme, so a blow-up with centre `⊤` is an isomorphism, and the zero ideal sheaf `⊥` is the whole
space. "With nonzero stalks" reads Hironaka's "sheaf of non-zero ideals" at every stalk. The
*monoidal transformation* with centre $`D` is the blow-up along the ideal sheaf of $`D`; "blow-up"
and "monoidal transformation" are used interchangeably, as are Kollár's "cosupport" and the
library's {decl}`support` of an ideal sheaf.

# Names
%%%
tag := "conv-names"
%%%

Declarations are referred to by their full Lean names. On each page the names in rendered signatures
are shown relative to the namespaces that page opens, as its legend says; links and hovers keep the
full name. The library names its declarations after what they are, in the manner of Mathlib. The
algebraic vocabulary is in `AlgebraicGeometry`, most of it in `AlgebraicGeometry.Scheme` (the
singular locus, blow-up sequences and divisor families) and
`AlgebraicGeometry.Scheme.IdealSheafData` (ideal sheaves, the blow-up and the transforms), with the
order of an ideal of a local ring in `IsLocalRing`, and the inputs and functors of the functorial
theorems, with the properties these theorems assert of them, in `AlgebraicGeometry`. The analytic
vocabulary is in `AnalyticManifold` (manifolds, their ideal sheaves and finite successions), built
on the infrastructure in `Manifold`; analytic spaces, their vocabulary and their resolution theorems
are in `AnalyticSpace`.

# Sources
%%%
tag := "conv-sources"
%%%

The sources are cited by the keys of `references.bib`, the bibliography of the library, as
`[Kol07, Definition 29]`: a citation links to the entry in the Blueprint Bibliography, the last part
of this document, which lists the sources that the chapters and the annotations cite, with the
places they are cited from. Item numbers in citations are the source's own.
