import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import Blueprint.SchemeBlowUp
import Blueprint.Conventions
import Hironaka.Scheme.Resolution.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal
open CategoryTheory AlgebraicGeometry Scheme Scheme.IdealSheafData

set_option verso.blueprint.autoDeps true
-- Infer from directly referenced declarations only, as before v4.34; walking through unassociated
-- helpers would traverse Mathlib.
set_option verso.blueprint.autoDeps.expandUntagged false

#doc (Manual) "Successions of blow-ups and functors" =>
%%%
tag := "ch-sequences"
file := "blow-up-sequences"
%%%

A resolution is in general not one blow-up with a non-singular centre but a finite succession of
them. This chapter describes the library's successions of blow-ups of schemes (Kollár's blow-up
sequences), the transforms of ideal sheaves and divisors along them, Kollár's divisor families and
simple normal crossings, the operations of pulling back a succession, deleting its empty blow-ups
and pushing it forward, and the blow-up sequence functors in which the functorial theorems are
stated. What a main theorem asserts of its successions or of its functor, and the inputs particular
to a functorial theorem, are stated with the theorem ({ref "ch-algebraic"}[Algebraic schemes]).
The declarations are in `AlgebraicGeometry.Scheme` (successions, divisor families) and
`AlgebraicGeometry` (functors).

# Finite successions of blow-ups
%%%
tag := "sec-successions"
%%%

A finite *succession of blow-ups* {cite Kol07}[Definition 29] is a chain

$$`X_r \xrightarrow{\ \pi_{r-1}\ } X_{r-1} \to \cdots \to X_1 \xrightarrow{\ \pi_0\ } X_0 = X, \qquad \pi_i \colon X_{i+1} = \mathrm{Bl}_{Z_i} X_i \to X_i,`

with a centre $`Z_i \subseteq X_i` chosen at each stage. The centres are part of the data: two
successions with the same composite but different centres are different successions.

::::definition "def:blowup_sequence" (lean := "AlgebraicGeometry.Scheme.BlowUpSequence, AlgebraicGeometry.Scheme.BlowUpSequence.length, AlgebraicGeometry.Scheme.BlowUpSequence.stage, AlgebraicGeometry.Scheme.BlowUpSequence.center, AlgebraicGeometry.Scheme.BlowUpSequence.stageMap, AlgebraicGeometry.Scheme.BlowUpSequence.last, AlgebraicGeometry.Scheme.BlowUpSequence.composite")
%%%
paperIdentity := some { label := "[Kol07, Definition 29]", href := "https://arxiv.org/abs/math/0508332" }
%%%
A `BlowUpSequence X` is a finite succession of monoidal transformations starting at $`X`,
defined inductively: `nil X` is the empty succession, and `cons X D S'` is the blow-up of $`X` with
centre $`D` followed by a succession `S'` starting at `D.blowUp`. From it one reads off

- the length $`r` ({decl}`length`),
- the stages $`X_0 = X, X_1, \dots, X_r` (`stage i`, indexed by `Fin (r + 1)`),
- the centres $`D_i \subseteq X_i` for $`i < r` (`center i`, an ideal sheaf on stage `i.castSucc`),
- the partial composites $`\Pi_i \colon X_i \to X` (`stageMap i`),
- the last stage $`X_r` ({decl}`last`) and the composite $`\Pi \colon X_r \to X`
  ({decl}`composite`).

The centres are arbitrary closed subschemes: empty and trivial centres are allowed
{cite Kol07}[Warning 20], and the main theorems state the conditions they ask of the centres.
Because the stages are defined by recursion, a centre lives on a stage whose type depends on the
succession; the statements index the stages by `Fin (S.length + 1)` and the centres by
`Fin S.length`, with `i.castSucc` the stage on which the `i`-th centre lies and `Fin.last S.length`
the last stage.
::::

::::definition "def:sequence_transforms" (lean := "AlgebraicGeometry.Scheme.BlowUpSequence.weakTransformSeq, AlgebraicGeometry.Scheme.BlowUpSequence.boundarySeq, AlgebraicGeometry.Scheme.BlowUpSequence.strictTransformSeq")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II (ii), (iii)]", href := "https://doi.org/10.2307/1970486" }
%%%
Along a succession $`S`, by recursion on the stages:

- `S.weakTransformSeq J i` is Hironaka's sequence of weak transforms: $`J_0 = J` and $`J_{i+1}` the
  weak transform of $`J_i` along the $`i`-th blow-up ({bpref "def:transforms"}[]);
- `S.boundarySeq E i` is Hironaka's sequence of boundaries: $`E_0 = E` and
  $`E_{i+1} = \mathrm{red}(f_i^{-1}(E_i) \cup f_i^{-1}(D_i))`;
- `S.strictTransformSeq Y i` is the strict transform $`Y_i` of a closed subscheme $`Y`
  {cite Kol07}[Definition 30.2]; Włodarczyk's $`Y_i` {cite Wlo05}[Theorem 1.0.2 (b)].
::::

# Divisor families and simple normal crossings

::::definition "def:divisor_family" (lean := "AlgebraicGeometry.Scheme.DivisorFamily, AlgebraicGeometry.Scheme.DivisorFamily.ι, AlgebraicGeometry.Scheme.DivisorFamily.component, AlgebraicGeometry.Scheme.DivisorFamily.fintype, AlgebraicGeometry.Scheme.DivisorFamily.linearOrder, AlgebraicGeometry.Scheme.DivisorFamily.empty, AlgebraicGeometry.Scheme.DivisorFamily.support, AlgebraicGeometry.Scheme.DivisorFamily.singularLocus, AlgebraicGeometry.Scheme.DivisorFamily.comap")
%%%
paperIdentity := some { label := "[Kol07, Definition 31]", href := "https://arxiv.org/abs/math/0508332" }
%%%
Kollár's divisor $`E = \sum E^i` with an ordered index set: a `DivisorFamily X` is a finite linearly
ordered index type `ι` (with its {decl}`fintype` and {decl}`linearOrder`) and a closed subscheme
`component i` for each index, given by its ideal sheaf. The order matters to Kollár's algorithm, in
which new exceptional divisors come after old ones. `DivisorFamily.empty X` is the empty divisor;
{decl}`support` is the set of points on at least one component and {decl}`singularLocus`
($`\operatorname{Sing} E`) the set of points on at least two; `E.comap h` is the inverse image
family $`h^{-1}(E)` {cite Kol07}[34.1].
::::

::::definition "def:snc" (lean := "AlgebraicGeometry.Scheme.DivisorFamily.IsSncAt, AlgebraicGeometry.Scheme.DivisorFamily.IsSnc, AlgebraicGeometry.Scheme.DivisorFamily.HasSncWith")
%%%
paperIdentity := some { label := "[Kol07, Definition 24]", href := "https://arxiv.org/abs/math/0508332" }
%%%
Kollár's simple normal crossings, illustrated with Hironaka's notion in
{ref "sec-normal-crossings"}[Normal crossings]. At a point $`x`, `E.IsSncAt x z` says that
$`z_1, \dots, z_n` is a regular system of parameters of $`\mathcal{O}_{X,x}` and each component of
$`E` through $`x` is cut out near $`x` by its own coordinate $`z_{c(i)}`, distinct components by
distinct coordinates. `E.IsSnc` asks every component to be smooth and such coordinates to exist at
every point {cite Kol07}[Definition 24 (1)–(3)]; since the coordinates are asked for also at the
points on no component, `E.IsSnc` makes $`X` itself regular. `E.HasSncWith Z` says that at every
point of $`Z` the coordinates can be chosen so that in addition $`Z` is cut out by some of them
{cite Kol07}[Definition 24 (4)]; some components may contain $`Z`.
::::

::::definition "def:snc_divisor" (lean := "AlgebraicGeometry.Scheme.IdealSheafData.IsIdealOfSncDivisor, AlgebraicGeometry.Scheme.IsSncDivisor")
%%%
paperIdentity := some { label := "[Kol07, Definition 24]", href := "https://arxiv.org/abs/math/0508332" }
%%%
Divisors with simple normal crossings, as ideal sheaves and as sets. `IsIdealOfSncDivisor I` says
that $`I` is the ideal sheaf of an effective divisor $`\sum a_j F_j` supported on a simple normal
crossings family $`F` ({bpref "def:snc"}[]); Kollár's principalization makes the pull-back of an
ideal sheaf of this form {cite Kol07}[Theorem 35 (2)]. `IsSncDivisor Z` says that the set $`Z` is
the support of a simple normal crossings divisor family {cite Kol07}[Definition 24], with its reduced
structure; a strong resolution asks this of the preimage of the singular locus {cite Kol07}[(3)].
::::

::::definition "def:total_transform" (lean := "AlgebraicGeometry.Scheme.DivisorFamily.totalTransform, AlgebraicGeometry.Scheme.BlowUpSequence.totalTransformSeq")
%%%
paperIdentity := some { label := "[Kol07, Definition 25]", href := "https://arxiv.org/abs/math/0508332" }
%%%
Kollár's total transform of a divisor family under one blow-up with centre $`D` is the family of the
birational transforms of the components of $`E`, followed by the exceptional divisor $`f^{-1}(D)`
with the largest index ({decl}`DivisorFamily.totalTransform`, {cite Kol07}[Definitions 25 and 65]).
Along a succession it gives
$`E_i = (\pi_0 \cdots \pi_{i-1})^{-1}_*(E) + \mathrm{Ex}_{tot}(\pi_0 \cdots \pi_{i-1})`
({decl}`BlowUpSequence.totalTransformSeq`); starting from the empty family it is the family of
exceptional divisors, as in the embedded desingularization theorem ({bpref "thm:embedded"}[]).
::::

# Operations on successions

For a succession $`S` of $`X` and a morphism $`h \colon Y \to X`, the pull-back $`h^* S` blows
up, at each stage, the inverse image of the corresponding centre (`S.pullback h`). For smooth
$`h` its stages are the fibre products $`X_i \times_X Y`
({ref "sec-universal"}[The universal property]): it does on $`Y` what $`S` does on $`X`. For a
projection $`X \times \mathbb{A}^1 \to X` the pull-back is $`S \times \mathbb{A}^1`; for an open
immersion $`U \hookrightarrow X` it is the restriction of $`S` to $`U`, in which a centre disjoint
from $`U` becomes the empty centre.

::::definition "def:sequence_ops" (lean := "AlgebraicGeometry.Scheme.BlowUpSequence.pullback, AlgebraicGeometry.Scheme.BlowUpSequence.eraseEmpty, AlgebraicGeometry.Scheme.BlowUpSequence.pushforward")
%%%
paperIdentity := some { label := "[Kol07, Definition 30]", href := "https://arxiv.org/abs/math/0508332" }
%%%
These operations compare successions on different schemes:

- `S.pullback h` is the pull-back $`h^* S` along $`h \colon Y \to X` {cite Kol07}[Definition 30.1]: blow
  up the inverse images of the centres, using the induced morphisms of blow-ups
  ({bpref "def:blowup_lift"}[]); for smooth (more generally flat) $`h` the stages are
  $`X_i \times_X Y`;
- `S.eraseEmpty` deletes every blow-up whose centre is empty and reindexes the rest
  {cite Kol07}[32 and 34.1], carrying the tail back along the isomorphism of the empty blow-up;
- `S.pushforward j` is the push-forward $`j_* S` of a succession on a closed subscheme along the
  closed immersion $`j` {cite Kol07}[Definition 30.3]: the centres viewed in the ambient stages
  ({decl}`Scheme.Hom.pushforwardBlowUp`, {bpref "def:exceptional_divisor"}[]).

A pulled-back succession may have empty centres where the image of $`h` misses a centre, which is
why, for a non-surjective $`h`, the functorial theorems compare with `(S.pullback h).eraseEmpty`.
::::

# Blow-up sequence functors
%%%
tag := "sec-functors"
%%%

Hironaka's theorems assert that, for each input, a succession of blow-ups with the required
properties exists. Kollár's and Włodarczyk's assert more: one rule, a *blow-up sequence functor*
$`B`, assigns a succession $`B(X)` to every input $`X` at once {cite Kol07}[31 and 34]. The inputs
form a category, which differs from theorem to theorem (triples, disjoint unions of varieties,
embedded pairs), and each input has an underlying algebraic $`k`-scheme. As defined, $`B` is data
on objects only; its compatibility with smooth morphisms and with change of the base field is a
property that the theorems assert, explained with functorial principalization
({ref "sec-principalization"}[Functorial principalization]).

::::definition "def:functors" (lean := "AlgebraicGeometry.HasUnderlyingScheme, AlgebraicGeometry.HasUnderlyingScheme.forget, AlgebraicGeometry.HasUnderlyingScheme.scheme, AlgebraicGeometry.HasUnderlyingScheme.hom, AlgebraicGeometry.BlowUpSequenceFunctor")
%%%
paperIdentity := some { label := "[Kol07, Definition 31]", href := "https://arxiv.org/abs/math/0508332" }
%%%
`HasUnderlyingScheme C k` equips a category of inputs `C` with a functor {decl}`forget` to
`AlgScheme k`; `scheme X` is the underlying scheme of an input and `hom h` the underlying morphism
of schemes of a morphism of inputs. A *blow-up sequence functor* `BlowUpSequenceFunctor C` assigns
to every input `X` a succession of blow-ups `B X : BlowUpSequence (scheme X)` of its underlying
scheme {cite Kol07}[Definition 31]. It carries no conditions: the conditions on the values, and the
compatibility with smooth morphisms ({bpref "def:commutes_smooth"}[]), are asserted by the main
theorems, which quantify over the input so that a single functor works for all inputs, and over the
field so that a single family of functors works for all fields.
::::
