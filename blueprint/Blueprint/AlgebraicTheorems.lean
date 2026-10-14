import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import Blueprint.BlowUpSequences
import Blueprint.ProjectiveMorphisms
import Hironaka.Resolution.Algebraic.Hir64.ComponentwiseMainTheorems
import Hironaka.Resolution.Algebraic.Hir64.ComponentwiseCorollaries
import Hironaka.Resolution.Algebraic.Hir64.MainTheoremI
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.FunctorClauses
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses

open Verso.Genre
open Verso.Genre.Manual
open Informal
open CategoryTheory AlgebraicGeometry Scheme Scheme.IdealSheafData

set_option verso.blueprint.autoDeps true
-- Infer from directly referenced declarations only, as before v4.34; walking through unassociated
-- helpers would traverse Mathlib.
set_option verso.blueprint.autoDeps.expandUntagged false

#doc (Manual) "Algebraic schemes" =>
%%%
tag := "ch-algebraic"
file := "algebraic-theorems"
%%%

The theorems of this chapter are the algebraic main theorems of the library. They are about
algebraic schemes over a field `k` of characteristic zero, and all but Main Theorem I and its weak
form produce a finite succession of blow-ups, a {decl}`BlowUpSequence`
({bpref "def:blowup_sequence"}[]).

Every scheme in these statements is an *algebraic `k`-scheme*, an object `X : AlgScheme k` whose
underlying scheme `X.left` is separated and of finite type over $`\operatorname{Spec} k`
({ref "conv-schemes"}[algebraic k-schemes], {bpref "def:alg_scheme"}[]). Closed subschemes are given
by their ideal sheaves (Mathlib's `X.IdealSheafData`), the monoidal transformation with centre `D`
is the blow-up `D.blowUp` ({bpref "def:blowup_construction"}[]), and "non-singular" is
{decl}`IsRegular`, every local ring regular ({bpref "def:is_regular"}[]), except in the hypotheses
of Main Theorems II and II(N) and Corollaries 1 and 3, where it is smoothness over `k`.

The theorems come in four groups.

- Hironaka's Main Theorems II and II(N) and his Corollaries 1 and 3: order reduction,
  principalization, the trivialization of a system of ideal sheaves and the simplification of a
  boundary, each by one succession of blow-ups with conditions on its centres, weak transforms and
  boundaries.
- Kollár's functorial principalization and resolution: a single assignment of blow-up sequences to
  all inputs at once ({ref "sec-functors"}[Blow-up sequence functors]), compatible with smooth
  morphisms and with change of the base field ({bpref "def:commutes_smooth"}[],
  {bpref "def:change_of_fields"}[]); and his strong resolution of a variety, read off the
  functorial resolution.
- Hironaka's Main Theorem I and its weak form: one blow-up resolves a reduced irreducible algebraic
  scheme.
- Włodarczyk's embedded desingularization with smooth centres, in functorial form.

Main Theorems II and II(N) and Corollary 1 are derived from Kollár's order reduction
{cite Kol07}[Theorem 68]; Corollary 3 from functorial principalization; Kollár's Theorem 27 and Main
Theorem I from functorial resolution, together with Hironaka's remark that a finite succession of
monoidal transformations is a single monoidal transformation {cite Hir64}[pp. 132–133]; and the weak
form of Main Theorem I from Main Theorem I.

The section of each theorem states, before the theorem, the properties it asserts of its
successions or of its functor and the inputs particular to it. A property asserted by several
theorems is stated at the first of them in this chapter, and the later ones refer back to it.

# Main Theorem II: order reduction
%%%
tag := "sec-mt2"
%%%

Main Theorem II is one round of order reduction. Its statement uses two of Hironaka's conditions on
a succession of blow-ups, one on its centres and one on its boundaries, which Main Theorem II(N)
and Corollary 1 use again.

*Hironaka's conditions on centres and boundaries.*

::::definition "def:hironaka_conditions" (lean := "AlgebraicGeometry.Scheme.BlowUpSequence.HasRegularIrreducibleCenters, AlgebraicGeometry.Scheme.BlowUpSequence.HasSncBoundaries")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II, pp. 142–143]", href := "https://doi.org/10.2307/1970486" }
%%%
Two conditions of Hironaka's Main Theorems II and II(N) and of his Corollary 1, for a succession
`S` of a scheme $`X`:

- `S.HasRegularIrreducibleCenters`: every centre $`D_i` is non-singular (every local ring regular,
  {bpref "def:is_regular"}[]) and irreducible {cite Hir64}[Main Theorem II (i), Main Theorem II(N)
  (1); Corollary 1, "non-singular irreducible centers D(i)", p. 143];
- `S.HasSncBoundaries E`: with the boundaries $`E_0 = E`,
  $`E_{i+1} = \mathrm{red}(f_i^{-1}(E_i) \cup f_i^{-1}(D_i))` ({bpref "def:sequence_transforms"}[]),
  every $`E_i` has only normal crossings with $`D_i`, and $`E_r` has only normal crossings
  ({bpref "def:normal_crossings"}[]) {cite Hir64}[Main Theorem II (iii) and the first half of (iv);
  Main Theorem II(N) (3) and the first half of (4)].
::::

::::theorem "thm:mt2" (lean := "AlgebraicGeometry.exists_blowUpSequence_ord_weakTransformSeq_lt")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II, pp. 142–143]", href := "https://doi.org/10.2307/1970486" }
%%%
Let $`X` be a smooth algebraic $`k`-scheme, $`k` of characteristic zero, $`J` an ideal sheaf on
$`X` with nonzero stalks, $`d` the maximum over the points $`x` of the orders $`\nu(J_x)`, and
$`E_0` a reduced closed subscheme having only normal crossings. Then there is a finite succession
of monoidal transformations $`f_i \colon X_{i+1} \to X_i` with centres $`D_i \subseteq X_i` such
that

1. every centre $`D_i` is non-singular and irreducible;
2. the weak transform $`J_i` of $`J` has order at least $`d` at every point of $`D_i`;
3. the boundary $`E_i`, defined by $`E_{i+1} = \mathrm{red}(f_i^{-1}(E_i) \cup f_i^{-1}(D_i))`,
   has only normal crossings with $`D_i`;
4. the last boundary $`E_r` has only normal crossings, and the last weak transform $`J_r` has
   order less than $`d` at every point of $`X_r`.

This is one round of order reduction: it lowers the maximal order of the ideal while keeping the
accumulated exceptional divisor, together with the original boundary, a normal crossings divisor.
Iterating it gives Main Theorem II(N) ({bpref "thm:mt2n"}[]). The statement includes the degenerate
case $`d = 0`, in which $`J = \mathcal{O}_X` and condition (4) can hold only on an empty $`X_r`;
blowing up the irreducible components of $`X` one after another achieves it, since Hironaka's
monoidal transformation is empty over a centre that is a whole component.

Condition (1) is {decl}`HasRegularIrreducibleCenters`, and condition (3) with the first half of (4)
is {decl}`HasSncBoundaries` ({bpref "def:hironaka_conditions"}[]). The statement also uses the order
$`\nu(J_x)` ({bpref "def:order"}[]), stalks and nonzero stalks ({bpref "def:stalk_ideal"}[]),
Hironaka's normal crossings ({bpref "def:normal_crossings"}[]), and the weak transforms and
boundaries along a succession ({bpref "def:sequence_transforms"}[], {bpref "def:transforms"}[]).
::::

:::proof "thm:mt2"
For $`0 < d`: on each irreducible component of $`X` on which the order $`d` is attained, one round
of Kollár's order reduction of order $`d` {cite Kol07}[Theorem 68] on the triple (component, $`J`,
$`E_0`), with $`E_0` read as the simple normal crossings family of its irreducible components. Its
value is a smooth blow-up sequence of order $`d` {cite Kol07}[Definition 66] whose last weak transform
has maximal order less than $`d`. Its centres are smooth but possibly reducible; blowing up their
(disjoint) irreducible components one after another gives irreducible centres with the same
composite, last weak transform and last boundary. Hironaka's conditions are read off Kollár's
Definition 66; the successions of the components, each extended by the unit ideal across the
complement, are concatenated, and the conditions, all pointwise, transport along the stage lifts and
the untouched opens. In the degenerate case $`d = 0` the succession blows up the irreducible
components of $`X` one after another: they are pairwise disjoint on the smooth $`X`, the blow-up
along a whole component deletes it and is an open immersion elsewhere, so the last stage is empty,
condition (2) reads $`0 \le \nu`, and condition (4) is vacuous.
:::

# Main Theorem II(N): principalization
%%%
tag := "sec-mt2n"
%%%

::::theorem "thm:mt2n" (lean := "AlgebraicGeometry.exists_blowUpSequence_weakTransformSeq_eq_top")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II(N), p. 176]", href := "https://doi.org/10.2307/1970486" }
%%%
Let $`X` be a smooth algebraic $`k`-scheme, $`J` an ideal sheaf with nonzero stalks and $`E` a
reduced closed subscheme having only normal crossings. Then there is a finite succession of
monoidal transformations with centres $`B_i` such that

1. every centre $`B_i` is non-singular and irreducible;
2. for each $`i` there is a positive integer $`d_i` which is the maximal order of the weak
   transform $`J_i` and is its order at every point of $`B_i`;
3. the boundary $`E_i` has only normal crossings with $`B_i`;
4. $`E_r` has only normal crossings and $`J_r = \mathcal{O}_{X_r}`.

This is principalization: after the succession the weak transform of $`J` is the unit ideal, so
the total transform of $`J` is a product of powers of the exceptional divisors. Every centre lies
in the locus of maximal order of the current weak transform. Hironaka writes the boundaries as
$`\mathrm{red}(f_i^{-1}(E_i \cup B_i))`, Main Theorem II as
$`\mathrm{red}(f_i^{-1}(E_i) \cup f_i^{-1}(D_i))`: the same reduced subscheme. For
$`J = \mathcal{O}_X` the empty succession satisfies every condition.

Conditions (1), (3) and the first half of (4) are those of Main Theorem II
({bpref "def:hironaka_conditions"}[]).
::::

:::proof "thm:mt2n"
By induction on a bound for the maximal order of $`J`, iterating the order reduction of Main
Theorem II ({bpref "thm:mt2"}[]): if the maximal order is $`0` then $`J` is the unit ideal and
the empty succession does; otherwise one round of order $`d = \max \operatorname{ord} J` lowers the
maximal order of the weak transform, and the induction hypothesis applies at its last stage.
Condition (2) at the stages of a round is the order-$`d` condition on its centres, which is why
Kollár's Theorem 68 rather than his Theorem 35 is iterated. Hironaka instead deduces Main Theorem
II(N) from his fundamental theorem II₂^N, applied on each irreducible component to the resolution
datum $`(E_1, \dots, E_\alpha \mid 0, \dots, 0 \mid J, 1)` {cite Hir64}[pp. 176–177]; that route is
not followed.
:::

# Corollary 1: trivialization of a system of ideal sheaves
%%%
tag := "sec-cor1"
%%%

Corollary 1 makes one of finitely many ideal sheaves the unit ideal at every point. Its centres
satisfy the condition of Main Theorem II ({bpref "def:hironaka_conditions"}[]), and along them
the order of every weak transform is constant and positive.

*Constant positive order along the centres.*

::::definition "def:constant_order" (lean := "AlgebraicGeometry.Scheme.BlowUpSequence.HasConstantPositiveOrderAlongCenters")
%%%
paperIdentity := some { label := "[Hir64, Corollary 1, pp. 143–144]", href := "https://doi.org/10.2307/1970486" }
%%%
For a succession `S` of a scheme $`X` and an ideal sheaf $`J` on $`X`,
`S.HasConstantPositiveOrderAlongCenters J` says that for every $`i` there is a positive integer
$`c` that is the order of the weak transform $`J_i` ({bpref "def:sequence_transforms"}[],
{bpref "def:order"}[]) at every point of the centre $`D_i` {cite Hir64}[Corollary 1 (1)].
::::

::::theorem "thm:cor1" (lean := "AlgebraicGeometry.exists_blowUpSequence_forall_exists_stalkIdeal_weakTransformSeq_eq_top")
%%%
paperIdentity := some { label := "[Hir64, Corollary 1, pp. 143–144]", href := "https://doi.org/10.2307/1970486" }
%%%
Let $`X` be a smooth algebraic $`k`-scheme, $`k` of characteristic zero, and
$`J_1, \dots, J_e` ($`e \ge 1`) ideal sheaves on $`X` with nonzero stalks. Then there is a finite
succession of monoidal transformations $`f_i \colon X_{i+1} \to X_i` with non-singular irreducible
centres $`D_i \subseteq X_i` such that

1. every weak transform $`J_j(i)` of every $`J_j` has a constant positive order along $`D_i`;
2. at every point of the end result $`X_r` at least one of the weak transforms $`J_j(r)` is the
   unit ideal.

This is Hironaka's trivialization of a system of coherent sheaves of ideals: after the succession
the common cosupport of the weak transforms is empty. The constant of (1) may depend on $`i` and
$`j`. The condition on the centres is {decl}`HasRegularIrreducibleCenters`
({bpref "def:hironaka_conditions"}[]), and condition (1) is
{decl}`HasConstantPositiveOrderAlongCenters` for each $`J_j` ({bpref "def:constant_order"}[]); the
weak transforms are those of Main Theorem II ({bpref "def:sequence_transforms"}[]).
::::

:::proof "thm:cor1"
For $`X` smooth of a single relative dimension, Hironaka's own argument: induction on the maximal
order $`d` of $`\prod_j J_j` on the common cosupport $`\bigcap_j |J_j|`, each step one round of
the order reduction of Main Theorem II ({bpref "thm:mt2"}[]) on the open set $`X \setminus S`,
$`S` being Hironaka's closed set of the points of $`T = \{\nu(\prod_j J_j) \ge d\}` at which some
$`J_j` is already trivial, extended back across $`S`. The orders of the factors add up to that of
the product, so each factor has constant positive order along the centres, and the induction ends
when the common cosupport is empty, that is, when at every point some factor is trivial. A general
smooth $`X` is treated component by component: its irreducible components are disjoint closed
opens, each smooth of one relative dimension, and their successions, extended by the unit ideal
across the complement, are concatenated.
:::

# Functorial principalization
%%%
tag := "sec-principalization"
%%%

Kollár's functorial principalization assigns a succession of blow-ups to every triple at once,
by one rule. It asserts of each value that it principalizes the triple, and of the rule that it
commutes with smooth morphisms, with change of the base field and, for an empty boundary, with
closed embeddings. Functorial resolution and embedded desingularization assert some of these
properties again.

*Triples.*

::::definition "def:triple" (lean := "AlgebraicGeometry.Triple, AlgebraicGeometry.Triple.X, AlgebraicGeometry.Triple.I, AlgebraicGeometry.Triple.E, AlgebraicGeometry.Triple.instCategory, AlgebraicGeometry.Triple.hasUnderlyingScheme, AlgebraicGeometry.Triple.hasChangeOfFields")
%%%
paperIdentity := some { label := "[Kol07, Notation 64]", href := "https://arxiv.org/abs/math/0508332" }
%%%
A `Triple k` is Kollár's triple $`(X, I, E)`, the input of functorial principalization
({bpref "thm:principalization"}[]): a smooth, equidimensional algebraic $`k`-scheme `X` (smooth of
a single relative dimension over $`k`), an ideal sheaf `I` with nonzero stalks, and a simple normal
crossings divisor family `E` with ordered index set ({bpref "def:snc"}[]). A morphism
$`(Y, J, F) \to (X, I, E)` is a $`k`-morphism $`h \colon Y \to X` with $`J = h^* I` and
$`F = h^{-1} E`, so that the source is the pull-back of the target {cite Kol07}[34.1]. A base change
along $`\sigma \colon k \to L` is a cartesian square over $`\operatorname{Spec} \sigma` along
which the ideal sheaf and the boundary pull back.
::::

*Principalization of a triple.*

::::definition "def:principalized_by" (lean := "AlgebraicGeometry.Scheme.BlowUpSequence.HasSmoothSncCenters, AlgebraicGeometry.Triple.IsPrincipalizedBy")
%%%
paperIdentity := some { label := "[Kol07, Theorem 35 (1)–(3)]", href := "https://arxiv.org/abs/math/0508332" }
%%%
`S.HasSmoothSncCenters E`: every centre of `S` is smooth over $`k` and has simple normal crossings
with the total transform of the divisor family $`E` at its stage ({bpref "def:total_transform"}[])
{cite Kol07}[Theorem 35 (1)]. A triple $`T = (X, I, E)` is *principalized* by a succession with
composite $`\Pi` (`T.IsPrincipalizedBy S`) when (1) `S.HasSmoothSncCenters E`; (2) $`\Pi^* I` is
the ideal sheaf of a simple normal crossings divisor ({decl}`IsIdealOfSncDivisor`,
{bpref "def:snc_divisor"}[]); (3) $`\Pi` is an
isomorphism over $`X \setminus (\operatorname{cosupp} I \cup \operatorname{Sing} E)`.
::::

*Commuting with smooth morphisms.* Kollár's condition {cite Kol07}[34.1] on a blow-up sequence
functor $`B` ({bpref "def:functors"}[]) is an equality of successions: for every smooth morphism of
inputs $`h \colon Y \to X`,

$$`B(Y) = \bigl(h^* B(X)\bigr)_{\text{empty blow-ups deleted}}`

(`((B X).pullback h).eraseEmpty`, {bpref "def:sequence_ops"}[]). The deletion is needed because a
restriction can contain empty blow-ups; taking $`h` to be the identity shows that $`B(X)` has none.
Since the centres are closed subschemes and their pull-back is a function, the equality is literal,
not up to isomorphism. For open immersions it makes $`B` local: $`B(X)` can be computed on an open
cover and glued {cite Kol07}[Proposition 37]. Commuting with change of fields (34.2) is the same
equality along the base change $`X_L \to X` for a field extension $`k \to L`, which is why $`B` is
one family of functors for all fields of characteristic zero.

::::definition "def:commutes_smooth" (lean := "AlgebraicGeometry.CommutesWithSmoothMorphisms")
%%%
paperIdentity := some { label := "[Kol07, 34.1]", href := "https://arxiv.org/abs/math/0508332" }
%%%
A blow-up sequence functor $`B` *commutes with smooth morphisms* (`CommutesWithSmoothMorphisms B`,
{cite Kol07}[34.1]) if, for every morphism of inputs $`h \colon Y \to X` with smooth underlying
morphism, $`B(Y)` is the pull-back $`h^* B(X)` when $`h` is surjective, and $`h^* B(X)` with the
blow-ups with empty centre deleted in general ({bpref "def:sequence_ops"}[]). These are Kollár's
two bullets. The first follows from the second when $`B(X)` has no empty blow-ups, since a
surjective $`h` pulls back no nonempty centre to an empty one; and the second, for $`h` the
identity, says that $`B(X)` has no empty blow-ups. Kollár states both, and so does the
definition.
::::

*Commuting with change of fields.*

::::definition "def:change_of_fields" (lean := "AlgebraicGeometry.HasChangeOfFields, AlgebraicGeometry.HasChangeOfFields.IsFieldBaseChange, AlgebraicGeometry.CommutesWithChangeOfFields")
%%%
paperIdentity := some { label := "[Kol07, 34.2]", href := "https://arxiv.org/abs/math/0508332" }
%%%
`HasChangeOfFields C`, for a family of categories of inputs indexed by the fields, says what a base
change of an input along a field extension is: `IsFieldBaseChange σ p` for inputs `X` over $`k`,
`XL` over $`L` and a morphism `p` of underlying schemes says that `p` exhibits `XL` as
$`X \times_{\operatorname{Spec} k} \operatorname{Spec} L` with its extra structure
({bpref "def:triple"}[], {bpref "def:inputs_36"}[]).

A family $`B` of blow-up sequence functors, one for each field of characteristic zero, *commutes
with change of fields* (`CommutesWithChangeOfFields B`, {cite Kol07}[34.2]) if, for a field extension
$`\sigma \colon k \to L` and an input over $`L` exhibited as the base change of an input $`X` over
$`k` by $`p`, the value over $`L` is $`p^* B_k(X)`. The ring map $`\sigma` may be an automorphism
of $`k`, so the condition includes invariance under the automorphisms of $`k`, as Kollár's does.
::::

*Commuting with closed embeddings.*

::::definition "def:commutes_closed_embeddings" (lean := "AlgebraicGeometry.CommutesWithClosedEmbeddingsOfEmptyBoundary")
%%%
paperIdentity := some { label := "[Kol07, 34.3]", href := "https://arxiv.org/abs/math/0508332" }
%%%
A blow-up sequence functor $`B` on triples *commutes with closed embeddings of empty boundary*
(`CommutesWithClosedEmbeddingsOfEmptyBoundary B`, {cite Kol07}[34.3] for $`E = \emptyset`) if, for
a closed embedding $`j \colon Y \hookrightarrow X` and triples $`(Y, I_Y, \emptyset)` and
$`(X, j_* I_Y, \emptyset)`, $`B(X, j_* I_Y, \emptyset) = j_* B(Y, I_Y, \emptyset)`, the
push-forward of a succession along $`j` ({bpref "def:sequence_ops"}[]). Kollár states 34.3 for a
boundary having simple normal crossings with $`Y`; his Theorem 35 (5) asserts it only for
$`E = \emptyset`.
::::

::::theorem "thm:principalization" (lean := "AlgebraicGeometry.exists_functorial_principalization")
%%%
paperIdentity := some { label := "[Kol07, Theorem 35]", href := "https://arxiv.org/abs/math/0508332" }
%%%
There is a family $`BP` of blow-up sequence functors on triples, one for each field $`k` of
characteristic zero, assigning a succession of blow-ups $`\Pi \colon X_r \to X` to every triple
$`(X, I, E)` of a smooth equidimensional algebraic $`k`-scheme, an ideal sheaf with nonzero stalks
and a simple normal crossings divisor family, such that

1. every centre is smooth over $`k` and has simple normal crossings with the total transform of
   $`E` at its stage;
2. $`\Pi^* I` is the ideal sheaf of a simple normal crossings divisor;
3. $`\Pi` is an isomorphism over $`X \setminus (\operatorname{cosupp} I \cup \operatorname{Sing} E)`;
4. $`BP` commutes with smooth morphisms $`h \colon Y \to X` (the value on the pulled-back triple
   is $`h^* BP(X, I, E)`, with empty blow-ups deleted when $`h` is not surjective) and with
   change of the base field;
5. when $`E = \emptyset`, $`BP` commutes with closed embeddings.

What distinguishes Kollár's theorem from Main Theorem II(N) ({bpref "thm:mt2n"}[]) is that the
succession is chosen for all inputs at once, by one rule, and the rule is compatible with smooth
morphisms and field extensions; this is what lets the resolution of an arbitrary scheme be glued
from local pieces ({bpref "thm:resolution"}[]).

Conditions (1)–(3) are {decl}`Triple.IsPrincipalizedBy` ({bpref "def:principalized_by"}[]);
condition (4) is {decl}`CommutesWithSmoothMorphisms` and {decl}`CommutesWithChangeOfFields`
({bpref "def:commutes_smooth"}[], {bpref "def:change_of_fields"}[]), and condition (5)
{decl}`CommutesWithClosedEmbeddingsOfEmptyBoundary` ({bpref "def:commutes_closed_embeddings"}[]).
The inputs are triples ({bpref "def:triple"}[]), and the vocabulary is that of blow-up sequences and
their functors ({bpref "def:blowup_sequence"}[], {bpref "def:sequence_ops"}[],
{bpref "def:functors"}[]), divisor families and simple normal crossings
({bpref "def:divisor_family"}[], {bpref "def:snc"}[], {bpref "def:total_transform"}[]).
::::

:::proof "thm:principalization"
The functor is Kollár's construction {cite Kol07}[72]: blow up the intersections of the components
of $`E`, which makes them disjoint, then run the order reduction $`BMO_1` of
{cite Kol07}[Theorem 69] on the resulting triple, deleting the empty blow-ups {cite Kol07}[32]. Each
of the five conditions is a separate theorem of the library about this functor.
:::

# Corollary 3: simplification of a boundary
%%%
tag := "sec-cor3"
%%%

::::theorem "thm:cor3" (lean := "AlgebraicGeometry.exists_blowUpSequence_isInvertible_isSncBoundary_radical_comap")
%%%
paperIdentity := some { label := "[Hir64, Corollary 3, p. 146]", href := "https://doi.org/10.2307/1970486" }
%%%
Let $`X` be a smooth algebraic $`k`-scheme, $`k` of characteristic zero, and $`W` a nowhere dense
closed subscheme of $`X`. Then there is a finite succession of monoidal transformations
$`f_i \colon X_{i+1} \to X_i` with non-singular centres $`D_i \subseteq X_i` such that

1. the end result $`X_r` is non-singular;
2. every centre lies over $`W`: $`D_i \subseteq \bar f_i^{-1}(W)`, where
   $`\bar f_i = f_0 \circ \cdots \circ f_{i-1} \colon X_i \to X`;
3. the associated reduced scheme $`\mathrm{red}(\bar f_r^{-1}(W))` of $`\bar f_r^{-1}(W)` is
   defined by an invertible sheaf of ideals on $`X_r` and has only normal crossings.

This is the simplification of an algebraic boundary: after blowing up over $`W` only, the inverse
image of $`W` becomes a normal crossings divisor. Hironaka asks nothing of $`W` beyond nowhere
density; $`W` may be empty, for which the empty succession satisfies every condition.

The statement uses regularity ({bpref "def:is_regular"}[]), invertible ideal sheaves
({bpref "def:invertible"}[]) and Hironaka's normal crossings ({bpref "def:normal_crossings"}[]).
::::

:::proof "thm:cor3"
For $`X` smooth of a single relative dimension, Kollár's functorial principalization
({bpref "thm:principalization"}[]) applied to the triple $`(X, I_W, \emptyset)` rather than, as in
Hironaka, Main Theorem II. Nowhere density of the support makes $`I_W` nonzero on every irreducible
component, as a triple requires; the centres of the principalization lie over $`V(I_W)`, its end
result is smooth over $`k` and hence non-singular, and its condition (2) writes the pull-back of
$`I_W` as a product of powers of the members of a simple normal crossings family, whose radical is
the reduced union of the members that occur, invertible and with only normal crossings. Every smooth
$`X` is treated component by component, the final conditions read on the stalks.
:::

# Functorial resolution
%%%
tag := "sec-resolution"
%%%

Kollár's functorial resolution assigns a succession of blow-ups to every reduced equidimensional
algebraic $`k`-scheme. It asserts of each value that it is a strong resolution, and of the rule that
it commutes with smooth morphisms and with change of the base field, as functorial principalization
does ({bpref "def:commutes_smooth"}[], {bpref "def:change_of_fields"}[]).

*Reduced equidimensional schemes.*

::::definition "def:inputs_36" (lean := "AlgebraicGeometry.ReducedEquidimensionalScheme, AlgebraicGeometry.Scheme.IsReducedEquidimensional, AlgebraicGeometry.ReducedEquidimensionalScheme.hasUnderlyingScheme, AlgebraicGeometry.ReducedEquidimensionalScheme.hasChangeOfFields")
%%%
paperIdentity := some { label := "[Kol07, Theorem 36]", href := "https://arxiv.org/abs/math/0508332" }
%%%
`ReducedEquidimensionalScheme k` is the full subcategory of `AlgScheme k` of the schemes $`X` that
are reduced and equidimensional ({decl}`Scheme.IsReducedEquidimensional`: $`X` is reduced and its
smooth locus over $`k` is smooth of a single relative dimension). The irreducible components of such an $`X` may
meet: the two axes $`xy = 0` in the plane are an input, and so is every reduced simple normal
crossings scheme. These are the inputs of Kollár's functorial resolution
({bpref "thm:resolution"}[]); the equidimensionality is that of {cite Kol07}[Notation 64 (1)],
transported from smooth to reduced schemes through the smooth locus. For a reduced $`X` of finite
type over a field of characteristic zero the smooth locus is dense and contains every generic
point, so the condition says that all irreducible components of $`X` have the same dimension; it is
phrased through the smooth locus because the intrinsic form needs the dimension of an integral
scheme of finite type over $`k` to be the transcendence degree of its function field, which Mathlib
does not provide. A base change along a field extension $`\sigma \colon k \to L` is a cartesian
square over $`\operatorname{Spec} \sigma` ({decl}`hasChangeOfFields`). The class is stable under
open subschemes and under finite disjoint unions of open subschemes of one input; it is also stable
under change of fields and under étale morphisms (a reduced scheme of finite type over a field of
characteristic zero is geometrically reduced, and smoothness is stable under base change and local
in the fpqc topology on the base), facts the library records but does not formalize.
::::

*Strong resolutions.*

::::definition "def:strong_resolution" (lean := "AlgebraicGeometry.Scheme.BlowUpSequence.IsResolution, AlgebraicGeometry.Scheme.BlowUpSequence.IsStrongResolution")
%%%
paperIdentity := some { label := "[Kol07, (2) and (3)]", href := "https://arxiv.org/abs/math/0508332" }
%%%
For a succession `S` of an algebraic $`k`-scheme $`X` with composite $`\Pi \colon X_r \to X`:

- `S.IsResolution` {cite Kol07}[(2)]: $`X_r` is smooth over $`k`, $`\Pi` is projective
  ({decl}`IsProjective`, {bpref "def:projective"}[]; hence proper), and $`\Pi` is birational, an
  isomorphism over a dense open subset of $`X`. Reading birationality as an isomorphism over a dense
  open subset is right for a reduced $`X`, the case of the theorems.
- `S.IsStrongResolution` {cite Kol07}[(3)], conditions (1)–(3) of Theorem 36: a resolution that is an
  isomorphism over the smooth locus $`X^{ns}` (Mathlib's {decl Scheme.Hom.smoothLocus}`smoothLocus`
  of the structure morphism) and such that $`\Pi^{-1}(\operatorname{Sing} X)`,
  $`\operatorname{Sing} X` the complement of the smooth locus, is a simple normal crossings divisor
  ({decl}`IsSncDivisor`, {bpref "def:snc_divisor"}[]). Over a field of characteristic zero the
  smooth locus is the set of points with regular local ring
  (`Scheme.mem_smoothLocus_iff_isRegularAt`), so the smooth and the regular readings of Kollár's
  conditions agree; and for a reduced $`X` the smooth locus is dense, so the isomorphism over it
  already gives the birationality asked of a resolution.
::::

*Kollár's resolution functor.* Kollár's resolution functor {cite Kol07}[(4)] is a resolution
$`\Pi_X \colon R(X) \to X` of every $`X` together with, for every smooth $`h \colon Y \to X`, a
morphism $`R(h) \colon R(Y) \to R(X)` over $`h`, functorial in $`h`, such that every square is
cartesian: $`R(Y) \cong R(X) \times_X Y` over $`Y`. A blow-up sequence functor $`B` that commutes
with smooth morphisms ({bpref "def:commutes_smooth"}[]) and whose values are resolutions gives this,
with $`R(X)` the last stage of $`B(X)` and $`\Pi_X` its composite: the stages of $`h^* B(X)` are
fibre products, so $`R(h)` is the projection from $`R(X) \times_X Y`, and deleting empty blow-ups
does not change the composite, an empty blow-up being an isomorphism. Conversely $`R(h)` is
determined by the values: two morphisms $`R(Y) \to R(X)` over $`h` agree over the smooth locus of
$`Y`, which $`h` maps into that of $`X`, where $`\Pi_X` is an isomorphism; its preimage is dense in
the smooth $`R(Y)`, and $`R(X)` is separated, so they agree everywhere. Hence $`R(h)` is unique, its
functoriality is automatic, and a functor commuting with smooth morphisms amounts to its values
together with the property $`\Pi_Y \cong h^* \Pi_X` {cite Kol07}[34]; this is why Kollár specifies $`R`
by its values alone, and why the library states it as an assignment of successions with a property.
Smooth morphisms are the most one can ask for: the quotient map $`\mathbb{A}^2 \to (uv = w^2)` does
not lift to resolutions {cite Kol07}[Example 3.4].

::::theorem "thm:resolution" (lean := "AlgebraicGeometry.exists_functorial_resolution")
%%%
paperIdentity := some { label := "[Kol07, Theorem 36]", href := "https://arxiv.org/abs/math/0508332" }
%%%
There is a family $`BR` of blow-up sequence functors, one for each field $`k` of characteristic
zero, assigning a succession of blow-ups $`\Pi \colon X_r \to X` to every reduced equidimensional
algebraic $`k`-scheme $`X` over $`k`, such that

1. $`X_r` is smooth over $`k`;
2. $`\Pi` is an isomorphism over the smooth locus of $`X`;
3. $`\Pi^{-1}(\operatorname{Sing} X)` is the support of a simple normal crossings divisor;
4. $`BR` commutes with smooth morphisms and with change of the base field.

Moreover $`\Pi` is projective and birational. This is resolution of singularities in its functorial
form: a smooth $`X_r` mapping onto $`X`, changing nothing over the smooth points, with exceptional
locus a simple normal crossings divisor, and compatible with the smooth morphisms between inputs —
every open subscheme and every étale cover by inputs among them — so that it is local on $`X` in
the smooth topology as far as inputs reach. A smooth equidimensional scheme is an input, and
$`\Pi` may then be the identity; the irreducible components of an input may meet.

Conditions (1)–(3) are {decl}`BlowUpSequence.IsStrongResolution`
({bpref "def:strong_resolution"}[]), and condition (4) is {decl}`CommutesWithSmoothMorphisms` and
{decl}`CommutesWithChangeOfFields` ({bpref "def:commutes_smooth"}[],
{bpref "def:change_of_fields"}[]); the inputs are the objects of
{decl}`ReducedEquidimensionalScheme` ({bpref "def:inputs_36"}[]).
::::

:::proof "thm:resolution"
On an affine input the functor embeds $`X` in a smooth affine scheme $`A` and runs the
principalization $`BP(A, I_X, \emptyset)` ({bpref "thm:principalization"}[]), restricted to $`X` and
truncated at the first centre containing the strict transform of $`X`, as in the proof of {cite Kol07}[Corollary 22]. That centre contains the strict transform of every irreducible component of $`X` at
once. The centre absorbing a component $`C` has a point over every point of $`C`, in particular over
a smooth closed point of $`C`; a centre that comes before the absorption of another component $`C'`
has no point over the generic point of $`C'`, hence none over a general smooth closed point of
$`C'`. But when all components have one dimension, any two smooth closed points of $`X` are étale
equivalent as embedded points of $`A`, through a pair of étale neighbourhoods, along which the run
pulls back ({bpref "thm:principalization"}[], (4)); so a centre has a point over one exactly when it
has one over the other, and no component is absorbed before another. How the components meet plays
no role. On any input the functor is obtained by descent along the smooth surjection from a finite
affine cover {cite Kol07}[Proposition 37 and Warning 38]; independence of the embedding is {cite Kol07}[Lemma 39], and condition (4) uses Kollár's reduction of (34.1) to Theorem 35 through {cite Kol07}[Lemma
41]. $`\Pi` is projective as a composite of blow-ups of a Noetherian scheme: the composite is a
single blow-up (Hironaka's remark after Main Theorem I; {cite Sta}[Tag 080B]), and a blow-up is a
closed subscheme of the projective bundle of its ideal sheaf ({bpref "def:projective"}[]).
:::

# Strong resolution of a variety
%%%
tag := "sec-strong-resolution"
%%%

::::theorem "thm:strong_resolution" (lean := "AlgebraicGeometry.exists_strong_resolution")
%%%
paperIdentity := some { label := "[Kol07, Theorem 27]", href := "https://arxiv.org/abs/math/0508332" }
%%%
Let $`X` be a variety, an integral algebraic $`k`-scheme, over a field $`k` of characteristic zero.
Then there is a birational and projective morphism $`\Pi \colon X' \to X`, the composite of a
succession of blow-ups of $`X`, such that

1. $`X'` is smooth over $`k`;
2. $`\Pi` is an isomorphism over the smooth locus $`X^{ns}`;
3. $`\Pi^{-1}(\operatorname{Sing} X)` is the support of a simple normal crossings divisor.

This is resolution of singularities in its usual, strong form {cite Kol07}[(3)]: a smooth $`X'` with a
projective birational morphism to $`X`, here a succession of blow-ups. Kollár's weaker form {cite Kol07}[Corollary 22], a smooth $`X'` with a birational projective morphism to $`X` and no conditions (2)
and (3), is the part {decl}`IsResolution` of the conclusion. The conclusion is
{decl}`BlowUpSequence.IsStrongResolution` ({bpref "def:strong_resolution"}[]), the same as in
functorial resolution ({bpref "thm:resolution"}[]); birationality is the isomorphism over a dense
open subset of $`X`, here the smooth locus.
::::

:::proof "thm:strong_resolution"
An integral $`X` is an input of Kollár's functorial resolution ({bpref "thm:resolution"}[]): it is
reduced, and its smooth locus is a nonempty integral open subscheme, smooth of one relative
dimension. The succession is the value $`BR(X)`.
:::

# Main Theorem I
%%%
tag := "sec-mt1"
%%%

::::theorem "thm:mt1" (lean := "AlgebraicGeometry.exists_support_eq_singularLocus_isRegular_blowUp")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem I, p. 132]", href := "https://doi.org/10.2307/1970486" }
%%%
Let $`k` be a field of characteristic zero and $`X` a reduced and irreducible algebraic
$`k`-scheme. Then there is a closed subscheme $`D \subseteq X` whose set of points is exactly the
singular locus of $`X`, and such that the monoidal transformation of $`X` with centre $`D` is
non-singular.

In words: one blow-up, with a centre supported exactly on the singular points, resolves $`X`.
When $`X` is already non-singular the singular locus is empty, $`D` is the empty subscheme (the
unit ideal sheaf) and its blow-up is $`X` itself. The centre $`D` need not be reduced: it comes
from a finite succession of blow-ups, which is a single blow-up with a suitably chosen centre.

The definitions the statement uses are the singular locus and regularity
({bpref "def:is_regular"}[]), the monoidal transformation, which is the blow-up
({bpref "def:blowup_construction"}[]), and, underneath it, the construction of the blow-up
({bpref "def:gluing"}[], {bpref "def:affine_blowup"}[], {bpref "def:rees"}[]).
::::

:::proof "thm:mt1"
The library derives the theorem from functorial resolution ({bpref "thm:resolution"}[]) and
functorial principalization ({bpref "thm:principalization"}[]). The integral scheme $`X` is an
input of the resolution functor, whose value is a finite succession of blow-ups with smooth last
stage; its centres lie over the singular locus, since the principalization functor from which it
is built never blows up over a smooth point. It is followed by a principalization of the pull-back
of the reduced ideal $`\mathcal{J}` of the singular locus. By Hironaka's remark
{cite Hir64}[pp. 132–133] the composite is one blow-up `K.blowUp`, with $`K` supported in the
singular locus. Then $`D = K \cdot \mathcal{J}` has support the whole singular locus, and its
blow-up is that of $`K` followed by the blow-up of an invertible ideal, an isomorphism; so it is
smooth over $`k`, hence non-singular.
:::

# Main Theorem I, weak form
%%%
tag := "sec-mt1-weak"
%%%

::::theorem "thm:mt1_weak" (lean := "AlgebraicGeometry.exists_dense_isIso_restrict_isRegular_blowUp")
%%%
paperIdentity := some { label := "[Hir64, p. 132], the paragraph after Main Theorem I", href := "https://doi.org/10.2307/1970486" }
%%%
Let $`k` be a field of characteristic zero and $`X` a reduced and irreducible algebraic
$`k`-scheme. Then there is a closed subscheme $`D` with dense open complement $`U` such that the
monoidal transformation $`f \colon X' \to X` with centre $`D` restricts to an isomorphism
$`f^{-1}(U) \to U` and $`X'` is non-singular.

Hironaka states this form in the paragraph after Main Theorem I, by weakening condition (i). The
density of $`U` excludes the trivial centre $`D = X`. As in Main Theorem I, "reduced and
irreducible" is {decl AlgebraicGeometry.IsIntegral}`IsIntegral`.
::::

:::proof "thm:mt1_weak"
Hironaka's derivation from Main Theorem I ({bpref "thm:mt1"}[]) by weakening its first condition
{cite Hir64}[p. 132]: for the centre $`D` of Main Theorem I, with $`|D| = \operatorname{Sing} X`, the
blow-up is an isomorphism over the complement of its centre, and that complement is open and
contains the generic point of the irreducible $`X`, whose local ring is a field, so it is dense.
:::

# Embedded desingularization with smooth centres
%%%
tag := "sec-embedded"
%%%

Włodarczyk's embedded desingularization assigns a succession of blow-ups to every embedded pair.
It asserts of each value that it desingularizes the pair, and of the rule a form of commuting with
smooth morphisms adapted to the embedded subscheme.

*Embedded pairs.*

::::definition "def:embedded_pair" (lean := "AlgebraicGeometry.EmbeddedPair, AlgebraicGeometry.EmbeddedPair.X, AlgebraicGeometry.EmbeddedPair.Y, AlgebraicGeometry.EmbeddedPair.instCategory, AlgebraicGeometry.EmbeddedPair.hasUnderlyingScheme")
%%%
paperIdentity := some { label := "[Wlo05, Theorem 1.0.2]", href := "https://arxiv.org/abs/math/0401401" }
%%%
An `EmbeddedPair k` is a reduced closed subscheme `Y` of a smooth, equidimensional algebraic
$`k`-scheme `X`, given by its ideal sheaf: the input of Włodarczyk's embedded desingularization
({bpref "thm:embedded"}[]). A morphism $`(X', Y') \to (X, Y)` is a $`k`-morphism
$`h \colon X' \to X` along which the ideal sheaf of $`Y` pulls back to that of $`Y'`.
::::

*Embedded desingularization of a pair.*

::::definition "def:desingularized_by" (lean := "AlgebraicGeometry.EmbeddedPair.IsDesingularizedBy")
%%%
paperIdentity := some { label := "[Wlo05, Theorem 1.0.2 (a)–(c), (e)]", href := "https://arxiv.org/abs/math/0401401" }
%%%
An embedded pair $`P = (X, Y)` is *desingularized* by a succession `S` with composite
$`\sigma \colon X_r \to X` (`P.IsDesingularizedBy S`) when, with exceptional divisors $`E_i` (the
total transforms of the empty divisor family) and strict transforms $`Y_i` of $`Y`
({bpref "def:sequence_transforms"}[], {bpref "def:total_transform"}[]):

- every centre $`C_i` is smooth over $`k` and has simple normal crossings with $`E_i`
  (`S.HasSmoothSncCenters` of the empty family, {bpref "def:principalized_by"}[]);
- (a) every $`E_i`, the last included, is a simple normal crossings family;
- (b) no point of $`C_i \cap Y_i` lies over a point of $`\operatorname{Reg}(Y)`, the image in
  $`X` of the smooth locus of $`Y \to \operatorname{Spec} k`;
- (c) $`\tilde Y = Y_r` is smooth over $`k` and has simple normal crossings with $`E_r`;
- (e) $`\sigma^*(I_Y) = I_{\tilde Y} \cdot J` for the ideal sheaf $`J` of a simple normal
  crossings divisor supported in $`E_r`.
::::

*Commuting with smooth morphisms meeting the components.*

::::definition "def:commutes_meeting_components" (lean := "AlgebraicGeometry.CommutesWithSmoothMorphismsMeetingComponents")
%%%
paperIdentity := some { label := "[Wlo05, Theorem 1.0.2 (d)]", href := "https://arxiv.org/abs/math/0401401" }
%%%
A blow-up sequence functor $`B` on embedded pairs *commutes with smooth morphisms meeting the
components* (`CommutesWithSmoothMorphismsMeetingComponents B`) if, for every morphism of embedded
pairs $`h \colon (X', Y') \to (X, Y)` with smooth underlying morphism, $`B(X', Y')` is the
pull-back $`h^* B(X, Y)` when $`h` is surjective, and $`h^* B(X, Y)` with the blow-ups with empty
centre deleted when the image of $`h` meets every irreducible component of $`Y`
({bpref "def:sequence_ops"}[]). This is Włodarczyk's {cite Wlo05}[Theorem 1.0.2 (d)] in the form
proved here; Kollár's commuting with smooth morphisms ({bpref "def:commutes_smooth"}[]) asks the
second equality for every smooth $`h`.
::::

::::theorem "thm:embedded" (lean := "AlgebraicGeometry.exists_functorial_embeddedDesingularization")
%%%
paperIdentity := some { label := "[Wlo05, Theorem 1.0.2]", href := "https://arxiv.org/abs/math/0401401" }
%%%
There is a family $`ED` of blow-up sequence functors on embedded pairs, one for each field $`k` of
characteristic zero, assigning a succession of blow-ups $`\sigma \colon X_r \to X` to every
reduced closed subscheme $`Y` of a smooth equidimensional algebraic $`k`-scheme $`X`, such that,
with $`E_i` the exceptional divisors and $`Y_i` the strict transforms of $`Y`:

- every centre $`C_i` is smooth over $`k`;
- (a) every $`E_i` is a simple normal crossings family, and $`C_i` has simple normal crossings
  with $`E_i`;
- (b) no point of $`C_i \cap Y_i` lies over a smooth point of $`Y`;
- (c) the final strict transform $`\tilde Y = Y_r` is smooth and has simple normal crossings
  with $`E_r`;
- (e) $`\sigma^*(I_Y) = I_{\tilde Y} \cdot J` with $`J` the ideal of a simple normal crossings
  divisor supported on $`E_r`;
- (d) for a morphism of embedded pairs $`h \colon (X', Y') \to (X, Y)` with smooth underlying
  morphism, $`ED(X', Y')` is $`h^* ED(X, Y)` if $`h` is surjective, and $`h^* ED(X, Y)` with the
  empty blow-ups deleted if the image of $`h` meets every irreducible component of $`Y`.

Embedded desingularization resolves $`Y` inside its ambient $`X` while keeping everything in
normal crossings position, and condition (b) says that nothing is blown up over the smooth part
of $`Y`. If $`Y = X`, (b) forces every centre to be empty; if $`Y` is empty or smooth, the
conditions other than (d) hold for the empty succession.

The conditions other than (d) are {decl}`EmbeddedPair.IsDesingularizedBy`
({bpref "def:desingularized_by"}[]) and (d) is {decl}`CommutesWithSmoothMorphismsMeetingComponents`
({bpref "def:commutes_meeting_components"}[]); the
inputs are embedded pairs ({bpref "def:embedded_pair"}[]). The statement uses strict and total
transforms along a succession ({bpref "def:sequence_transforms"}[], {bpref "def:total_transform"}[])
and simple normal crossings ({bpref "def:snc"}[]).
::::

:::proof "thm:embedded"
The functor is the stop rule of Włodarczyk's modification of the canonical resolution of the
marked ideal $`(X, I_Y, \emptyset, 1)` {cite Wlo05}[§4.6–4.7]: run Kollár's order reduction $`BMO_1`
{cite Kol07}[Theorem 69] until a centre would contain the strict transform of a component of $`Y`,
stop before it, divide the ideal by the reduced ideal of the absorbed strict transforms, and
restart with the remaining components, until none remain; his reordering of the monomial part is
not transcribed.
:::
