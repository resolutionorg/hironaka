import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import Blueprint.Conventions
import Hironaka.Scheme.Snc.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal
open CategoryTheory AlgebraicGeometry Scheme Scheme.IdealSheafData

set_option verso.blueprint.autoDeps true
-- Infer from directly referenced declarations only, as before v4.34; walking through unassociated
-- helpers would traverse Mathlib.
set_option verso.blueprint.autoDeps.expandUntagged false

#doc (Manual) "Algebraic k-schemes, singularities and normal crossings" =>
%%%
tag := "ch-scheme-vocab"
file := "scheme-singularities"
%%%

This chapter collects the basic vocabulary of the algebraic theorems: algebraic $`k`-schemes,
regular points and the singular locus, the stalk and the order of an ideal sheaf, invertible ideal sheaves, and
Hironaka's normal crossings. Regularity and the singular locus are in `AlgebraicGeometry`. The
stalk and the order of an ideal sheaf, invertibility and Hironaka's normal crossings are in
`AlgebraicGeometry.Scheme.IdealSheafData`, the order of an ideal of a local ring and regular
systems of parameters in `IsLocalRing`.

An ideal sheaf on a scheme is Mathlib's `X.IdealSheafData`: a quasi-coherent ideal sheaf, given by
an ideal of $`\Gamma(X, U)` for every affine open $`U`, compatible with localization. Closed
subschemes are handled through their ideal sheaves ({ref "conv-ideals"}[Ideal sheaves and closed
subschemes]).

# Algebraic k-schemes
%%%
tag := "conv-schemes"
%%%

An *algebraic `k`-scheme* is a scheme `X` with a structure morphism to $`\operatorname{Spec} k` that
is of finite type (locally of finite type and quasi-compact) and separated: Hironaka's "algebraic
$`B`-scheme" (p. 119, "scheme" as opposed to "prescheme"), and Kollár's "scheme of finite type over
a field", made separated. In the statements it is an object `X : AlgScheme k` of the category of
algebraic `k`-schemes with the `k`-morphisms ({bpref "def:alg_scheme"}[]); `X.left` is the
underlying scheme, `X.hom : X.left ⟶ Spec (.of k)` the structure morphism, also written
`X.left ↘ Spec (.of k)`, and `.of k` is the ring `k` as an object of {decl}`CommRingCat`. In prose
`X` also denotes the scheme `X.left`. *Reduced and irreducible* is `IsIntegral X.left`. *Smooth over
`k`* is Mathlib's {decl}`Smooth` of the structure morphism, and *equidimensional* means smooth of a
single relative dimension, `∃ n, SmoothOfRelativeDimension n (X.left ↘ Spec (.of k))`, or, for a
possibly singular `X`, that its smooth locus is smooth of a single relative dimension
({decl}`Scheme.IsReducedEquidimensional` for a reduced `X`, {bpref "def:inputs_36"}[]). The
functorial theorems quantify over the field `k : Type u` as well as the input, so that commuting
with change of fields ({bpref "def:change_of_fields"}[]) can compare the values over `k` and over an
extension `L`.

::::definition "def:finite_type" (lean := "AlgebraicGeometry.FiniteType, AlgebraicGeometry.FiniteType.toLocallyOfFiniteType")
%%%
paperIdentity := some { label := "[Sta, Tag 01T0]", href := "https://stacks.math.columbia.edu/tag/01T0" }
%%%
A morphism of schemes is *of finite type* (`FiniteType f`) if it is locally of finite type and
quasi-compact {cite Sta}[Tag 01T0]. The class bundles Mathlib's {decl}`LocallyOfFiniteType` and
{decl}`QuasiCompact`, as Mathlib's {decl}`IsProper` bundles its parts: its parents are instances
({decl}`FiniteType.toLocallyOfFiniteType` supplies the {decl}`LocallyOfFiniteType` that Mathlib's
{decl Scheme.Hom.smoothLocus}`smoothLocus` asks for), and conversely `FiniteType f` is inferred from
the two parts.
::::

::::definition "def:alg_scheme" (lean := "AlgebraicGeometry.AlgScheme, AlgebraicGeometry.AlgScheme.over")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §1, p. 119]", href := "https://doi.org/10.2307/1970486" }
%%%
`AlgScheme k` is the category of algebraic `k`-schemes: Mathlib's {decl}`MorphismProperty.Over` for
the property "of finite type and separated" of the structure morphism to $`\operatorname{Spec} k`.
An object `X` is a scheme `X.left` with a structure morphism `X.hom` having the property, and a
morphism `h : Y ⟶ X` is a morphism of schemes `h.left` over $`\operatorname{Spec} k`. The instances
{decl}`AlgScheme.over` and `AlgScheme.finiteType` make the structure morphism available to Mathlib's
notation `X.left ↘ Spec (.of k)` and its finite type available to instance search, which does not
see through the bundled property.
::::

# Regular points and the singular locus

::::definition "def:is_regular" (lean := "AlgebraicGeometry.Scheme.IsRegularAt, AlgebraicGeometry.IsRegular, AlgebraicGeometry.Scheme.singularLocus")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §1]", href := "https://doi.org/10.2307/1970486" }
%%%
A point $`x` of a scheme $`X` is *simple* (`X.IsRegularAt x`) if the local ring
$`\mathcal{O}_{X,x}` is a regular local ring; $`X` is *non-singular* (`IsRegular X`, a class with
the single field `isRegularAt`) if every point is simple, and the *singular locus*
`X.singularLocus` is the set of points that are not simple.

These are Hironaka's notions, defined by the local rings alone and without reference to a base
field. In the functorial theorems the singular locus is instead the complement of Mathlib's
{decl Scheme.Hom.smoothLocus}`smoothLocus` of the structure morphism over `k`; over a field of
characteristic zero the two agree for a scheme of finite type, since regularity and smoothness
coincide over a perfect field.
::::

::::definition "def:regular_system" (lean := "IsLocalRing.IsRegularSystemOfParameters")
A family $`z_1, \dots, z_n` in a local ring $`R` is a *regular system of parameters* if it generates
the maximal ideal and $`n` is the Krull dimension of $`R`. In a regular local ring these are the
minimal generating systems of $`\mathfrak m`; they play the role of local coordinates in the normal
crossings conditions ({bpref "def:normal_crossings"}[], {bpref "def:snc"}[]).
::::

# Stalks and orders of ideal sheaves

::::definition "def:stalk_ideal" (lean := "AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal, AlgebraicGeometry.Scheme.IdealSheafData.IsNonzeroEverywhere")
%%%
paperIdentity := some { label := "[Hir64, Main Theorem II]", href := "https://doi.org/10.2307/1970486" }
%%%
The stalk $`J_x \subseteq \mathcal{O}_{X,x}` of an ideal sheaf, `J.stalkIdeal x`, is the ideal
generated by the germs at $`x` of the sections of $`J` over the affine opens containing $`x`. An
ideal sheaf *has nonzero stalks* (`IsNonzeroEverywhere J`) if $`J_x \ne 0` at every point:
Hironaka's "coherent sheaf of non-zero ideals", read at every stalk. On a non-singular scheme this
is Kollár's "not zero on any irreducible component" {cite Kol07}[Theorem 35].
::::

::::definition "def:order" (lean := "IsLocalRing.ord, AlgebraicGeometry.Scheme.IdealSheafData.ord")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §4]", href := "https://doi.org/10.2307/1970486" }
%%%
The *order* of an ideal $`I` of a local ring $`(R, \mathfrak m)` is
$`\operatorname{ord} I = \sup\{r : I \subseteq \mathfrak m^r\}` in $`\mathbb{N} \cup \{\infty\}`
({decl}`IsLocalRing.ord`, {cite Kol07}[Definition 47]). The order of an ideal sheaf at a point,
`J.ord x`, is the order of the stalk: Hironaka's $`\nu(J_x)`. It is $`\infty` exactly when
$`J_x = 0` (by the Krull intersection theorem) and $`0` exactly when $`J_x` is the unit ideal, so
an ideal sheaf with nonzero stalks has finite order everywhere, and the maximal order of Main
Theorem II ({bpref "thm:mt2"}[]) is a natural number.
::::

# Invertible ideal sheaves

::::definition "def:invertible" (lean := "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible")
%%%
paperIdentity := some { label := "[Sta, Tag 01WS]", href := "https://stacks.math.columbia.edu/tag/01WS" }
%%%
An ideal sheaf is *invertible* if it is locally generated by a single nonzerodivisor; its closed
subscheme is then an effective Cartier divisor. {decl}`IdealSheafData.IsInvertible` is the form used
by the blow-up construction: every point has an affine open neighbourhood $`U` on which $`J(U)` is
generated by one nonzerodivisor {cite Sta}[Tag 01WS]; {cite Kol07}[Warning 20]. The unit ideal sheaf is
invertible (`isInvertible_top`), which is why a blow-up with empty centre is an isomorphism
({bpref "def:blowup_lift"}[]). The invertibility of a boundary follows from the hypotheses of the
main theorems and is not a separate hypothesis ({bpref "thm:mt2"}[]); the notion enters their
statements through the blow-up and in the conclusion of Corollary 3 ({bpref "thm:cor3"}[]).
::::

# Normal crossings
%%%
tag := "sec-normal-crossings"
%%%

On a regular scheme, a union of hypersurfaces has *simple normal crossings* when its components
are regular and meet like coordinate hyperplanes: near every point $`x` there is a regular system
of parameters $`z_1, \dots, z_n` of $`\mathcal{O}_{X,x}` in which each component through $`x` is a
hyperplane $`z_j = 0`, distinct components using distinct coordinates. In the plane the two axes
$`xy = 0`, or a smooth curve crossing a line transversally, have simple normal crossings; a curve
tangent to a line ($`x = y^2` and $`x = 0`) and three lines through a point do not, the second
because the plane has only two coordinates; the node $`y^2 = x^2(x + 1)` has normal crossings but
not simple ones, its single component not being regular. Hironaka's form of the condition
follows; Kollár's is {bpref "def:snc"}[].

::::definition "def:normal_crossings" (lean := "AlgebraicGeometry.Scheme.IdealSheafData.IsSncBoundaryWith, AlgebraicGeometry.Scheme.IdealSheafData.IsSncBoundary")
%%%
paperIdentity := some { label := "[Hir64, Ch. 0, §5, Definition 2]", href := "https://doi.org/10.2307/1970486" }
%%%
Hironaka's Definition 2: $`E` *has only normal crossings with* $`D` if at every point $`x` of $`D`
there is a regular system of parameters $`(z_1, \dots, z_n)` of $`\mathcal{O}_{X,x}` such that
the ideal of each irreducible component of $`E` through $`x` (a minimal prime of $`E_x`) is
generated by one of the $`z_i`, and the ideal of $`D` is generated by some of the $`z_i`. With
$`D = X` (the zero ideal sheaf) one says that $`E` *has only normal crossings*.

The components are read locally, as the minimal primes of the stalk, as Hironaka does; on a
scheme these are the local ideals of the global irreducible components of $`E`, each asked to be
a parameter, so at the points of $`D` the condition is simple normal crossings of the reduced
subscheme $`E`, and with $`D`. Nothing is asserted at the points off $`D` (for the empty $`D` the
condition always holds), whereas the manifold predicate of the same name
({bpref "def:snc_boundary"}[]) also asserts simple normal crossings of the boundary at every
point. The functorial theorems use Kollár's simple normal crossings, which is phrased on a family
of global components ({bpref "def:snc"}[]); the two agree on the family of irreducible components
of $`E` (`isSncBoundaryWith_iff_hasSncWith_componentFamily`, and
`isSncBoundary_iff_isSnc_componentFamily` on a scheme smooth over $`k`).
::::
