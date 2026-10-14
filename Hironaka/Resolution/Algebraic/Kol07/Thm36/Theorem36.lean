/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.BR
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AdmissiblePairs
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineFunctoriality
import Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Kol07.Thm36.BaseChangeAffine
import Hironaka.Resolution.Algebraic.Kol07.Thm36.RelativeDimensionConstancy
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36Assembly
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Scheme.FiniteType
public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.Resolution.Defs
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Algebra.RegularSmooth.SingularLocus
import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.Snc.RelativeDimensionConstant
public import Hironaka.Scheme.ReducedEquidimensional
import Hironaka.Scheme.Resolution.Basic
import Hironaka.Scheme.BlowUpSequence.Projective

/-!
# Kollár's Theorems 36 and 27: functorial and strong resolution

The functorial resolution theorem (`AlgebraicGeometry.exists_functorial_resolution`, at the end of
this file) is stated on the category `AlgebraicGeometry.ReducedEquidimensionalScheme k`
(`Hironaka.Scheme.Resolution.Defs`), the full subcategory of the algebraic `k`-schemes `X` with
`X.left.IsReducedEquidimensional k`: the reduced algebraic `k`-schemes whose smooth locus over `k`
has one relative dimension — Kollár's standing convention that his schemes are equidimensional
[Kol07, Notation 64], as a hypothesis; the irreducible components may meet. The proof works on
the underlying schemes of the inputs, the membership being `X.property`: clauses (1)–(3) are
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36Assembly`, the change of fields (4b) is
`Hironaka.Resolution.Algebraic.Kol07.Thm36.BaseChangeAffine`, and the two statements of the
smooth-morphism clause (4a) [Kol07, 34.1] are derived here: a smooth `k`-morphism `h : Y ⟶ X`
between class members has the constant relative dimension `dY - dX`
(`smoothOfRelativeDimension_sub_of_smoothLocus`,
`Hironaka.Resolution.Algebraic.Kol07.Thm36.RelativeDimensionConstancy`), and at that dimension the
versions of (4a) taking the relative dimension as an input (`BR_eq_eraseEmpty_pullback_of_smooth`,
`BRAffine_eq_eraseEmpty_pullback_of_smooth`) give `BR_pullback_smooth_of_class` and
`BRAffine_pullback_smooth_of_class`: for surjective `h` the resolution of `Y` is the pullback of
the resolution of `X`, and in general it is the pullback with its empty blow-ups deleted.

Kollár's strong resolution [Kol07, Theorem 27] (`AlgebraicGeometry.exists_strong_resolution`)
follows, at the end of the file, by applying the functorial resolution to an integral algebraic
`k`-scheme, a class member (`isReducedEquidimensional_of_isIntegral`); so does Hironaka's Main
Theorem I (`Hironaka.Resolution.Algebraic.Hir64.MainTheoremI`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- Clause (4a) of [Kol07, Theorem 36], the smooth morphisms [Kol07, 34.1], on the class: for a
smooth `k`-morphism `h : Y ⟶ X` between class members, the resolution of `Y` is the pullback of the
resolution of `X` when `h` is surjective, and in general the pullback with its empty blow-ups
deleted. The relative dimension of `h` is `dY - dX`
(`smoothOfRelativeDimension_sub_of_smoothLocus`, from the second conjuncts of the two class
hypotheses); the two statements are `BR_eq_pullback_of_smooth_surjective` and
`BR_eq_eraseEmpty_pullback_of_smooth` at that dimension. -/
theorem BR_pullback_smooth_of_class (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k)
    (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    (hY : Y.IsReducedEquidimensional k)
    (h : Y ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] [Smooth h] :
    (Function.Surjective h → (BRFunctor k).seq Y = ((BRFunctor k).seq X).pullback h) ∧
      (BRFunctor k).seq Y = (((BRFunctor k).seq X).pullback h).eraseEmpty := by
  have := hX.1
  have := hY.1
  obtain ⟨dX, hdX⟩ := hX.2
  obtain ⟨dY, hdY⟩ := hY.2
  have hd : SmoothOfRelativeDimension (dY - dX) h :=
    smoothOfRelativeDimension_sub_of_smoothLocus (k := k) (dX := dX) (dY := dY) X Y h
  exact ⟨fun hs => BR_eq_pullback_of_smooth_surjective X Y hX hY h (dY - dX) hs,
    BR_eq_eraseEmpty_pullback_of_smooth X Y hX hY h (dY - dX)⟩

/-- Clause (4a) [Kol07, 34.1] for the affine construction `BRAffine` on the class. The relative
dimension of `h` is `dY - dX` (`smoothOfRelativeDimension_sub_of_smoothLocus`); the second
statement is `BRAffine_eq_eraseEmpty_pullback_of_smooth` at that dimension with admissible
embeddings of `X` and `Y` (`exists_admissibleEmbedding`), and the first follows for surjective `h`
(`eraseEmpty_pullback_of_flat_surjective`, `eraseEmpty_BRAffine`). -/
theorem BRAffine_pullback_smooth_of_class (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IsAffine X]
    (hX : X.IsReducedEquidimensional k)
    (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [IsAffine Y]
    (hY : Y.IsReducedEquidimensional k)
    (h : Y ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] [Smooth h] :
    (Function.Surjective h → BRAffine k Y = (BRAffine k X).pullback h) ∧
      BRAffine k Y = ((BRAffine k X).pullback h).eraseEmpty := by
  have := hX.1
  have := hY.1
  obtain ⟨dX, hdX⟩ := hX.2
  obtain ⟨dY, hdY⟩ := hY.2
  have hd : SmoothOfRelativeDimension (dY - dX) h :=
    smoothOfRelativeDimension_sub_of_smoothLocus (k := k) (dX := dX) (dY := dY) X Y h
  obtain ⟨TX, embX, hadmX⟩ := exists_admissibleEmbedding (k := k) X
  obtain ⟨TY, embY, hadmY⟩ := exists_admissibleEmbedding (k := k) Y
  have h2 : BRAffine k Y = ((BRAffine k X).pullback h).eraseEmpty :=
    BRAffine_eq_eraseEmpty_pullback_of_smooth X Y hX hY h (dY - dX) TX embX hadmX TY embY hadmY
  refine ⟨fun hs => ?_, h2⟩
  rw [h2, eraseEmpty_pullback_of_flat_surjective _ _ hs, eraseEmpty_BRAffine]

end Hironaka.Resolution

end

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme

namespace AlgebraicGeometry

/-- **Kollár's functorial resolution** [Kol07, Theorem 36]. There is a family `BR` of blow-up
sequence functors on reduced equidimensional algebraic `k`-schemes (`BlowUpSequenceFunctor
(ReducedEquidimensionalScheme k)`), one for each field `k` of characteristic zero, such that
* every value `BR(X)`, with composite `Π : X_r → X`, is a strong resolution of `X` [Kol07, (3)]
  (`BlowUpSequence.IsStrongResolution`): `Π` is projective and birational, and (1) `X_r` is smooth
  over `k`; (2) `Π` is an isomorphism over the smooth locus `X^{ns}`; (3) `Π⁻¹(Sing X)` is the
  support of a simple normal crossing divisor;
* (4) `BR` commutes with smooth morphisms [Kol07, 34.1] (`CommutesWithSmoothMorphisms`) and with
  change of fields [Kol07, 34.2] (`CommutesWithChangeOfFields`).

A smooth equidimensional scheme is an input, and `Π` may then be the identity. The irreducible
components of an input may meet: the two axes `xy = 0` in the plane are an input.

Relation to the source.
* **Translation.** `(X.left ↘ Spec (.of k)).smoothLocus`, Mathlib's `smoothLocus` of the structure
  morphism, is Kollár's $X^{ns}$, and its complement is $\operatorname{Sing} X$; over a field of
  characteristic zero it is the set of points with regular local ring
  (`Scheme.mem_smoothLocus_iff_isRegularAt`).
* **Interpretation.** Kollár's clause (3), "$\Pi^{-1}(\operatorname{Sing} X)$ is a divisor with
  simple normal crossings", is read with the reduced structure on $\Pi^{-1}(\operatorname{Sing} X)$:
  it is `IsSncDivisor` of that set of points.
* **Gap.** Kollár states the theorem for all schemes of finite type over `k`. The inputs here
  (`ReducedEquidimensionalScheme`) are the reduced, equidimensional ones
  (`Scheme.IsReducedEquidimensional`), whose irreducible components may meet; the non-reduced
  schemes and the schemes with components of different dimensions are excluded, and (4) is asserted
  only between inputs. Kollár proves the theorem by feeding triples in the sense of
  [Kol07, Notation 64] (smooth equidimensional ambient schemes) to Theorem 35, and the construction
  here needs both restrictions: for a non-reduced `X` the strict transform at which the run is
  truncated need not be reduced; for components of different dimensions (4) fails. For `X` the
  cuspidal curve `y² = x³`, `Y = X ⊔ (X × 𝔸¹)` and the smooth surjection `h = 𝟙 ⊔ pr₁`, the run on
  an embedding of `Y` first blows up only the cusp line of the second piece, where the order is `2`,
  whereas `h^* BR(X)` first blows up the preimage of the cusp point, which contains the cusp point
  of the first piece. Kollár's remark that 34.1 is a local property is where a proof for mixed
  dimensions would be needed; none is printed.
* **Restatement.** Kollár's clauses (1)–(3) for the blow-up sequence $BR(X)$ are stated as
  `IsStrongResolution`, which also asks that $\Pi$ be projective and birational: a strong
  resolution in the sense of [Kol07, (3)], as the sentence introducing the theorem says ("we obtain
  strong and functorial resolution"). Both follow from the other clauses: the composite of a
  succession of blow-ups of a Noetherian scheme is projective, and by (2) $\Pi$ is an isomorphism
  over the smooth locus, which is dense.
* **Formalisation note.** The class of inputs is stable under change of fields and under étale
  `k`-morphisms, so (4) covers the base change of every input along every field extension and
  every étale morphism to an input: over a field of characteristic zero a reduced scheme of finite
  type is geometrically reduced [Sta, Tag 020I], smoothness is stable under base change
  [Sta, Tag 01VB] and fpqc local on the base [Sta, Tag 02VL], an étale morphism has reduced source
  when its target is reduced [Sta, Tag 033B], and smoothness descends along smooth surjections
  [Sta, Tag 02K5]. These stability facts are not formalized: applying (4) to a given base change
  requires showing that it is an input.

Source statement: [Kol07, Theorem 36] -/
theorem exists_functorial_resolution :
    ∃ BR : ∀ (k : Type u) [Field k] [CharZero k],
        BlowUpSequenceFunctor (ReducedEquidimensionalScheme k),
      -- (1)–(3)
      (∀ (k : Type u) [Field k] [CharZero k] (X : ReducedEquidimensionalScheme k),
        (BR k X).IsStrongResolution) ∧
      -- (4), 34.1
      (∀ (k : Type u) [Field k] [CharZero k], CommutesWithSmoothMorphisms (BR k)) ∧
      -- (4), 34.2
      CommutesWithChangeOfFields BR := by
  refine ⟨fun k _ _ X => (Hironaka.Resolution.BRFunctor k).seq X.obj.left,
    fun k _ _ X => ?_, fun _ _ _ => ⟨?_, ?_⟩, ?_⟩
  · have : IsReduced X.obj.left := X.property.isReduced
    have hdense : Dense ((X.obj.left ↘ Spec (.of k)).smoothLocus : Set X.obj.left) := by
      convert Scheme.dense_setOf_isRegularAt (X.obj.left ↘ Spec (.of k)) using 1
      ext x
      exact Scheme.mem_smoothLocus_iff_isRegularAt _ x
    have hiso := Hironaka.Resolution.BR_isIso_over_smoothLocus_of_class X.obj.left X.property
    have : IsNoetherian X.obj.left := (X.obj.left ↘ Spec (.of k)).isNoetherian_of_field
    exact ⟨⟨Hironaka.Resolution.BR_smooth_last_of_class X.obj.left X.property,
        @Scheme.BlowUpSequence.isProjective_composite _ this _, _, hdense, hiso⟩, hiso,
      Hironaka.Resolution.BR_exists_snc_support_of_class X.obj.left X.property⟩
  · intro X Y h hs hsurj
    have : Smooth h.hom.left := hs
    exact (Hironaka.Resolution.BR_pullback_smooth_of_class X.obj.left X.property Y.obj.left
      Y.property h.hom.left).1 hsurj
  · intro X Y h hs
    have : Smooth h.hom.left := hs
    exact (Hironaka.Resolution.BR_pullback_smooth_of_class X.obj.left X.property Y.obj.left
      Y.property h.hom.left).2
  · intro k L _ _ _ _ σ X XL p sq
    exact Hironaka.Resolution.BR_baseChange_of_class X.obj.left X.property L σ XL.obj.left
      XL.property p sq

/-- **Kollár's strong resolution of singularities** [Kol07, Theorem 27]. Let `X` be a variety (an
integral algebraic `k`-scheme) over a field `k` of characteristic zero. Then there is a birational
and projective morphism `Π : X' → X`, the composite `S.composite` of a succession of blow-ups `S`
of `X`, that is a strong resolution of `X` (`BlowUpSequence.IsStrongResolution`): (1) `X'` is
smooth over `k`; (2) `Π` is an isomorphism over the smooth locus `X^{ns}`; (3) `Π⁻¹(Sing X)` is
the support of a simple normal crossing divisor. Projectivity and birationality are part of
`BlowUpSequence.IsResolution`; birationality is the isomorphism over a dense open subset of `X`,
here the smooth locus.

This is resolution of singularities in its usual form: a smooth `X'` with a projective birational
morphism to `X`, here a succession of blow-ups. Kollár's weaker form [Kol07, Corollary 22], a
smooth `X'` with a birational projective morphism to `X` and no conditions (2) and (3), is the part
`BlowUpSequence.IsResolution` of the conclusion.

Relation to the source.
* **Translation.** Kollár's variety is an integral algebraic `k`-scheme, `X : AlgScheme k` with
  `[IsIntegral X.left]`.
* **Translation.** Kollár's "birational and projective morphism" is the projectivity
  (`IsProjective`, [Sta, Tag 01W8]) and the birationality of `BlowUpSequence.IsResolution`.
* **Interpretation.** Kollár's clause (3), "$\Pi^{-1}(\operatorname{Sing} X)$ is a divisor with
  simple normal crossing", is read with the reduced structure on $\Pi^{-1}(\operatorname{Sing} X)$,
  as in Theorem 36 (`AlgebraicGeometry.exists_functorial_resolution`).
* **Strengthening.** Kollár assumes `X` quasi-projective, which his proof uses to embed `X` in a
  projective space; no such hypothesis is made here.
* **Strengthening.** Here $\Pi$ (`S.composite`) is in addition the composite of a succession of
  blow-ups of `X`, whose centres are not asserted to be smooth; Theorem 27 as printed does not say
  this. It matches Kollár's construction: his $R(X)$ is the birational transform of $X$ that is a
  centre $Z_j$ of a succession of smooth blow-ups of an ambient smooth $P$, and by restriction
  [Kol07, 30.2] his $\Pi$ is the composite of the blow-ups of the birational transforms of $X$ along
  their intersections with the earlier centres, which may be singular [Kol07, Warning 23].

Source statement: [Kol07, Theorem 27] -/
theorem exists_strong_resolution {k : Type u} [Field k] [CharZero k] (X : AlgScheme k)
    [IsIntegral X.left] :
    ∃ S : Scheme.BlowUpSequence X.left, S.IsStrongResolution := by
  obtain ⟨BR, hBR, -, -⟩ := exists_functorial_resolution.{u}
  have h := Hironaka.Resolution.isReducedEquidimensional_of_isIntegral (k := k) X.left
  let Y : ReducedEquidimensionalScheme k := ⟨X, h.1, h.2⟩
  exact ⟨BR k Y, hBR k Y⟩

end AlgebraicGeometry
