/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.Resolution.Defs

/-!
# Resolution of singularities: the algebraic main theorems

## Conventions

An *algebraic `k`-scheme* (`X : AlgScheme k`) is a scheme `X.left` whose structure morphism
`X.left ↘ Spec k` is separated and of finite type (`FiniteType`; Hironaka's "algebraic `B`-scheme";
Kollár's "scheme of finite type over a field", made separated); its morphisms are the `k`-morphisms.
In prose `X` also denotes the scheme `X.left`.
*Reduced and irreducible* is `IsIntegral` (`isIntegral_iff_irreducibleSpace_and_isReduced`).
*Non-singular* (`IsRegular`) means that every local ring `𝒪_{X,x}` is a regular local ring, and the
*singular locus* (`singularLocus`) is the set of points where it is not. *Smooth over `k`* is
Mathlib's `Smooth` of the structure morphism, and *equidimensional* means that the smooth locus has
a single relative dimension over `k` (`X.left.IsReducedEquidimensional k`: reduced and
equidimensional); for a smooth `X` this is smoothness of a single relative dimension `n`
(`SmoothOfRelativeDimension n`), written "smooth and equidimensional". Over the perfect field `k` a
smooth scheme is non-singular. The *monoidal transformation* of `X` with centre the closed subscheme
of ideal sheaf `D` is `D.blowUp`, with projection `D.blowUpπ`; a *finite succession of monoidal
transformations* is a `BlowUpSequence X`, Kollár's blow-up sequence with specified centres
(`S.center i`), stages (`S.stage i`) and composite `S.composite : S.last ⟶ X`. A morphism is
*projective* (`IsProjective`) when it is a closed immersion into the projective bundle
`P(E) = Proj (Sym E)` (`E.projectiveBundle`) of a quasi-coherent sheaf of modules `E` of finite type
(Mathlib's `Y.Modules` with `IsQuasicoherent` and `IsFiniteType`), followed by the projection of the
bundle [Sta, Tag 01W8]; a projective morphism is proper. Ideal sheaves are
Mathlib's `X.IdealSheafData`, closed subschemes are given by their ideal sheaves, and "`D` is
reduced" is `IsReduced D.subscheme`. Two hypotheses of Main Theorems II and II(N) and Corollary 1
(the second also of Corollary 3) are given in the transcription's reading rather than in Hironaka's
words: his "coherent sheaf of non-zero ideals" is an ideal sheaf with nonzero stalks, and his
"non-singular" is smoothness over `k`. Of his "reduced subscheme of everywhere codimension one" only
the reducedness is assumed. The regularity of every local ring and the invertibility of the ideal
sheaf of the boundary are not separate hypotheses: both follow from the hypotheses kept (regularity
from `IsSncBoundary` and from smoothness over the perfect field `k`; invertibility of the boundary
ideal from reducedness and normal crossings on a regular scheme). The order `J.ord x` of an ideal
sheaf at a point is Hironaka's `ν(J_x)`, the largest `ν` with `J_x ⊆ 𝔪_x^ν` for the stalk
`J_x = J.stalkIdeal x`, valued in `ℕ∞`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme

namespace AlgebraicGeometry

/-! ### Principalization -/

/-! #### The conditions of Hironaka's Main Theorems II and II(N) -/

section ClausesII

/-- An algebraic `k`-scheme is a scheme over `Spec k` whose structure morphism is of finite type and
separated. -/
example {k : Type u} [Field k] (X : AlgScheme k) :
    -- of finite type over `k`
    FiniteType (X.left ↘ Spec (.of k)) ∧
    -- separated over `k`
    IsSeparated (X.left ↘ Spec (.of k)) :=
  X.prop

/-- Every centre of a succession of blow-ups is non-singular and irreducible [Hir64, Main Theorem II
(i), Main Theorem II(N) (1); Corollary 1, "non-singular irreducible centers D(i)", p. 143]. -/
example {X : Scheme.{u}} (S : BlowUpSequence X) :
    S.HasRegularIrreducibleCenters ↔ ∀ i : Fin S.length,
      -- the `i`-th centre is non-singular: every local ring is regular
      IsRegular (S.center i).subscheme ∧
      -- and irreducible
      IrreducibleSpace (S.center i).subscheme :=
  Iff.rfl

/-- Starting from `E`, every boundary `E_i` has only normal crossings with the centre `D_i`, and the
last boundary `E_r` has only normal crossings [Hir64, Main Theorem II (iii) and the first half of
(iv); Main Theorem II(N) (3) and the first half of (4)]. The boundaries are `E_0 = E` and
`E_{i+1} = red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`. -/
example {X : Scheme.{u}} (S : BlowUpSequence X) (E : X.IdealSheafData) :
    S.HasSncBoundaries E ↔
      -- each boundary `E_i` has only normal crossings with the centre `D_i`
      (∀ i : Fin S.length, (S.boundarySeq E i.castSucc).IsSncBoundaryWith (S.center i)) ∧
      -- the last boundary `E_r` has only normal crossings
      (S.boundarySeq E (Fin.last S.length)).IsSncBoundary :=
  BlowUpSequence.hasSncBoundaries_iff S E

/-- A reduced closed subscheme `E` has only normal crossings with a closed subscheme `D`
[Hir64, Ch. 0, §5, Definition 2] when at every point `x` of `D` some regular system of parameters
`z_1, …, z_n` of the local ring `𝒪_{X,x}` cuts out each irreducible component of `E` through `x`
by one of its members and cuts out `D` by some of its members. This is a condition at the points
of `D` only: nothing is asserted at the points off `D`. -/
example {X : Scheme.{u}} (E D : X.IdealSheafData) :
    E.IsSncBoundaryWith D ↔ ∀ x ∈ D.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      -- `z` is a regular system of parameters of `𝒪_{X,x}`
      IsLocalRing.IsRegularSystemOfParameters z ∧
      -- the ideal of each component of `E` through `x` (a minimal prime of `E_x`) is some `(z_i)`
      (∀ P ∈ (E.stalkIdeal x).minimalPrimes, ∃ i, P = Ideal.span {z i}) ∧
      -- the ideal of `D` at `x` is generated by some of the `z_i`
      ∃ s : Finset (Fin n), D.stalkIdeal x = Ideal.span (z '' ↑s) :=
  Iff.rfl

/-- A reduced closed subscheme `E` has only normal crossings [Hir64, Ch. 0, §5, Definition 2] when
it has only normal crossings with `X` itself, the closed subscheme of the zero ideal sheaf `⊥`: the
condition above at every point of `X`. -/
example {X : Scheme.{u}} (E : X.IdealSheafData) :
    E.IsSncBoundary ↔ E.IsSncBoundaryWith ⊥ :=
  Iff.rfl

end ClausesII

/-- **Hironaka's Main Theorem II** [Hir64, Main Theorem II, pp. 142–143]: order reduction. Let `X`
be a smooth algebraic `k`-scheme (`AlgScheme k`), `k` of characteristic zero, `J` an ideal sheaf on
`X` with nonzero stalks whose greatest order `ν(J_x)` over the points `x` of `X` is `d`, and `E₀` a
reduced closed subscheme of `X` with only normal crossings. Then there is a finite succession of
monoidal transformations `f_i : X_{i+1} → X_i` with centres `D_i ⊆ X_i` such that
* (i) each `D_i` is non-singular and irreducible (`BlowUpSequence.HasRegularIrreducibleCenters`);
* (ii) the weak transform `J_i` of `J` on `X_i` has order at least `d` at every point of `D_i`;
* (iii) with `E_{i+1} = red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`, each `E_i` has only normal crossings with
  `D_i`;
* (iv) `E_r` has only normal crossings and `J_r` has order less than `d` at every point of `X_r`.

Clause (iii) and the first half of (iv) are `BlowUpSequence.HasSncBoundaries`; the second half of
(iv) is the last conjunct. The weak transform `J_{i+1}` is the pull-back of `J_i` along `f_i`
divided by the largest power of the ideal of the exceptional divisor that divides it; "has only
normal crossings (with)" is Hironaka's Definition 2 (`IsSncBoundary`, `IsSncBoundaryWith`), which
on a scheme is simple normal crossings of the reduced `E_i`: the condition `DivisorFamily.IsSnc`
(`DivisorFamily.HasSncWith`) of the functorial theorems, read on the family of irreducible
components of `E_i`.

For `d = 0` (`J = 𝒪_X`), which the printed statement does not exclude, clause (iv) forces `X_r` to
be empty; blowing up the irreducible components of `X` one after another achieves it
(`Hironaka.Sequence.exists_blowUpSequence_isEmpty_last_of_smooth`). Hironaka's monoidal
transformation, defined by a universal property [Hir64, pp. 129, 166], is empty over a centre that
is a whole component, and clause (i) asks no density.

Relation to the source.
* **Translation.** `S.weakTransformSeq J i` is Hironaka's $J_i$, `S.boundarySeq E₀ i` his $E_i$,
  and `J.ord x` his $\nu(J_x)$; `IsGreatest (Set.range J.ord) d` says that $d$ is the greatest
  of the orders $\nu(J_x)$.
* **Translation.** `[Smooth (X.left ↘ Spec (.of k))]` is Hironaka's "non-singular": for a scheme of
  finite type over the perfect field `k` the two agree (smoothness gives the regularity of every
  local ring, and a non-singular such scheme is smooth). As in the print, the irreducible components
  of `X` may have different dimensions.
* **Interpretation.** Hironaka's "coherent sheaf of non-zero ideals" is read as an ideal sheaf
  (`X.left.IdealSheafData`, quasi-coherent, hence coherent on the Noetherian `X`) with nonzero
  stalks (`hJ`).
* **Restatement.** The regularity of the local rings of `X` and the invertibility of the ideal sheaf
  of `E₀` ("of everywhere codimension one"), which Hironaka also assumes, are not separate
  hypotheses: they follow from the hypotheses kept (regularity from smoothness over the perfect
  field `k`; invertibility from reducedness and normal crossings on a regular scheme, see
  `IsSncBoundaryWith`). Of his "reduced subscheme of everywhere codimension one" only the
  reducedness, `[IsReduced E₀.subscheme]`, is assumed.
* **Out of scope.** Hironaka's remark that the theorem remains true over any local ring of his class
  ℬ [Hir64, p. 151; ℬ defined on p. 161], which he uses for local rings of analytic spaces (Main
  Theorem II′, p. 152). The base here is a field of characteristic zero, as in the print ("a field
  **B** of characteristc [sic] zero").

Source statement: [Hir64, Main Theorem II, pp. 142–143] -/
theorem exists_blowUpSequence_ord_weakTransformSeq_lt {k : Type u} [Field k] [CharZero k]
    (X : AlgScheme k) [Smooth (X.left ↘ Spec (.of k))]
    (J : X.left.IdealSheafData) (hJ : IsNonzeroEverywhere J)
    (d : ℕ) (hd : IsGreatest (Set.range J.ord) (d : ℕ∞))
    (E₀ : X.left.IdealSheafData) [IsReduced E₀.subscheme] (hE₀ : IsSncBoundary E₀) :
    ∃ S : BlowUpSequence X.left,
      -- (i)
      S.HasRegularIrreducibleCenters ∧
      -- (ii)
      (∀ i : Fin S.length, ∀ x ∈ (S.center i).support,
        (d : ℕ∞) ≤ (S.weakTransformSeq J i.castSucc).ord x) ∧
      -- (iii) and the first half of (iv)
      S.HasSncBoundaries E₀ ∧
      -- the second half of (iv)
      ∀ y : S.last, (S.weakTransformSeq J (Fin.last S.length)).ord y < d :=
  sorry

/-- **Hironaka's Main Theorem II(N)** [Hir64, Main Theorem II(N), p. 176]: principalization by
iterated order reduction. Let `X` be a smooth algebraic `k`-scheme (`AlgScheme k`), `k` of
characteristic zero, `J` an ideal sheaf on `X` with nonzero stalks, and `E` a reduced closed
subscheme of `X` with only normal crossings. Then there is a finite succession of monoidal
transformations `f_i : X_{i+1} → X_i` with centres `B_i ⊆ X_i` such that
* (1) each `B_i` is non-singular and irreducible (`BlowUpSequence.HasRegularIrreducibleCenters`);
* (2) for each `i` there is a positive integer `d_i` that is the greatest order of the weak
  transform `J_i` of `J` on `X_i` and its order at every point of `B_i`;
* (3) with `E_{i+1} = red(f_i⁻¹(E_i ∪ B_i))`, each `E_i` has only normal crossings with `B_i`;
* (4) `E_r` has only normal crossings and `J_r = 𝒪_{X_r}`.

Clause (3) and the first half of (4) are `BlowUpSequence.HasSncBoundaries`; the second half of (4)
is the last conjunct. II(N) writes `red(f_i⁻¹(E_i ∪ B_i))` where II writes
`red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`, the same reduced subscheme: both are the reduced structure on
`f_i⁻¹(|E_i| ∪ |B_i|)`. For `J = 𝒪_X` the empty succession satisfies every clause.

Relation to the source.
* **Translation.** The notation is that of Main Theorem II
  (`exists_blowUpSequence_ord_weakTransformSeq_lt`): `S.weakTransformSeq J i` is $J_i$ and
  `S.boundarySeq E i` is $E_i$. `S.weakTransformSeq J (Fin.last S.length) = ⊤` is
  $J_r = \mathcal{O}_{X_r}$, the top ideal sheaf `⊤` being the unit ideal.
* **Translation.** As in Main Theorem II, `[Smooth (X.left ↘ Spec (.of k))]` is Hironaka's
  "non-singular" (the two agree for a scheme of finite type over the perfect field `k`).
* **Interpretation.** As in Main Theorem II, Hironaka's "coherent sheaf of non-zero ideals" is read
  as an ideal sheaf with nonzero stalks (`hJ`).
* **Gap.** Hironaka's "algebraic scheme" [Hir64, Ch. I, p. 162] is a scheme of finite type over
  $\operatorname{Spec} S$ for some local ring $S$ of his class ℬ (Noetherian, residue field of
  characteristic zero, his condition (ii) on completions, p. 161), a class containing every field of
  characteristic zero and the local rings of analytic spaces. Here `X` is separated and of finite
  type over a field `k` of characteristic zero.
* **Restatement.** As in Main Theorem II, the regularity of `X` and the invertibility of the ideal
  sheaf of `E`, which Hironaka also assumes, are not separate hypotheses: they follow from the
  hypotheses kept (regularity from smoothness over the perfect field `k`; invertibility from
  reducedness and normal crossings on a regular scheme).
* **Restatement.** Hironaka states the theorem for $X$ of dimension $N$, the index of the
  fundamental theorem II₂^N from which he deduces it [Hir64, p. 176]; $N$ does not appear in the
  conclusion. The statement here is II(N) for all $N$ at once. As in the print, `X` may have several
  irreducible components (Hironaka reduces the proof to irreducible $X$).

Source statement: [Hir64, Main Theorem II(N), p. 176] -/
theorem exists_blowUpSequence_weakTransformSeq_eq_top {k : Type u} [Field k] [CharZero k]
    (X : AlgScheme k) [Smooth (X.left ↘ Spec (.of k))]
    (J : X.left.IdealSheafData) (hJ : IsNonzeroEverywhere J)
    (E : X.left.IdealSheafData) [IsReduced E.subscheme] (hE : IsSncBoundary E) :
    ∃ S : BlowUpSequence X.left,
      -- (1)
      S.HasRegularIrreducibleCenters ∧
      -- (2)
      (∀ i : Fin S.length, ∃ d : ℕ, 0 < d ∧
        IsGreatest (Set.range (S.weakTransformSeq J i.castSucc).ord) (d : ℕ∞) ∧
        ∀ z ∈ (S.center i).support, (S.weakTransformSeq J i.castSucc).ord z = d) ∧
      -- (3) and the first half of (4)
      S.HasSncBoundaries E ∧
      -- the second half of (4)
      S.weakTransformSeq J (Fin.last S.length) = ⊤ :=
  sorry

/-! #### The condition of Hironaka's Corollary 1 -/

/-- The weak transform of an ideal sheaf `J` has a constant positive order along every centre of a
succession of blow-ups [Hir64, Corollary 1 (1)]. -/
example {X : Scheme.{u}} (S : BlowUpSequence X) (J : X.IdealSheafData) :
    S.HasConstantPositiveOrderAlongCenters J ↔ ∀ i : Fin S.length,
      -- a positive integer `c`
      ∃ c : ℕ, 0 < c ∧
        -- that is the order of the weak transform `J_i` at every point of the centre `D_i`
        ∀ y ∈ (S.center i).support, (S.weakTransformSeq J i.castSucc).ord y = c :=
  Iff.rfl

/-- **Hironaka's Corollary 1** [Hir64, Corollary 1, pp. 143–144], the trivialization of a system of
coherent sheaves of ideals. Let `X` be a smooth algebraic `k`-scheme (`AlgScheme k`), `k` of
characteristic zero, and `J_1, …, J_e` (`e ≥ 1`) ideal sheaves on `X` with nonzero stalks. Then
there is a finite succession of monoidal transformations `f_i : X_{i+1} → X_i` with non-singular
irreducible centres `D_i ⊆ X_i` (`BlowUpSequence.HasRegularIrreducibleCenters`) such that
* (1) every weak transform `J_j(i)` of every `J_j` has a constant positive order along `D_i`
  (`BlowUpSequence.HasConstantPositiveOrderAlongCenters`);
* (2) at every point of the end result `X_r` at least one of the weak transforms `J_j(r)` is the
  unit ideal.

Relation to the source.
* **Translation.** The weak transforms are those of Main Theorem II
  (`exists_blowUpSequence_ord_weakTransformSeq_lt`): `S.weakTransformSeq (J j) i` is Hironaka's
  $J_j(i)$. "$\nu(J_j(i)_y)$ is a positive constant for the points $y$ of $D(i)$" is `ord` equal to
  a natural number `c` with `0 < c` at every point of the support of the centre ($\nu$ is
  integer-valued on non-zero ideals), and his $J_j(r)_x = \mathcal{O}_{X(r),x}$ is
  `(S.weakTransformSeq (J j) (Fin.last S.length)).stalkIdeal x = ⊤`, read on the stalk. His
  $e \ge 1$ is `0 < e`.
* **Translation.** `[Smooth (X.left ↘ Spec (.of k))]` is Hironaka's "non-singular": for a scheme of
  finite type over the perfect field `k` the two agree (smoothness gives the regularity of every
  local ring, and a non-singular such scheme is smooth).
* **Interpretation.** Hironaka's "coherent sheaves of non-zero ideals" are read as ideal sheaves
  with nonzero stalks (`hJ`), as in Main Theorem II.
* **Restatement.** The regularity of the local rings of `X` is not a separate hypothesis: it follows
  from smoothness over the perfect field `k`.

Source statement: [Hir64, Corollary 1, pp. 143–144] -/
theorem exists_blowUpSequence_forall_exists_stalkIdeal_weakTransformSeq_eq_top
    {k : Type u} [Field k] [CharZero k] (X : AlgScheme k) [Smooth (X.left ↘ Spec (.of k))]
    {e : ℕ} (he : 0 < e) (J : Fin e → X.left.IdealSheafData)
    (hJ : ∀ j, IsNonzeroEverywhere (J j)) :
    ∃ S : BlowUpSequence X.left,
      -- non-singular irreducible centres
      S.HasRegularIrreducibleCenters ∧
      -- (1)
      (∀ j, S.HasConstantPositiveOrderAlongCenters (J j)) ∧
      -- (2)
      ∀ x : S.last, ∃ j, (S.weakTransformSeq (J j) (Fin.last S.length)).stalkIdeal x = ⊤ :=
  sorry

/-! #### The conditions of Theorem 35 -/

section Clauses35

open HasUnderlyingScheme

/-- A triple `(X, I, E)` is a smooth, equidimensional algebraic `k`-scheme `X` with an ideal sheaf
`I` nonzero at every point and a simple normal crossing divisor family `E` [Kol07, Notation 64]. -/
example {k : Type u} [Field k] (T : Triple k) :
    -- the ambient scheme is smooth of a single relative dimension over `k`
    (∃ n : ℕ, SmoothOfRelativeDimension n (T.X.left ↘ Spec (.of k))) ∧
    -- the ideal sheaf is nonzero at every point
    T.I.IsNonzeroEverywhere ∧
    -- the boundary is a simple normal crossing divisor family
    T.E.IsSnc :=
  ⟨T.smoothOfRelativeDimension, T.isNonzeroEverywhere, T.isSnc⟩

/-- A succession of blow-ups `Π : X_r → X` principalizes the triple `(X, I, E)` when every centre is
smooth and has simple normal crossings with the total transform of the boundary at its stage, the
pull-back of `I` becomes the ideal of a simple normal crossing divisor, and nothing changes away
from the cosupport of `I` and the self-intersections of `E` [Kol07, Theorem 35 (1)–(3)] (Kollár
prints `X ∖ cosupp I` in (3)). -/
example {k : Type u} [Field k] (T : Triple k) (S : BlowUpSequence T.X.left) :
    T.IsPrincipalizedBy S ↔
      -- (1) smooth centres with simple normal crossings with the boundary
      S.HasSmoothSncCenters T.E ∧
      -- (2) `Π^* I` is the ideal sheaf of a simple normal crossing divisor
      (T.I.comap S.composite).IsIdealOfSncDivisor ∧
      -- (3) `Π` is an isomorphism over `X ∖ (cosupp I ∪ Sing E)`
      IsIso (S.composite ∣_ (T.I.support ⊔ T.E.singularLocus).compl) :=
  Triple.isPrincipalizedBy_iff T S

/-- Every centre of the succession is smooth over `k` and has simple normal crossings with the total
transform of the boundary at the stage where it is blown up [Kol07, Theorem 35 (1)]. -/
example {k : Type u} [Field k] {X : AlgScheme k} (S : BlowUpSequence X.left)
    (E : DivisorFamily X.left) :
    S.HasSmoothSncCenters E ↔ ∀ i : Fin S.length,
      -- the `i`-th centre is smooth over `k`
      Smooth ((S.center i).subschemeι ≫ S.stageMap i.castSucc ≫ X.hom) ∧
      -- and has simple normal crossings with the total transform of `E` at stage `i`
      (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i) :=
  Iff.rfl

/-- A blow-up sequence functor commutes with smooth morphisms when pulling an input back along a
smooth morphism pulls its blow-up sequence back too: exactly for smooth surjections, and up to
deleting the blow-ups whose centre becomes empty for any smooth morphism [Kol07, 34.1]. -/
example {k : Type u} [Field k] (B : BlowUpSequenceFunctor (Triple k)) :
    CommutesWithSmoothMorphisms B ↔
      -- along a smooth surjection `h`, `B(Y)` is the pull-back `h^* B(X)`
      (∀ ⦃X Y : Triple k⦄ (h : Y ⟶ X), Smooth (hom h) → Function.Surjective (hom h) →
        B Y = (B X).pullback (hom h)) ∧
      -- along a smooth `h`, `B(Y)` is `h^* B(X)` with the empty blow-ups deleted
      ∀ ⦃X Y : Triple k⦄ (h : Y ⟶ X), Smooth (hom h) →
        B Y = ((B X).pullback (hom h)).eraseEmpty :=
  commutesWithSmoothMorphisms_iff B

/-- A morphism of triples `(Y, I_Y, E_Y) ⟶ (X, I_X, E_X)` is a `k`-morphism of the ambient schemes
along which the ideal sheaf and the boundary of `X` pull back to those of `Y`. -/
example {k : Type u} [Field k] {X Y : Triple k} (h : Y ⟶ X) :
    -- the ideal sheaf pulls back
    Y.I = X.I.comap (hom h) ∧
    -- the boundary pulls back
    Y.E = X.E.comap (hom h) :=
  h.2

/-- A family of blow-up sequence functors on triples commutes with change of fields when, for a
field extension `k → L` (an automorphism of `k` included), the functor over `L` applied to the base
change of a triple is the pull-back of the functor over `k` applied to the triple [Kol07, 34.2]. -/
example (B : ∀ (k : Type u) [Field k] [CharZero k], BlowUpSequenceFunctor (Triple k)) :
    CommutesWithChangeOfFields B ↔
      ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L) (X : Triple k)
        (XL : Triple L) (p : XL.X.left ⟶ X.X.left),
        -- `p` exhibits `XL` as the base change `X ×_{Spec k} Spec L`
        IsPullback p XL.X.hom X.X.hom (Spec.map (CommRingCat.ofHom σ)) ∧
          -- along which the ideal sheaf and the boundary pull back
          XL.I = X.I.comap p ∧ XL.E = X.E.comap p →
        B L XL = (B k X).pullback p :=
  Iff.rfl

/-- A blow-up sequence functor on triples commutes with closed embeddings (with empty boundary)
when, for a closed embedding `j : Y ↪ X`, the functor applied to `X` with the ideal pushed forward
from `Y` is the push-forward of the functor applied to `Y` [Kol07, 34.3]. -/
example {k : Type u} [Field k] (B : BlowUpSequenceFunctor (Triple k)) :
    CommutesWithClosedEmbeddingsOfEmptyBoundary B ↔
      ∀ (T Y : Triple k) (j : Y.X ⟶ T.X) [IsClosedImmersion j.left],
        -- both boundaries are empty
        IsEmpty T.E.ι → IsEmpty Y.E.ι →
        -- the ideal sheaf on `X` is pushed forward from `Y`
        T.I = Y.I.map j.left →
          B T = (B Y).pushforward j.left :=
  Iff.rfl

end Clauses35

/-- **Kollár's functorial principalization** [Kol07, Theorem 35]. There is a family `BP` of blow-up
sequence functors on triples (`BlowUpSequenceFunctor (Triple k)`), one for each field `k` of
characteristic zero, such that
* every value `BP(X, I, E)`, with composite `Π : X_r → X`, is a principalization of the triple
  (`Triple.IsPrincipalizedBy`): (1) every centre is smooth over `k` and has simple normal
  crossings with the total transform of `E` at its stage; (2) `Π^* I` is the ideal sheaf of a simple
  normal crossing divisor; (3) `Π` is an isomorphism over `X ∖ (cosupp I ∪ Sing E)`;
* (4) `BP` commutes with smooth morphisms [Kol07, 34.1] (`CommutesWithSmoothMorphisms`) and with
  change of fields [Kol07, 34.2] (`CommutesWithChangeOfFields`);
* (5) `BP` commutes with closed embeddings when the boundary is empty [Kol07, 34.3]
  (`CommutesWithClosedEmbeddingsOfEmptyBoundary`).

A triple (`Triple`, [Kol07, Notation 64]) is a smooth, equidimensional algebraic `k`-scheme `X` with
an ideal sheaf `I` nonzero at every point and a simple normal crossing divisor family `E`.

Relation to the source.
* **Translation.** `S.pullback h` is Kollár's pull-back $h^* S$ [Kol07, 30.1],
  `(S.pullback h).eraseEmpty` the same with the blow-ups with empty centre deleted [Kol07, 32], and
  `S.pushforward j` the push-forward $j_* S$ along a closed embedding [Kol07, 30.3];
  `T.I.comap S.composite` is $\Pi^* I$, and `T.E.singularLocus` is $\operatorname{Sing} E$, the set
  of points on at least two components of $E$.
* **Correction.** Clause (3) is stated over
  $X \setminus (\operatorname{cosupp} I \cup \operatorname{Sing} E)$ (`Triple.IsPrincipalizedBy`):
  $\Pi$ is an isomorphism away from the cosupport of $I$ and from the points on at least two
  components of $E$. Kollár prints $X \setminus \operatorname{cosupp} I$, but his functor first
  blows up the intersections of the components of $E$ [Kol07, 72], which need not lie in
  $\operatorname{cosupp} I$; the two loci agree when $E = \emptyset$.
* **Correction.** The order reduction $BMO_1$ of [Kol07, Theorem 107] that the proof runs splits a
  marked ideal as $I = M(I) \cdot N(I)$ with the monomial part
  $M(I) = \prod_D \mathcal{I}_D^{\operatorname{ord}_D I}$ taking one exponent per irreducible
  component $D$ of the boundary members
  (`Hironaka.BMO.monomialPart`; the split of [Wlo05, Section 3, Step 2]). Kollár's construction
  [Kol07, 111] takes one exponent per member, the minimum of $\operatorname{ord}_D I$ over the
  member's components; that split does not commute with open immersions, so clause (2) of
  [Kol07, Theorem 107] fails for it: on $\mathbb{A}^2$ with $E^1 = V(x(x-1))$, $E^2 = V(y(y-1))$ and
  $I = (xy)$ both exponents are $0$, and both are $1$ on the open set $x \ne 1$, $y \ne 1$. The
  fine split commutes with smooth pull-back, since orders at generic points are preserved.
* **Gap.** The inputs are the triples $(X, I, E)$ of [Kol07, Notation 64] (`Triple`), under which
  Kollár proves the theorem: their ambient scheme $X$ is smooth and equidimensional, whereas Theorem
  35 as printed does not ask $X$ to be equidimensional. The base change of a triple along a field
  extension is again a triple.
* **Gap.** Kollár's $E$ is an unordered simple normal crossing divisor. Here it is an ordered family
  (`DivisorFamily`), and clause (4) compares values on families with the induced orders; nothing
  relates the values at two orderings of one divisor.

Source statement: [Kol07, Theorem 35] -/
theorem exists_functorial_principalization :
    ∃ BP : ∀ (k : Type u) [Field k] [CharZero k], BlowUpSequenceFunctor (Triple k),
      -- (1)–(3)
      (∀ (k : Type u) [Field k] [CharZero k] (T : Triple k), T.IsPrincipalizedBy (BP k T)) ∧
      -- (4), 34.1
      (∀ (k : Type u) [Field k] [CharZero k], CommutesWithSmoothMorphisms (BP k)) ∧
      -- (4), 34.2
      CommutesWithChangeOfFields BP ∧
      -- (5), 34.3 with `E = ∅`
      (∀ (k : Type u) [Field k] [CharZero k],
        CommutesWithClosedEmbeddingsOfEmptyBoundary (BP k)) :=
  sorry

/-- **Hironaka's Corollary 3** [Hir64, Corollary 3, p. 146], the simplification of an algebraic
boundary. Let `X` be a smooth algebraic `k`-scheme (`AlgScheme k`), `k` of characteristic zero, and
`W` a nowhere dense closed subscheme of `X`, given by its ideal sheaf. Then there is a finite
succession of monoidal transformations `f_i : X_{i+1} → X_i` with non-singular centres `D_i ⊆ X_i`
such that
* (i) the end result `X_r` is non-singular;
* (ii) every centre lies over `W`: `D_i ⊆ f̄_i⁻¹(W)`, where `f̄_i = f_0 ∘ ⋯ ∘ f_{i-1} : X_i → X`;
* (iii) the associated reduced scheme `red(f̄_r⁻¹(W))` of `f̄_r⁻¹(W)` is defined by an invertible
  sheaf of ideals on `X_r` and has only normal crossings.

Hironaka asks nothing of `W` beyond nowhere density; `W` may be empty (the unit ideal sheaf, of
nowhere dense support), for which the empty succession satisfies every clause.

Relation to the source.
* **Translation.** $\bar f_i$ is `S.stageMap i.castSucc` and $\bar f_r$ is `S.composite`. The
  associated reduced scheme $\mathrm{red}(\bar f_r^{-1}(W))$ is the radical
  `(W.comap S.composite).radical` of the inverse image ideal sheaf; "invertible" is `IsInvertible`
  (generated on an affine neighbourhood of every point by a nonzerodivisor, an effective Cartier
  divisor; on the locally Noetherian `X_r` this is the stalkwise condition that every stalk is
  generated by a nonzerodivisor of the local ring, `isInvertible_iff_forall_stalkIdeal_eq_span`),
  and "has only normal crossings" is Hironaka's Definition 2 (`IsSncBoundary`).
* **Translation.** Clause (ii) is read on points: every point of a centre maps into the support of
  `W`; since $D_i$ is non-singular, hence reduced, this is the inclusion
  $D_i \subseteq \bar f_i^{-1}(W)$ of subschemes.
* **Interpretation.** Hironaka's "nowhere dense" for the closed subscheme $W$ of $X$ is read
  topologically, of its support (`IsNowhereDense (W.support : Set X.left)`).
* **Translation.** `[Smooth (X.left ↘ Spec (.of k))]` is Hironaka's "non-singular" for `X`: for a
  scheme of finite type over the perfect field `k` the two agree (smoothness gives the regularity of
  every local ring, and a non-singular such scheme is smooth).
* **Restatement.** The regularity of the local rings of `X` is not a separate hypothesis: it follows
  from smoothness over the perfect field `k`.

Source statement: [Hir64, Corollary 3, p. 146] -/
theorem exists_blowUpSequence_isInvertible_isSncBoundary_radical_comap
    {k : Type u} [Field k] [CharZero k] (X : AlgScheme k) [Smooth (X.left ↘ Spec (.of k))]
    (W : X.left.IdealSheafData) (hW : IsNowhereDense (W.support : Set X.left)) :
    ∃ S : BlowUpSequence X.left,
      -- non-singular centres
      (∀ i : Fin S.length, IsRegular (S.center i).subscheme) ∧
      -- (i)
      IsRegular S.last ∧
      -- (ii)
      (∀ i : Fin S.length, ∀ x ∈ (S.center i).support, S.stageMap i.castSucc x ∈ W.support) ∧
      -- (iii)
      (W.comap S.composite).radical.IsInvertible ∧
      (W.comap S.composite).radical.IsSncBoundary :=
  sorry

/-! ### Resolution -/

/-! #### The conditions of Theorem 36 -/

section Clauses36

open HasUnderlyingScheme

/-- An input of Theorem 36 is an algebraic `k`-scheme that is reduced and equidimensional: its
smooth locus has a single relative dimension, which over a perfect field (in particular in
characteristic zero) means that its irreducible components all have the same dimension. The
components may meet. -/
example {k : Type u} [Field k] (X : ReducedEquidimensionalScheme k) :
    X.obj.left.IsReducedEquidimensional k :=
  X.property

/-- A scheme over `k` is reduced and equidimensional when it is reduced and its smooth locus has a
single relative dimension over `k` [Kol07, Notation 64]. -/
example {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    X.IsReducedEquidimensional k ↔
      -- reduced
      IsReduced X ∧
      -- equidimensional
      ∃ d : ℕ, SmoothOfRelativeDimension d
        ((X ↘ Spec (.of k)).smoothLocus.ι ≫ (X ↘ Spec (.of k))) :=
  Iff.rfl

/-- A succession of blow-ups `Π : X_r → X` is a strong resolution when it is a resolution, changes
nothing over the smooth locus of `X`, and turns the singular locus into a simple normal crossing
divisor [Kol07, (3)]; these are clauses (1)–(3) of Theorem 36. -/
example {k : Type u} [Field k] {X : AlgScheme k} (S : BlowUpSequence X.left) :
    S.IsStrongResolution ↔
      -- (1) a resolution
      S.IsResolution ∧
      -- (2) an isomorphism over the smooth locus `X^{ns}`
      IsIso (S.composite ∣_ (X.left ↘ Spec (.of k)).smoothLocus) ∧
      -- (3) `Π⁻¹(Sing X)` is the support of a simple normal crossing divisor
      IsSncDivisor (S.composite ⁻¹' ((X.left ↘ Spec (.of k)).smoothLocus : Set X.left)ᶜ) :=
  BlowUpSequence.isStrongResolution_iff S

/-- A succession of blow-ups `Π : X_r → X` is a resolution when `X_r` is smooth, `Π` is projective,
and `Π` is birational [Kol07, (2)]. -/
example {k : Type u} [Field k] {X : AlgScheme k} (S : BlowUpSequence X.left) :
    S.IsResolution ↔
      -- `X_r` is smooth over `k`
      Smooth (S.composite ≫ X.hom) ∧
      -- `Π` is projective
      IsProjective S.composite ∧
      -- `Π` is an isomorphism over a dense open subset
      ∃ U : X.left.Opens, Dense (U : Set X.left) ∧ IsIso (S.composite ∣_ U) :=
  BlowUpSequence.isResolution_iff S

/-- A morphism `f : X ⟶ Y` is projective when it is a closed immersion into the projective bundle
`P(E) = Proj_Y (Sym E)` of a quasi-coherent `𝒪_Y`-module `E` of finite type, followed by the
projection `P(E) ⟶ Y` [Sta, Tag 01W8]. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsProjective f ↔ ∃ (E : Y.Modules) (_ : E.IsQuasicoherent)
      (_ : SheafOfModules.IsFiniteType.{u} E) (i : X ⟶ E.projectiveBundle),
      -- a closed immersion into `P(E)`
      IsClosedImmersion i ∧
      -- over `Y`
      i ≫ E.projectiveBundleπ = f :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- A set of points is a simple normal crossing divisor when it is the support of a simple normal
crossing divisor family [Kol07, Definition 24]. -/
example {X : Scheme.{u}} (Z : Set X) :
    IsSncDivisor Z ↔ ∃ F : DivisorFamily X, F.IsSnc ∧ (F.support : Set X) = Z :=
  Iff.rfl

/-- A family of blow-up sequence functors on schemes commutes with change of fields when, for a
field extension `k → L` (an automorphism of `k` included), the functor over `L` applied to the base
change of a scheme is the pull-back of the functor over `k` applied to the scheme [Kol07, 34.2]. -/
example (B : ∀ (k : Type u) [Field k] [CharZero k],
      BlowUpSequenceFunctor (ReducedEquidimensionalScheme k)) :
    CommutesWithChangeOfFields B ↔
      ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L)
        (X : ReducedEquidimensionalScheme k) (XL : ReducedEquidimensionalScheme L)
        (p : XL.obj.left ⟶ X.obj.left),
        -- `p` exhibits `XL` as the base change `X ×_{Spec k} Spec L`
        IsPullback p XL.obj.hom X.obj.hom (Spec.map (CommRingCat.ofHom σ)) →
        B L XL = (B k X).pullback p :=
  Iff.rfl

end Clauses36

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
      CommutesWithChangeOfFields BR :=
  sorry

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
    ∃ S : Scheme.BlowUpSequence X.left, S.IsStrongResolution :=
  sorry

/-- **Hironaka's Main Theorem I** [Hir64, Main Theorem I, p. 132]. Let `X` be a reduced and
irreducible (`IsIntegral`) algebraic `k`-scheme (`AlgScheme k`), `k` of characteristic zero. Then
there is a closed subscheme `D` of `X`, given by its ideal sheaf, whose set of points is exactly the
singular locus of `X` (the points whose local ring is not regular), such that the monoidal
transformation `D.blowUp` of `X` with centre `D` is non-singular. If `X` is non-singular, `D` is the
empty subscheme (`D = ⊤`) and `D.blowUpπ` is an isomorphism.

Relation to the source.
* **Translation.** `(D.support : Set X.left) = X.left.singularLocus` is Hironaka's (i), "the set
  of points of $D$ is exactly the singular locus of $X$"; `IsRegular D.blowUp` is his (ii), the
  non-singularity of the result of the monoidal transformation of $X$ with centre $D$.
* **Interpretation.** Hironaka's "say reduced and irreducible" is read as a hypothesis
  (`IsIntegral`). His Introduction describes Main Theorem I as "the resolution of singularities of
  an arbitary [sic] reduced algebraic **B**-scheme X" [Hir64, p. 112], irreducible or not;
  reducible `X` is not covered here.
* **Out of scope.** Hironaka's strong form [Hir64, pp. 132–133], that `D.blowUpπ` is the composite
  of a finite succession of monoidal transformations whose centres $D_i$ are non-singular (a),
  contain no simple point of $X_i$ (b), and along which $X_i$ is normally flat (c), and Main Theorem
  I*: both rest on the Hilbert–Samuel function and normal flatness, whereas the library follows the
  route through the order of an ideal and hypersurfaces of maximal contact, as in Włodarczyk's and
  Kollár's proofs. The statement here is Main Theorem I as printed.

Source statement: [Hir64, Main Theorem I, p. 132] -/
theorem exists_support_eq_singularLocus_isRegular_blowUp {k : Type u} [Field k]
    [CharZero k] (X : AlgScheme k) [IsIntegral X.left] :
    ∃ D : X.left.IdealSheafData,
      (D.support : Set X.left) = X.left.singularLocus ∧ IsRegular D.blowUp :=
  sorry

/-- **Hironaka's Main Theorem I, weak form** [Hir64, p. 132, the paragraph after Main Theorem I].
Let `X` be a reduced and irreducible (`IsIntegral`) algebraic `k`-scheme (`AlgScheme k`), `k` of
characteristic zero. Then there is a closed subscheme `D` of `X` whose open complement `U` is dense
in `X`, such that the monoidal transformation `f : D.blowUp → X` with centre `D` restricts to an
isomorphism `f⁻¹(U) → U` and `D.blowUp` is non-singular.

Density of `U` excludes `D = X`.

Relation to the source.
* **Translation.** `D.support.compl` is the open complement $U = X \setminus D$, and
  `IsIso (D.blowUpπ ∣_ U)` says that the restriction $f^{-1}(U) \to U$ of the projection
  `D.blowUpπ` over $U$ is an isomorphism.
* **Interpretation.** As in Main Theorem I, Hironaka's "say reduced and irreducible" is read as a
  hypothesis (`IsIntegral`), although his Introduction [Hir64, p. 112] describes Main Theorem I for
  every reduced $X$.

Source statement: [Hir64, the paragraph after Main Theorem I, p. 132] -/
theorem exists_dense_isIso_restrict_isRegular_blowUp {k : Type u} [Field k] [CharZero k]
    (X : AlgScheme k) [IsIntegral X.left] :
    ∃ D : X.left.IdealSheafData,
      -- `U = X ∖ D` is dense in `X`
      Dense (D.support.compl : Set X.left) ∧
      -- `f⁻¹(U) → U` is an isomorphism
      IsIso (D.blowUpπ ∣_ D.support.compl) ∧
      -- `D.blowUp` is non-singular
      IsRegular D.blowUp :=
  sorry

/-! ### Embedded resolution -/

/-! #### The conditions of Włodarczyk's theorem -/

section ClausesWlo

open HasUnderlyingScheme

/-- An embedded pair `(X, Y)` is a reduced closed subscheme `Y` of a smooth, equidimensional
algebraic `k`-scheme `X`. -/
example {k : Type u} [Field k] (P : EmbeddedPair k) :
    -- the ambient scheme is smooth of a single relative dimension over `k`
    (∃ n : ℕ, SmoothOfRelativeDimension n (P.X.left ↘ Spec (.of k))) ∧
    -- the subscheme is reduced
    IsReduced P.Y.subscheme :=
  ⟨P.smoothOfRelativeDimension, P.isReduced⟩

/-- A morphism of embedded pairs `(X', Y') ⟶ (X, Y)` is a `k`-morphism of the ambient schemes along
which the ideal sheaf of `Y` pulls back to that of `Y'`. -/
example {k : Type u} [Field k] {P Q : EmbeddedPair k} (h : Q ⟶ P) :
    Q.Y = P.Y.comap (hom h) :=
  h.2

/-- A succession of blow-ups `σ : X_r → X` desingularizes the embedded pair `(X, Y)` when, with
exceptional divisors `E_i` (the total transforms of the empty divisor family) and strict transforms
`Y_i` of `Y`, its centres `C_i` are smooth with simple normal crossings with the `E_i`, the `E_i`
have simple normal crossings, no centre meets `Y_i` over a point where `Y` is smooth, the last
strict transform is smooth with simple normal crossings with `E_r`, and `σ^* I_Y` factors through
it [Wlo05, Theorem 1.0.2 (a)–(c), (e)]. -/
example {k : Type u} [Field k] (P : EmbeddedPair k) (S : BlowUpSequence P.X.left) :
    P.IsDesingularizedBy S ↔
      -- smooth centres `C_i` with simple normal crossings with the exceptional divisors `E_i`
      S.HasSmoothSncCenters (DivisorFamily.empty _) ∧
      -- (a) every `E_i`, the last included, is a simple normal crossing family
      (∀ i, (S.totalTransformSeq (DivisorFamily.empty _) i).IsSnc) ∧
      -- (b) no point of `C_i ∩ Y_i` lies over a point at which `Y` is smooth over `k`
      (∀ i : Fin S.length, ∀ x ∈ (S.center i).support,
        x ∈ (S.strictTransformSeq P.Y i.castSucc).support →
        S.stageMap i.castSucc x ∉
          P.Y.subschemeι '' ((P.Y.subschemeι ≫ (P.X.left ↘ Spec (.of k))).smoothLocus : Set _)) ∧
      -- (c) the strict transform `Ỹ = Y_r` is smooth over `k`
      Smooth ((S.strictTransformSeq P.Y (Fin.last _)).subschemeι ≫ S.composite ≫ P.X.hom) ∧
      -- (c) and has simple normal crossings with `E_r`
      (S.totalTransformSeq (DivisorFamily.empty _) (Fin.last _)).HasSncWith
        (S.strictTransformSeq P.Y (Fin.last _)) ∧
      -- (e) `σ^* I_Y = I_Ỹ · J`, `J` the ideal of a simple normal crossing divisor inside `E_r`
      ∃ J : (S.stage (Fin.last _)).IdealSheafData, J.IsIdealOfSncDivisor ∧
        J.support ≤ (S.totalTransformSeq (DivisorFamily.empty _) (Fin.last _)).support ∧
        P.Y.comap S.composite = S.strictTransformSeq P.Y (Fin.last _) * J :=
  EmbeddedPair.isDesingularizedBy_iff P S

/-- A blow-up sequence functor on embedded pairs commutes with smooth morphisms meeting the
components when pulling a pair back along a smooth morphism pulls its blow-up sequence back too:
exactly for smooth surjections, and up to deleting the blow-ups whose centre becomes empty when the
image of the morphism meets every irreducible component of the embedded subscheme
[Wlo05, Theorem 1.0.2 (d)]. -/
example {k : Type u} [Field k] (B : BlowUpSequenceFunctor (EmbeddedPair k)) :
    CommutesWithSmoothMorphismsMeetingComponents B ↔
      -- along a smooth surjection `h`, `B(X', Y')` is the pull-back `h^* B(X, Y)`
      (∀ ⦃P Q : EmbeddedPair k⦄ (h : Q ⟶ P), Smooth (hom h) → Function.Surjective (hom h) →
        B Q = (B P).pullback (hom h)) ∧
      -- along a smooth `h` whose image meets every irreducible component of `Y`,
      -- `B(X', Y')` is `h^* B(X, Y)` with the empty blow-ups deleted
      ∀ ⦃P Q : EmbeddedPair k⦄ (h : Q ⟶ P), Smooth (hom h) →
        (∀ Z ∈ irreducibleComponents P.Y.subscheme,
          (Set.range (hom h) ∩ P.Y.subschemeι '' Z).Nonempty) →
        B Q = ((B P).pullback (hom h)).eraseEmpty :=
  commutesWithSmoothMorphismsMeetingComponents_iff B

end ClausesWlo

/-- **Włodarczyk's embedded desingularization with smooth centres** [Wlo05, Theorem 1.0.2]. There
is a family `ED` of blow-up sequence functors on embedded pairs
(`BlowUpSequenceFunctor (EmbeddedPair k)`), one for each field `k` of characteristic zero, such
that
* every value `S = ED(X, Y)`, with composite `σ : X_r → X`, exceptional divisors `E_i` (the total
  transforms of the empty divisor family) and strict transforms `Y_i` of `Y`, is an embedded
  desingularization of the pair (`EmbeddedPair.IsDesingularizedBy`): every centre `C_i` is smooth
  over `k`; (a) every `E_i`, the last included, is a simple normal crossing family, and `C_i` has
  simple normal crossings with `E_i`; (b) no point of `C_i ∩ Y_i` lies over a point of `Reg(Y)`,
  the image in `X` of the smooth locus of `Y → Spec k` (the points where `Y`, not `Y_i`, is
  smooth); (c) `Ỹ = Y_r` is smooth over `k` and has simple normal crossings with `E_r`; (e)
  `σ^*(I_Y) = I_Ỹ · J` for the ideal sheaf `J` of a simple normal crossing divisor supported in
  `E_r`;
* (d) for a morphism of embedded pairs `h : (X', Y') ⟶ (X, Y)` whose underlying morphism is
  smooth, `ED(X', Y')` is the pull-back `h^* S` if `h` is surjective, and `h^* S` with the empty
  blow-ups deleted if the image of `h` meets every irreducible component of `Y`
  (`CommutesWithSmoothMorphismsMeetingComponents`).

An embedded pair (`EmbeddedPair`) is a reduced closed subscheme `Y` of a smooth, equidimensional
algebraic `k`-scheme `X` (smooth of one relative dimension over `k`); a morphism
`(X', Y') ⟶ (X, Y)` is a `k`-morphism `h : X' → X` along which the ideal sheaf of `Y` pulls back to
that of `Y'`. If `Y = X` (the ideal sheaf `⊥`), (b) forces every centre to be empty. If `Y` is
empty or smooth, the clauses on `S` alone hold for the empty succession.

Relation to the source.
* **Translation.** `S.totalTransformSeq (DivisorFamily.empty _) i` is Włodarczyk's exceptional
  divisor $E_i$, `S.strictTransformSeq P.Y i` his strict transform $Y_i$, and the image in `X` of
  the smooth locus of `Y → Spec k` is his $\operatorname{Reg}(Y)$.
* **Interpretation.** Włodarczyk's "subvariety $Y$ of a smooth variety $X$" is read as a reduced
  closed subscheme `Y` of a smooth, equidimensional algebraic `k`-scheme `X` (`EmbeddedPair`). His
  Bravo–Villamayor strengthening, the source of clause (e), is stated for "a reduced closed
  subscheme" [Wlo05, Theorem 4.7.1].
* **Gap.** In clause (e), $\sigma^*(I_Y) = I_{\tilde Y} I_{\tilde E}$, Włodarczyk's divisor
  $\tilde E$ is "a natural combination of the irreducible components of the divisor $E_r$"; here `J`
  is only asked to be the ideal sheaf of a simple normal crossing divisor supported in $E_r$.
* **Gap.** In clause (d) the deletion form, in which `ED(X', Y')` is the pull-back of `ED(X, Y)`
  with the empty blow-ups deleted, is asserted only when the image of `h` meets every component of
  `Y`, whereas Włodarczyk's (d), read through his Definition 2.1.5 (extensions by isomorphisms) and
  Proposition 2.4.2, asserts it for every smooth `h`. The construction handles the components of `Y`
  in rounds whose boundary data depend on all of them, and over an open subset missing a component
  the runs fall out of step: for `Y` the disjoint union of a smooth surface and the three coordinate
  axes through a point off it, in a smooth threefold, the pull-back of `ED(X, Y)` to the complement
  of the surface has three non-empty centres that the run on that complement lacks.
* **Gap.** The parts of Włodarczyk's (d) on embeddings of ambient varieties and on equivariance
  under group actions have no counterpart; in particular, although the family `ED` has one functor
  for each field, no clause relates the functors of different fields, as Kollár's change of fields
  [Kol07, 34.2] (`CommutesWithChangeOfFields`) does. The functor built here is not Włodarczyk's
  single invariant-driven run, and functoriality for closed embeddings is, in Kollár's words, "quite
  delicate" [Kol07, 34 and Claim 71.2]: he proves it only for an empty boundary, whereas the later
  rounds here run with the exceptional divisors of the earlier ones as boundary.

Source statement: [Wlo05, Theorem 1.0.2] -/
theorem exists_functorial_embeddedDesingularization :
    ∃ ED : ∀ (k : Type u) [Field k] [CharZero k], BlowUpSequenceFunctor (EmbeddedPair k),
      (∀ (k : Type u) [Field k] [CharZero k] (P : EmbeddedPair k),
        P.IsDesingularizedBy (ED k P)) ∧
      ∀ (k : Type u) [Field k] [CharZero k],
        CommutesWithSmoothMorphismsMeetingComponents (ED k) :=
  sorry

end AlgebraicGeometry
