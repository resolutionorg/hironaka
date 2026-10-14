/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.BR
public import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Hironaka.Resolution.Algebraic.Hir64.EraseEmptyCenters
import Hironaka.Resolution.Algebraic.Hir64.SingleCenter
import Hironaka.Resolution.Algebraic.Hir64.SingleCenterTools
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AdmissiblePairs
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36IsoSnc
import Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36Assembly
import Hironaka.Scheme.BlowUpSequence.CompositeBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Scheme.FiniteType
public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.ReducedEquidimensional
public import Hironaka.Scheme.Resolution.Defs
import Hironaka.Scheme.Resolution.Basic

/-!
# Hironaka's Main Theorem I and its weak form

Hironaka's Main Theorem I [Hir64, Main Theorem I, p. 132]: for `X` a reduced irreducible algebraic
`k`-scheme, `k` of characteristic zero, there is a closed subscheme `D` of `X` whose set of points
is exactly the singular locus and whose monoidal transformation (the blow-up of `X` in `D`) is
non-singular. It is derived from Kollár's functorial resolution [Kol07, Theorem 36]: the sequence
`BR X` of the resolution functor (`Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`) is a finite
succession of blow-ups of `X` with smooth last stage (clause (1)) whose centres lie over `Sing X` (a
property of the construction, stronger than clause (2), an isomorphism over the smooth locus, proved
below). The enlargement of the centre (`exists_center_support_eq_singularLocus`,
`Hironaka.Resolution.Algebraic.Hir64.SingleCenter`; Hironaka's remark [Hir64, pp. 132–133] that a
finite succession of monoidal transformations is one monoidal transformation with a suitably chosen
centre) then produces ONE centre `D` with `|D| = Sing X` and `D.blowUp` non-singular.

**The centres lie over the singular locus** (`stageMap_mem_singularLocus_of_mem_center_BR`; the
argument of [Kol07, 4.2] and of the proof of [Kol07, Theorem 27]: a functorial resolution is an
isomorphism over the smooth points, read through the clauses). Let `z` be a point of the centre
`Z_i` of `BR X` and suppose `x := Π_i z` is a smooth point. Take a member `U` of the finite affine
cover of `X` through `x` (the cover of [Kol07, Proposition 37, proof]): `U` is integral and
affine, an algebraic `k`-scheme through `U → X → Spec k`, so a class member
(`isReducedEquidimensional_of_isIntegral`). Clause (4a)
(`BR_pullback_smooth_of_class`) for the open immersion `U → X` gives
`BR U = ((BR X).pullback (U → X)).eraseEmpty`, and on the integral affine `U` the resolution is
the embedding-free affine resolution `BR_affine' k U` with its empty blow-ups deleted
(`BR_eq_BR_affine'_of_integral`), that is, the restriction to `U` of a truncated run of `BP` on an
admissible embedding `emb : U → A` (`exists_admissibleEmbedding`). The point `z` transports along
the flat pullback (`exists_restrictedCenterHasPointOver_pullback_iff`), across the deletions of
empty blow-ups (`exists_restrictedCenterHasPointOver_bot_eraseEmpty_iff`) and along the closed
immersion (`restrictedCenterHasPointOver_iff_of_isClosedImmersion`) to a centre of the `BP` run
with a point over `emb x`, `x` a smooth point of `U` (`Scheme.Hom.preimage_smoothLocus_eq`) —
against `not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36IsoSnc`): no centre of the
principalization sequence of `I_X` has a point over a smooth point of `X`.

**The single-blow-up form** (`resolution_eq_single_blowUp`): `Π : X_r → X` is one blow-up
`K.blowUp` over `X` with `|K| = ⋃ Π_i(|Z_i|) ⊆ Sing X`
(`AlgebraicGeometry.exists_blowUp_composite_iso`: the composite of a sequence of blow-ups is a
single blow-up, the composition of blow-ups [Sta, Tag 080B] iterated).

**The theorem** (`exists_support_eq_singularLocus_isRegular_blowUp`):
`exists_center_support_eq_singularLocus` at `S := BR X`, with clause (1)
(`BR_smooth_last_of_class`) and the centres over `Sing X` as its two hypotheses. The
theorem is `AlgebraicGeometry.exists_support_eq_singularLocus_isRegular_blowUp`, below.

**The weak form** (`AlgebraicGeometry.exists_dense_isIso_restrict_isRegular_blowUp`, at the
end of the file) is Hironaka's weakening of the first condition [Hir64, p. 132]: the blow-up is an
isomorphism over the complement of its centre (`blowUp.isIso_π_restrict_compl_support`), and the
complement of `Sing X` is a nonempty open of the irreducible `X`, hence dense, since the local ring
at the generic point is a field (`isRegularAt_genericPoint_of_isIntegral`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Hironaka.Sequence
open AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section CentersOverSing

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
  [IsReduced X] [IrreducibleSpace X]

/-- The local step: no centre of `BR X` has a point over a smooth point `x = f w` lying in an
affine open `U` of `X` (the argument of [Kol07, 4.2] and of the proof of [Kol07, Theorem 27]).
Through `BR U = ((BR X).pullback f).eraseEmpty` (clause (4a) for the open immersion `f`),
`BR U = (BR_affine' k U).eraseEmpty` on the integral affine `U`, the transports of the centre
point, and `not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus` on an admissible embedding of
`U`. -/
theorem not_exists_restrictedCenterHasPointOver_BR_of_isOpenImmersion {U : Scheme.{u}}
    [IsAffine U] (f : U ⟶ X) [IsOpenImmersion f] {w : U} {x : X} (hw : f w = x)
    (hx : x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus) :
    ¬ ∃ i, RestrictedCenterHasPointOver ((BRFunctor k).seq X) ⊥ i x := by
  classical
  subst hw
  have hint : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hX : X.IsReducedEquidimensional k := isReducedEquidimensional_of_isIntegral X
  -- `U` as an algebraic `k`-scheme through `f`
  let _ : U.Over (Spec (CommRingCat.of k)) := ⟨f ≫ (X ↘ Spec (CommRingCat.of k))⟩
  have _ : f.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have : Nonempty U := ⟨w⟩
  have hUint : IsIntegral U := isIntegral_of_isOpenImmersion f
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ (X ↘ Spec (CommRingCat.of k))))
  have : IsSeparated (U ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (IsSeparated (f ≫ (X ↘ Spec (CommRingCat.of k))))
  have : QuasiCompact (U ↘ Spec (CommRingCat.of k)) := inferInstance
  have hUcls : U.IsReducedEquidimensional k := isReducedEquidimensional_of_isIntegral U
  -- clause (4a) along the open immersion, and `BR U` as the affine resolution of the integral `U`
  have h4a : (BRFunctor k).seq U = (((BRFunctor k).seq X).pullback f).eraseEmpty :=
    (BR_pullback_smooth_of_class X hX U hUcls f).2
  have hpin : BR k U = (BR_affine' k U).eraseEmpty := BR_eq_BR_affine'_of_integral U
  have hex := exists_admissibleEmbedding (k := k) U
  obtain ⟨hCI, hIsOver, -, hE, hI⟩ := hex.choose_spec.choose_spec
  have hw' : w ∈ (U ↘ Spec (CommRingCat.of k)).smoothLocus := by
    change w ∈ (f ≫ (X ↘ Spec (CommRingCat.of k))).smoothLocus
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact hx
  -- transport the centre point down to the `BP` run
  rintro ⟨i, hi⟩
  have h1 : ∃ i, RestrictedCenterHasPointOver (((BRFunctor k).seq X).pullback f) ⊥ i w := by
    have key := exists_restrictedCenterHasPointOver_pullback_iff ((BRFunctor k).seq X) f ⊥ w
    rw [comap_bot] at key
    exact key.2 ⟨i, hi⟩
  have h2 : ∃ i,
      RestrictedCenterHasPointOver (BR_affine hex.choose hex.choose_spec.choose) ⊥ i w := by
    have := (exists_restrictedCenterHasPointOver_bot_eraseEmpty_iff _ w).2 h1
    rw [← h4a] at this
    change ∃ i, RestrictedCenterHasPointOver (BR k U) ⊥ i w at this
    rw [hpin, exists_restrictedCenterHasPointOver_bot_eraseEmpty_iff,
      BR_affine'_of_pos k U hex] at this
    exact this
  obtain ⟨i', hi'⟩ := h2
  rw [restrictedCenterHasPointOver_bot_iff] at hi'
  obtain ⟨p, hZ, hp⟩ := hi'
  have hres := (restrictedCenterHasPointOver_iff_of_isClosedImmersion
    ((BP hex.choose).take (firstCenterIndex (BP hex.choose) hex.choose.I)) hex.choose_spec.choose
    (Fin.cast (length_pullback _ _) i') w).1 ⟨p, hZ, hp⟩
  rw [hI] at hres
  exact not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus hex.choose hex.choose_spec.choose
    hE hI hw' _ hres

/-- No centre of `BR X` has a point over a smooth point of `X` — clause (2) of [Kol07, Theorem 36]
read as "no centre over the smooth locus": the local step on the member of the finite affine cover
through the point. -/
theorem not_exists_restrictedCenterHasPointOver_BR_of_mem_smoothLocus {x : X}
    (hx : x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus) :
    ¬ ∃ i, RestrictedCenterHasPointOver ((BRFunctor k).seq X) ⊥ i x := by
  have hc : CompactSpace X := compactSpace_of_quasiCompact_over k X
  obtain ⟨w, hw⟩ := (finiteAffineCover X).covers x
  exact not_exists_restrictedCenterHasPointOver_BR_of_isOpenImmersion X
    ((finiteAffineCover X).f ((finiteAffineCover X).idx x)) hw hx

/-- Every point of every centre of `BR X` lies over the singular locus of `X`, the complement of
the smooth locus (`Scheme.singularLocus_eq_compl_smoothLocus`). -/
theorem stageMap_mem_singularLocus_of_mem_center_BR
    (i : Fin ((BRFunctor k).seq X).length) (z : ((BRFunctor k).seq X).stage i.castSucc)
    (hz : z ∈ (((BRFunctor k).seq X).center i).support) :
    ((BRFunctor k).seq X).stageMap i.castSucc z ∈ X.singularLocus := by
  rw [Scheme.singularLocus_eq_compl_smoothLocus (X ↘ Spec (CommRingCat.of k))]
  intro hx
  exact not_exists_restrictedCenterHasPointOver_BR_of_mem_smoothLocus X hx
    ⟨i, (restrictedCenterHasPointOver_bot_iff _ i _).2 ⟨z, hz, rfl⟩⟩

/-- The single-blow-up form: the resolution `Π : X_r → X` of the resolution functor is one blow-up
of `X` in a centre whose support lies in `Sing X` (`AlgebraicGeometry.exists_blowUp_composite_iso`:
the support of the centre is the union of the images of the centres of the sequence). -/
theorem resolution_eq_single_blowUp :
    ∃ K : X.IdealSheafData, (K.support : Set X) ⊆ X.singularLocus ∧
      ∃ e : ((BRFunctor k).seq X).last ≅ K.blowUp,
        e.hom ≫ K.blowUpπ = ((BRFunctor k).seq X).composite := by
  have : IsNoetherian X := (X ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  obtain ⟨K, hK, e, he, -⟩ := exists_blowUp_composite_iso ((BRFunctor k).seq X)
  refine ⟨K, ?_, e, he⟩
  rw [hK]
  refine Set.iUnion_subset fun i => ?_
  rintro _ ⟨z, hz, rfl⟩
  exact stageMap_mem_singularLocus_of_mem_center_BR X i z hz

end CentersOverSing

end Hironaka.Resolution

end

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme

namespace AlgebraicGeometry

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
      (D.support : Set X.left) = X.left.singularLocus ∧ IsRegular D.blowUp := by
  have hX : X.left.IsReducedEquidimensional k :=
    Hironaka.Resolution.isReducedEquidimensional_of_isIntegral X.left
  exact Hironaka.Resolution.exists_center_support_eq_singularLocus X.left
    ((Hironaka.Resolution.BRFunctor k).seq X.left)
    (Hironaka.Resolution.BR_smooth_last_of_class X.left hX)
    (Hironaka.Resolution.stageMap_mem_singularLocus_of_mem_center_BR X.left)

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
      IsRegular D.blowUp := by
  obtain ⟨D, hsupp, hreg⟩ := exists_support_eq_singularLocus_isRegular_blowUp X
  refine ⟨D, D.support.compl.isOpen.dense ⟨genericPoint X.left, ?_⟩,
    blowUp.isIso_π_restrict_compl_support D, hreg⟩
  change genericPoint X.left ∉ (D.support : Set X.left)
  rw [hsupp]
  exact fun h => h Hironaka.Resolution.isRegularAt_genericPoint_of_isIntegral

end AlgebraicGeometry
