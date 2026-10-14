/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.SmoothCharts
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.BR
import Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SigmaCharts
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functoriality of the affine resolution under smooth morphisms of a given relative dimension

Clause (4) of [Kol07, Theorem 36], commutation with smooth morphisms [Kol07, 34.1], for the
affine resolution `BRAffine` (`Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`) of affine reduced
equidimensional schemes (`IsReducedEquidimensional`): for a smooth `h : Y ⟶ X` of relative
dimension `d` between such schemes, with admissible pairs of `X` and of `Y` given,
`BRAffine k Y = ((BRAffine k X).pullback h).eraseEmpty`. The relative dimension and the admissible
pairs are inputs here; they are supplied by
`Hironaka.Resolution.Algebraic.Kol07.Thm36.RelativeDimensionConstancy` and
`Hironaka.Resolution.Algebraic.Kol07.Thm36.AdmissiblePairs` when the clause is derived for the
resolution functor (`Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent`).

## The argument

Kollár reduces (34.1) for `BR` to (34.1) for the principalization sequence through the charts of
[Kol07, Lemma 41] and the locality of (34.1) [Kol07, Theorem 36, proof]. Fix admissible pairs
`(TX, embX)` of `X` and `(TY, embY)` of `Y` and finitely many charts `cᵢ : Chart h embX embY d`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.SmoothCharts`) whose opens `Wᵢ` cover `Y`. Let `Z := ∐
Wᵢ`, an affine reduced equidimensional scheme (a disjoint union of open subschemes of the member
`Y`, `IsReducedEquidimensional.sigma`), over `k` through `e := Sigma.desc eᵢ : Z ⟶ Y`, a surjective
flat (étale) morphism.

* **Over `Y`.** The squares of the charts over `AY` glue (`admissibleEmbedding_sigma`) to an
  admissible pair of `Z` in the triple `∐ D(Gᵢ)` over `TY`, with `Sigma.desc (D(Gᵢ)).ι` smooth of
  relative dimension `0` and `TY.IsPullbackOf`; `BRAffine_eq_eraseEmpty_pullback_of_admissible`
  (`Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback`) gives
  `BRAffine k Z = ((BRAffine k Y).pullback e).eraseEmpty`, and since `e` is flat and surjective the
  deletion of empty blow-ups is trivial (`eraseEmpty_pullback_of_flat_surjective`,
  `eraseEmpty_BRAffine`): `BRAffine k Z = (BRAffine k Y).pullback e`.
* **Over `X`.** The squares over `AX` glue to an admissible pair of `Z` in the triple `∐ Bᵢ` over
  `TX`, with `Sigma.desc qᵢ` smooth of relative dimension `d`; the same lemma along `e ≫ h` gives
  `BRAffine k Z = (((BRAffine k X).pullback h).pullback e).eraseEmpty`, which by the same flat
  surjective `e` is `((BRAffine k X).pullback h).eraseEmpty.pullback e`.
* **Descent.** Both sides of the identity pull back to the same sequence on `Z`, hence agree on each
  `Wᵢ`; a blow-up sequence is determined by its pullbacks to an open cover
  (`eq_of_pullback_of_covers`).

`BRAffine_eq_eraseEmpty_pullback_of_smooth` supplies the charts: `exists_chart_mem` at every point
of `Y` and a finite subcover (`Y` is quasi-compact over `k`); the empty `Y` is the degenerate case
`nil = nil` (`eraseEmpty_eq_nil_of_isEmpty`).
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Scheme Hironaka
  BlowUpSequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- Commutation of `BRAffine` with a smooth `h` of relative dimension `d`, from a finite family of
charts covering `Y` [Kol07, Theorem 36, proof; 34.1]: `Z := ∐ (c i).W` carries two admissible pairs
(`admissibleEmbedding_sigma` over `Y` and over `X`), `BRAffine_eq_eraseEmpty_pullback_of_admissible`
computes `BRAffine Z` from both, the surjective `Sigma.desc e` turns the deletion of empty blow-ups
into an equality on the nose, and `eq_of_pullback_of_covers` descends to `Y`. -/
theorem BRAffine_eq_eraseEmpty_pullback_of_charts {ι : Type u} [Finite ι] [Nonempty ι]
    (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) (hY : Y.IsReducedEquidimensional k)
    (h : Y ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] [Smooth h] (d : ℕ)
    (TX : Triple k) (embX : X ⟶ TX.X.left) (hadmX : AdmissibleEmbedding k X TX embX)
    (TY : Triple k) (embY : Y ⟶ TY.X.left) (hadmY : AdmissibleEmbedding k Y TY embY)
    (c : ι → Chart h embX embY d) (hcov : ∀ y, ∃ i w, (c i).e w = y) :
    BRAffine k Y = ((BRAffine k X).pullback h).eraseEmpty := by
  have hclX : IsClosedImmersion embX := hadmX.1
  have hclY : IsClosedImmersion embY := hadmY.1
  have hAY : IsAffine TY.X.left := hadmY.2.2.1
  -- the coproduct of the charts over `k`
  let _ : (∐ fun i => (c i).W).Over (Spec (CommRingCat.of k)) :=
    ⟨Sigma.desc (fun i => (c i).e) ≫ (Y ↘ Spec (CommRingCat.of k))⟩
  have hoverE : HomIsOver (Sigma.desc fun i => (c i).e) (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have hdesc : (Sigma.desc fun i => (c i).e ≫ h) = Sigma.desc (fun i => (c i).e) ≫ h :=
    Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
  have hoverEh : HomIsOver (Sigma.desc fun i => (c i).e ≫ h) (Spec (CommRingCat.of k)) := by
    constructor
    rw [hdesc, Category.assoc, HomIsOver.comp_over (f := h) (S := Spec (CommRingCat.of k))]
    rfl
  -- the coproduct is an affine class member
  have hZlfT : LocallyOfFiniteType ((∐ fun i => (c i).W) ↘ Spec (CommRingCat.of k)) := by
    change LocallyOfFiniteType (Sigma.desc (fun i => (c i).e) ≫ (Y ↘ Spec (CommRingCat.of k)))
    have := locallyOfFiniteType_sigmaDesc fun i => (c i).e
    infer_instance
  have hZ : (∐ fun i => (c i).W).IsReducedEquidimensional k :=
    .sigma _ (fun i => (c i).e) (fun i => by
      change Sigma.ι _ i ≫ Sigma.desc (fun i => (c i).e) ≫ (Y ↘ Spec (CommRingCat.of k)) = _
      rw [← Category.assoc, Sigma.ι_comp_desc]) hY
  have hZqc : QuasiCompact ((∐ fun i => (c i).W) ↘ Spec (CommRingCat.of k)) := by
    have := isAffineHom_of_isAffine ((∐ fun i => (c i).W) ↘ Spec (CommRingCat.of k))
    infer_instance
  have hsurj : Function.Surjective (Sigma.desc fun i => (c i).e) := surjective_sigmaDesc _ hcov
  have hflat : Flat (Sigma.desc fun i => (c i).e) := flat_sigmaDesc _
  -- Y-side: the pair `(sigmaTriple TY (D(Gᵢ)).ι 0, Sigma.map jY)`
  have hBaff : ∀ i, IsAffine (TY.X.left.basicOpen (c i).G : Scheme.{u}) := fun i =>
    (isAffineOpen_top TY.X.left).basicOpen _
  have hadmZY := admissibleEmbedding_sigma TY (fun i => (TY.X.left.basicOpen (c i).G).ι) 0 embY
    hadmY (fun i => (c i).jY) (fun i => (c i).e) (fun i => (c i).sqY)
  have hsmι : ∀ i, Smooth (TY.X.left.basicOpen (c i).G).ι := fun i =>
    SmoothOfRelativeDimension.smooth 0 _
  have hsmY : @Smooth (sigmaTriple TY (fun i => (TY.X.left.basicOpen (c i).G).ι) 0).X.left TY.X.left
      (Sigma.desc fun i => (TY.X.left.basicOpen (c i).G).ι) :=
    smooth_sigmaDesc fun i => (TY.X.left.basicOpen (c i).G).ι
  have hbY := BRAffine_eq_eraseEmpty_pullback_of_admissible Y (∐ fun i => (c i).W) hY hZ TY
    (sigmaTriple TY (fun i => (TY.X.left.basicOpen (c i).G).ι) 0) embY
    (Limits.Sigma.map fun i => (c i).jY)
    hadmY hadmZY (Sigma.desc fun i => (TY.X.left.basicOpen (c i).G).ι)
    (sigmaTriple_isPullbackOf TY _ 0) (Sigma.desc fun i => (c i).e)
    (sigmaMap_comp_desc _ _ _ embY fun i => (c i).sqY.w)
  -- X-side: the pair `(sigmaTriple TX (c i).q d, Sigma.map j)`
  have hadmZX := admissibleEmbedding_sigma TX (fun i => (c i).q) d embX hadmX
    (fun i => (c i).j) (fun i => (c i).e ≫ h) (fun i => (c i).sqX)
  have hsmq : ∀ i, Smooth (c i).q := fun i => SmoothOfRelativeDimension.smooth d _
  have hsmX : @Smooth (sigmaTriple TX (fun i => (c i).q) d).X.left TX.X.left
    (Sigma.desc fun i => (c i).q) :=
    smooth_sigmaDesc fun i => (c i).q
  have hflatX : Flat (Sigma.desc fun i => (c i).e ≫ h) := by
    rw [hdesc]
    infer_instance
  have hbX := BRAffine_eq_eraseEmpty_pullback_of_admissible X (∐ fun i => (c i).W) hX hZ TX
    (sigmaTriple TX (fun i => (c i).q) d) embX (Limits.Sigma.map fun i => (c i).j)
    hadmX hadmZX (Sigma.desc fun i => (c i).q) (sigmaTriple_isPullbackOf TX _ d)
    (Sigma.desc fun i => (c i).e ≫ h) (sigmaMap_comp_desc _ _ _ embX fun i => (c i).sqX.w)
  -- combine: the surjective `Sigma.desc e` turns both erasures into pull-backs
  rw [eraseEmpty_pullback_of_flat_surjective _ _ hsurj, eraseEmpty_BRAffine k Y] at hbY
  rw [hdesc, pullback_comp, eraseEmpty_pullback_of_flat_surjective _ _ hsurj] at hbX
  have key := hbY.symm.trans hbX
  refine eq_of_pullback_of_covers _ _ (fun i => (c i).e) hcov fun i => ?_
  have hi : (c i).e = Sigma.ι (fun i => (c i).W) i ≫ Sigma.desc (fun i => (c i).e) :=
    (Sigma.ι_comp_desc (fun i => (c i).e) i).symm
  rw [hi, pullback_comp, pullback_comp, key]

/-- Commutation of `BRAffine` with a smooth `h` of relative dimension `d` between affine reduced
equidimensional schemes, given admissible pairs of both [Kol07, Theorem 36, proof; 34.1]:
the charts of `exists_chart_mem` at every point, a finite subcover, and
`BRAffine_eq_eraseEmpty_pullback_of_charts`. -/
theorem BRAffine_eq_eraseEmpty_pullback_of_smooth (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) (hY : Y.IsReducedEquidimensional k)
    (h : Y ⟶ X) [h.IsOver (Spec (CommRingCat.of k))] (d : ℕ) [SmoothOfRelativeDimension d h]
    (TX : Triple k) (embX : X ⟶ TX.X.left) (hadmX : AdmissibleEmbedding k X TX embX)
    (TY : Triple k) (embY : Y ⟶ TY.X.left) (hadmY : AdmissibleEmbedding k Y TY embY) :
    BRAffine k Y = ((BRAffine k X).pullback h).eraseEmpty := by
  have := SmoothOfRelativeDimension.smooth d h
  have hclX : IsClosedImmersion embX := hadmX.1
  have hclY : IsClosedImmersion embY := hadmY.1
  have hAY : IsAffine TY.X.left := hadmY.2.2.1
  rcases isEmpty_or_nonempty Y with hYe | hYn
  · rw [← eraseEmpty_BRAffine k Y, eraseEmpty_eq_nil_of_isEmpty _ hYe,
      eraseEmpty_eq_nil_of_isEmpty _ hYe]
  · have hch : ∀ y : Y, ∃ c : Chart h embX embY d, y ∈ Set.range c.e := fun y =>
      exists_chart_mem h d embX embY y
    choose c hc using hch
    have hcpt : CompactSpace Y := compactSpace_of_quasiCompact_over k Y
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : Y => Set.range (c y).e)
      (fun y => (c y).e.isOpenEmbedding.isOpen_range)
      (fun y _ => Set.mem_iUnion.mpr ⟨y, hc y⟩)
    have hcov : ∀ y, ∃ (i : {y : Y // y ∈ t}) (w : (c i.1).W), (c i.1).e w = y := by
      intro y
      obtain ⟨i, hi, w, hw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
      exact ⟨⟨i, hi⟩, w, hw⟩
    obtain ⟨i₀, w₀, -⟩ := hcov hYn.some
    have : Nonempty {y : Y // y ∈ t} := ⟨i₀⟩
    exact BRAffine_eq_eraseEmpty_pullback_of_charts X Y hX hY h d TX embX hadmX TY embY hadmY
      (fun i : {y : Y // y ∈ t} => c i.1) hcov

end Hironaka.Resolution
