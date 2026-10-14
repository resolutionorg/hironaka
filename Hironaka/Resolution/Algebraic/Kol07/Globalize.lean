/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.Pullback
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The proof of Theorem 105: the local cover, the kernel pair, uniqueness of the extension

Kollár's proof of the globalization theorem [Kol07, Theorem 105] for `M = {open immersions}`, in
this library the class `openImmersionCoprods` of coproducts of open immersions, has four moves:
(a) a global triple `(X, I, E)` is covered by finitely many local `M`-covers `gₓᵢ : Uₓᵢ → X`
(clause (i) of the data at every point, quasi-compactness of `X`), and `X' := ∐ᵢ Uₓᵢ` with
`g : X' → X` is a local triple by clause (ii); (b) `X'' := X' ×_X X'` with its projections
`τ₁, τ₂` is a local triple (the hypothesis `LocalCoversFibreClosed`) and the `τᵢ` are surjective
members of `M`; (c) `B` commutes with the `τᵢ`, so `τ₁^* B(X') = B(X'') = τ₂^* B(X')`; (d) the
sequence `B(X')` descends to `X` along `g` (the gluing of Proposition 37,
`Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Descent.lean`), and the extension is `B̄(X) :=`
that descent. This module proves (a), (b) and (c), the uniqueness of the extension, the instance of
the hypotheses for the classes of Proposition 37 (all triples, affine triples), and two lemmas on
the class; the descent (d) and the construction of `B̄` are in
`Hironaka/Resolution/Algebraic/Kol07/GlobalizeDescent.lean`.

## The class lemmas

*Composition* (`openImmersionCoprods_comp`): if `Y = ∐ᵢ Uᵢ` maps to `Z = ∐ⱼ Vⱼ` by open immersions
on the summands and `Z` maps to `W` likewise, then `Y` is the coproduct of the `Uᵢ ×_Z Vⱼ` (open
subschemes of the `Uᵢ`, disjoint, covering) and each maps to `W` by an open immersion. Used for the
composite local cover `Y' → Y → X` of the commutation step.

*Separatedness* (`openImmersionCoprods_isSeparated`): a coproduct of open immersions `f : Y → X` is
separated. The diagonal `Y → Y ×_X Y` is an immersion (Mathlib), so it is a closed immersion as
soon as its range is closed; the complement of the range is the union of the opens
`τ₁^{-1}(Uᵢ) ∩ τ₂^{-1}(Uⱼ)` for `i ≠ j` — a point over `(Uᵢ, Uᵢ)` lies in the image of
`Uᵢ ×_X Uᵢ → Y ×_X Y`, and `Uᵢ ×_X Uᵢ ≅ Uᵢ` by the diagonal because `Uᵢ → X` is a monomorphism, so
such a point is on the diagonal; a point over `(Uᵢ, Uⱼ)` with `i ≠ j` is not, the summands being
disjoint. This is what makes `X'` and `X''` triples: `X' → Spec k` factors through the separated
`g`, and `X'' → Spec k` through the separated `τ₁`.

## The statements proved here

* The local cover: `Triple.exists_finite_localCover` is clause (i) at every point plus a finite
  subcover (`CompactSpace X` from `QuasiCompact (X → Spec k)`, the ranges of members of `M` being
  open); `Triple.exists_isLocalCover` builds `X' = ∐ Uₓᵢ` as the pullback triple `Triple.pullback`
  of `T` along `g = Sigma.desc`, which is a coproduct of open immersions (`sigmaDesc`), smooth
  and separated, with `X'` quasi-compact (a finite coproduct of quasi-compact schemes) and of the
  relative dimension of `X` (`g` étale), and shows `X' ∈ LT` by clause (ii): `X'` is the disjoint
  union of the `Uₓᵢ` with the restricted data (`IsSigmaOf`).
* The kernel pair: `Triple.exists_kernelPair` takes Mathlib's `pullback g g` with its
  projections: they are in `M` by base change, surjective (a point `y'` lifts to `(y', y')`), and
  `X''` is `Triple.pullback` of `X'` along `τ₁`; the data along `τ₂` agree because
  `τ₁ ≫ g = τ₂ ≫ g`; `X'' ∈ LT` is the hypothesis `LocalCoversFibreClosed` applied to the cover
  twice.
* The descent datum: `OrderSeqAssignment.pullback_eq_of_kernelPair` is two applications of the
  hypothesis on `B`.
* Uniqueness (`OrderSeqAssignment.globalization_unique`): for two extensions and a global `T` with a
  point, `g^* B̄ᵢ(T) = B̄ᵢ(X') = B(X')` along a local cover (`X' ∈ GT` by `hLG`), and pullback
  along the surjective flat `g` is injective (`pullback_injective_of_surjective`); on an empty
  `T.X.left` both values are `nil`, every center on the empty scheme being empty
  (`eq_nil_of_noEmptyCenters`).
* The instance (`globalizationData_isAffineScheme`, `localCoversFibreClosed_isAffineScheme`):
  every point of a triple lies in an affine open, whose triple is affine and local; the affine
  triples are closed under finite disjoint unions; and the fibre product of two affine local
  covers is affine because `X` is separated over `k` (`g₂` is then an affine morphism and the
  base change of an affine morphism to an affine scheme is affine). This is the setting of
  [Kol07, Proposition 37], recovered from Theorem 105.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme TopologicalSpace

namespace Hironaka.Sequence

/-! ### Lemmas on the class of coproducts of open immersions -/

section ClassLemmas

variable {X Y Z : Scheme.{u}}

/-- The range of a coproduct of open immersions is open (the union of the ranges of the
summands). -/
theorem openImmersionCoprods.isOpen_range {f : Y ⟶ X} (hf : openImmersionCoprods f) :
    IsOpen (Set.range f) := by
  obtain ⟨σ, U, ι, hc, hι⟩ := hf
  have : Set.range f = ⋃ i, Set.range (ι i ≫ f) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨i, u, rfl⟩ := exists_eq_of_isColimit_cofan ι hc y
      exact Set.mem_iUnion.mpr ⟨i, u, Scheme.Hom.comp_apply _ _ _⟩
    · intro hx
      obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨ι i u, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [this]
  exact isOpen_iUnion fun i => have := hι i; (ι i ≫ f).isOpenEmbedding.isOpen_range

/-- A coproduct of open immersions is smooth (it is étale, `openImmersionCoprods_etale`). -/
theorem openImmersionCoprods.smooth {f : Y ⟶ X} (hf : openImmersionCoprods f) : Smooth f :=
  have := openImmersionCoprods_etale f hf
  inferInstance

/-- A coproduct of open immersions is flat: flatness is local on the source and the summand
inclusions are open immersions. -/
theorem openImmersionCoprods.flat {f : Y ⟶ X} (hf : openImmersionCoprods f) : Flat f := by
  obtain ⟨σ, U, ι, hc, hι⟩ := hf
  have := isIso_sigmaDesc_of_isColimit_cofan ι hc
  have hdesc : Sigma.desc ι ≫ f = Sigma.desc fun i => ι i ≫ f := by
    ext i
    simp
  have : IsZariskiLocalAtSource @Flat :=
    @HasRingHomProperty.instIsZariskiLocalAtSource @Flat _ inferInstance
  have h1 : Flat (Sigma.desc fun i => ι i ≫ f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Flat) fun i => have := hι i; inferInstance
  have h2 : Flat (inv (Sigma.desc ι) ≫ Sigma.desc ι ≫ f) := by
    rw [hdesc]
    infer_instance
  rwa [IsIso.inv_hom_id_assoc] at h2

/-- A composite of coproducts of open immersions is a coproduct of open immersions: the summands
of the source are cut along the summands of the middle scheme. -/
theorem openImmersionCoprods_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : openImmersionCoprods f)
    (hg : openImmersionCoprods g) : openImmersionCoprods (f ≫ g) := by
  obtain ⟨σ, U, ι, hc, hι⟩ := hf
  obtain ⟨τ, V, κ, hc', hκ⟩ := hg
  have hιo : ∀ i, IsOpenImmersion (ι i) := isOpenImmersion_of_isColimit_cofan ι hc
  have hκo : ∀ j, IsOpenImmersion (κ j) := isOpenImmersion_of_isColimit_cofan κ hc'
  have hfst : ∀ p : σ × τ, IsOpenImmersion (pullback.fst (ι p.1 ≫ f) (κ p.2)) := fun p =>
    have := hκo p.2
    inferInstance
  have hsnd : ∀ p : σ × τ, IsOpenImmersion (pullback.snd (ι p.1 ≫ f) (κ p.2)) := fun p =>
    have := hι p.1
    inferInstance
  refine ⟨σ × τ, fun p => pullback (ι p.1 ≫ f) (κ p.2),
    fun p => pullback.fst (ι p.1 ≫ f) (κ p.2) ≫ ι p.1, ?_, fun p => ?_⟩
  · have : ∀ p : σ × τ, IsOpenImmersion (pullback.fst (ι p.1 ≫ f) (κ p.2) ≫ ι p.1) := fun p =>
      have := hfst p
      have := hιo p.1
      inferInstance
    refine nonempty_isColimit_cofanMk_of_range _ ?_ ?_
    · intro x
      obtain ⟨i, u, rfl⟩ := exists_eq_of_isColimit_cofan ι hc x
      obtain ⟨j, v, hv⟩ := exists_eq_of_isColimit_cofan κ hc' (f (ι i u))
      obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ι i ≫ f) (g := κ j) u v
        (by rw [Scheme.Hom.comp_apply, hv])
      exact ⟨⟨i, j⟩, w, by rw [Scheme.Hom.comp_apply, hw₁]⟩
    · rintro ⟨i, j⟩ ⟨i', j'⟩ hne w w' hww
      simp only [Scheme.Hom.comp_apply] at hww
      by_cases hii : i = i'
      · subst hii
        have hj : j ≠ j' := fun h => hne (by rw [h])
        have := hιo i
        have hu := (ι i).isOpenEmbedding.injective hww
        apply ne_of_isColimit_cofan κ hc' hj (pullback.snd (ι i ≫ f) (κ j) w)
          (pullback.snd (ι i ≫ f) (κ j') w')
        have e1 : κ j (pullback.snd (ι i ≫ f) (κ j) w) = f (ι i (pullback.fst (ι i ≫ f) (κ j) w)) :=
          calc κ j (pullback.snd (ι i ≫ f) (κ j) w)
              = (pullback.snd (ι i ≫ f) (κ j) ≫ κ j) w := (Scheme.Hom.comp_apply _ _ _).symm
            _ = (pullback.fst (ι i ≫ f) (κ j) ≫ (ι i ≫ f)) w := by rw [pullback.condition]
            _ = f (ι i (pullback.fst (ι i ≫ f) (κ j) w)) := by
              rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        have e2 : κ j' (pullback.snd (ι i ≫ f) (κ j') w') =
            f (ι i (pullback.fst (ι i ≫ f) (κ j') w')) :=
          calc κ j' (pullback.snd (ι i ≫ f) (κ j') w')
              = (pullback.snd (ι i ≫ f) (κ j') ≫ κ j') w' := (Scheme.Hom.comp_apply _ _ _).symm
            _ = (pullback.fst (ι i ≫ f) (κ j') ≫ (ι i ≫ f)) w' := by rw [pullback.condition]
            _ = f (ι i (pullback.fst (ι i ≫ f) (κ j') w')) := by
              rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        rw [e1, e2, hu]
      · exact ne_of_isColimit_cofan ι hc hii _ _ hww
  · have := hsnd p
    have := hκ p.2
    have e : (pullback.fst (ι p.1 ≫ f) (κ p.2) ≫ ι p.1) ≫ f ≫ g =
        pullback.snd (ι p.1 ≫ f) (κ p.2) ≫ κ p.2 ≫ g := by
      rw [Category.assoc, ← Category.assoc (ι p.1) f g, ← Category.assoc, pullback.condition,
        Category.assoc]
    rw [e]
    infer_instance

/-- A coproduct of open immersions `f : Y ⟶ X` is separated: the diagonal `Y → Y ×_X Y` is an
immersion whose range is closed, its complement being the union of the opens
`τ₁^{-1}(Uᵢ) ∩ τ₂^{-1}(Uⱼ)`, `i ≠ j`, since a point over `(Uᵢ, Uᵢ)` comes from `Uᵢ ×_X Uᵢ ≅ Uᵢ`
(`Uᵢ → X` is a monomorphism) and so lies on the diagonal. This is what makes `X' → Spec k` and
`X'' → Spec k` separated. -/
theorem openImmersionCoprods_isSeparated {f : Y ⟶ X} (hf : openImmersionCoprods f) :
    IsSeparated f := by
  obtain ⟨σ, U, ι, hc, hι⟩ := hf
  have hιo : ∀ i, IsOpenImmersion (ι i) := isOpenImmersion_of_isColimit_cofan ι hc
  constructor
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [← isOpen_compl_iff]
  have key : (Set.range (pullback.diagonal f))ᶜ = ⋃ (i : σ) (j : σ) (_ : i ≠ j),
      pullback.fst f f ⁻¹' Set.range (ι i) ∩ pullback.snd f f ⁻¹' Set.range (ι j) := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage]
    constructor
    · intro hz
      obtain ⟨i, u, hu⟩ := exists_eq_of_isColimit_cofan ι hc (pullback.fst f f z)
      obtain ⟨j, v, hv⟩ := exists_eq_of_isColimit_cofan ι hc (pullback.snd f f z)
      refine ⟨i, j, fun hij => ?_, ⟨u, hu⟩, ⟨v, hv⟩⟩
      subst hij
      have hmem : z ∈ Set.range
          (pullback.map (ι i ≫ f) (ι i ≫ f) f f (ι i) (ι i) (𝟙 X) (by simp) (by simp)) := by
        rw [Scheme.Pullback.range_map]
        exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
      obtain ⟨w, rfl⟩ := hmem
      have hmono : Mono (ι i ≫ f) := have := hι i; inferInstance
      obtain ⟨w₀, rfl⟩ := (pullback.diagonal (ι i ≫ f)).surjective w
      have hnat : pullback.diagonal (ι i ≫ f) ≫
          pullback.map (ι i ≫ f) (ι i ≫ f) f f (ι i) (ι i) (𝟙 X) (by simp) (by simp) =
            ι i ≫ pullback.diagonal f := by
        apply pullback.hom_ext <;>
          simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
            pullback.diagonal_fst_assoc, pullback.diagonal_snd_assoc, pullback.diagonal_fst,
            pullback.diagonal_snd, Category.comp_id]
      refine hz (ι i w₀) ?_
      have h1 : (pullback.diagonal f) (ι i w₀) = (ι i ≫ pullback.diagonal f) w₀ :=
        (Scheme.Hom.comp_apply _ _ _).symm
      rw [h1, ← hnat, Scheme.Hom.comp_apply]
    · rintro ⟨i, j, hij, ⟨u, hu⟩, ⟨v, hv⟩⟩ y hy
      apply ne_of_isColimit_cofan ι hc hij u v
      rw [hu, hv, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.diagonal_fst,
        pullback.diagonal_snd]
  rw [key]
  refine isOpen_iUnion fun i => isOpen_iUnion fun j => isOpen_iUnion fun _ => ?_
  have := hιo i
  have := hιo j
  exact ((ι i).isOpenEmbedding.isOpen_range.preimage (pullback.fst f f).continuous).inter
    ((ι j).isOpenEmbedding.isOpen_range.preimage (pullback.snd f f).continuous)

end ClassLemmas

/-! ### No empty centers on the empty scheme means `nil` -/

/-- On the empty scheme every ideal sheaf is `⊤` (two ideal sheaves with equal stalks are equal,
vacuously), so a blow-up sequence without empty centers is `nil`. -/
theorem _root_.AlgebraicGeometry.Scheme.BlowUpSequence.eq_nil_of_noEmptyCenters {X : Scheme.{u}}
    [IsEmpty X]
    (S : BlowUpSequence X) (h : S.NoEmptyCenters) : S = BlowUpSequence.nil X := by
  cases S with
  | nil => rfl
  | cons X D rest =>
    exfalso
    apply h ⟨0, Nat.succ_pos _⟩
    change D = ⊤
    exact Scheme.IdealSheafData.ext_stalkIdeal fun x => isEmptyElim x

end Hironaka.Sequence

namespace Hironaka

variable {k : Type u} [Field k] {m : ℕ} {GT LT : Triple k → Prop}

open Hironaka.Sequence Scheme AlgebraicGeometry

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k] {m : ℕ} {GT LT : Triple k → Prop}

open Hironaka.Sequence Scheme AlgebraicGeometry

open AlgebraicGeometry Scheme

/-! ### The finite local cover and `X' = ∐ Uₓᵢ` -/

/-- Clause (i) of the data of [Kol07, Theorem 105] at every point, and a finite subcover of the
quasi-compact `T.X.left` by the (open) ranges. -/
theorem exists_finite_localCover (D : GlobalizationData openImmersionCoprods GT LT) {T : Triple k}
    (hT : GT T) :
    ∃ (σ : Type u) (_ : Finite σ) (Ts : σ → Triple k) (g : ∀ i, (Ts i).X.left ⟶ T.X.left),
      (∀ i, openImmersionCoprods (g i)) ∧ (∀ i, LT (Ts i)) ∧ (∀ i, (Ts i).IsPullbackOf T (g i)) ∧
        ∀ x : T.X.left, ∃ i, x ∈ Set.range (g i) := by
  choose Tx gx hM hx hp hL using fun x : T.X.left => D.exists_isPullbackOf T hT x
  have : CompactSpace T.X.left :=
    QuasiCompact.compactSpace_of_compactSpace (T.X.left ↘ Spec (CommRingCat.of k))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (gx x))
    (fun x => openImmersionCoprods.isOpen_range (hM x)) (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨t, inferInstance, fun i => Tx i.1, fun i => gx i.1, fun i => hM i.1, fun i => hL i.1,
    fun i => hp i.1, fun x => ?_⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, hxi⟩

/-- `X' := ∐ᵢ Uₓᵢ` with the induced `g : X' → X` is a local `M`-cover of a nonempty global triple
(the proof of [Kol07, Theorem 105]): the pullback triple along `g`, in `LT` by clause (ii) as the
disjoint union of the `Uₓᵢ` with the restricted data. -/
theorem exists_isLocalCover [CharZero k] (D : GlobalizationData openImmersionCoprods GT LT)
    {T : Triple k} (hT : GT T) [Nonempty T.X.left] :
    ∃ (T' : Triple k) (g : T'.X.left ⟶ T.X.left),
      IsLocalCover openImmersionCoprods GT LT T T' g := by
  obtain ⟨σ, _, Ts, g, hM, hL, hp, hcov⟩ := exists_finite_localCover D hT
  have hne : Nonempty σ := by
    obtain ⟨x⟩ := ‹Nonempty T.X.left›
    obtain ⟨i, -⟩ := hcov x
    exact ⟨i⟩
  let Y : Scheme.{u} := ∐ fun i => (Ts i).X.left
  let g' : Y ⟶ T.X.left := Sigma.desc g
  have hM' : openImmersionCoprods g' := isGlobalizationClass_openImmersionCoprods.sigmaDesc g hM
  have hsurj : Function.Surjective g' := by
    intro x
    obtain ⟨i, y, hy⟩ := hcov x
    exact ⟨Sigma.ι (fun i => (Ts i).X.left) i y,
      by rw [← hy, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩
  have hsm : Smooth g' := openImmersionCoprods.smooth hM'
  have hsep : IsSeparated g' := openImmersionCoprods_isSeparated hM'
  have het : Etale g' := openImmersionCoprods_etale g' hM'
  let _ : Y.Over (Spec (CommRingCat.of k)) := ⟨g' ≫ (T.X.left ↘ Spec (CommRingCat.of k))⟩
  have _ : g'.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have hcpt : CompactSpace Y := by
    have : ∀ i, CompactSpace (Ts i).X.left := fun i =>
      QuasiCompact.compactSpace_of_compactSpace ((Ts i).X.left ↘ Spec (CommRingCat.of k))
    exact (sigmaMk fun i => (Ts i).X.left).compactSpace
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (g' ≫ (T.X.left ↘ Spec (CommRingCat.of k))))
  have : IsSeparated (Y ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (IsSeparated (g' ≫ (T.X.left ↘ Spec (CommRingCat.of k))))
  have : QuasiCompact (Y ↘ Spec (CommRingCat.of k)) := inferInstance
  have hY : ∃ n : ℕ, SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of k))
    := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact ⟨n, by simpa using smoothOfRelativeDimension_comp 0 n g'
                   (T.X.left ↘ Spec (CommRingCat.of k))⟩
  refine ⟨Triple.pullback T hY g', g', hT, ?_, hM', hsurj, isPullbackOf_pullback T hY g'⟩
  refine D.closedUnderSigma Ts (Triple.pullback T hY g')
    (fun i => Sigma.ι (fun i => (Ts i).X.left) i)
    ⟨⟨coproductIsCoproduct (fun i => (Ts i).X.left)⟩, fun i => ?_, fun i => ?_, fun i => ?_⟩ hL
  · change Sigma.ι (fun i => (Ts i).X.left) i ≫ (g' ≫ (T.X.left ↘ Spec (CommRingCat.of k))) = _
    rw [Sigma.ι_comp_desc_assoc]
    exact (hp i).1
  · change (Ts i).I = (T.I.comap g').comap (Sigma.ι (fun i => (Ts i).X.left) i)
    rw [← Scheme.IdealSheafData.comap_comp, Sigma.ι_comp_desc]
    exact (hp i).2.1
  · change (Ts i).E = (T.E.comap g').comap (Sigma.ι (fun i => (Ts i).X.left) i)
    rw [← DivisorFamily.comap_comp, Sigma.ι_comp_desc]
    exact (hp i).2.2

/-! ### The kernel pair `X'' = X' ×_X X'` -/

/-- The kernel pair of a local `M`-cover as a local triple (the proof of [Kol07, Theorem 105]):
`X'' = X' ×_X X'` with its projections, in `M` by base change, surjective, with the pullback data
of `X'` along both projections, in `LT` by the hypothesis `LocalCoversFibreClosed`. -/
theorem exists_kernelPair [CharZero k] (hF : LocalCoversFibreClosed openImmersionCoprods GT LT)
    {T T' : Triple k} {g : T'.X.left ⟶ T.X.left}
    (hc : IsLocalCover openImmersionCoprods GT LT T T' g) :
    ∃ (T'' : Triple k) (τ₁ τ₂ : T''.X.left ⟶ T'.X.left), IsPullback τ₁ τ₂ g g ∧
      T''.IsPullbackOf T' τ₁ ∧ T''.IsPullbackOf T' τ₂ ∧
      openImmersionCoprods τ₁ ∧ openImmersionCoprods τ₂ ∧
      Function.Surjective τ₁ ∧ Function.Surjective τ₂ ∧ LT T'' := by
  obtain ⟨hT, hT', hM, hs, hp⟩ := hc
  have sq : IsPullback (Limits.pullback.fst g g) (Limits.pullback.snd g g) g g :=
    IsPullback.of_hasPullback g g
  have hM₁ : openImmersionCoprods (Limits.pullback.fst g g) :=
    isStableUnderBaseChange_openImmersionCoprods.of_isPullback sq.flip hM
  have hM₂ : openImmersionCoprods (Limits.pullback.snd g g) :=
    isStableUnderBaseChange_openImmersionCoprods.of_isPullback sq hM
  have hs₁ : Function.Surjective (Limits.pullback.fst g g) := fun y => by
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := g) y y rfl
    exact ⟨z, hz⟩
  have hs₂ : Function.Surjective (Limits.pullback.snd g g) := fun y => by
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := g) y y rfl
    exact ⟨z, hz⟩
  have hsm : Smooth (Limits.pullback.fst g g) := openImmersionCoprods.smooth hM₁
  have hsep : IsSeparated (Limits.pullback.fst g g) := openImmersionCoprods_isSeparated hM₁
  have het : Etale (Limits.pullback.fst g g) := openImmersionCoprods_etale _ hM₁
  let _ : (Limits.pullback g g).Over (Spec (CommRingCat.of k)) :=
    ⟨Limits.pullback.fst g g ≫ (T'.X.left ↘ Spec (CommRingCat.of k))⟩
  have _ : (Limits.pullback.fst g g).IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have hqc : QuasiCompact g := by
    have : QuasiCompact (g ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := by
      rw [hp.1]
      infer_instance
    exact QuasiCompact.of_comp g (T.X.left ↘ Spec (CommRingCat.of k))
  have hcpt : CompactSpace T'.X.left :=
    QuasiCompact.compactSpace_of_compactSpace (T'.X.left ↘ Spec (CommRingCat.of k))
  have : LocallyOfFiniteType ((Limits.pullback g g) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.fst g g ≫
      (T'.X.left ↘ Spec (CommRingCat.of k))))
  have : IsSeparated ((Limits.pullback g g) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (IsSeparated (Limits.pullback.fst g g ≫ (T'.X.left ↘ Spec (CommRingCat.of k))))
  have : QuasiCompact ((Limits.pullback g g) ↘ Spec (CommRingCat.of k)) := inferInstance
  have hY : ∃ n : ℕ, SmoothOfRelativeDimension n ((Limits.pullback g g) ↘ Spec (CommRingCat.of k))
    := by
    obtain ⟨n, hn⟩ := T'.smoothOfRelativeDimension
    exact ⟨n, by
      simpa using smoothOfRelativeDimension_comp 0 n (Limits.pullback.fst g g)
        (T'.X.left ↘ Spec (CommRingCat.of k))⟩
  have hp₁ := isPullbackOf_pullback T' hY (Limits.pullback.fst g g)
  have hcond : Limits.pullback.fst g g ≫ g = Limits.pullback.snd g g ≫ g :=
    Limits.pullback.condition
  have hp₂ : (Triple.pullback T' hY (Limits.pullback.fst g g)).IsPullbackOf T' (Limits.pullback.snd
    g g) := by
    refine ⟨?_, ?_, ?_⟩
    · change Limits.pullback.snd g g ≫ (T'.X.left ↘ Spec (CommRingCat.of k)) =
        Limits.pullback.fst g g ≫ (T'.X.left ↘ Spec (CommRingCat.of k))
      rw [← hp.1, ← Category.assoc, ← Category.assoc, hcond]
    · change T'.I.comap (Limits.pullback.fst g g) = T'.I.comap (Limits.pullback.snd g g)
      rw [hp.2.1, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcond]
    · change T'.E.comap (Limits.pullback.fst g g) = T'.E.comap (Limits.pullback.snd g g)
      rw [hp.2.2, ← DivisorFamily.comap_comp, ← DivisorFamily.comap_comp, hcond]
  refine ⟨Triple.pullback T' hY (Limits.pullback.fst g g), Limits.pullback.fst g g,
    Limits.pullback.snd g g, sq, hp₁,
    hp₂,
    hM₁, hM₂, hs₁, hs₂, ?_⟩
  exact hF ⟨hT, hT', hM, hs, hp⟩ ⟨hT, hT', hM, hs, hp⟩ sq hp₁

/-! ### The classes of Proposition 37 as an instance -/

/-- The data of [Kol07, Theorem 105] for the classes of [Kol07, Proposition 37] (all triples, and
the affine triples): every point of a triple has an affine open neighbourhood, whose triple (the
pullback along the open immersion) is affine; the affine triples are closed under finite disjoint
unions. -/
theorem globalizationData_isAffineScheme [CharZero k] :
    GlobalizationData openImmersionCoprods (fun _ : Triple k => True) Triple.IsAffineScheme where
  exists_isPullbackOf T _ x := by
    let 𝒰 := T.X.left.affineCover
    let u : 𝒰.X (𝒰.idx x) ⟶ T.X.left := 𝒰.f (𝒰.idx x)
    have haff : IsAffine (𝒰.X (𝒰.idx x)) := inferInstance
    let _ : (𝒰.X (𝒰.idx x)).Over (Spec (CommRingCat.of k)) :=
      ⟨u ≫ (T.X.left ↘ Spec (CommRingCat.of k))⟩
    have _ : u.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
    have : LocallyOfFiniteType ((𝒰.X (𝒰.idx x)) ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (u ≫ (T.X.left ↘ Spec (CommRingCat.of k))))
    have : IsSeparated ((𝒰.X (𝒰.idx x)) ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (IsSeparated (u ≫ (T.X.left ↘ Spec (CommRingCat.of k))))
    have : QuasiCompact ((𝒰.X (𝒰.idx x)) ↘ Spec (CommRingCat.of k)) := inferInstance
    have hY : ∃ n : ℕ, SmoothOfRelativeDimension n ((𝒰.X (𝒰.idx x)) ↘ Spec (CommRingCat.of k)) := by
      obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
      exact ⟨n, by simpa using smoothOfRelativeDimension_comp 0 n u
                     (T.X.left ↘ Spec (CommRingCat.of k))⟩
    exact ⟨Triple.pullback T hY u, u, openImmersionCoprods_of_isOpenImmersion u, 𝒰.covers x,
      isPullbackOf_pullback T hY u, haff⟩
  closedUnderSigma := Triple.closedUnderSigma_isAffine

/-- The fibre product over a triple of two affine local covers is affine (as `isAffine_coverPair`
of `Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Setting.lean`): `T.X.left` is separated over
`k`, so `g₂` is an affine morphism, and its base change to the affine `T₁.X.left` has affine source.
-/ theorem localCoversFibreClosed_isAffineScheme :
    LocalCoversFibreClosed openImmersionCoprods (fun _ : Triple k => True) Triple.IsAffineScheme :=
      by
  intro T T₁ T₂ g₁ g₂ hc₁ hc₂ T₁₂ p₁ p₂ sq _
  obtain ⟨-, h₁, -, -, -⟩ := hc₁
  obtain ⟨-, h₂, -, -, hp₂⟩ := hc₂
  have : IsAffine T₁.X.left := h₁
  have : IsAffine T₂.X.left := h₂
  have : IsAffineHom (g₂ ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := by
    rw [hp₂.1]
    infer_instance
  have : IsAffineHom g₂ := IsAffineHom.of_comp (f := g₂) (g := T.X.left ↘ Spec (CommRingCat.of k))
  have : IsAffine (Limits.pullback g₁ g₂) := inferInstance
  change IsAffine T₁₂.X.left
  exact IsAffine.of_isIso sq.isoPullback.hom

end AlgebraicGeometry.Triple

namespace Hironaka

variable {k : Type u} [Field k] {m : ℕ} {GT LT : Triple k → Prop}

open Hironaka.Sequence Scheme AlgebraicGeometry

namespace OrderSeqAssignment

open AlgebraicGeometry

/-! ### The descent datum (105.4) for whole sequences -/

/-- `τ₁^* B(X') = B(X'') = τ₂^* B(X')` (the compatibility (105.4) in the proof of
[Kol07, Theorem 105]), two applications of "`B` commutes with surjections in `M`". -/
theorem pullback_eq_of_kernelPair (B : OrderSeqAssignment k m LT)
    (hB : B.CommutesWithSurjectionsIn openImmersionCoprods) {T' T'' : Triple k}
    {τ₁ τ₂ : T''.X.left ⟶ T'.X.left} (hM₁ : openImmersionCoprods τ₁) (hM₂ : openImmersionCoprods τ₂)
    (hs₁ : Function.Surjective τ₁) (hs₂ : Function.Surjective τ₂) (h₁ : T''.IsPullbackOf T' τ₁)
    (h₂ : T''.IsPullbackOf T' τ₂) (hT' : LT T') (hT'' : LT T'') :
    (B.seq T' hT').pullback τ₁ = B.seq T'' hT'' ∧ B.seq T'' hT'' = (B.seq T' hT').pullback τ₂ :=
  ⟨(hB T' T'' τ₁ hM₁ hs₁ h₁ hT' hT'').symm, hB T' T'' τ₂ hM₂ hs₂ h₂ hT' hT''⟩

/-! ### Uniqueness of the extension -/

/-- "A unique extension" [Kol07, Theorem 105]: two functors on the global triples agreeing with
`B` on the local ones and commuting with surjections in `M` are equal. Along a local cover
`g : X' → X` (with `X' ∈ GT` by `hLG`) both pull back to `B(X')`, and pullback along the
surjective flat `g` is injective; on an empty scheme both are `nil`. -/
theorem globalization_unique [CharZero k] (D : Triple.GlobalizationData openImmersionCoprods GT LT)
    (hLG : ∀ T, LT T → GT T) (B : OrderSeqAssignment k m LT) {B₁ B₂ : OrderSeqAssignment k m GT}
    (h₁ : ∀ (T : Triple k) (hL : LT T) (hG : GT T), B₁.seq T hG = B.seq T hL)
    (h₂ : ∀ (T : Triple k) (hL : LT T) (hG : GT T), B₂.seq T hG = B.seq T hL)
    (c₁ : B₁.CommutesWithSurjectionsIn openImmersionCoprods)
    (c₂ : B₂.CommutesWithSurjectionsIn openImmersionCoprods) : B₁ = B₂ := by
  have hseq : B₁.seq = B₂.seq := by
    funext T hG
    by_cases hne : Nonempty T.X.left
    · obtain ⟨T', g, hc⟩ := Triple.exists_isLocalCover D hG
      obtain ⟨-, hT', hM, hs, hp⟩ := hc
      have hG' := hLG T' hT'
      have e₁ := c₁ T T' g hM hs hp hG hG'
      have e₂ := c₂ T T' g hM hs hp hG hG'
      have : Flat g := openImmersionCoprods.flat hM
      apply pullback_injective_of_surjective g hs
      rw [← e₁, ← e₂, h₁ T' hT' hG', h₂ T' hT' hG']
    · have : IsEmpty T.X.left := not_nonempty_iff.mp hne
      rw [BlowUpSequence.eq_nil_of_noEmptyCenters _ (B₁.noEmptyCenters T hG),
        BlowUpSequence.eq_nil_of_noEmptyCenters _ (B₂.noEmptyCenters T hG)]
  cases B₁
  cases B₂
  cases hseq
  rfl

end OrderSeqAssignment

end Hironaka
