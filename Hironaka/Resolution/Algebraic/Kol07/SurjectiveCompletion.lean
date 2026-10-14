/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Setting
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The surjective completion of an étale pair

The functoriality package [Kol07, 34.1] gives the commutation of a blow-up sequence functor with
smooth surjections outright (its first bullet; for the principalization functor this is clause
(4) of [Kol07, Theorem 35]), and with a general smooth morphism only up to the deletion of empty
blow-ups (the second bullet). To use the first bullet alone, an étale pair `ψ, ψ' : W ⟶ A` over
`k` with `I.comap ψ = I.comap ψ'` is completed to a surjective étale pair `hψ, hψ' : Y ⟶ A` by
adding the pieces of the finite affine cover of `A` (`Triple.affineCover`), `Y := W ⨿ ∐ᵢ Uᵢ`. `Y`
is affine (a finite coproduct of affine schemes), hence separated and quasi-compact over `k`,
smooth of the relative dimension of `A` (locality on the source), and the triple
`T_Y := Triple.pullback TA _ hψ` carries the pullback data of `TA` along both `hψ` and `hψ'`: the
ideals agree on every piece of the coproduct (`eq_of_comap_eq_of_covers`), the boundary is empty,
and the structure maps agree (`Sigma.hom_ext`). So
`BP T_Y = (BP TA).pullback hψ = (BP TA).pullback hψ'`: one sequence, two readings, with the same
indices, and a truncation can then be taken on the base sequence. This is the device by which the
resolution functor is shown to be an isomorphism over the smooth locus; it is in the spirit of the
passage from affine schemes to all schemes in [Kol07, Proposition 37].

* `completionScheme W TA`: `∐ (Option TA.affineCover.I₀)` with `W` at `none`.
* `completionDesc ψ`: `Sigma.desc` of `ψ` and the cover maps; étale for étale `ψ`
  (`IsZariskiLocalAtSource.sigmaDesc`), surjective (the cover), and the structure maps of two
  such completions agree when `ψ ≫ str = ψ' ≫ str`.
* `exists_completion_isPullbackOf`: the completion triple and the two pullback-data facts, with a
  point `y` over `q` for both maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Hironaka Scheme

namespace Hironaka.Sequence

variable {k : Type u} [Field k]

/-- The family of schemes of the completion: `W` at `none`, the pieces of the finite affine cover
of `TA.X.left` at `some i`. -/
noncomputable abbrev completionFamily (W : Scheme.{u}) (TA : Triple k) :
    Option TA.affineCover.I₀ → Scheme.{u}
  | none => W
  | some i => TA.affineCover.X i

/-- The components of the completion map: `ψ` on `W`, the cover maps on the pieces. -/
noncomputable abbrev completionHom {W : Scheme.{u}} {TA : Triple k} (ψ : W ⟶ TA.X.left) :
    ∀ o, completionFamily W TA o ⟶ TA.X.left
  | none => ψ
  | some i => TA.affineCover.f i

/-- The completion scheme `Y := W ⨿ ∐ᵢ Uᵢ`. -/
noncomputable abbrev completionScheme (W : Scheme.{u}) (TA : Triple k) : Scheme.{u} :=
  ∐ completionFamily W TA

/-- The map of the completion: `ψ` on `W`, the cover maps on the pieces. -/
noncomputable def completionDesc {W : Scheme.{u}} {TA : Triple k} (ψ : W ⟶ TA.X.left) :
    completionScheme W TA ⟶ TA.X.left :=
  Sigma.desc (completionHom ψ)

@[reassoc]
theorem ι_none_comp_completionDesc {W : Scheme.{u}} {TA : Triple k} (ψ : W ⟶ TA.X.left) :
    Sigma.ι (completionFamily W TA) none ≫ completionDesc ψ = ψ :=
  Sigma.ι_comp_desc _ _

@[reassoc]
theorem ι_some_comp_completionDesc {W : Scheme.{u}} {TA : Triple k} (ψ : W ⟶ TA.X.left)
    (i : TA.affineCover.I₀) :
    Sigma.ι (completionFamily W TA) (some i) ≫ completionDesc ψ = TA.affineCover.f i :=
  Sigma.ι_comp_desc _ _

instance isAffine_completionFamily (W : Scheme.{u}) [IsAffine W] (TA : Triple k)
    (o : Option TA.affineCover.I₀) : IsAffine (completionFamily W TA o) := by
  cases o with
  | none => exact ‹IsAffine W›
  | some i => exact Triple.isAffine_affineCover_X TA i

instance isAffine_completionScheme (W : Scheme.{u}) [IsAffine W] (TA : Triple k) :
    IsAffine (completionScheme W TA) :=
  inferInstance

-- The transparency-respecting defeq check at the type of the goal does not unfold the `abbrev`
-- `completionHom` inside `Etale (completionHom ψ o)`, so `IsZariskiLocalAtSource.sigmaDesc` fails
-- to unify its family with `completionHom ψ`; the older behaviour is restored for this declaration.
set_option backward.isDefEq.respectTransparency.types false in
/-- The completion of an étale map is étale (locality on the source; the cover maps are open
immersions). -/
theorem etale_completionDesc {W : Scheme.{u}} {TA : Triple k} (ψ : W ⟶ TA.X.left) [Etale ψ] :
    Etale (completionDesc ψ) :=
  IsZariskiLocalAtSource.sigmaDesc fun o => by
    cases o with
    | none => exact ‹Etale ψ›
    | some i => change Etale (TA.affineCover.f i); infer_instance

/-- The completion is surjective: the cover pieces already cover `TA.X.left`. -/
theorem surjective_completionDesc {W : Scheme.{u}} {TA : Triple k} (ψ : W ⟶ TA.X.left) :
    Function.Surjective (completionDesc ψ) := by
  intro x
  obtain ⟨i, y, hy⟩ : ∃ i, ∃ y : TA.affineCover.X i, TA.affineCover.f i y = x := by
    have := TA.affineCover.iUnion_range
    have hx : x ∈ ⋃ i, Set.range (TA.affineCover.f i) := by rw [this]; trivial
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 hx
    exact ⟨i, y, hy⟩
  refine ⟨Sigma.ι (completionFamily W TA) (some i) y, ?_⟩
  change (Sigma.ι (completionFamily W TA) (some i) ≫ completionDesc ψ) y = x
  rw [ι_some_comp_completionDesc]
  exact hy

/-- Two completions have the same composite with the structure map when the two étale maps do. -/
theorem completionDesc_comp_over {W : Scheme.{u}} {TA : Triple k} (ψ ψ' : W ⟶ TA.X.left)
    (h : ψ ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) = ψ' ≫ (TA.X.left ↘ Spec (CommRingCat.of k))) :
    completionDesc ψ ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) =
      completionDesc ψ' ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) :=
  Sigma.hom_ext _ _ fun o => by
    cases o with
    | none =>
      rw [ι_none_comp_completionDesc_assoc, ι_none_comp_completionDesc_assoc]
      exact h
    | some i => rw [ι_some_comp_completionDesc_assoc, ι_some_comp_completionDesc_assoc]

/-- Two completions pull an ideal sheaf back to the same ideal sheaf when the two étale maps do
(extensionality of ideal sheaves along the open cover by the pieces). -/
theorem comap_completionDesc_eq {W : Scheme.{u}} {TA : Triple k} (ψ ψ' : W ⟶ TA.X.left)
    (I : TA.X.left.IdealSheafData) (h : I.comap ψ = I.comap ψ') :
    I.comap (completionDesc ψ) = I.comap (completionDesc ψ') := by
  refine Scheme.IdealSheafData.eq_of_comap_eq_of_covers (Sigma.ι (completionFamily W TA)) ?_
    fun o => ?_
  · intro x
    obtain ⟨⟨o, w⟩, rfl⟩ := (sigmaMk (completionFamily W TA)).surjective x
    exact ⟨o, w, (sigmaMk_mk _ o w).symm⟩
  · cases o with
    | none =>
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        ι_none_comp_completionDesc, ι_none_comp_completionDesc]
      exact h
    | some i =>
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        ι_some_comp_completionDesc, ι_some_comp_completionDesc]

/-- The inverse images of a divisor family with an empty index type along two morphisms agree. -/
theorem _root_.AlgebraicGeometry.Scheme.DivisorFamily.comap_eq_comap_of_isEmpty {X Y : Scheme.{u}}
    (E : DivisorFamily X)
    (h h' : Y ⟶ X) (hE : IsEmpty E.ι) : E.comap h = E.comap h' := by
  unfold DivisorFamily.comap
  congr 1
  funext i
  exact (hE.false i).elim

/-! ### The completion triple -/

section Triple

variable [CharZero k] {W : Scheme.{u}} [IsAffine W] {TA : Triple k}

/-- The completion scheme is a scheme over `Spec k` through the completion of `ψ`. -/
noncomputable abbrev completionOver (ψ : W ⟶ TA.X.left) :
    (completionScheme W TA).Over (Spec (CommRingCat.of k)) :=
  ⟨completionDesc ψ ≫ (TA.X.left ↘ Spec (CommRingCat.of k))⟩

omit [CharZero k] [IsAffine W] in
/-- The completion scheme is smooth of the relative dimension of `TA.X.left` over `k`, when `ψ` is
étale (each piece is étale over `TA.X.left`; locality on the source). -/
theorem exists_smoothOfRelativeDimension_completion (ψ : W ⟶ TA.X.left) [Etale ψ] :
    letI := completionOver ψ
    ∃ n : ℕ, SmoothOfRelativeDimension n (completionScheme W TA ↘ Spec (CommRingCat.of k)) := by
  let := completionOver ψ
  obtain ⟨n, hn⟩ := TA.smoothOfRelativeDimension
  refine ⟨n, ?_⟩
  change SmoothOfRelativeDimension n (completionDesc ψ ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))
  have : SmoothOfRelativeDimension 0 (completionDesc ψ) := by
    have := etale_completionDesc ψ
    infer_instance
  simpa using smoothOfRelativeDimension_comp 0 n (completionDesc ψ)
    (TA.X.left ↘ Spec (CommRingCat.of k))

/-- **The surjective completion of an étale pair**, which makes the first bullet of [Kol07, 34.1]
(commutation with smooth surjections) applicable. For étale `ψ, ψ' : W ⟶ TA.X.left` with the same
composite to `Spec k` and the same inverse image of `TA.I`, and `TA.E` empty, there are a triple
`T'` and surjective étale maps `g, g' : T'.X.left ⟶ TA.X.left` along both of which `T'` carries the
pullback data of `TA`, and every `q : W` has a point `y : T'.X.left` with `g y = ψ q`,
`g' y = ψ' q`. -/ theorem exists_completion_isPullbackOf (ψ ψ' : W ⟶ TA.X.left) [Etale ψ] [Etale ψ']
    (hover : ψ ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) = ψ' ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))
    (hI : TA.I.comap ψ = TA.I.comap ψ') (hE : IsEmpty TA.E.ι) :
    ∃ (T' : Triple k) (g g' : T'.X.left ⟶ TA.X.left), Etale g ∧ Etale g' ∧ Function.Surjective g ∧
      Function.Surjective g' ∧ T'.IsPullbackOf TA g ∧ T'.IsPullbackOf TA g' ∧
      ∀ q : W, ∃ y : T'.X.left, g y = ψ q ∧ g' y = ψ' q := by
  let := completionOver ψ
  have hg : Etale (completionDesc ψ) := etale_completionDesc ψ
  have hg' : Etale (completionDesc ψ') := etale_completionDesc ψ'
  have hY := exists_smoothOfRelativeDimension_completion ψ
  have hsep : IsSeparated (completionScheme W TA ↘ Spec (CommRingCat.of k)) :=
    IsSeparated.of_isAffineHom _
  have : (completionDesc ψ).IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have : (completionDesc ψ').IsOver (Spec (CommRingCat.of k)) :=
    ⟨(completionDesc_comp_over ψ ψ' hover).symm⟩
  have hLFT : LocallyOfFiniteType (completionScheme W TA ↘ Spec (CommRingCat.of k)) := by
    change LocallyOfFiniteType (completionDesc ψ ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))
    infer_instance
  have hQC : QuasiCompact (completionScheme W TA ↘ Spec (CommRingCat.of k)) := inferInstance
  refine ⟨Triple.pullback TA hY (completionDesc ψ), completionDesc ψ, completionDesc ψ', hg, hg',
    surjective_completionDesc ψ, surjective_completionDesc ψ', Triple.isPullbackOf_pullback TA hY _,
    ?_,
    fun q => ⟨Sigma.ι (completionFamily W TA) none q, ?_, ?_⟩⟩
  · refine ⟨(completionDesc_comp_over ψ ψ' hover).symm, ?_, ?_⟩
    · exact comap_completionDesc_eq ψ ψ' TA.I hI
    · exact DivisorFamily.comap_eq_comap_of_isEmpty TA.E _ _ hE
  · exact congrArg (fun f => f q) (ι_none_comp_completionDesc ψ)
  · exact congrArg (fun f => f q) (ι_none_comp_completionDesc ψ')

end Triple

end Hironaka.Sequence
