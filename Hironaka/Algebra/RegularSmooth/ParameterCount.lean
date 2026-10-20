/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.RegularSmooth.QuotientRegular
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Regular systems of parameters: the basis of `𝔪/𝔪²` and the size of a generating system

Two facts of commutative algebra about a regular local ring `R` with maximal ideal `𝔪`. In a
regular local ring of dimension `m`, the classes in `𝔪/𝔪²` of `m` generators of `𝔪` are linearly
independent over the residue field, since they span a space of dimension `m`
(`linearIndependent_toCotangent_of_span_eq`); and two families of elements of `𝔪` with linearly
independent classes generating the same ideal have the same size, by the dimension count of
[Sta, Tag 00NQ] (`quotient_span_range_of_linearIndependent`) applied to both families
(`card_eq_of_span_range_eq`). Not stated as such in the sources; they are the algebra behind the
comparison of two systems of local coordinates cutting out the same subspace.

Used by the submanifold and normal-crossings criteria of `Hironaka/Manifold/Snc/` and `Space/`.
-/

public section

open IsLocalRing

namespace IsRegularLocalRing

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- In a regular local ring of dimension `m`, the classes in `𝔪/𝔪²` of `m` generators of `𝔪` are
linearly independent over the residue field (they span a space of dimension `m`). -/
theorem linearIndependent_toCotangent_of_span_eq {m : ℕ} (z : Fin m → R)
    (hz : ∀ i, z i ∈ maximalIdeal R) (hspan : Ideal.span (Set.range z) = maximalIdeal R)
    (hdim : (m : WithBot ℕ∞) = ringKrullDim R) :
    LinearIndependent (ResidueField R) fun i => (maximalIdeal R).toCotangent ⟨z i, hz i⟩ := by
  have hsub : Submodule.span R (Set.range fun i => (⟨z i, hz i⟩ : maximalIdeal R)) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    exact hspan
  have hspanκ : Submodule.span (ResidueField R)
      (Set.range fun i => (maximalIdeal R).toCotangent ⟨z i, hz i⟩) = ⊤ := by
    have := (CotangentSpace.span_image_eq_top_iff (R := R)
      (s := Set.range fun i => (⟨z i, hz i⟩ : maximalIdeal R))).mpr hsub
    rwa [← Set.range_comp] at this
  have hfin : Module.finrank (ResidueField R) (CotangentSpace R) = m := by
    have h1 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [← hdim] at h1
    have h2 : (maximalIdeal R).spanFinrank = m := by exact_mod_cast h1
    rw [← h2]
    exact (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspanκ.ge
    (by rw [Fintype.card_fin, hfin])

/-- Two families of elements of `𝔪` with linearly independent classes in `𝔪/𝔪²` generating the same
ideal have the same size: the dimension count of [Sta, Tag 00NQ]
(`quotient_span_range_of_linearIndependent`) applied to both families. -/
theorem card_eq_of_span_range_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → R) (g : κ → R)
    (hf : ∀ i, f i ∈ maximalIdeal R) (hg : ∀ j, g j ∈ maximalIdeal R)
    (hfl : LinearIndependent (ResidueField R) fun i => (maximalIdeal R).toCotangent ⟨f i, hf i⟩)
    (hgl : LinearIndependent (ResidueField R) fun j => (maximalIdeal R).toCotangent ⟨g j, hg j⟩)
    (heq : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    Fintype.card ι = Fintype.card κ := by
  obtain ⟨-, hd₁⟩ := quotient_span_range_of_linearIndependent f hf hfl
  obtain ⟨hreg₂, hd₂⟩ := quotient_span_range_of_linearIndependent g hg hgl
  rw [heq] at hd₁
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : WithBot ℕ∞) = ringKrullDim (R ⧸ Ideal.span (Set.range g)) :=
    ⟨_, hreg₂.spanFinrank_maximalIdeal⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : WithBot ℕ∞) = ringKrullDim R :=
    ⟨_, IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  rw [← hd, ← hm] at hd₁ hd₂
  have h1 : d + Fintype.card ι = m := by exact_mod_cast hd₁
  have h2 : d + Fintype.card κ = m := by exact_mod_cast hd₂
  omega

end IsRegularLocalRing
