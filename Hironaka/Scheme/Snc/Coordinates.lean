/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Scheme.Smooth.AdaptedCoordinates

/-!
# Local coordinates at a point

Kollár's "local coordinates `z_1, …, z_n ∈ 𝔪_x` in the maximal ideal of the local ring `𝒪_{X,x}`" of
a smooth variety [Kol07, Definition 24] are a regular system of parameters — a family generating
`𝔪_x` with as many members as `dim 𝒪_{X,x}` (`IsRegularSystemOfParameters`, stated here in its
unfolded form `span (range z) = 𝔪 ∧ n = dim`). They exist at every point of a scheme smooth over a
field (the stalks are regular local rings, and a regular local ring has a generating system of `𝔪`
with `dim` members by definition), they lie in `𝔪 ∖ 𝔪²` and are a basis of `𝔪/𝔪²`, and distinct
coordinates generate distinct ideals (an element of `𝔪` generating the same ideal as `z_j` is a unit
multiple of `z_j`, so its class in `𝔪/𝔪²` is proportional to that of `z_j`; a basis has no two
proportional members).
-/

public section

universe u

open IsLocalRing Ideal AlgebraicGeometry

namespace AlgebraicGeometry

section RegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A regular local ring has a regular system of parameters indexed by `Fin n`, `n = dim R` — a
generating family of `𝔪` with `spanFinrank 𝔪 = dim R` members. -/
theorem exists_fin_span_eq_maximalIdeal (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    ∃ (n : ℕ) (z : Fin n → R),
      span (Set.range z) = maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal R))
  let e : ↥s ≃ Fin s.card := Fintype.equivFinOfCardEq (Fintype.card_coe s)
  refine ⟨s.card, fun i => ((e.symm i : ↥s) : R), ?_, ?_⟩
  · have hrange : Set.range (fun i => ((e.symm i : ↥s) : R)) = (s : Set R) := by
      rw [show (fun i => ((e.symm i : ↥s) : R)) = Subtype.val ∘ e.symm from rfl, Set.range_comp,
        Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe_subtype]
      rfl
    rw [hrange]
    exact hspan
  · rw [hcard]
    exact IsRegularLocalRing.spanFinrank_maximalIdeal

variable {n : ℕ} {z : Fin n → R}

/-- The members of a regular system of parameters lie in `𝔪` and outside `𝔪²` (Kollár's
"`z_1, …, z_n ∈ 𝔪_x`"). -/
theorem mem_maximalIdeal_and_notMem_sq_of_span_eq
    (hz : span (Set.range z) = maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R) (i : Fin n) :
    z i ∈ maximalIdeal R ∧ z i ∉ maximalIdeal R ^ 2 :=
  ⟨x_mem_maximalIdeal_of_span_eq z hz.1.symm i,
    notMem_sq_of_span_eq z hz.1.symm hz.2 i⟩

/-- Distinct members of a regular system of parameters generate distinct ideals — their classes form
a basis of `𝔪/𝔪²`, and two members generating the same ideal have proportional classes. -/
theorem span_singleton_ne_of_ne
    (hz : span (Set.range z) = maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R) {i j : Fin n}
    (hij : i ≠ j) : span {z i} ≠ span {z j} := by
  intro heq
  obtain ⟨b, hb⟩ := exists_basis_cotangentSpace_of_span_eq z hz.1.symm hz.2
  have hmem : z i ∈ span {z j} := heq ▸ Ideal.mem_span_singleton_self (z i)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
  have hzi := x_mem_maximalIdeal_of_span_eq z hz.1.symm i
  have hzj := x_mem_maximalIdeal_of_span_eq z hz.1.symm j
  -- the classes: `b i = residue u • b j`
  have hcot : b i = residue R u • b j := by
    rw [hb i, hb j, ← ResidueField.algebraMap_eq, algebraMap_smul (ResidueField R) u,
      ← LinearMap.map_smul]
    congr 1
    ext
    exact hu.symm
  have := congrArg (fun v => b.repr v i) hcot
  simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
    ite_eq_right (Ne.symm hij), smul_zero] at this
  exact one_ne_zero this

end RegularLocalRing

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- At every point of a scheme smooth over `k` there are local coordinates in the sense of
[Kol07, Definition 24], a regular system of parameters of `𝒪_{X,x}`. -/
theorem exists_fin_span_eq_maximalIdeal_stalk (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) :=
  have := isRegularLocalRing_stalk f x
  exists_fin_span_eq_maximalIdeal (X.presheaf.stalk x)

end Scheme

end AlgebraicGeometry
