/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.Snc.Coordinates
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Families of divisors with simple normal crossings at a point

[Kol07, Definition 24] at a point `x`, for a family `E : ι → X.IdealSheafData` of closed subschemes:
local coordinates `z : Fin n → 𝒪_{X,x}` (a regular system of parameters,
`Hironaka.Scheme.Snc.Coordinates`) and an injective assignment `c` of a coordinate to each component
through `x` with `(E i)_x = (z_{c(i)})`. The predicate `DivisorFamily.IsSncAt` is exactly this
data, so the lemmas here take the data as explicit hypotheses.

* Kollár's (1)–(2): a component not through `x` has stalk `⊤`
  (`stalkIdeal_eq_top_of_notMem_support`), a component through `x` has stalk `(z_j)`
  (`stalkIdeal_eq_top_or_exists_eq_span`).
* Kollár's (3): distinct components through `x` have distinct stalks (`stalkIdeal_ne_of_ne`, from
  `span_singleton_ne_of_ne`).
* Each component is a smooth divisor (`isSmoothDivisor_of_snc_data`): its generator `z_{c(i)}` lies
  in `𝔪_x ∖ 𝔪_x²`.
* The empty family, a single smooth divisor (complete its local generator to a regular system of
  parameters), and an injective reindexing of a family all have the snc data.
* The product of the stalks of all components is the monomial ideal `(∏_{i : x ∈ E i} z_{c(i)})`
  (`prod_stalkIdeal_eq_span`; [Hau14, Remark 3.16, Proposition 3.17, Remark 3.20]).
-/

public section

universe u

open AlgebraicGeometry IsLocalRing Ideal

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {ι : Type*} {E : ι → X.IdealSheafData} {x : X} {n : ℕ}
  {z : Fin n → X.presheaf.stalk x}

/-- Kollár (1)–(2): every component either misses `x` (stalk `⊤`) or has stalk `(z_j)` at `x`. -/
theorem stalkIdeal_eq_top_or_exists_eq_span (c : {i : ι // x ∈ (E i).support} → Fin n)
    (hc : ∀ i, (E i.1).stalkIdeal x = span {z (c i)}) (i : ι) :
    (E i).stalkIdeal x = ⊤ ∨ ∃ j : Fin n, (E i).stalkIdeal x = span {z j} := by
  by_cases hi : x ∈ (E i).support
  · exact Or.inr ⟨c ⟨i, hi⟩, hc ⟨i, hi⟩⟩
  · exact Or.inl (Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support (E i) hi)

/-- Kollár (3): distinct components through `x` have distinct stalks. -/
theorem stalkIdeal_ne_of_ne [IsRegularLocalRing (X.presheaf.stalk x)]
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (c : {i : ι // x ∈ (E i).support} → Fin n) (hcinj : Function.Injective c)
    (hc : ∀ i, (E i.1).stalkIdeal x = span {z (c i)}) {i i' : ι} (hi : x ∈ (E i).support)
    (hi' : x ∈ (E i').support) (hne : i ≠ i') : (E i).stalkIdeal x ≠ (E i').stalkIdeal x := by
  rw [hc ⟨i, hi⟩, hc ⟨i', hi'⟩]
  exact span_singleton_ne_of_ne hz fun h => hne (congrArg Subtype.val (hcinj h))

/-- Each component of a family with the snc data at every point of a regular scheme is a smooth
divisor: at `x ∈ E i` the generator `z_{c(i)}` lies in `𝔪_x ∖ 𝔪_x²`. -/
theorem isSmoothDivisor_of_snc_data (E : ι → X.IdealSheafData)
    (hreg : ∀ i, IsRegular (E i).subscheme)
    (h : ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      ∃ c : {i : ι // x ∈ (E i).support} → Fin n, Function.Injective c ∧
        ∀ i, (E i.1).stalkIdeal x = span {z (c i)})
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (i : ι) : IsSmoothDivisor (E i) := by
  refine ⟨hreg i, fun x hx => ?_⟩
  obtain ⟨n, z, hz, c, -, hc⟩ := h x
  have := hX x
  exact ⟨z (c ⟨i, hx⟩), (mem_maximalIdeal_and_notMem_sq_of_span_eq hz _).1,
    (mem_maximalIdeal_and_notMem_sq_of_span_eq hz _).2, hc ⟨i, hx⟩⟩

/-- The snc data transport along an injective reindexing (drop indices, keep the coordinates). -/
theorem exists_snc_data_of_injective {κ : Type*} {F : κ → X.IdealSheafData} (φ : κ → ι)
    (hφ : Function.Injective φ) (hF : ∀ j, F j = E (φ j))
    (c : {i : ι // x ∈ (E i).support} → Fin n) (hcinj : Function.Injective c)
    (hc : ∀ i, (E i.1).stalkIdeal x = span {z (c i)}) :
    ∃ c' : {j : κ // x ∈ (F j).support} → Fin n, Function.Injective c' ∧
      ∀ j, (F j.1).stalkIdeal x = span {z (c' j)} := by
  refine ⟨fun j => c ⟨φ j.1, by rw [← hF j.1]; exact j.2⟩, ?_, fun j => ?_⟩
  · intro j j' h
    have h' := hcinj h
    exact Subtype.ext (hφ (congrArg Subtype.val h'))
  · rw [hF j.1]
    exact hc ⟨φ j.1, by rw [← hF j.1]; exact j.2⟩

/-- The empty family has the snc data at every point of a regular scheme. -/
theorem exists_snc_data_of_isEmpty [IsEmpty ι] [IsRegularLocalRing (X.presheaf.stalk x)]
    (E : ι → X.IdealSheafData) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      ∃ c : {i : ι // x ∈ (E i).support} → Fin n, Function.Injective c ∧
        ∀ i, (E i.1).stalkIdeal x = span {z (c i)} := by
  obtain ⟨m, z, hz⟩ := exists_fin_span_eq_maximalIdeal (X.presheaf.stalk x)
  exact ⟨m, z, hz, fun i => isEmptyElim i.1, fun i => isEmptyElim i.1, fun i => isEmptyElim i.1⟩

/-- A family with a single component, a smooth divisor `D`, has the snc data at every point of a
regular scheme: at `x ∈ D` complete the local generator of `D` to a regular system of parameters; at
`x ∉ D` any regular system of parameters serves. -/
theorem exists_snc_data_of_unique [Unique ι] [IsRegularLocalRing (X.presheaf.stalk x)]
    (E : ι → X.IdealSheafData) (D : X.IdealSheafData) (hE : ∀ i, E i = D)
    (hD : IsSmoothDivisor D) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      ∃ c : {i : ι // x ∈ (E i).support} → Fin n, Function.Injective c ∧
        ∀ i, (E i.1).stalkIdeal x = span {z (c i)} := by
  by_cases hx : x ∈ D.support
  · obtain ⟨a, ha, ha2, hDa⟩ := hD.2 x hx
    obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast (X.presheaf.stalk x)
    obtain ⟨y, ⟨i₀, hi₀⟩, hspan⟩ :=
      exists_span_eq_maximalIdeal_of_notMem_sq hm.symm ha ha2
    refine ⟨m, y, ⟨hspan.symm, hm.symm⟩, fun _ => i₀,
      fun a b _ => Subtype.ext (Subsingleton.elim a.1 b.1), fun i => ?_⟩
    rw [hE, hDa, hi₀]
  · obtain ⟨m, y, hy⟩ := exists_fin_span_eq_maximalIdeal (X.presheaf.stalk x)
    have hempty : ∀ i : {i : ι // x ∈ (E i).support}, False := fun i => hx (hE i.1 ▸ i.2)
    exact ⟨m, y, hy, fun i => (hempty i).elim, fun i => (hempty i).elim, fun i => (hempty i).elim⟩

/-- The product of the stalks of all components — the ideal of the union of the components, taken as
a scheme — is the monomial ideal generated by `∏_{i : x ∈ E i} z_{c(i)}`; the components not through
`x` contribute the factor `⊤` ([Hau14, Remark 3.16, Proposition 3.17, Remark 3.20]). -/
theorem prod_stalkIdeal_eq_span [Fintype ι] [DecidablePred fun i : ι => x ∈ (E i).support]
    (c : {i : ι // x ∈ (E i).support} → Fin n)
    (hc : ∀ i, (E i.1).stalkIdeal x = span {z (c i)}) :
    ∏ i, (E i).stalkIdeal x = span {∏ i, z (c i)} := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : ι => x ∈ (E i).support)
    (fun i => (E i).stalkIdeal x)]
  have h2 : ∏ i : {i : ι // ¬ x ∈ (E i).support}, (E i.1).stalkIdeal x = 1 :=
    Finset.prod_eq_one fun i _ => by
      rw [Ideal.one_eq_top]
      exact Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ i.2
  rw [h2, mul_one, Finset.prod_congr rfl fun i _ => hc i]
  exact Ideal.prod_span_singleton _ _

end AlgebraicGeometry
