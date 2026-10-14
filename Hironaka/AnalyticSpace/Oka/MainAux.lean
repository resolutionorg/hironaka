/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Oka.PolySection
public import Hironaka.AnalyticSpace.Coherent
import Hironaka.Analytic.Rueckert.Irreducible
import Hironaka.AnalyticSpace.CoherentLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# Auxiliary lemmas for the induction of Oka's theorem

Bookkeeping for `Hironaka.AnalyticSpace.Oka.Main`: membership in a finite infimum of open sets,
composed restrictions of sections and the agreement on a neighbourhood of two sections with the same
germ (`exists_res_eq_of_germ_eq`), the Weierstrass polynomial as the polynomial of a padded
coefficient list (`weierstrassList`, `polyOfCoeff_weierstrassList`), the regularity in `x_0` of the
factors of a finite product (`isRegularIn_of_mul` iterated), and the restriction of a row's relation
system to a smaller open set and back (`hasLocalGeneratorsOn_row_res`,
`hasLocalGeneratorsOn_row_of_res`). None of this is in the sources as a separate statement.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Manifold
open Analytic

universe u

namespace AnalyticSpace

section Opens

variable {X : Type*} [TopologicalSpace X]

/-- A point lying in every member of a finite family of opens lies in their infimum. -/
theorem mem_finset_inf_opens {ι : Type*} (s : Finset ι) (f : ι → Opens X) {x : X}
    (h : ∀ i ∈ s, x ∈ f i) : x ∈ s.inf f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, ← SetLike.mem_coe, Opens.coe_inf]
    exact ⟨h a (Finset.mem_insert_self a s), ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

theorem finset_inf_opens_le {ι : Type*} (s : Finset ι) (f : ι → Opens X) {i : ι} (hi : i ∈ s) :
    s.inf f ≤ f i :=
  Finset.inf_le hi

end Opens

section Restriction

variable {X : TopCat.{u}} (F : TopCat.Sheaf CommRingCat.{u} X)

/-- Restricting twice is restricting once. -/
theorem res_res_eq_res {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) (s : F.presheaf.obj (op U)) :
    F.presheaf.map (homOfLE hWV).op (F.presheaf.map (homOfLE hVU).op s) =
      F.presheaf.map (homOfLE (hWV.trans hVU)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- Two sections with the same germ at `x` agree after restriction to some open neighbourhood of
`x`. -/
theorem exists_res_eq_of_germ_eq {U : Opens X} {x : X} (hx : x ∈ U) (s t : F.presheaf.obj (op U))
    (h : F.presheaf.germ U x hx s = F.presheaf.germ U x hx t) :
    ∃ (W : Opens X) (hWU : W ≤ U) (_ : x ∈ W),
      F.presheaf.map (homOfLE hWU).op s = F.presheaf.map (homOfLE hWU).op t := by
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq F.presheaf x hx hx s t h
  refine ⟨W, iU.le, hxW, ?_⟩
  have e1 : iU = homOfLE iU.le := Subsingleton.elim _ _
  have e2 : iV = homOfLE iU.le := Subsingleton.elim _ _
  rwa [e1, e2] at hW

end Restriction

section WeierstrassList

variable {R : Type*} [CommRing R]

/-- The coefficient list of `weierstrassPolynomial e c` padded to length `d > e`:
`x_0^e + Σ_j c_j x_0^{e−1−j}` has coefficient `1` at `e`, `c_{e−1−t}` at `t < e`, and `0` above `e`.
-/
def weierstrassList (e : ℕ) (c : Fin e → R) (d : ℕ) : Fin d → R :=
  fun t => if h : (t : ℕ) < e then c ⟨e - 1 - t, by omega⟩ else if (t : ℕ) = e then 1 else 0

theorem polyOfCoeff_weierstrassList [Nontrivial R] {e d : ℕ} (he : e < d) (c : Fin e → R) :
    polyOfCoeff (weierstrassList e c d) = weierstrassPolynomial e c := by
  ext k
  rw [coeff_polyOfCoeff]
  by_cases hke : k < e
  · rw [dite_eq_left (by omega : k < d), weierstrassList, dite_eq_left hke,
      coeff_weierstrassPolynomial_of_lt _ _ hke]
  · by_cases hk : k = e
    · subst hk
      rw [dite_eq_left he, weierstrassList, dite_eq_right (lt_irrefl _), ite_eq_left rfl]
      have := (monic_weierstrassPolynomial (R := R) k c).coeff_natDegree
      rw [natDegree_weierstrassPolynomial] at this
      exact this.symm
    · have hgt : e < k := lt_of_le_of_ne (not_lt.mp hke) (Ne.symm hk)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [natDegree_weierstrassPolynomial]; exact hgt)]
      by_cases hkd : k < d
      · rw [dite_eq_left hkd]
        simp only [weierstrassList, dite_eq_right hke, ite_eq_right hk]
      · rw [dite_eq_right hkd]

/-- The list is natural in ring homomorphisms. -/
theorem map_weierstrassList {S : Type*} [CommRing S] (f : R →+* S) (e : ℕ) (c : Fin e → R) (d : ℕ)
    (t : Fin d) :
    f (weierstrassList e c d t) = weierstrassList e (fun j => f (c j)) d t := by
  unfold weierstrassList
  split_ifs <;> simp

end WeierstrassList

section Regular

variable {K : Type*} [RCLike K] {m : ℕ}

/-- The factors of an `x_0`-regular finite product are `x_0`-regular (`isRegularIn_of_mul`). -/
theorem exists_isRegularIn_of_prod {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries (Fin (m + 1)) K) {d : ℕ} (h : IsRegularIn (∏ i ∈ s, f i) d) {i : ι}
    (hi : i ∈ s) :
    ∃ d', IsRegularIn (f i) d' := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => exact absurd hi (Finset.notMem_empty _)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    obtain ⟨d₁, d₂, -, h₁, h₂⟩ := isRegularIn_of_mul h
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ⟨d₁, h₁⟩
    · exact ih h₂ hi'

end Regular

section Rows

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} X}

/-- Restricting a row's relation system to a smaller open. -/
theorem hasLocalGeneratorsOn_row_res {U W : Opens X} (hWU : W ≤ U) {p : ℕ}
    (g : Fin p → 𝒪.presheaf.obj (op U))
    (h : HasLocalGeneratorsOn 𝒪 U p fun y hy => relationSubmodule 𝒪 (fun _ : Fin 1 => g) y hy) :
    HasLocalGeneratorsOn 𝒪 W p fun y hy =>
      relationSubmodule 𝒪 (fun _ : Fin 1 => fun j => 𝒪.presheaf.map (homOfLE hWU).op (g j))
        y hy := by
  refine (h.mono hWU).congr fun y hy => ?_
  exact (relationSubmodule_res hWU (fun _ : Fin 1 => g) hy).symm

/-- Conversely, local generators for the restricted row at `x` are local generators for the row. -/
theorem hasLocalGeneratorsOn_row_of_res {U W : Opens X} (hWU : W ≤ U) {x : X} (hx : x ∈ W) {p : ℕ}
    (g : Fin p → 𝒪.presheaf.obj (op U))
    (h : HasLocalGeneratorsOn 𝒪 W p fun y hy =>
      relationSubmodule 𝒪 (fun _ : Fin 1 => fun j => 𝒪.presheaf.map (homOfLE hWU).op (g j))
        y hy) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_ : x ∈ V) (k : ℕ) (r : Fin k → Fin p → 𝒪.presheaf.obj (op V)),
      ∀ y (hy : y ∈ V), relationSubmodule 𝒪 (fun _ : Fin 1 => g) y (hVU hy) =
        Submodule.span (𝒪.presheaf.stalk y)
          (Set.range fun l => fun j => 𝒪.presheaf.germ V y hy (r l j)) := by
  obtain ⟨V, hVW, hxV, k, r, hr⟩ := h x hx
  refine ⟨V, hVW.trans hWU, hxV, k, r, fun y hy => ?_⟩
  have := hr y hy
  dsimp only at this
  rw [relationSubmodule_res hWU (fun _ : Fin 1 => g) (hVW hy)] at this
  exact this

end Rows

end AnalyticSpace
