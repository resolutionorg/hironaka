/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.Sequence.Remark33Iso
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUp.Transform.TransformIso
import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional
import Hironaka.Scheme.BlowUpSequence.Remark33Iso
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Remark 33 on the affine model: the exceptional divisors

[Kol07, Remark 33]: under the isomorphism `e : X_2 ≅ X_2'` of
`HironakaExamples/Sequence/Remark33Iso.lean`, the exceptional divisors are interchanged,
`E_0' ↔ E_1` and `E_1' ↔ E_0`, where on `X_2 = B_{C'} B_p 𝔸³` the divisors are `E_1 = π_1⁻¹(C')` and
the birational transform of `E_0 = π_0⁻¹(p)`, and on `X_2' = B_D B_C 𝔸³` they are `E_1' = σ_1⁻¹(D)`
and the birational transform of `E_0' = σ_0⁻¹(C)`. The main result is `exists_iso_last_exceptional`.

**Only the compatibility `e ≫ Σ = Π` is used.** Write `F := π_1⁻¹ E_0 = Π⁻¹(p)` and
`E_1 = π_1⁻¹ C'` on `X_2`. Since `D = σ_0⁻¹(p)`, the pullback of `E_1' = σ_1⁻¹ D` along `e` is
`Π⁻¹(p) = F`, and the pullback of the total transform `σ_1⁻¹ σ_0⁻¹ C` is
`Π⁻¹(C) = π_1⁻¹(E_0 · C') = F · E_1` (the key identity `curve_comap_eq`). So the two assertions are

* `F.saturate E_1 = F`: the total transform of `E_0` under the blow-up of `C'` is already its
  birational transform (`C' ⊄ E_0`), and
* `(F · E_1).saturate F = E_1`: the birational transform of `E_0' = σ_0⁻¹ C` is `E_1`.

Both follow from the colon identities `(F : E_1) = F` and `(E_1 : F) = E_1` (the two divisors
share no component) together with `(F · E_1 : F) = E_1` for the invertible `F`, and the one-step
saturation lemma `saturate_eq_self_of_colon_eq`. The colon identities are checked on a cover of
`X_2`: over the `x`- and `y`-charts of `X_1` the ideal `C'` is the unit ideal, so the second
blow-up is an isomorphism there and `E_1 = ⊤`; over the `z`-chart, `C' = V(x, y)` and `E_0 = V(z)`
once more, so the second blow-up is `B_{V(x,y)} 𝔸³`, whose two charts carry `E_1 = (x_j)` and
`F = (z)`, two distinct coordinate hyperplanes, with `(x_j) : (z) = (x_j)` and `(z) : (x_j) = (z)`
because both are prime ideals of `k[x, y, z]` not containing the other's generator. The cover of
`X_2` by the blow-ups of the restrictions `C'|_{U_j}` comes from the pullback square
`isPullback_blowUpMap` along the open immersions `U_j → X_1`.

Invertibility of `F` is free from the isomorphism: `F` is the pullback along `e` of the
exceptional divisor `σ_1⁻¹ D` of `X_2'`.

The general lemmas (inequalities on covers by open immersions, colons along open immersions,
blow-ups of restrictions to opens) are in the library module
`Hironaka/Scheme/BlowUpSequence/Remark33Exceptional.lean`.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme.IdealSheafData Scheme.Hom CoordinateSubspace
  affineBlowUpAlgebra MvPolynomial

namespace Hironaka.Sequence.Remark33

open AlgebraicGeometry.Remark33

/-! ### Two coordinate hyperplanes of `𝔸³` share no component -/

section Ring

variable (k : Type u) [Field k]

/-- `(x_a)` is a prime ideal of `k[x, y, z]`. -/
theorem isPrime_span_X (a : Fin 3) : (Ideal.span {(X a : MvPolynomial (Fin 3) k)}).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero a)).mpr X_prime

/-- `x_b ∉ (x_a)` for `a ≠ b`. -/
theorem X_notMem_span_X {a b : Fin 3} (h : a ≠ b) :
    (X b : MvPolynomial (Fin 3) k) ∉ Ideal.span {(X a : MvPolynomial (Fin 3) k)} := by
  rw [Ideal.mem_span_singleton, X_dvd_X]
  exact h

/-- Two distinct coordinate hyperplanes share no component: `(x_a) : (x_b) = (x_a)`. -/
theorem colon_span_X_span_X {a b : Fin 3} (h : a ≠ b) :
    (Ideal.span {(X a : MvPolynomial (Fin 3) k)}).colon
        (↑(Ideal.span {(X b : MvPolynomial (Fin 3) k)}) : Set (MvPolynomial (Fin 3) k)) =
      Ideal.span {X a} := by
  refine le_antisymm (fun f hf => ?_) fun f hf => ?_
  · rw [Ideal.colon_span, Submodule.mem_colon_singleton, smul_eq_mul] at hf
    exact ((isPrime_span_X k a).mem_or_mem hf).resolve_right (X_notMem_span_X k h)
  · exact Submodule.mem_colon.mpr fun p _ => Ideal.mul_mem_right p _ hf

/-- The chart substitution of the `x_j`-chart of `B_{V(x,y)} 𝔸³` (`j < 2`): `x_i ↦ x_i x_j` for
`i < 2`, `i ≠ j`; `z ↦ z`. -/
noncomputable abbrev subst2 (j : Fin 3) : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  chartSubst k (center 3 2) j

theorem subst2_X (j i : Fin 3) :
    subst2 k j (X i) = if i.val < 2 ∧ i ≠ j then X i * X j else X i :=
  chartSubst_X k 3 2 j i

/-- In the chart of `x_j` (`j < 2`) of `B_{V(x,y)} 𝔸³`, the ideal `(x, y)` becomes `(x_j)`: the
exceptional ideal. -/
theorem map_centerIdeal_two_subst2 (j : Fin 3) (hj : j.val < 2) :
    (centerIdeal k 3 2).map (subst2 k j) = Ideal.span {X j} := by
  apply le_antisymm
  · rw [centerIdeal, coordinateIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, subst2_X]
    split_ifs with h
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · have hi' : i.val < 2 := hi
      have hij : i = j := by
        by_contra hne
        exact h ⟨hi', hne⟩
      subst hij
      exact Ideal.mem_span_singleton_self _
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have h : (X j : MvPolynomial (Fin 3) k) = subst2 k j (X j) := by
      rw [subst2_X, ite_eq_right (fun h => h.2 rfl)]
    rw [h]
    exact Ideal.mem_map_of_mem _ (X_mem_centerIdeal k 3 2 hj)

/-- The plane `z = 0` is untouched by the charts of `B_{V(x,y)} 𝔸³`. -/
theorem map_span_X_two_subst2 (j : Fin 3) :
    (Ideal.span {(X 2 : MvPolynomial (Fin 3) k)}).map (subst2 k j) = Ideal.span {X 2} := by
  rw [Ideal.map_span, Set.image_singleton, subst2_X, ite_eq_right]
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- In the `z`-chart of `B_p 𝔸³`, the ideal `(x, y)` is `(z) · (x, y)` and its `(z)`-colon is
`(x, y)` again. -/
theorem colon_totalChart_excChart_two :
    (totalChart k 2).colon (↑(excChart k 2) : Set (MvPolynomial (Fin 3) k)) =
      centerIdeal k 3 2 := by
  rw [totalChart, excChart, map_centerIdeal_two_subst_two, map_centerIdeal_three_subst,
    Ideal.colon_span]
  ext f
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm f (X 2), Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨q, hq, hzq⟩
    have hz : (X 2 : MvPolynomial (Fin 3) k) ≠ 0 := X_ne_zero _
    rwa [mul_left_cancel₀ hz hzq] at hq
  · intro hf
    exact ⟨f, hf, rfl⟩

/-- In the `x`- and `y`-charts of `B_p 𝔸³` the ideal `(x, y)` is the exceptional ideal itself,
whose colon by itself is the unit ideal. -/
theorem colon_totalChart_excChart_of_lt (j : Fin 3) (hj : j.val < 2) :
    (totalChart k j).colon (↑(excChart k j) : Set (MvPolynomial (Fin 3) k)) = ⊤ := by
  rw [totalChart, excChart, map_centerIdeal_two_subst_of_lt k j hj, map_centerIdeal_three_subst,
    eq_top_iff]
  intro f _
  exact Submodule.mem_colon.mpr fun p hp => Ideal.mul_mem_left _ f hp

end Ring

/-! ### On `B_{V(x,y)} 𝔸³`: the exceptional divisor and the plane `z = 0` share no component -/

section Piece

variable (k : Type u) [Field k]

/-- The plane `z = 0` as an ideal sheaf on `Spec k[x, y, z]`: over the `z`-chart of `B_p 𝔸³` it is
the exceptional divisor `E_0`. -/
noncomputable abbrev Zc : (Spec (.of (MvPolynomial (Fin 3) k))).IdealSheafData :=
  specIdealSheaf (Ideal.span {(X 2 : MvPolynomial (Fin 3) k)})

theorem isInvertible_specIdealSheaf_span_X (a : Fin 3) :
    (specIdealSheaf (Ideal.span {(X a : MvPolynomial (Fin 3) k)})).IsInvertible :=
  isInvertible_specIdealSheaf_span_singleton (mem_nonZeroDivisors_of_ne_zero (X_ne_zero a))

/-- The charts of `B_{V(x,y)} 𝔸³` through a chosen isomorphism with the model blow-up. -/
noncomputable abbrev chart2 (e : blowUp (Ys k) ≅ modelBlowUp k 3 2)
    (j : {j : Fin 3 // j.val < 2}) : Spec (.of (MvPolynomial (Fin 3) k)) ⟶ blowUp (Ys k) :=
  modelChart k 3 2 j.1 j.2 ≫ e.inv

theorem iSup_opensRange_chart2 (e : blowUp (Ys k) ≅ modelBlowUp k 3 2) :
    ⨆ j, (chart2 k e j).opensRange = ⊤ := by
  have h2 : ⨆ j : {j : Fin 3 // j.val < 2}, (modelChart k 3 2 j.1 j.2).opensRange = ⊤ :=
    (iSup_subtype' (p := fun j : Fin 3 => j.val < 2)
      (f := fun j hj => (modelChart k 3 2 j hj).opensRange)).symm.trans
      (iSup_opensRange_modelChart k 3 2)
  simp only [chart2, Scheme.Hom.opensRange_comp]
  rw [← Scheme.Hom.image_iSup, h2, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.opensRange_of_isIso]

theorem chart2_π (e : blowUp (Ys k) ≅ modelBlowUp k 3 2)
    (he : e.hom ≫ affineBlowUp.π (centerIdeal k 3 2) = blowUpπ (Ys k))
    (j : {j : Fin 3 // j.val < 2}) :
    chart2 k e j ≫ blowUpπ (Ys k) = Spec.map (CommRingCat.ofHom (subst2 k j.1).toRingHom) := by
  rw [← he]
  simp only [chart2, Category.assoc, Iso.inv_hom_id_assoc]
  exact modelChart_π k 3 2 j.1 j.2

theorem Zc_comap_chart2 (e : blowUp (Ys k) ≅ modelBlowUp k 3 2)
    (he : e.hom ≫ affineBlowUp.π (centerIdeal k 3 2) = blowUpπ (Ys k))
    (j : {j : Fin 3 // j.val < 2}) :
    ((Zc k).comap (blowUpπ (Ys k))).comap (chart2 k e j) = Zc k := by
  rw [← comap_comp, chart2_π k e he j]
  exact (comap_ofIdealTop_Spec_map _ _).trans
    (congrArg specIdealSheaf (map_span_X_two_subst2 k j.1))

theorem Ys_comap_chart2 (e : blowUp (Ys k) ≅ modelBlowUp k 3 2)
    (he : e.hom ≫ affineBlowUp.π (centerIdeal k 3 2) = blowUpπ (Ys k))
    (j : {j : Fin 3 // j.val < 2}) :
    ((Ys k).comap (blowUpπ (Ys k))).comap (chart2 k e j) =
      specIdealSheaf (Ideal.span {(X j.1 : MvPolynomial (Fin 3) k)}) := by
  rw [← comap_comp, chart2_π k e he j]
  exact (comap_ofIdealTop_Spec_map _ _).trans
    (congrArg specIdealSheaf (map_centerIdeal_two_subst2 k j.1 j.2))

/-- On `B_J 𝔸³` with `J = V(x, y)` and `A = V(z)`: the total transforms of `A` and `J` share no
component, in the form of both colon identities. Stated for `J` and `A` given by equations so
that it applies to the restrictions of the second blow-up's data. -/
theorem colon_comap_π_eq_of_eq {J A : (Spec (.of (MvPolynomial (Fin 3) k))).IdealSheafData}
    (hJ : J = Ys k) (hA : A = Zc k) (hAinv : (A.comap (blowUpπ J)).IsInvertible) :
    (A.comap (blowUpπ J)).colon (J.comap (blowUpπ J)) = A.comap (blowUpπ J) ∧
      (J.comap (blowUpπ J)).colon (A.comap (blowUpπ J)) = J.comap (blowUpπ J) := by
  subst hJ hA
  obtain ⟨e, he⟩ := exists_iso_blowUp_coordinateSubspace k 3 2
  have hJinv : ((Ys k).comap (blowUpπ (Ys k))).IsInvertible := blowUp.isInvertible_comap_π _
  have hne : ∀ j : {j : Fin 3 // j.val < 2}, (2 : Fin 3) ≠ j.1 := fun j h => by
    have := j.2
    rw [← h] at this
    exact absurd this (by decide)
  refine ⟨le_antisymm ?_ (le_colon_self _ _), le_antisymm ?_ (le_colon_self _ _)⟩
  · refine le_of_comap_le_of_iSup_eq_top (chart2 k e) (iSup_opensRange_chart2 k e) fun j => ?_
    rw [comap_colon_of_isOpenImmersion _ _ hJinv, Zc_comap_chart2 k e he j,
      Ys_comap_chart2 k e he j,
      specIdealSheaf_colon _ _ (isInvertible_specIdealSheaf_span_X k j.1), specIdealSheaf_le_iff]
    exact (colon_span_X_span_X k (hne j)).le
  · refine le_of_comap_le_of_iSup_eq_top (chart2 k e) (iSup_opensRange_chart2 k e) fun j => ?_
    rw [comap_colon_of_isOpenImmersion _ _ hAinv, Ys_comap_chart2 k e he j,
      Zc_comap_chart2 k e he j,
      specIdealSheaf_colon _ _ (isInvertible_specIdealSheaf_span_X k 2), specIdealSheaf_le_iff]
    exact (colon_span_X_span_X k (hne j).symm).le

/-- The trivial case: over a chart where the center is the unit ideal, both colon identities hold
for free. -/
theorem colon_comap_π_top {J A : (Spec (.of (MvPolynomial (Fin 3) k))).IdealSheafData}
    (hJ : J = ⊤) :
    (A.comap (blowUpπ J)).colon (J.comap (blowUpπ J)) = A.comap (blowUpπ J) ∧
      (J.comap (blowUpπ J)).colon (A.comap (blowUpπ J)) = J.comap (blowUpπ J) := by
  subst hJ
  rw [comap_top, colon_top]
  exact ⟨rfl, top_le_iff.mp (le_colon_self _ _)⟩

end Piece

/-! ### On `X_2 = B_{C'} B_p 𝔸³`: `F = π_1⁻¹ E_0` and `E_1 = π_1⁻¹ C'` share no component -/

section Second

variable (k : Type u) [Field k]

/-- The exceptional divisor `E_0` of the point blow-up, as an ideal sheaf on `blowUp (Zs k)`. -/
noncomputable abbrev Ezero : (blowUp (Zs k)).IdealSheafData := (Zs k).comap (blowUpπ (Zs k))

/-- The birational transform `C'` of the `z`-axis under the point blow-up. -/
noncomputable abbrev Cprime : (blowUp (Zs k)).IdealSheafData :=
  (Ys k).strictTransformAlong (blowUpπ (Zs k)) (Ezero k)

/-- The total transform `F = π_1⁻¹ E_0` on `X_2 = B_{C'} X_1`. -/
noncomputable abbrev Fzero : (blowUp (Cprime k)).IdealSheafData :=
  (Ezero k).comap (blowUpπ (Cprime k))

/-- The exceptional divisor `E_1 = π_1⁻¹ C'` of the second blow-up. -/
noncomputable abbrev Eone : (blowUp (Cprime k)).IdealSheafData :=
  (Cprime k).comap (blowUpπ (Cprime k))

variable (e₀ : blowUp (Zs k) ≅ M k)

/-- The three charts of `X_1 = B_p 𝔸³`, through a chosen isomorphism with the model. -/
noncomputable abbrev u (j : Fin 3) : Spec (.of (MvPolynomial (Fin 3) k)) ⟶ blowUp (Zs k) :=
  chart k j ≫ e₀.inv

theorem iSup_opensRange_u : ⨆ j, (u k e₀ j).opensRange = ⊤ := by
  simp only [u, Scheme.Hom.opensRange_comp]
  rw [← Scheme.Hom.image_iSup, iSup_opensRange_chart k, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.opensRange_of_isIso]

/-- The blow-ups of the restrictions `C'|_{U_j}` cover `X_2`. -/
theorem exists_blowUpMap_u_eq (x : blowUp (Cprime k)) :
    ∃ (j : Fin 3) (y : blowUp ((Cprime k).comap (u k e₀ j))),
      blowUpMap (u k e₀ j) (Cprime k) y = x := by
  have hx : blowUpπ (Cprime k) x ∈ (⊤ : (blowUp (Zs k)).Opens) := trivial
  rw [← iSup_opensRange_u k e₀] at hx
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hj
  obtain ⟨z, hz⟩ := exists_blowUpMap_eq (u k e₀ j) (Cprime k) x y hy.symm
  exact ⟨j, z, hz⟩

theorem u_π (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) (j : Fin 3) :
    u k e₀ j ≫ blowUpπ (Zs k) = chart k j ≫ πm k := by
  rw [← he₀]
  simp only [u, Category.assoc, Iso.inv_hom_id_assoc]

theorem Ezero_comap_u (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) (j : Fin 3) :
    (Ezero k).comap (u k e₀ j) = specIdealSheaf (excChart k j) := by
  rw [Ezero, ← comap_comp, u_π k e₀ he₀ j, comap_comp]
  exact Em_comap_chart k j

/-- The restriction of `C'` to the chart of `x_j`, as the chart ideal `((x, y)·𝒪 : E_0)`. -/
theorem Cprime_comap_u (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) (j : Fin 3) :
    (Cprime k).comap (u k e₀ j) =
      specIdealSheaf ((totalChart k j).colon (↑(excChart k j) : Set (MvPolynomial (Fin 3) k))) := by
  have h1 : Cprime k = ((Im k).colon (Em k)).comap e₀.hom := by
    rw [← strictTransformAlong_πm_eq, Cprime, strictTransformAlong, strictTransformAlong,
      comap_saturate_of_isIso, ← comap_comp, ← comap_comp, he₀]
  rw [h1, ← comap_comp, u, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    comap_colon_of_isOpenImmersion _ _ (Em_isInvertible k), Im_comap_chart, Em_comap_chart,
    specIdealSheaf_colon _ _ (excChart_isInvertible k j)]

/-- Over the `z`-chart, `C'` is the `z`-axis `V(x, y)` again. -/
theorem Cprime_comap_u_two (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) :
    (Cprime k).comap (u k e₀ 2) = Ys k := by
  rw [Cprime_comap_u k e₀ he₀ 2, colon_totalChart_excChart_two]

/-- Over the `x`- and `y`-charts, `C'` is the unit ideal: the birational transform misses them. -/
theorem Cprime_comap_u_of_lt (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) (j : Fin 3)
    (hj : j.val < 2) : (Cprime k).comap (u k e₀ j) = ⊤ := by
  rw [Cprime_comap_u k e₀ he₀ j, colon_totalChart_excChart_of_lt k j hj]
  exact specIdealSheaf_top

theorem Fzero_comap_blowUpMap (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) (j : Fin 3) :
    (Fzero k).comap (blowUpMap (u k e₀ j) (Cprime k)) =
      (specIdealSheaf (excChart k j)).comap (blowUpπ ((Cprime k).comap (u k e₀ j))) := by
  rw [Fzero, ← comap_comp, blowUpMap_π, comap_comp (Ezero k) (blowUpπ _) (u k e₀ j),
    Ezero_comap_u k e₀ he₀ j]

theorem Eone_comap_blowUpMap (j : Fin 3) :
    (Eone k).comap (blowUpMap (u k e₀ j) (Cprime k)) =
      ((Cprime k).comap (u k e₀ j)).comap (blowUpπ ((Cprime k).comap (u k e₀ j))) := by
  rw [Eone, ← comap_comp, blowUpMap_π, comap_comp (Cprime k) (blowUpπ _) (u k e₀ j)]

theorem specIdealSheaf_excChart_two : specIdealSheaf (excChart k 2) = Zc k :=
  congrArg specIdealSheaf (map_centerIdeal_three_subst k 2)

/-- `(F : E_1) = F` on `X_2`. -/
theorem colon_Fzero_Eone (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) (hF : (Fzero k).IsInvertible) :
    (Fzero k).colon (Eone k) = Fzero k := by
  refine le_antisymm ?_ (le_colon_self _ _)
  refine le_of_comap_le_of_forall_exists (fun j => blowUpMap (u k e₀ j) (Cprime k))
    (exists_blowUpMap_u_eq k e₀) fun j => ?_
  rw [comap_colon_of_isOpenImmersion' _ _ (blowUp.isInvertible_comap_π (Cprime k)),
    Fzero_comap_blowUpMap k e₀ he₀ j, Eone_comap_blowUpMap k e₀ j]
  by_cases hj : j.val < 2
  · exact (colon_comap_π_top k (Cprime_comap_u_of_lt k e₀ he₀ j hj)).1.le
  · have h2 : j = 2 := by
      apply Fin.ext
      have := j.isLt
      change j.val = 2
      omega
    subst h2
    have hinv : ((specIdealSheaf (excChart k 2)).comap
        (blowUpπ ((Cprime k).comap (u k e₀ 2)))).IsInvertible := by
      rw [← Fzero_comap_blowUpMap k e₀ he₀ 2]
      exact hF.comap_of_isOpenImmersion _
    exact (colon_comap_π_eq_of_eq k (Cprime_comap_u_two k e₀ he₀)
      (specIdealSheaf_excChart_two k) hinv).1.le

/-- `(E_1 : F) = E_1` on `X_2`. -/
theorem colon_Eone_Fzero (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) (hF : (Fzero k).IsInvertible) :
    (Eone k).colon (Fzero k) = Eone k := by
  refine le_antisymm ?_ (le_colon_self _ _)
  refine le_of_comap_le_of_forall_exists (fun j => blowUpMap (u k e₀ j) (Cprime k))
    (exists_blowUpMap_u_eq k e₀) fun j => ?_
  rw [comap_colon_of_isOpenImmersion' _ _ hF, Fzero_comap_blowUpMap k e₀ he₀ j,
    Eone_comap_blowUpMap k e₀ j]
  by_cases hj : j.val < 2
  · exact (colon_comap_π_top k (Cprime_comap_u_of_lt k e₀ he₀ j hj)).2.le
  · have h2 : j = 2 := by
      apply Fin.ext
      have := j.isLt
      change j.val = 2
      omega
    subst h2
    have hinv : ((specIdealSheaf (excChart k 2)).comap
        (blowUpπ ((Cprime k).comap (u k e₀ 2)))).IsInvertible := by
      rw [← Fzero_comap_blowUpMap k e₀ he₀ 2]
      exact hF.comap_of_isOpenImmersion _
    exact (colon_comap_π_eq_of_eq k (Cprime_comap_u_two k e₀ he₀)
      (specIdealSheaf_excChart_two k) hinv).2.le

/-- The total transform of `E_0` under the blow-up of `C'` is its birational transform:
`F.saturate E_1 = F`. -/
theorem saturate_Fzero_Eone (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k))
    (hF : (Fzero k).IsInvertible) : (Fzero k).saturate (Eone k) = Fzero k :=
  saturate_eq_self_of_colon_eq (I := Fzero k) (K := Eone k) (colon_Fzero_Eone k e₀ he₀ hF)

/-- The birational transform of `F · E_1` along `F` is `E_1`: `(F · E_1).saturate F = E_1`
(`(F · E_1 : F) = E_1` for the invertible `F`). -/
theorem saturate_mul_Fzero_Eone (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k))
    (hF : (Fzero k).IsInvertible) : (Fzero k * Eone k).saturate (Fzero k) = Eone k := by
  have hcol := colon_Eone_Fzero k e₀ he₀ hF
  have h1 : (Fzero k * Eone k).colon (Fzero k) = Eone k := by
    have := colon_pow_eq_of_mul_eq (I := Fzero k * Eone k) hF 1 (Eone k) (by rw [pow_one])
    rwa [pow_one] at this
  have h2 : ∀ i : ℕ, (Eone k).colon (Fzero k ^ i) = Eone k := by
    intro i
    induction i with
    | zero => rw [pow_zero, one_eq_top, colon_top]
    | succ i ih => rw [pow_succ', ← colon_colon, hcol, ih]
  refine le_antisymm ?_ ?_
  · rw [saturate]
    refine iSup_le fun i => ?_
    cases i with
    | zero =>
      rw [pow_zero, one_eq_top, colon_top]
      exact (mul_comm _ _).le.trans (mul_le_self_left _ _)
    | succ i => rw [pow_succ', ← colon_colon, h1, h2]
  · have := colon_pow_le_saturate (Fzero k * Eone k) (Fzero k) 1
    rwa [pow_one, h1] at this

/-- `F` is invertible: it is the pullback along the isomorphism `e` of the exceptional divisor of
`X_2' = B_D B_C 𝔸³`. -/
theorem isInvertible_Fzero_of_iso
    (e : blowUp (Cprime k) ≅ blowUp ((Zs k).comap (blowUpπ (Ys k))))
    (he : e.hom ≫ blowUpπ ((Zs k).comap (blowUpπ (Ys k))) ≫ blowUpπ (Ys k) =
      blowUpπ (Cprime k) ≫ blowUpπ (Zs k)) :
    (Fzero k).IsInvertible := by
  have h : Fzero k = (((Zs k).comap (blowUpπ (Ys k))).comap
      (blowUpπ ((Zs k).comap (blowUpπ (Ys k))))).comap e.hom := by
    rw [Fzero, Ezero, ← comap_comp, ← he, comap_comp, comap_comp]
  rw [h]
  exact (blowUp.isInvertible_comap_π _).comap_of_isOpenImmersion e.hom

/-- Under any isomorphism `e : X_2 ≅ X_2'` over `𝔸³` (stated for the coordinate subspaces `Zs`
and `Ys`), the birational transform of `E_0' = σ_0⁻¹ C` pulls back to `E_1`, and `E_1' = σ_1⁻¹ D`
pulls back to the birational transform of `E_0`. -/
theorem divisors_matched_aux
    (e : blowUp (Cprime k) ≅ blowUp ((Zs k).comap (blowUpπ (Ys k))))
    (he : e.hom ≫ blowUpπ ((Zs k).comap (blowUpπ (Ys k))) ≫ blowUpπ (Ys k) =
      blowUpπ (Cprime k) ≫ blowUpπ (Zs k)) :
    ((((Ys k).comap (blowUpπ (Ys k))).comap (blowUpπ ((Zs k).comap (blowUpπ (Ys k))))).saturate
        (((Zs k).comap (blowUpπ (Ys k))).comap
          (blowUpπ ((Zs k).comap (blowUpπ (Ys k)))))).comap e.hom = Eone k ∧
      (((Zs k).comap (blowUpπ (Ys k))).comap (blowUpπ ((Zs k).comap (blowUpπ (Ys k))))).comap
          e.hom = (Fzero k).saturate (Eone k) := by
  obtain ⟨e₀, he₀⟩ := exists_iso_blowUp_coordinateSubspace k 3 3
  have hF := isInvertible_Fzero_of_iso k e he
  have hFe : (((Zs k).comap (blowUpπ (Ys k))).comap
      (blowUpπ ((Zs k).comap (blowUpπ (Ys k))))).comap e.hom = Fzero k := by
    rw [← comap_comp, ← comap_comp, Category.assoc, he, comap_comp]
  have hCe : (((Ys k).comap (blowUpπ (Ys k))).comap
      (blowUpπ ((Zs k).comap (blowUpπ (Ys k))))).comap e.hom = Fzero k * Eone k := by
    rw [← comap_comp, ← comap_comp, Category.assoc, he, comap_comp, coordinateSubspace_comap_eq,
      comap_mul]
  refine ⟨?_, ?_⟩
  · rw [comap_saturate_of_isIso, hCe, hFe]
    exact saturate_mul_Fzero_Eone k e₀ he₀ hF
  · rw [hFe, saturate_Fzero_Eone k e₀ he₀ hF]

/-- The matching of the exceptional divisors for centers `p`, `C` given by equations, in the
shape the recursive definitions of `BlowUpSequence` produce (the identity arms of `step` at
index `0`). -/
theorem divisors_matched {p C : (Spec (.of (MvPolynomial (Fin 3) k))).IdealSheafData}
    (hp : p = Zs k) (hC : C = Ys k)
    (e : blowUp (C.strictTransformAlong (blowUpπ p) (p.comap (blowUpπ p))) ≅
      blowUp (p.comap (blowUpπ C)))
    (he : e.hom ≫ (𝟙 _ ≫ blowUpπ (p.comap (blowUpπ C))) ≫ blowUpπ C =
      (𝟙 _ ≫ blowUpπ (C.strictTransformAlong (blowUpπ p) (p.comap (blowUpπ p)))) ≫
        blowUpπ p) :
    (((C.comap (𝟙 _ ≫ blowUpπ C)).comap (blowUpπ (p.comap (blowUpπ C)))).saturate
        ((p.comap (blowUpπ C)).comap (blowUpπ (p.comap (blowUpπ C))))).comap e.hom =
      (C.strictTransformAlong (blowUpπ p) (p.comap (blowUpπ p))).comap
        (𝟙 _ ≫ blowUpπ (C.strictTransformAlong (blowUpπ p) (p.comap (blowUpπ p)))) ∧
    ((p.comap (blowUpπ C)).comap (𝟙 _ ≫ blowUpπ (p.comap (blowUpπ C)))).comap e.hom =
      ((p.comap (𝟙 _ ≫ blowUpπ p)).comap
          (blowUpπ (C.strictTransformAlong (blowUpπ p) (p.comap (blowUpπ p))))).saturate
        ((C.strictTransformAlong (blowUpπ p) (p.comap (blowUpπ p))).comap
          (blowUpπ (C.strictTransformAlong (blowUpπ p) (p.comap (blowUpπ p))))) := by
  subst hp hC
  simp only [Category.id_comp] at he ⊢
  exact divisors_matched_aux k e he

/-- [Kol07, Remark 33]: the isomorphism `X_2 ≅ X_2'` over `𝔸³` matches the exceptional divisors,
`E_0' ↔ E_1` and `E_1' ↔ E_0`. -/
theorem exists_iso_last_exceptional :
    ∃ e : (seqPointCurve k).last ≅ (seqCurvePoint k).last,
      e.hom ≫ (seqCurvePoint k).composite = (seqPointCurve k).composite ∧
        (excFirstTransformCurvePoint k).comap e.hom = excSecondPointCurve k ∧
          (excSecondCurvePoint k).comap e.hom = excFirstTransformPointCurve k := by
  obtain ⟨e, he⟩ := exists_iso_last k
  exact ⟨e, he, divisors_matched k (point_eq_coordinateSubspace k)
    (curve_eq_coordinateSubspace k) e he⟩

end Second

end Hironaka.Sequence.Remark33
