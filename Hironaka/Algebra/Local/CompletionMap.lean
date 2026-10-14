/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CoefficientField
public import Hironaka.Algebra.Local.Order
import Hironaka.Algebra.Local.CohenIso
import Mathlib.Combinatorics.Matroid.Init

/-!
# The map induced on maximal-adic completions by a local homomorphism

Kollár writes the chart map of a blow-up in power series, `f ↦ f(y₁y_r, …, y_{r-1}y_r, y_r, …, yₙ)`
[Kol07, Definition 60, (60.3)], which is the map induced on completions by the local
homomorphism `R → R'_{𝔪'}` from the base to the local ring of the chart.  Mathlib has the
functoriality of `AdicCompletion` in the module (`AdicCompletion.map`, same ring) and the
universal property of a completion for maps *into* it (`AdicCompletion.liftRingHom`: a
compatible family `R →+* S ⧸ Iⁿ` lifts to `R →+* AdicCompletion I S`), but not the ring map
`Â → B̂` induced by a local homomorphism `φ : A → B` between local rings.  This file builds it:
the level-`n` components `Â → A/𝔪_Aⁿ → B/𝔪_Bⁿ` (evaluation, then the quotient map of `φ`, which
exists because `φ(𝔪_A) ⊆ 𝔪_B`) form a compatible family, and `liftRingHom` assembles them.

Properties: `completionMap φ` extends `φ` along the canonical maps (`completionMap_of`), its
level-`n` evaluation is the quotient map of `φ` (`evalₐ_completionMap`), it is characterized by
that (`completionMap_unique`), and it is local (`isLocalHom_completionMap`).  It is used for the
completed chart map (`Hironaka/Algebra/Local/ChartCompletion.lean`), for the transfer of orders
through the completion (`Hironaka/Algebra/Local/Lemma61.lean`, `ChartOrderFaithful.lean`) and for
the completion of the graph of an étale map (`Hironaka/Scheme/Smooth/GraphCompletion.lean`).
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing AdicCompletion

section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The evaluations of the completion at levels `m ≤ n` are compatible through the factor map
`R ⧸ Iⁿ → R ⧸ Iᵐ`. -/
theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  have hn : (I ^ n • ⊤ : Ideal R) ≤ I ^ n := le_of_eq (Ideal.mul_top _)
  have hm : (I ^ m • ⊤ : Ideal R) ≤ I ^ m := le_of_eq (Ideal.mul_top _)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := (I ^ n • ⊤ : Ideal R)) (x.val n)
  have hxm : x.val m = Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) y := by
    rw [← x.property hle, ← hy]
    exact transitionMap_ideal_mk I hle y
  rw [← factor_eval_eq_evalₐ I x hn, ← factor_eval_eq_evalₐ I x hm, eval_apply, eval_apply, ← hy,
    hxm]
  rfl

end

section

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  (φ : A →+* B) [IsLocalHom φ]

theorem maximalIdeal_pow_le_comap (n : ℕ) :
    maximalIdeal A ^ n ≤ (maximalIdeal B ^ n).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (map_maximalIdeal_le φ) n

/-- The level-`n` component of the induced map: `Â → A/𝔪_Aⁿ → B/𝔪_Bⁿ`. -/
noncomputable def completionMapLevel (n : ℕ) :
    AdicCompletion (maximalIdeal A) A →+* B ⧸ maximalIdeal B ^ n :=
  (Ideal.quotientMap (maximalIdeal B ^ n) φ (maximalIdeal_pow_le_comap φ n)).comp
    (evalₐ (maximalIdeal A) n : AdicCompletion (maximalIdeal A) A →+* A ⧸ maximalIdeal A ^ n)

theorem completionMapLevel_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp (completionMapLevel φ n) =
      completionMapLevel φ m := by
  ext x
  simp only [completionMapLevel, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) n x)
  have hym : evalₐ (maximalIdeal A) m x = Ideal.Quotient.mk (maximalIdeal A ^ m) y := by
    rw [← factorPow_evalₐ (maximalIdeal A) hle x, ← hy]
    exact Ideal.Quotient.factor_mk _ y
  rw [← hy, hym, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  exact Ideal.Quotient.factor_mk _ (φ y)

/-- The ring map `Â → B̂` induced on maximal-adic completions by the local homomorphism `φ`. -/
noncomputable def completionMap :
    AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B :=
  AdicCompletion.liftRingHom (maximalIdeal B) (completionMapLevel φ)
    fun hle => completionMapLevel_compat φ hle

theorem evalₐ_completionMap (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    evalₐ (maximalIdeal B) n (completionMap φ x) =
      Ideal.quotientMap (maximalIdeal B ^ n) φ (maximalIdeal_pow_le_comap φ n)
        (evalₐ (maximalIdeal A) n x) := by
  rw [completionMap, evalₐ_liftRingHom]
  rfl

/-- The induced map extends `φ`: `Â → B̂` composed with `A → Â` is `B → B̂` composed with `φ`. -/
theorem completionMap_of (a : A) :
    completionMap φ (of (maximalIdeal A) A a) = of (maximalIdeal B) B (φ a) := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_completionMap, evalₐ_of, evalₐ_of, Ideal.quotientMap_mk]

theorem completionMap_algebraMap (a : A) :
    completionMap φ (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
      algebraMap B (AdicCompletion (maximalIdeal B) B) (φ a) :=
  completionMap_of φ a

/-- Uniqueness: a ring map `Â → B̂` whose level-`n` evaluations are the quotient maps of `φ` is
the induced map. -/
theorem completionMap_unique
    (F : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
    (hF : ∀ n x, evalₐ (maximalIdeal B) n (F x) =
      Ideal.quotientMap (maximalIdeal B ^ n) φ (maximalIdeal_pow_le_comap φ n)
        (evalₐ (maximalIdeal A) n x)) :
    F = completionMap φ := by
  refine RingHom.ext fun x => ext_evalₐ fun n => ?_
  rw [hF, evalₐ_completionMap]

end

section

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]

/-- The induced map sends `𝔪_Âᵏ` into `𝔪_B̂ᵏ` (`𝔪_Â = 𝔪_A Â`, `𝔪_B̂ = 𝔪_B B̂`, and
`φ(𝔪_A) ⊆ 𝔪_B`). -/
theorem map_maximalIdeal_pow_completionMap_le (k : ℕ) :
    (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ k).map (completionMap φ) ≤
      maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ k := by
  rw [AdicCompletion.maximalIdeal_eq_map, AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
    ← Ideal.map_pow, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.comp_apply, completionMap_algebraMap]
  exact Ideal.mem_map_of_mem _ (maximalIdeal_pow_le_comap φ k ha)

theorem completionMap_mem_maximalIdeal_pow {x : AdicCompletion (maximalIdeal A) A} {k : ℕ}
    (hx : x ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ k) :
    completionMap φ x ∈ maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ k :=
  map_maximalIdeal_pow_completionMap_le φ k (Ideal.mem_map_of_mem _ hx)

/-- The induced map is a local homomorphism. -/
instance isLocalHom_completionMap : IsLocalHom (completionMap φ) := by
  refine ((local_hom_TFAE (completionMap φ)).out 1 3).mpr ?_
  simpa using map_maximalIdeal_pow_completionMap_le φ 1

/-- Orders do not decrease along the induced map. -/
theorem ordElem_le_ordElem_completionMap (x : AdicCompletion (maximalIdeal A) A) :
    ordElem x ≤ ordElem (completionMap φ x) := by
  refine ENat.forall_natCast_le_iff_le.mp fun k hk => ?_
  rw [← mem_maximalIdeal_pow_iff_le_ordElem] at hk ⊢
  exact completionMap_mem_maximalIdeal_pow φ hk

end

section Functoriality

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsLocalRing A] [IsLocalRing B]
  [IsLocalRing C]

theorem completionMap_congr {φ ψ : A →+* B} [IsLocalHom φ] [IsLocalHom ψ] (h : φ = ψ) :
    completionMap φ = completionMap ψ := by
  subst h
  rfl

theorem completionMap_id :
    completionMap (RingHom.id A) = RingHom.id (AdicCompletion (maximalIdeal A) A) := by
  symm
  refine completionMap_unique _ _ fun n x => ?_
  rw [RingHom.id_apply]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) n x)
  rw [← hy, Ideal.quotientMap_mk, RingHom.id_apply]

theorem completionMap_comp (φ : A →+* B) (ψ : B →+* C) [IsLocalHom φ] [IsLocalHom ψ] :
    completionMap (ψ.comp φ) = (completionMap ψ).comp (completionMap φ) := by
  symm
  refine completionMap_unique _ _ fun n x => ?_
  rw [RingHom.comp_apply, evalₐ_completionMap, evalₐ_completionMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) n x)
  rw [← hy, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, RingHom.comp_apply]

/-- A ring isomorphism is a local homomorphism (instance form of `isLocalHom_ringEquiv`). -/
instance instIsLocalHomRingEquivToRingHom (e : A ≃+* B) : IsLocalHom (e : A →+* B) :=
  isLocalHom_ringEquiv e

theorem completionMap_eq_id_of (φ : A →+* A) [IsLocalHom φ] (h : ∀ a, φ a = a) :
    completionMap φ = RingHom.id (AdicCompletion (maximalIdeal A) A) := by
  symm
  refine completionMap_unique _ _ fun n x => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) n x)
  rw [RingHom.id_apply, ← hy, Ideal.quotientMap_mk, h]

/-- An isomorphism of local rings induces an isomorphism of their completions. -/
noncomputable def completionEquiv (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B :=
  RingEquiv.ofRingHom (completionMap (e : A →+* B)) (completionMap (e.symm : B →+* A))
    (by rw [← completionMap_comp]; exact completionMap_eq_id_of _ fun b => e.apply_symm_apply b)
    (by rw [← completionMap_comp]; exact completionMap_eq_id_of _ fun a => e.symm_apply_apply a)

theorem completionEquiv_apply (e : A ≃+* B) (x : AdicCompletion (maximalIdeal A) A) :
    completionEquiv e x = completionMap (e : A →+* B) x := rfl

end Functoriality

section Residue

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]

/-- The induced map on completions is compatible with the identifications of residue fields
(`residueFieldEquiv`): `ResidueField.map φ̂ ∘ residueFieldEquiv A =
residueFieldEquiv B ∘ ResidueField.map φ`. -/
theorem residueField_map_completionMap_comp :
    (ResidueField.map (completionMap φ)).comp
        (residueFieldEquiv A :
          ResidueField A →+* ResidueField (AdicCompletion (maximalIdeal A) A)) =
      (residueFieldEquiv B :
          ResidueField B →+* ResidueField (AdicCompletion (maximalIdeal B) B)).comp
        (ResidueField.map φ) := by
  refine RingHom.ext fun k => ?_
  obtain ⟨a, rfl⟩ := residue_surjective k
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, residueFieldEquiv,
    RingEquiv.ofBijective_apply, ResidueField.map_residue, completionMap_algebraMap]

/-- For the coefficient field on `B̂` transported from `A` along the induced map
(`ι_B := completionMap φ ∘ coefficientField A ∘ e⁻¹`, `e` the induced isomorphism of residue
fields when `ResidueField.map φ` is bijective), the section property `IsCoefficientAlgebra`
holds. -/
theorem residue_completionMap_coefficientField [Algebra ℚ A]
    (hbij : Function.Bijective (ResidueField.map φ)) (k : ResidueField B) :
    residue (AdicCompletion (maximalIdeal B) B) (completionMap φ (coefficientField A
      ((RingEquiv.ofBijective (ResidueField.map φ) hbij).symm k))) = residueFieldEquiv B k := by
  rw [← ResidueField.map_residue, residue_coefficientField]
  have h := congrArg
    (fun g : ResidueField A →+* ResidueField (AdicCompletion (maximalIdeal B) B) =>
      g ((RingEquiv.ofBijective (ResidueField.map φ) hbij).symm k))
    (residueField_map_completionMap_comp φ)
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom] at h
  rw [h]
  congr 1
  exact (RingEquiv.ofBijective (ResidueField.map φ) hbij).apply_symm_apply k

end Residue

end IsLocalRing
