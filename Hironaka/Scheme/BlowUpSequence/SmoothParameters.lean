/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Stalk
public import Hironaka.Algebra.Local.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.RegularSmooth.Cotangent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.Derivative.Pullback
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.EtaleParameters
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
/-!
# Regular systems of parameters along a smooth stalk map

Pulling back a smooth blow-up sequence along a smooth morphism `h : Y ⟶ X` ([Kol07, 30.1 and
34.1]; [Wlo05, Proposition 2.4.2]) transports the simple normal crossing conditions of
[Kol07, Definition 24] along `h`: a regular system of parameters `z_1, …, z_n` of `𝒪_{X, h y}` in
which the components of `E` through `h y` are coordinate hypersurfaces must extend, through the
stalk map `φ : 𝒪_{X, h y} → 𝒪_{Y, y}`, to a regular system of parameters of `𝒪_{Y, y}`. This
module proves that local statement (`exists_isRegularSystemOfParameters_stalkMap`); the normal
crossing predicates themselves are transported in `Hironaka/Scheme/BlowUpSequence/PullbackSnc.lean`.

## The argument

Both stalks are regular local rings (the schemes are smooth over `k`), and `φ` is a formally
smooth local homomorphism (`Scheme.Hom.formallySmooth_stalkMap` in
`Hironaka/Scheme/IdealSheaf/Derivative/Pullback.lean`: every point lies in Mathlib's smooth locus).
The classes of `z_1, …, z_n` form a basis of `𝔪_A/𝔪_A²`; because `κ(A)/k` is separable (`k` perfect)
the conormal map `𝔪_A/𝔪_A² → κ(A) ⊗_A Ω_{A/k}` is injective (`injective_cotangentSpaceToTensor`), so
there are `k`-derivations `δ_i : A → κ(A)` with `δ_i z_j = δ_ij`. Pushed into `κ(B)` and extended
along the formally smooth `φ` (`exists_derivation_extend`, the Jacobi–Zariski sequence with
`H¹(L_{B/A}) = 0` and `Ω_{B/A}` projective), they give derivations `∂_i : B → κ(B)` with
`∂_i (φ z_j) = δ_ij`, which detect the linear independence of the classes of the `φ z_j` in
`𝔪_B/𝔪_B²` (`linearIndependent_toCotangent_of_derivations_residueField`). A linearly independent
family in `𝔪_B/𝔪_B²` extends to a regular system of parameters of `B`
(`exists_span_eq_maximalIdeal_of_linearIndependent`, [Sta, Tag 00NR]), which completes the proof.

The facts about formally smooth algebras used here are standard ([Sta, Tags 00TA, 00TI and 00TV]);
none of the lemmas of this module is stated in the printed proofs.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace AlgebraicGeometry

/-! ### Extension of derivations along a formally smooth map -/

section DerivationExtension

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-- Along a formally smooth `A → B` every `k`-derivation of `A` into a `B`-module extends to `B`
(the infinitesimal lifting property in its Kähler form, [Sta, Tag 00TI]). The Jacobi–Zariski
sequence `H¹(L_{B/A}) → B ⊗_A Ω_{A/k} → Ω_{B/k} → Ω_{B/A} → 0` has `H¹ = 0` and `Ω_{B/A}`
projective (Mathlib's definition of formal smoothness), so `B ⊗_A Ω_{A/k} → Ω_{B/k}` is a split
injection and a linear functional on it extends. -/
theorem exists_derivation_extend [Algebra.FormallySmooth A B] {M : Type*} [AddCommGroup M]
    [Module k M] [Module A M] [Module B M] [IsScalarTower k A M] [IsScalarTower k B M]
    [IsScalarTower A B M] (δ : Derivation k A M) :
    ∃ Dx : Derivation k B M, ∀ a, Dx (algebraMap A B a) = δ a := by
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k A B) := by
    rw [← LinearMap.ker_eq_bot, (Algebra.H1Cotangent.exact_δ_mapBaseChange k A B).linearMap_ker_eq]
    exact LinearMap.range_eq_bot.mpr (Subsingleton.elim _ _)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (KaehlerDifferential.map k A B B)
    LinearMap.id (KaehlerDifferential.map_surjective k A B)
  have h01 := (KaehlerDifferential.exact_mapBaseChange_map k A B).split_tfae'.out 1 2
  obtain ⟨-, l, hl⟩ := h01.mp ⟨hinj, s, hs⟩
  let L : Ω[B⁄k] →ₗ[B] M := (δ.liftKaehlerDifferential.liftBaseChange B) ∘ₗ l
  refine ⟨L.compDer (KaehlerDifferential.D k B), fun a => ?_⟩
  change L (KaehlerDifferential.D k B (algebraMap A B a)) = δ a
  have h1 : KaehlerDifferential.D k B (algebraMap A B a) =
      KaehlerDifferential.mapBaseChange k A B (1 ⊗ₜ KaehlerDifferential.D k A a) := by
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rw [h1]
  simp only [L, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply l, hl, LinearMap.id_apply, LinearMap.liftBaseChange_tmul, one_smul,
    Derivation.liftKaehlerDifferential_comp_D]

end DerivationExtension

/-! ### Independence in the cotangent space detected by derivations into the residue field -/

section CotangentIndependence

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The maximal ideal acts trivially on the residue field. -/
theorem smul_residueField_eq_zero_of_mem {m : R} (hm : m ∈ maximalIdeal R) (x : ResidueField R) :
    m • x = 0 := by
  rw [Algebra.smul_def, ResidueField.algebraMap_eq, (residue_eq_zero_iff m).mpr hm, zero_mul]

/-- A derivation into the residue field kills `𝔪²` (Leibniz). -/
theorem derivation_apply_eq_zero_of_mem_sq {k : Type*} [CommRing k] [Algebra k R]
    (D : Derivation k R (ResidueField R)) {a : R} (ha : a ∈ maximalIdeal R ^ 2) : D a = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun m hm n hn => ?_) (fun x y hx hy => ?_)
  · rw [D.leibniz, smul_residueField_eq_zero_of_mem hm, smul_residueField_eq_zero_of_mem hn,
      add_zero]
  · rw [map_add, hx, hy, add_zero]

/-- The independence criterion `linearIndependent_toCotangent_of_derivations` with derivations
into the residue field: if `D_i (w_j) = δ_ij` in `κ` then the classes of the `w_j` in `𝔪/𝔪²` are
linearly independent. -/
theorem linearIndependent_toCotangent_of_derivations_residueField {k : Type*} [CommRing k]
    [Algebra k R] {ι : Type*} [Finite ι] [DecidableEq ι] (w : ι → R)
    (hw : ∀ i, w i ∈ maximalIdeal R) (D : ι → Derivation k R (ResidueField R))
    (hD : ∀ i j, D i (w j) = if i = j then 1 else 0) :
    LinearIndependent (ResidueField R) fun i => (maximalIdeal R).toCotangent ⟨w i, hw i⟩ := by
  cases nonempty_fintype ι
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun j => residue_surjective (R := R) (g j)
  set W : ι → maximalIdeal R := fun j => ⟨w j, hw j⟩ with hW
  have hsum : (∑ j, g j • (maximalIdeal R).toCotangent (W j)) =
      (maximalIdeal R).toCotangent (∑ j, a j • W j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← ha j, ← ResidueField.algebraMap_eq, algebraMap_smul]
  have hmem : ((∑ j, a j • W j : maximalIdeal R) : R) ∈ maximalIdeal R ^ 2 :=
    ((maximalIdeal R).toCotangent_eq_zero _).mp (hsum.symm.trans hg)
  have hcoe : ((∑ j, a j • W j : maximalIdeal R) : R) = ∑ j, a j * w j := by
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun j _ => rfl
  rw [hcoe] at hmem
  have hDi : D i (∑ j, a j * w j) = residue R (a i) := by
    rw [map_sum]
    have : ∀ j, D i (a j * w j) = if i = j then residue R (a j) else 0 := by
      intro j
      rw [(D i).leibniz, hD i j, smul_residueField_eq_zero_of_mem (hw j), add_zero, smul_ite,
        smul_zero, Algebra.smul_def, ResidueField.algebraMap_eq, mul_one]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← ha i, ← hDi]
  exact derivation_apply_eq_zero_of_mem_sq (D i) hmem

end CotangentIndependence

/-! ### The algebraic core: parameters extend along a formally smooth local homomorphism -/

section Core

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-- For a formally smooth local homomorphism `A → B` of regular local rings with `κ(A)/k`
separable, the image of a regular system of parameters of `A` is part of a regular system of
parameters of `B`; the algebra behind the proof of [Wlo05, Proposition 2.4.2] ("`C'_i` has simple
normal crossings with `E'_i`"). The classes of `z_1, …, z_n` form a basis of `𝔪_A/𝔪_A²`; the
conormal map `𝔪_A/𝔪_A² → κ(A) ⊗ Ω_{A/k}` is injective, so dual derivations `δ_i : A → κ(A)` with
`δ_i z_j = δ_ij` exist; pushed to `κ(B)` and extended along `A → B` (`exists_derivation_extend`)
they detect the independence of the classes of the `φ(z_j)` in `𝔪_B/𝔪_B²`, and a linearly
independent family in `𝔪_B/𝔪_B²` extends to a regular system of parameters of `B`. -/
theorem exists_isRegularSystemOfParameters_extend [IsRegularLocalRing A] [IsRegularLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.FormallySmooth A B]
    [Algebra.FormallySmooth k (ResidueField A)] {n : ℕ} (z : Fin n → A)
    (hz : IsRegularSystemOfParameters z) :
    ∃ (m : ℕ) (w : Fin m → B), IsRegularSystemOfParameters w ∧
      ∃ σ : Fin n → Fin m, Function.Injective σ ∧ ∀ i, w (σ i) = algebraMap A B (z i) := by
  classical
  have hzm : ∀ i, z i ∈ maximalIdeal A := fun i => hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  set Z : Fin n → maximalIdeal A := fun i => ⟨z i, hzm i⟩ with hZ
  -- the classes of a regular system of parameters form a basis of `𝔪/𝔪²`
  have hspan : ⊤ ≤ Submodule.span (ResidueField A)
      (Set.range fun i => (maximalIdeal A).toCotangent (Z i)) := by
    rw [top_le_iff, Set.range_comp' (maximalIdeal A).toCotangent Z,
      CotangentSpace.span_image_eq_top_iff]
    apply Submodule.map_injective_of_injective (maximalIdeal A).injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp']
    exact hz.1
  have hcard : Fintype.card (Fin n) = Module.finrank (ResidueField A) (CotangentSpace A) := by
    rw [Fintype.card_fin]
    have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
    rw [← hz.2] at h1
    exact_mod_cast h1.symm
  have hli : LinearIndependent (ResidueField A) fun i => (maximalIdeal A).toCotangent (Z i) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard
  -- their images `1 ⊗ dz_i` in `κ ⊗ Ω_{A/k}` (the conormal map is injective, `κ/k` separable)
  set v : Fin n → ResidueField A ⊗[A] Ω[A⁄k] :=
    fun i => cotangentSpaceToTensor k A ((maximalIdeal A).toCotangent (Z i)) with hv
  have hli2 : LinearIndependent (ResidueField A) v :=
    hli.map' (cotangentSpaceToTensor k A)
      (LinearMap.ker_eq_bot.mpr (injective_cotangentSpaceToTensor k A))
  have hvz : ∀ j, (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (z j) = v j := fun j =>
    (cotangentSpaceToTensor_toCotangent k A (Z j)).symm
  -- dual functionals and the derivations `δ_i : A → κ(A)` with `δ_i z_j = δ_ij`
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_leftInverse_of_injective
    (Finsupp.linearCombination (ResidueField A) v) (LinearMap.ker_eq_bot.mpr hli2)
  let δ : Fin n → Derivation k A (ResidueField A) := fun i =>
    ((Finsupp.lapply (R := ResidueField A) i ∘ₗ ℓ).restrictScalars A ∘ₗ
      TensorProduct.mk A (ResidueField A) Ω[A⁄k] 1).compDer (KaehlerDifferential.D k A)
  have hδ : ∀ i j, δ i (z j) = if i = j then 1 else 0 := by
    intro i j
    have hvj : (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (z j) =
        Finsupp.linearCombination (ResidueField A) v (Finsupp.single j 1) := by
      rw [Finsupp.linearCombination_single, one_smul, hvz]
    have hℓv : ℓ (Finsupp.linearCombination (ResidueField A) v (Finsupp.single j 1)) =
        Finsupp.single j 1 := by
      have := LinearMap.congr_fun hℓ (Finsupp.single j 1)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this
    change ((Finsupp.lapply (R := ResidueField A) i ∘ₗ ℓ).restrictScalars A ∘ₗ
      TensorProduct.mk A (ResidueField A) Ω[A⁄k] 1) (KaehlerDifferential.D k A (z j)) = _
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.comp_apply,
      TensorProduct.mk_apply, hvj, hℓv, Finsupp.lapply_apply, Finsupp.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
  -- push the values to `κ(B)` and extend along the formally smooth `A → B`
  let ρ : ResidueField A →ₗ[A] ResidueField B :=
    (IsScalarTower.toAlgHom A (ResidueField A) (ResidueField B)).toLinearMap
  let δ' : Fin n → Derivation k A (ResidueField B) := fun i => ρ.compDer (δ i)
  have hδ' : ∀ i j, δ' i (z j) = if i = j then 1 else 0 := by
    intro i j
    change ρ (δ i (z j)) = _
    rw [hδ]
    split_ifs <;> simp [ρ]
  choose Dx hDx using fun i => exists_derivation_extend (k := k) (A := A) (B := B) (δ' i)
  have hwm : ∀ i, algebraMap A B (z i) ∈ maximalIdeal B := fun i =>
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp (hzm i) (IsLocalHom.map_nonunit _ hu)
  have hliB : LinearIndependent (ResidueField B)
      fun i => (maximalIdeal B).toCotangent ⟨algebraMap A B (z i), hwm i⟩ :=
    linearIndependent_toCotangent_of_derivations_residueField _ hwm Dx fun i j => by
      rw [hDx, hδ']
  exact exists_span_eq_maximalIdeal_of_linearIndependent _ hwm hliB

end Core

/-! ### At the stalks of a smooth morphism -/

section Stalk

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The stalk of a scheme locally of finite type over `k` is essentially of finite type over `k`:
`Γ(U)` is of finite type for an affine `U ∋ x`, and the stalk is its localization. -/
theorem essFiniteType_stalk_of_locallyOfFiniteType (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) :
    let := f.stalkAlgebra x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  let := f.stalkAlgebra x
  obtain ⟨U, hxU⟩ := Scheme.IdealSheafData.exists_affineOpens_mem x
  let := f.sectionsAlgebra U.1
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U.1 hxU
  have : Algebra.FiniteType k Γ(X, U.1) := by
    have h1 : (f.appLE ⊤ U.1 le_top).hom.FiniteType :=
      f.finiteType_appLE (isAffineOpen_top _) U.2 le_top
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 le_top).hom.FiniteType
    rw [CommRingCat.hom_comp]
    exact h1.comp h2
  have : IsLocalization (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.EssFiniteType Γ(X, U.1) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp k Γ(X, U.1) _

/-- Along the stalk map of a smooth morphism between schemes smooth over a perfect field, a regular
system of parameters at `h y` extends to one at `y`: the local statement behind the transport of
simple normal crossings [Kol07, Definition 24] along a smooth morphism
([Wlo05, Proposition 2.4.2, proof]). -/
theorem exists_isRegularSystemOfParameters_stalkMap [PerfectField k] (f : X ⟶ Spec (.of k))
    [Smooth f] (h : Y ⟶ X) [Smooth h] (y : Y) {n : ℕ} (z : Fin n → X.presheaf.stalk (h y))
    (hz : IsRegularSystemOfParameters z) :
    ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y), IsRegularSystemOfParameters w ∧
      ∃ σ : Fin n → Fin m, Function.Injective σ ∧ ∀ i, w (σ i) = (h.stalkMap y).hom (z i) := by
  let : Algebra k (X.presheaf.stalk (h y)) := f.stalkAlgebra (h y)
  let : Algebra (X.presheaf.stalk (h y)) (Y.presheaf.stalk y) := (h.stalkMap y).hom.toAlgebra
  let : Algebra k (Y.presheaf.stalk y) :=
    ((h.stalkMap y).hom.comp (algebraMap k (X.presheaf.stalk (h y)))).toAlgebra
  have : IsScalarTower k (X.presheaf.stalk (h y)) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsRegularLocalRing (X.presheaf.stalk (h y)) :=
    isRegularLocalRing_stalk f (h y)
  have : IsRegularLocalRing (Y.presheaf.stalk y) :=
    isRegularLocalRing_stalk (h ≫ f) y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (h y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (h.stalkMap y).hom)
  have := h.formallySmooth_stalkMap y
  have : Algebra.EssFiniteType k (X.presheaf.stalk (h y)) :=
    essFiniteType_stalk_of_locallyOfFiniteType f (h y)
  have : Algebra.EssFiniteType k (ResidueField (X.presheaf.stalk (h y))) :=
    inferInstanceAs (Algebra.EssFiniteType k (_ ⧸ maximalIdeal (X.presheaf.stalk (h y))))
  exact exists_isRegularSystemOfParameters_extend (k := k) z hz

end Stalk

end AlgebraicGeometry
