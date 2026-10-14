/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Hironaka.Algebra.RegularSmooth.SmoothAt

/-!
# Embedding an affine scheme in affine space with ambient dimension at least two

Kollár's resolution of an affine scheme `X` starts from a closed embedding `X ↪ A` into a smooth
affine scheme with `dim A ≥ dim X + 2` [Kol07, Theorem 36, proof; Corollary 22, proof]. An affine
scheme of finite type over `k` whose ring of functions has `n` generators embeds in `𝔸^{n+2}` with
the last two coordinates zero; at every point the ambient local ring has dimension `≥ 2`, its prime
containing the kernel of the projection killing the last two variables, a prime of height `≥ 2`.

* `padProj`, `dropLast`, `padProj_surjective`: the coordinate projections `𝔸^{n+2} → 𝔸^n` and
  `𝔸^{n+2} → 𝔸^{n+1}` on coordinate rings;
* `two_le_height_of_ker_padProj_le`: a prime containing `ker padProj` has height `≥ 2`;
* `exists_affineEmbedding_aux`, `exists_affineEmbedding`: the embedding, with the dimension bound
  at every point, respectively at the generic points (the form used to build admissible pairs).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace Hironaka.Resolution

variable {k : Type u} [Field k]

/-! ### The coordinate projections -/

/-- The projection `𝔸^{n+2} → 𝔸^n` on the coordinate rings: `x_i ↦ x_i` for `i < n`, the last two
variables to `0`. -/
noncomputable def padProj (n : ℕ) : MvPolynomial (Fin (n + 2)) k →ₐ[k] MvPolynomial (Fin n) k :=
  aeval fun i : Fin (n + 2) => if h : i.val < n then X ⟨i.val, h⟩ else 0

/-- The projection `𝔸^{n+2} → 𝔸^{n+1}` killing the last variable only. -/
noncomputable def dropLast (n : ℕ) :
    MvPolynomial (Fin (n + 2)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i : Fin (n + 2) => if h : i.val < n + 1 then X ⟨i.val, h⟩ else 0

theorem padProj_X_of_lt (n : ℕ) (i : Fin (n + 2)) (h : i.val < n) :
    padProj (k := k) n (X i) = X ⟨i.val, h⟩ := by
  rw [padProj, aeval_X, dite_eq_left h]

theorem padProj_X_of_le (n : ℕ) (i : Fin (n + 2)) (h : n ≤ i.val) :
    padProj (k := k) n (X i) = 0 := by
  rw [padProj, aeval_X, dite_eq_right (not_lt.mpr h)]

theorem dropLast_X_of_lt (n : ℕ) (i : Fin (n + 2)) (h : i.val < n + 1) :
    dropLast (k := k) n (X i) = X ⟨i.val, h⟩ := by
  rw [dropLast, aeval_X, dite_eq_left h]

theorem dropLast_X_last (n : ℕ) : dropLast (k := k) n (X (Fin.last (n + 1))) = 0 := by
  rw [dropLast, aeval_X, dite_eq_right (by simp)]

theorem padProj_surjective (n : ℕ) : Function.Surjective (padProj (k := k) n) := by
  intro P
  refine ⟨rename (Fin.castLE (Nat.le_add_right n 2)) P, ?_⟩
  rw [padProj, aeval_rename]
  have : ((fun i : Fin (n + 2) =>
      if h : i.val < n then (X ⟨i.val, h⟩ : MvPolynomial (Fin n) k) else 0) ∘
        Fin.castLE (Nat.le_add_right n 2)) = X := by
    funext j
    simp [Fin.castLE]
  rw [this, aeval_X_left_apply]

/-- `padProj` factors through `dropLast`. -/
theorem padProj_eq_comp_dropLast (n : ℕ) :
    padProj (k := k) n =
      (aeval fun j : Fin (n + 1) =>
        if h : j.val < n then (X ⟨j.val, h⟩ : MvPolynomial (Fin n) k) else 0).comp
          (dropLast n) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply]
  by_cases h : i.val < n + 1
  · rw [dropLast_X_of_lt n i h, aeval_X]
    by_cases h' : i.val < n
    · rw [padProj_X_of_lt n i h', dite_eq_left h']
    · rw [padProj_X_of_le n i (not_lt.mp h'), dite_eq_right h']
  · have hi : i = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
    rw [hi, dropLast_X_last, map_zero, padProj_X_of_le n _ (by rw [Fin.val_last]; omega)]

/-! ### The height bound -/

/-- A prime of `k[x_0, …, x_{n+1}]` containing the kernel of the projection killing the last two
variables has height `≥ 2` (the chain `⊥ < ker dropLast < ker padProj`). -/
theorem two_le_height_of_ker_padProj_le (n : ℕ) (p : Ideal (MvPolynomial (Fin (n + 2)) k))
    (hp : RingHom.ker (padProj (k := k) n) ≤ p) : 2 ≤ p.height := by
  have h1 : (RingHom.ker (dropLast (k := k) n)).IsPrime := RingHom.ker_isPrime _
  have h2 : (RingHom.ker (padProj (k := k) n)).IsPrime := RingHom.ker_isPrime _
  have hbot : (⊥ : Ideal (MvPolynomial (Fin (n + 2)) k)) < RingHom.ker (dropLast (k := k) n) := by
    refine lt_of_le_of_ne bot_le fun h => ?_
    have hX : X (Fin.last (n + 1)) ∈ RingHom.ker (dropLast (k := k) n) :=
      RingHom.mem_ker.mpr (dropLast_X_last n)
    rw [← h] at hX
    exact X_ne_zero _ (Ideal.mem_bot.mp hX)
  have h12 : RingHom.ker (dropLast (k := k) n) < RingHom.ker (padProj (k := k) n) := by
    refine lt_of_le_of_ne ?_ fun h => ?_
    · intro P hP
      rw [RingHom.mem_ker] at hP ⊢
      rw [padProj_eq_comp_dropLast, AlgHom.comp_apply, hP, map_zero]
    · have hX : X (⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ : Fin (n + 2)) ∈
          RingHom.ker (padProj (k := k) n) :=
        RingHom.mem_ker.mpr (padProj_X_of_le n _ le_rfl)
      rw [← h, RingHom.mem_ker, dropLast_X_of_lt n _ (Nat.lt_succ_self n)] at hX
      exact X_ne_zero _ hX
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h12
  have e3 := Ideal.height_mono hp
  rw [Ideal.height_bot, zero_add] at e1
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ (RingHom.ker (dropLast (k := k) n)).height + 1 := add_le_add e1 (le_refl 1)
    _ ≤ (RingHom.ker (padProj (k := k) n)).height := e2
    _ ≤ p.height := e3

/-! ### The embedding -/

/-- An affine scheme of finite type over `k` embeds as a closed subscheme of `𝔸^{n+2}_k` over `k`
(`n` generators of its ring of functions and two zero coordinates) with the local rings of the
ambient space of dimension `≥ 2` at every point, as in the proof of [Kol07, Theorem 36]. -/
theorem exists_affineEmbedding_aux (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsAffine X] :
    ∃ (N : ℕ) (emb : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) k))),
      IsClosedImmersion emb ∧
        emb ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin N) k))) =
          X ↘ Spec (CommRingCat.of k) ∧
        ∀ x : X, 2 ≤ ringKrullDim
          ((Spec (CommRingCat.of (MvPolynomial (Fin N) k))).presheaf.stalk (emb x)) := by
  set f := X ↘ Spec (CommRingCat.of k) with hf
  let _ := f.sectionsAlgebra ⊤
  have hft : Algebra.FiniteType k Γ(X, ⊤) := f.finiteType_sectionsAlgebra (isAffineOpen_top X)
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  set g : MvPolynomial (Fin (n + 2)) k →ₐ[k] Γ(X, ⊤) := φ.comp (padProj n) with hgdef
  have hg : Function.Surjective g := hφ.comp (padProj_surjective n)
  set R := CommRingCat.of (MvPolynomial (Fin (n + 2)) k) with hR
  set emb : X ⟶ Spec R :=
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g : MvPolynomial (Fin (n + 2)) k →+* Γ(X, ⊤)))
    with hemb
  have hci : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (g : MvPolynomial (Fin (n + 2)) k →+* Γ(X, ⊤)))) :=
    IsClosedImmersion.spec_of_surjective _ hg
  refine ⟨n + 2, emb, inferInstance, ?_, ?_⟩
  · -- over `k`
    have h1 : Spec.map (CommRingCat.ofHom (g : MvPolynomial (Fin (n + 2)) k →+* Γ(X, ⊤))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin (n + 2)) k))) =
        Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, ⊤))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
    have h2 : X.toSpecΓ ≫ Spec.map (f.appLE ⊤ ⊤ le_top) =
        f ≫ (Spec (CommRingCat.of k)).toSpecΓ := by
      rw [Scheme.toSpecΓ_naturality]
      congr 2
      -- `f ⁻¹ᵁ ⊤` is `⊤` definitionally, so this is Mathlib's `appLE_eq_app` at `U = ⊤`
      exact f.appLE_eq_app
    rw [hemb, Category.assoc, h1, Scheme.Hom.algebraMap_sectionsAlgebra, CommRingCat.ofHom_hom,
      Spec.map_comp, Scheme.isoSpec, asIso_hom, ← Category.assoc, h2, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  · -- the height bound at every point
    intro x
    have hemb' : emb x =
        PrimeSpectrum.comap (g : MvPolynomial (Fin (n + 2)) k →+* Γ(X, ⊤)) (X.isoSpec.hom x) := by
      rw [hemb]
      change Spec.map (CommRingCat.ofHom (g : MvPolynomial (Fin (n + 2)) k →+* Γ(X, ⊤)))
        (X.isoSpec.hom x) = _
      rw [Spec.map_apply, CommRingCat.hom_ofHom]
    have hpr : (emb x).asIdeal.IsPrime := (emb x).isPrime
    let alg : Algebra ↑R ↑((Spec R).presheaf.stalk (emb x)) :=
      StructureSheaf.stalkAlgebra (↑R) (emb x)
    have hloc : IsLocalization.AtPrime (↑((Spec R).presheaf.stalk (emb x))) (emb x).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk R (emb x)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (emb x).asIdeal
      ((Spec R).presheaf.stalk (emb x))]
    have hp : RingHom.ker (padProj (k := k) n) ≤ (emb x).asIdeal := by
      rw [hemb']
      change RingHom.ker (padProj (k := k) n) ≤
        Ideal.comap (g : MvPolynomial (Fin (n + 2)) k →+* Γ(X, ⊤)) (X.isoSpec.hom x).asIdeal
      intro P hP
      rw [Ideal.mem_comap, RingHom.coe_coe]
      have : g P = 0 := by
        rw [hgdef, AlgHom.comp_apply, RingHom.mem_ker.mp hP, map_zero]
      rw [this]
      exact Ideal.zero_mem _
    have h2 := two_le_height_of_ker_padProj_le n (emb x).asIdeal hp
    rw [← WithBot.coe_ofNat]
    exact WithBot.coe_le_coe.mpr h2

/-- The embedding of `exists_affineEmbedding_aux` with the dimension bound stated only at the
generic points of `X` (a special case), the form in which it enters the construction of an
admissible embedding of an affine scheme. -/
theorem exists_affineEmbedding (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsAffine X] :
    ∃ (N : ℕ) (emb : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) k))),
      IsClosedImmersion emb ∧
        emb ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin N) k))) =
          X ↘ Spec (CommRingCat.of k) ∧
        ∀ η ∈ genericPoints X,
          2 ≤ ringKrullDim
            ((Spec (CommRingCat.of (MvPolynomial (Fin N) k))).presheaf.stalk (emb η)) := by
  obtain ⟨N, emb, hci, hover, hdim⟩ := exists_affineEmbedding_aux (k := k) X
  exact ⟨N, emb, hci, hover, fun η _ => hdim η⟩

end Hironaka.Resolution
