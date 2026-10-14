/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.DerivationLocalization
import Hironaka.Algebra.Derivative.Extension
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Coordinates at a point of an étale chart

Hauser's chart computation ([Hau14, Proposition 5.4 (6)]; [Hau03, Appendix C (7)]) reads the total
transform of an snc divisor in the chart of a smooth blow-up at a *rational* point, where the chart
functions `y_i` vanishing at the point are, by construction, local coordinates. At a general point
`x'` of the exceptional divisor — a prime `q` of the chart ring `A` — the vanishing chart functions
need not be a full system of parameters; this module says what survives. For a `k`-algebra `A` with
**étale coordinates** `y : Fin n → A` (the `k`-algebra map `k[t_0, …, t_{n-1}] → A`, `t_i ↦ y_i`, is
étale; the chart functions of `Hironaka.Scheme.Smooth.ChartEtale`) and any prime `q` of `A`:

* `A_q` is a regular local ring (`A` is smooth over `k`, being étale over `k[t]`);
* the coordinates vanishing at `q` are part of a regular system of parameters of `A_q`
  (`exists_span_eq_maximalIdeal_of_etale_coordinates`).

**Why the lemma holds.** The second clause is the regular-sequence criterion [Sta, Tag 00NR] with
[Sta, Tag 00UW]; the argument here is the classical one through *coordinate derivations*. The
partial derivative `∂/∂t_c` of `k[t]` extends to a `k`-derivation `D_c` of `A` because `A` is
formally smooth over `k[t]` (`Derivation.exists_extension_of_formallySmooth`), with
`D_c (y_{c'}) = δ_{c c'}`, and `D_c` localizes to `A_q` (`Derivation.localization`). A derivation
maps `𝔪² = 𝔪 · 𝔪` into `𝔪` by the Leibniz rule; so if a combination `∑ a_c y_c` of vanishing
coordinates lies in `𝔪_q²`, applying `D_c` shows `a_c ∈ 𝔪_q`: the classes of the vanishing `y_c` in
`𝔪_q/𝔪_q²` are linearly independent over `κ(q)` (`linearIndependent_toCotangent_of_derivations`). In
a regular local ring a linearly independent family of `𝔪/𝔪²` extends to a basis (Mathlib's
`Basis.extend`), the basis lifts to generators of `𝔪` (Nakayama,
`span_eq_maximalIdeal_and_card_eq_spanFinrank_iff`) whose number is `dim_κ 𝔪/𝔪² = dim R`: a regular
system of parameters containing the given elements
(`exists_span_eq_maximalIdeal_of_linearIndependent`).
-/

public section

universe u v

open IsLocalRing Ideal Module

namespace AlgebraicGeometry

section Cotangent

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A derivation maps `𝔪²` into `𝔪`: `D (m n) = m D n + n D m` (Leibniz). -/
theorem _root_.Derivation.map_mem_maximalIdeal_of_mem_sq {k : Type v} [CommRing k] [Algebra k R]
    (D : Derivation k R R) {a : R} (ha : a ∈ maximalIdeal R ^ 2) : D a ∈ maximalIdeal R := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun m hm n hn => ?_) (fun x y hx hy => ?_)
  · rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hn)
  · rw [map_add]
    exact add_mem hx hy

/-- The independence step (the classical criterion by coordinate derivations): elements `w_i ∈ 𝔪`
admitting "dual" derivations `D_i` with `D_i (w_j) = δ_{ij}` have linearly independent classes in
`𝔪/𝔪²` — if `∑ a_j w_j ∈ 𝔪²` then `a_i = D_i (∑ a_j w_j) − ∑ w_j D_i (a_j) ∈ 𝔪`. -/
theorem linearIndependent_toCotangent_of_derivations {k : Type v} [CommRing k] [Algebra k R]
    {ι : Type*} [Finite ι] [DecidableEq ι] (w : ι → R) (hw : ∀ i, w i ∈ maximalIdeal R)
    (D : ι → Derivation k R R) (hD : ∀ i j, D i (w j) = if i = j then 1 else 0) :
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
  have hDi : D i (∑ j, a j * w j) = a i + ∑ j, w j * D i (a j) := by
    rw [map_sum]
    have : ∀ j, D i (a j * w j) = (if i = j then a j else 0) + w j * D i (a j) := by
      intro j
      rw [(D i).leibniz, hD i j, smul_eq_mul, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hai : a i ∈ maximalIdeal R := by
    have h1 : D i (∑ j, a j * w j) ∈ maximalIdeal R :=
      (D i).map_mem_maximalIdeal_of_mem_sq hmem
    have h2 : (∑ j, w j * D i (a j)) ∈ maximalIdeal R :=
      sum_mem fun j _ => Ideal.mul_mem_right _ _ (hw j)
    rw [hDi] at h1
    simpa using sub_mem h1 h2
  rw [← ha i, residue_eq_zero_iff]
  exact hai

end Cotangent

section Regular

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The extension step ([Sta, Tag 00NR] in cotangent form): in a regular local ring, elements
`w_i ∈ 𝔪` whose classes in `𝔪/𝔪²` are linearly independent are part of a regular system of
parameters — extend the classes to a basis, lift the new basis vectors to `𝔪`, and count. -/
theorem exists_span_eq_maximalIdeal_of_linearIndependent {ι : Type*} (w : ι → R)
    (hw : ∀ i, w i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R) fun i => (maximalIdeal R).toCotangent ⟨w i, hw i⟩) :
    ∃ (m : ℕ) (z : Fin m → R),
      (span (Set.range z) = maximalIdeal R ∧ (m : WithBot ℕ∞) = ringKrullDim R) ∧
        ∃ σ : ι → Fin m, Function.Injective σ ∧ ∀ i, z (σ i) = w i := by
  classical
  set v : ι → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨w i, hw i⟩ with hv
  have hs : LinearIndepOn (ResidueField R) id (Set.range v) := hli.linearIndepOn_id
  set B : Set (CotangentSpace R) := hs.extend (Set.subset_univ _) with hB
  let b : Basis B (ResidueField R) (CotangentSpace R) := Basis.extend hs
  have : Fintype B := FiniteDimensional.fintypeBasisIndex b
  choose ℓ₀ hℓ₀ using fun x : B => (maximalIdeal R).toCotangent_surjective (x : CotangentSpace R)
  let ℓ : B → R := fun x =>
    if h : (x : CotangentSpace R) ∈ Set.range v then w (Classical.choose h) else (ℓ₀ x : R)
  have hℓmem : ∀ x, ℓ x ∈ maximalIdeal R := by
    intro x
    simp only [ℓ]
    split_ifs
    · exact hw _
    · exact (ℓ₀ x).2
  have hℓ : ∀ x : B, (maximalIdeal R).toCotangent ⟨ℓ x, hℓmem x⟩ = x := by
    intro x
    by_cases h : (x : CotangentSpace R) ∈ Set.range v
    · have h1 : ℓ x = w (Classical.choose h) := dite_eq_left h
      have h2 : v (Classical.choose h) = x := Classical.choose_spec h
      rw [← h2]
      exact congrArg _ (Subtype.ext h1)
    · have h1 : ℓ x = (ℓ₀ x : R) := dite_eq_right h
      rw [← hℓ₀ x]
      exact congrArg _ (Subtype.ext h1)
  obtain ⟨hspan, hcard⟩ :=
    (span_eq_maximalIdeal_and_card_eq_spanFinrank_iff ℓ hℓmem).mpr
      ⟨b, fun x => by rw [Basis.extend_apply_self, hℓ]⟩
  let e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  have hvB : ∀ i, v i ∈ B := fun i => hs.subset_extend _ ⟨i, rfl⟩
  refine ⟨Fintype.card B, ℓ ∘ e.symm, ⟨?_, ?_⟩, fun i => e ⟨v i, hvB i⟩, ?_, ?_⟩
  · rw [e.symm.surjective.range_comp, hspan]
  · rw [hcard]
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  · intro i j hij
    exact hli.injective (congrArg Subtype.val (e.injective hij))
  · intro i
    have h : (v i : CotangentSpace R) ∈ Set.range v := ⟨i, rfl⟩
    change ℓ (e.symm (e ⟨v i, hvB i⟩)) = w i
    rw [Equiv.symm_apply_apply]
    change (if h : (v i : CotangentSpace R) ∈ Set.range v then w (Classical.choose h)
      else (ℓ₀ ⟨v i, hvB i⟩ : R)) = w i
    rw [dite_eq_left h]
    exact congrArg w (hli.injective (Classical.choose_spec h))

end Regular

section Etale

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] {n : ℕ} (y : Fin n → A)

/-- Coordinates at a point of an étale chart ([Hau14, Proposition 5.4 (6)] and
[Hau03, Appendix C (7)] at a rational point): for a `k`-algebra `A` with étale coordinates
`y : Fin n → A` — `k[t] → A`, `t_i ↦ y_i`, étale — and any prime `q` of `A`, the local ring `A_q` is
regular and the coordinates vanishing at `q` are part of a regular system of parameters of `A_q`.
Regularity: `A` is smooth over `k` (étale over the polynomial ring), so `A_q` is regular; the
parameters: the coordinate derivations `∂/∂t_c` extend to `A`, localize to `A_q` and detect
independence mod `𝔪_q²`. -/
theorem exists_span_eq_maximalIdeal_of_etale_coordinates
    (hy : (MvPolynomial.aeval (R := k) y).toRingHom.Etale) (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) ∧
      ∃ (m : ℕ) (z : Fin m → Localization.AtPrime q),
        (span (Set.range z) = maximalIdeal (Localization.AtPrime q) ∧
          (m : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime q)) ∧
        ∃ σ : {c : Fin n // y c ∈ q} → Fin m, Function.Injective σ ∧
          ∀ c, z (σ c) = algebraMap A (Localization.AtPrime q) (y c.1) := by
  classical
  let _ : Algebra (MvPolynomial (Fin n) k) A := (MvPolynomial.aeval (R := k) y).toRingHom.toAlgebra
  have hEt : Algebra.Etale (MvPolynomial (Fin n) k) A := hy
  have halg : ∀ p : MvPolynomial (Fin n) k,
      algebraMap (MvPolynomial (Fin n) k) A p = MvPolynomial.aeval y p := fun p => rfl
  have : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [halg, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  have : Algebra.FormallySmooth k A :=
    Algebra.FormallySmooth.comp k (MvPolynomial (Fin n) k) A
  have : Algebra.FiniteType k A :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k (MvPolynomial (Fin n) k))
      (inferInstance : Algebra.FiniteType (MvPolynomial (Fin n) k) A)
  have hreg : IsRegularLocalRing (Localization.AtPrime q) :=
    Algebra.IsSmoothAt.isRegularLocalRing (k := k) q
  refine ⟨hreg, ?_⟩
  -- the coordinate derivations `∂/∂t_c` extend to `A`
  have hD : ∀ c : Fin n, ∃ D : Derivation k A A, ∀ c', D (y c') = if c = c' then 1 else 0 := by
    intro c
    obtain ⟨D, hD⟩ := Derivation.exists_extension_of_formallySmooth (k := k)
      (A := MvPolynomial (Fin n) k) (B := A) (MvPolynomial.pderiv c)
    refine ⟨D, fun c' => ?_⟩
    have h := hD (MvPolynomial.X c')
    rw [halg, halg, MvPolynomial.aeval_X, MvPolynomial.pderiv_X] at h
    rw [h]
    by_cases hcc : c = c'
    · subst hcc
      simp
    · rw [Pi.single_eq_of_ne (Ne.symm hcc), ite_eq_right hcc, map_zero]
  choose D hDy using hD
  -- localize to `A_q`
  let w : {c : Fin n // y c ∈ q} → Localization.AtPrime q := fun c => algebraMap A _ (y c.1)
  have hw : ∀ c, w c ∈ maximalIdeal (Localization.AtPrime q) := fun c =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q (y c.1)).mpr c.2
  let Dl : {c : Fin n // y c ∈ q} →
      Derivation k (Localization.AtPrime q) (Localization.AtPrime q) :=
    fun c => (D c.1).localization q.primeCompl
  have hDl : ∀ i j, Dl i (w j) = if i = j then 1 else 0 := by
    intro i j
    change (D i.1).localization q.primeCompl (algebraMap A (Localization q.primeCompl) (y j.1)) = _
    rw [Derivation.localization_algebraMap, hDy]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [ite_eq_right hij, ite_eq_right (fun h => hij (Subtype.ext h)), map_zero]
  exact exists_span_eq_maximalIdeal_of_linearIndependent w hw
    (linearIndependent_toCotangent_of_derivations w hw Dl hDl)

end Etale

end AlgebraicGeometry
