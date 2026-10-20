/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CompletionMap
public import Mathlib.RingTheory.RingHom.Flat
public import Hironaka.Algebra.Local.ChartRing
import Hironaka.Algebra.Local.ChartCompletion
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Localization

/-!
# Ring maps out of the chart ring: existence, the chart origin, and flatness

The algebra of a ring map `χ : R' → S` out of the chart ring `R' = R[xᵢ/x_r : i < r]` of the chart
dividing by `x_r` ([Kol07, (60.2)]).

* `exists_chartRing_hom_of_mul_eq`: a ring map `ρ : R → S` into a domain with `ρ(x_r) = w ≠ 0` and
  `ρ(xⱼ) = w · vⱼ` (`j < r`) extends to `χ : R' → S` with `χ(xⱼ / x_r) = vⱼ`. It is stated for an
  arbitrary family of ratios `v`, so that it applies to coordinates centred at a point of the
  exceptional divisor other than the origin of the chart.
* `comap_maximalIdeal_eq_chartOrigin`: if `S` is local and `χ` sends the `xⱼ / x_r` (`j < r`) and
  the `xᵢ` into `𝔪_S`, then `χ⁻¹(𝔪_S)` is the chart origin `𝔪' = (y₀, …, y_{n−1})`, a maximal
  ideal of `R'` (`chartOrigin_isMaximal`, `Hironaka/Algebra/Local/Chart.lean`).
* `chartLocalHom`: the local homomorphism `R'_{𝔪'} → S` induced by `χ` when `χ⁻¹(𝔪_S) = 𝔪'`.
* `flat_comp_algebraMap_adicCompletion`: **`R' → Ŝ` is flat** as soon as the induced map of
  completions `(R'_{𝔪'})^ → Ŝ` is bijective: `R' → R'_{𝔪'}` is a localization, hence flat;
  `R'_{𝔪'} → (R'_{𝔪'})^` is the completion of a Noetherian local ring, flat by
  [Mat89, Theorem 8.8] (Mathlib's `AdicCompletion.flat_of_isNoetherian`); and a bijective ring
  map is flat. The bijectivity is supplied by `Hironaka/Algebra/Local/ChartCompletionHom.lean`.

These are the algebraic inputs of the description of the strict transform at a point of the
exceptional divisor in `Hironaka/Manifold/BlowUp/Transform/StrictSubspaceCompletion.lean` and
`Hironaka/Manifold/BlowUp/Transform/StrictSubspaceProp313.lean` ([BM97, Proposition 3.13]), and
of the transport of the order bound of [Kol07, Lemma 61] to the analytic stalk
(`Hironaka/Algebra/Local/ChartOrderFaithful.lean`,
`Hironaka/Resolution/Analytic/GoingUp/MaxOrder.lean`). The statements are not in the sources.
-/

@[expose] public section

open IsLocalRing

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] {n : ℕ} (x : Fin n → R) (r : Fin n)

section Exists

variable {S : Type*} [CommRing S] [IsDomain S]

/-- A ring map `ρ : R → S` into a domain with `ρ(x_r) = w ≠ 0` and `ρ(xⱼ) = w · vⱼ` for `j < r`
extends to the chart ring of [Kol07, (60.2)], `xⱼ / x_r ↦ vⱼ`. -/
theorem exists_chartRing_hom_of_mul_eq (ρ : R →+* S) {w : S} (hw : w ≠ 0) (v : Fin n → S)
    (hρr : ρ (x r) = w) (hρj : ∀ j, j < r → ρ (x j) = w * v j) :
    ∃ χ : chartRing x r →+* S, (∀ s, χ (algebraMap R (chartRing x r) s) = ρ s) ∧
      (∀ j, j < r → χ (chartYR x r j) = v j) ∧ χ (algebraMap R (chartRing x r) (x r)) = w := by
  classical
  let L := FractionRing S
  let ι : S →+* L := algebraMap S L
  have hι : Function.Injective ι := IsFractionRing.injective S L
  have hunit : ∀ y : Submonoid.powers (x r), IsUnit ((ι.comp ρ) y) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy
    change IsUnit (ι (ρ (x r ^ k)))
    rw [map_pow, hρr, map_pow]
    refine (isUnit_iff_ne_zero.mpr ?_).pow k
    exact (IsFractionRing.to_map_eq_zero_iff (K := L)).not.mpr hw
  let Λ : Localization.Away (x r) →+* L := IsLocalization.lift hunit
  have hΛalg : ∀ s, Λ (algebraMap _ _ s) = ι (ρ s) := fun s => IsLocalization.lift_eq hunit s
  have hΛmk : ∀ j, j < r →
      Λ (Localization.mk (x j) ⟨x r, Submonoid.mem_powers _⟩) = ι (v j) := by
    intro j hj
    rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
    change ι (ρ (x j)) = ι (ρ (x r)) * _
    rw [hρj j hj, hρr, map_mul]
  have hrange : ∀ s : chartRing x r, ∃ b, ι b = Λ (s : Localization.Away (x r)) := by
    intro s
    have hs : (s : Localization.Away (x r)) ∈ Algebra.adjoin R
        ((fun j : Fin n => Localization.mk (x j) ⟨x r, Submonoid.mem_powers (x r)⟩) ''
          {j | j < r}) := s.2
    refine Algebra.adjoin_induction (p := fun z _ => ∃ b, ι b = Λ z) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨_, (hΛmk j hj).symm⟩
    · intro r'
      exact ⟨_, (hΛalg r').symm⟩
    · rintro a b _ _ ⟨a', ha'⟩ ⟨b', hb'⟩
      exact ⟨a' + b', by rw [map_add, ha', hb', map_add]⟩
    · rintro a b _ _ ⟨a', ha'⟩ ⟨b', hb'⟩
      exact ⟨a' * b', by rw [map_mul, ha', hb', map_mul]⟩
  choose χ₀ hχ₀ using hrange
  let χ : chartRing x r →+* S :=
    { toFun := χ₀
      map_one' := hι (by rw [hχ₀, OneMemClass.coe_one, map_one, map_one])
      map_mul' := fun a b => hι (by rw [hχ₀, MulMemClass.coe_mul, map_mul, map_mul, hχ₀, hχ₀])
      map_zero' := hι (by rw [hχ₀, ZeroMemClass.coe_zero, map_zero, map_zero])
      map_add' := fun a b => hι (by rw [hχ₀, AddMemClass.coe_add, map_add, map_add, hχ₀, hχ₀]) }
  have hχ : ∀ (z : chartRing x r) b, χ z = b ↔ Λ (z : Localization.Away (x r)) = ι b := by
    intro z b
    constructor
    · intro hz
      rw [← hz]
      exact (hχ₀ z).symm
    · intro hz
      exact hι ((hχ₀ z).trans hz)
  refine ⟨χ, fun s => (hχ _ _).mpr ?_, fun j hj => (hχ _ _).mpr ?_, (hχ _ _).mpr ?_⟩
  · rw [Subalgebra.coe_algebraMap, hΛalg]
  · rw [chartYR, coe_chartYROf, chartYOf_of_lt _ _ _ hj]
    exact hΛmk j hj
  · rw [Subalgebra.coe_algebraMap, hΛalg, hρr]

end Exists

section Local

variable {S : Type*} [CommRing S] [IsLocalRing S] [IsRegularLocalRing R]
  (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
  (χ : chartRing x r →+* S)

include hx hn in
/-- If `χ : R' → S` sends the `xⱼ / x_r` (`j < r`) and the `xᵢ` into `𝔪_S`, then `χ⁻¹(𝔪_S)` is the
chart origin `𝔪' = (y₀, …, y_{n−1})`, a maximal ideal (`chartOrigin_isMaximal`). -/
theorem comap_maximalIdeal_eq_chartOrigin (hY : ∀ j, j < r → χ (chartYR x r j) ∈ maximalIdeal S)
    (hX : ∀ i, χ (algebraMap R (chartRing x r) (x i)) ∈ maximalIdeal S) :
    (maximalIdeal S).comap χ = chartOrigin x r := by
  symm
  refine (chartOrigin_isMaximal x r hx hn).eq_of_le ?_ ?_
  · intro htop
    have h1 : (1 : chartRing x r) ∈ (maximalIdeal S).comap χ := htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal S).ne_top h1
  · rw [chartOrigin, chartOriginOf, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    by_cases hi : i < r
    · exact hY i hi
    · have hyi : chartYROf x r (x r) i = algebraMap R (chartRing x r) (x i) :=
        Subtype.ext (by
          rw [coe_chartYROf, chartYOf_of_not_lt x r (x r) hi, Subalgebra.coe_algebraMap])
      rw [hyi]
      exact hX i

variable [(chartOrigin x r).IsPrime] (hχ : (maximalIdeal S).comap χ = chartOrigin x r)

omit [IsRegularLocalRing R] in
include hχ in
theorem isUnit_of_mem_primeCompl_chartOrigin (y : (chartOrigin x r).primeCompl) :
    IsUnit (χ y) := by
  rw [← notMem_maximalIdeal]
  intro hy
  have hmem : (y : chartRing x r) ∈ (maximalIdeal S).comap χ := Ideal.mem_comap.mpr hy
  rw [hχ] at hmem
  exact y.2 hmem

omit [IsRegularLocalRing R] in
/-- The local homomorphism `R'_{𝔪'} → S` induced by `χ` when `χ⁻¹(𝔪_S) = 𝔪'`. -/
noncomputable def chartLocalHom : Localization.AtPrime (chartOrigin x r) →+* S :=
  IsLocalization.lift (isUnit_of_mem_primeCompl_chartOrigin x r χ hχ)

omit [IsRegularLocalRing R] in
theorem chartLocalHom_algebraMap (z : chartRing x r) :
    chartLocalHom x r χ hχ (algebraMap _ _ z) = χ z :=
  IsLocalization.lift_eq _ z

omit [IsRegularLocalRing R] in
theorem isLocalHom_chartLocalHom : IsLocalHom (chartLocalHom x r χ hχ) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (chartOrigin x r).primeCompl a
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  have hs : IsUnit (χ s) := by
    have := (IsLocalization.lift_mk'_spec (S := Localization.AtPrime (chartOrigin x r))
      (hg := isUnit_of_mem_primeCompl_chartOrigin x r χ hχ) s _ t).mp rfl
    rw [this]
    exact (isUnit_of_mem_primeCompl_chartOrigin x r χ hχ t).mul ha
  intro hs'
  rw [← hχ, SetLike.mem_coe, Ideal.mem_comap] at hs'
  exact (notMem_maximalIdeal.mpr hs) hs'

/-- **`R' → Ŝ` is flat** when the induced map of completions `(R'_{𝔪'})^ → Ŝ` is bijective:
`R' → R'_{𝔪'}` and `R'_{𝔪'} → (R'_{𝔪'})^` are flat ([Mat89, Theorem 8.8] for the completion) and
the last factor is an isomorphism. -/
theorem flat_comp_algebraMap_adicCompletion
    (hbij : Function.Bijective
      (haveI := isLocalHom_chartLocalHom x r χ hχ; completionMap (chartLocalHom x r χ hχ))) :
    ((algebraMap S (AdicCompletion (maximalIdeal S) S)).comp χ).Flat := by
  have := isLocalHom_chartLocalHom x r χ hχ
  have h1 : (algebraMap (chartRing x r) (Localization.AtPrime (chartOrigin x r))).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (chartOrigin x r).primeCompl)
  have h2 : (algebraMap (Localization.AtPrime (chartOrigin x r))
      (AdicCompletion (maximalIdeal (Localization.AtPrime (chartOrigin x r)))
        (Localization.AtPrime (chartOrigin x r)))).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have h3 := RingHom.Flat.of_bijective hbij
  have heq : (algebraMap S (AdicCompletion (maximalIdeal S) S)).comp χ =
      (completionMap (chartLocalHom x r χ hχ)).comp
        ((algebraMap (Localization.AtPrime (chartOrigin x r)) _).comp
          (algebraMap (chartRing x r) (Localization.AtPrime (chartOrigin x r)))) := by
    ext z
    simp only [RingHom.comp_apply]
    rw [completionMap_algebraMap, chartLocalHom_algebraMap]
  rw [heq]
  exact (h1.comp h2).comp h3

end Local

end IsLocalRing
