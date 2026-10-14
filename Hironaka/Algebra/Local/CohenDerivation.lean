/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CoefficientFieldOver
public import Hironaka.Algebra.Local.CoordsOver
public import Hironaka.Algebra.Local.CompletionCoords
public import Hironaka.Algebra.Local.FormalAut
import Hironaka.Algebra.Local.Prop94
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.FieldTheory.Perfect

/-!
# Derivatives and MC-invariance across the Cohen isomorphism

In the proof of the formal equivalence theorem [Kol07, 95], Kollár identifies `Ô_{p,X}` with
`K⟦x₁, …, xₙ⟧` by the Cohen structure theorem ([Kol07, Definition 55]) so that Proposition 94
applies there: since `x₁ − x₁' ∈ MC(I)`, the automorphism `φ^*` sending `x₁'` to `x₁` is of the
form `1 + MC(I)`, and Proposition 94 gives `φ^* Î = Î`.  Proposition 94 is proved on
`K⟦X⟧` with its standard coordinates (`Hironaka/Algebra/Local/Prop94.lean`); MC-invariance of `I`
passes to the completion in the coordinates `ĉ = c.adicCompletion`
(`Hironaka/Algebra/Local/DerivativeCompletion.lean`, Kollár's `D(Î) = D(I)^`).  This file carries
the derivative ideals from `(R̂, ĉ)` to
`(K⟦X⟧, ∂/∂Xᵢ)` along the `k`-linear Cohen isomorphism `Φ` of
`Hironaka/Algebra/Local/CoefficientFieldOver.lean`, and applies Proposition 94.

**Why it holds.** Let `R` be a regular local `k`-algebra with coordinates `c` whose `∂ᵢ` are
`k`-linear, `K = R/𝔪` algebraic over `k` (the residue field of a closed point), `σ` a `k`-linear
coefficient field and `Φ : K⟦X⟧ ≃ₐ[k] R̂` the Cohen isomorphism with `Φ(Xⱼ) = ι(xⱼ)`,
`Φ(C a) = σ(a)`.

1. *The completed derivations kill the coefficient field*
   (`adicCompletion_pderiv_coefficientField`): `∂̂ᵢ` kills `ι(k)`
   (`Hironaka/Algebra/Local/CompletionCoords.lean`), so it is a `k`-derivation of `R̂`; for `a ∈ K`
   with minimal polynomial `P` over `k`, `P(σ a) = 0`, hence `P'(σ a)·∂̂ᵢ(σ a) = 0`, and
   `P'(σ a) = σ(P'(a))` is a unit because `P` is separable (characteristic zero) and `σ` is a
   field embedding.
2. *Transport of the coordinate derivations* (`cohenAlgEquivCoords_pderiv`): `Φ⁻¹ ∘ ∂̂ᵢ ∘ Φ` is a
   `K`-derivation of `K⟦X⟧` (by 1), with value `δᵢⱼ` on `Xⱼ`; `mvPowerSeries_spansDerivations` of
   `Hironaka/Algebra/Local/CoordsOver.lean` (a `K`-derivation of `K⟦X⟧` is `∑ⱼ δ(Xⱼ) ∂/∂Xⱼ`) makes
   it `∂/∂Xᵢ`. So `Φ(∂F/∂Xᵢ) = ∂̂ᵢ(Φ F)`.
3. *Transport of the derivative ideals* (`D_map_cohenAlgEquivCoords`,
   `Dpow_map_cohenAlgEquivCoords`, `MC_map_cohenAlgEquivCoords`): `Φ(D(J)) = D(Φ(J))` by 2 and
   the description of `D` on generators (`D_span`); iterate.
4. *MC-invariance transports* (`isMCInvariant_comap_cohenAlgEquivCoords`) and *Proposition 94
   applies* (`isInvariantOnePlus_comap_cohenAlgEquivCoords`): `Φ⁻¹(Î)` is invariant under every
   automorphism of the form `1 + Φ⁻¹(MC(Î))`, the `1 + MC(I)` of Kollár's proof.
5. *Equality from inclusion* (`Ideal.map_eq_of_map_le`,
   `map_comap_cohenAlgEquivCoords_eq_of_isOnePlus`): Proposition 94 gives `g(J) ⊆ J` (the
   primitive of `IsInvariantOnePlus`); for an automorphism `g` of a Noetherian ring the chain
   `J ⊆ g⁻¹J ⊆ g⁻²J ⊆ ⋯` stabilizes, whence `g(J) = J` — Kollár's `φ^* Î = Î`,
   [Kol07, Definition 91, (2)].
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

section Noetherian

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- The maximal ideal of a local ring is the preimage of the maximal ideal under a ring
isomorphism. -/
theorem comap_maximalIdeal_ringEquiv {B : Type*} [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) : (maximalIdeal B).comap (e : A →+* B) = maximalIdeal A := by
  ext x
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff]
  constructor
  · intro h hx
    exact h (hx.map e)
  · intro h hx
    apply h
    have := hx.map e.symm
    rwa [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this

/-- In a Noetherian ring an automorphism mapping an ideal into itself maps it onto itself — the
ascending chain `J ⊆ e⁻¹J ⊆ e⁻²J ⊆ ⋯` stabilizes. -/
theorem _root_.Ideal.map_eq_of_map_le (e : A ≃+* A) (J : Ideal A) (h : J.map (e : A →+* A) ≤ J) :
    J.map (e : A →+* A) = J := by
  have h1 : J ≤ J.comap (e : A →+* A) := Ideal.map_le_iff_le_comap.mp h
  have hpow : ∀ n : ℕ, ((e ^ (n + 1) : A ≃+* A) : A →+* A) =
      (e : A →+* A).comp ((e ^ n : A ≃+* A) : A →+* A) := fun n => by
    ext x
    rw [pow_succ']
    rfl
  let S : ℕ →o Ideal A :=
    ⟨fun n => J.comap ((e ^ n : A ≃+* A) : A →+* A), monotone_nat_of_le_succ fun n => by
      rw [hpow, ← Ideal.comap_comap]
      exact Ideal.comap_mono h1⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance S
  have hNN := hN (N + 1) (Nat.le_succ N)
  change J.comap _ = J.comap _ at hNN
  rw [hpow, ← Ideal.comap_comap] at hNN
  have hJ : J = J.comap (e : A →+* A) :=
    Ideal.comap_injective_of_surjective ((e ^ N : A ≃+* A) : A →+* A) (e ^ N).surjective hNN
  conv_lhs => rw [hJ]
  exact Ideal.map_comap_of_surjective (e : A →+* A) e.surjective J

end Noetherian

section Cohen

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R]
variable {k : Type*} [Field k] [CharZero k] [Algebra k R]

local notation "R̂" => AdicCompletion (maximalIdeal R) R

variable {d : ℕ} (c : RegularCoords R d) (hk : c.IsLinearOver k)
variable (σ : ResidueField R →ₐ[k] AdicCompletion (maximalIdeal R) R)
  (hσ : ∀ a, residue (AdicCompletion (maximalIdeal R) R) (σ a) = residueFieldEquiv R a)

omit [CharZero k] in
include hk in
/-- The completed coordinate derivations are `k`-linear (`adicCompletion_algebraMap_eq_zero`). -/
theorem adicCompletion_isLinearOver : c.adicCompletion.IsLinearOver k := fun i a =>
  adicCompletion_algebraMap_eq_zero (c.pderiv i) (hk i) a

include hk in
/-- When the residue field is algebraic over `k` (the residue field of a closed point), the
completed coordinate derivations `∂̂ᵢ` vanish on the `k`-linear coefficient field `σ(K)` — for
`a ∈ K` with minimal polynomial `P`, `P'(σ a)·∂̂ᵢ(σ a) = 0` and `P'(σ a) = σ(P'(a))` is a unit,
`P` being separable in characteristic zero. -/
theorem adicCompletion_pderiv_coefficientField [Algebra.IsAlgebraic k (ResidueField R)] (i : Fin d)
    (a : ResidueField R) : c.adicCompletion.pderiv i (σ a) = 0 := by
  let δ : Derivation k R̂ R̂ := c.adicCompletion.pderivOver (adicCompletion_isLinearOver c hk) i
  have hP0 : Polynomial.aeval (σ a) (minpoly k a) = 0 := by
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have h1 := δ.map_aeval (minpoly k a) (σ a)
  rw [hP0, map_zero] at h1
  have hne : Polynomial.aeval a (Polynomial.derivative (minpoly k a)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable k a).aeval_derivative_ne_zero (minpoly.aeval k a)
  have hu : IsUnit (Polynomial.aeval (σ a) (Polynomial.derivative (minpoly k a))) := by
    rw [Polynomial.aeval_algHom_apply]
    exact (isUnit_iff_ne_zero.mpr hne).map σ
  have h2 : Polynomial.aeval (σ a) (Polynomial.derivative (minpoly k a)) * δ (σ a) = 0 := by
    rw [← smul_eq_mul]
    exact h1.symm
  exact (hu.mul_right_eq_zero).mp h2

/-- The Cohen isomorphism of the coordinates `c` for the coefficient field `σ`. -/
noncomputable abbrev cohenAlgEquivCoords (c : RegularCoords R d)
    (σ : ResidueField R →ₐ[k] AdicCompletion (maximalIdeal R) R)
    (hσ : ∀ a, residue (AdicCompletion (maximalIdeal R) R) (σ a) = residueFieldEquiv R a) :
    MvPowerSeries (Fin d) (ResidueField R) ≃ₐ[k] R̂ :=
  cohenAlgEquivOver σ hσ c.x c.span_x c.card

include hk in
/-- The coordinate derivation `∂/∂Xᵢ` of `K⟦X⟧` corresponds under the Cohen isomorphism to the
completed coordinate derivation `∂̂ᵢ` of `R̂`: `Φ(∂F/∂Xᵢ) = ∂̂ᵢ(Φ F)` (what makes "the
computations of (94) apply" in [Kol07, 95]). -/
theorem cohenAlgEquivCoords_pderiv [Algebra.IsAlgebraic k (ResidueField R)] (i : Fin d)
    (F : MvPowerSeries (Fin d) (ResidueField R)) :
    cohenAlgEquivCoords c σ hσ (pderiv (R := ResidueField R) i F) =
      c.adicCompletion.pderiv i (cohenAlgEquivCoords c σ hσ F) := by
  set Φ := cohenAlgEquivCoords c σ hσ with hΦ
  have hC : ∀ a, Φ (C a) = σ a := cohenAlgEquivOver_C σ hσ c.x c.span_x c.card
  have hX : ∀ j, Φ (X j) = algebraMap R R̂ (c.x j) := cohenAlgEquivOver_X σ hσ c.x c.span_x c.card
  have hkill : ∀ a, c.adicCompletion.pderiv i (σ a) = 0 :=
    adicCompletion_pderiv_coefficientField c hk σ i
  have hsymmC : ∀ a, Φ.symm (σ a) = C a := fun a => by rw [AlgEquiv.symm_apply_eq, hC]
  -- the transported derivation, as a `K`-derivation of `K⟦X⟧`
  let δ : Derivation (ResidueField R) (MvPowerSeries (Fin d) (ResidueField R))
      (MvPowerSeries (Fin d) (ResidueField R)) :=
    { toLinearMap :=
        { toFun := fun F => Φ.symm (c.adicCompletion.pderiv i (Φ F))
          map_add' := fun F G => by rw [map_add, map_add, map_add]
          map_smul' := fun a F => by
            simp only [RingHom.id_apply]
            rw [smul_eq_C_mul, map_mul, hC, Derivation.leibniz, hkill, smul_zero, add_zero,
              smul_eq_mul, map_mul, hsymmC, smul_eq_C_mul] }
      map_one_eq_zero' := by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [map_one, Derivation.map_one_eq_zero, map_zero]
      leibniz' := fun F G => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
          AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, smul_eq_mul, smul_eq_mul] }
  have hδX : ∀ j, δ (X j) = if i = j then 1 else 0 := fun j => by
    have h1 : c.adicCompletion.pderiv i (algebraMap R R̂ (c.x j)) = if i = j then 1 else 0 :=
      c.adicCompletion_pderiv_x i j
    change Φ.symm (c.adicCompletion.pderiv i (Φ (X j))) = _
    rw [hX, h1]
    split_ifs <;> simp
  have hspans := mvPowerSeries_spansDerivations (ResidueField R) d δ F
  have hδF : δ F = pderiv (R := ResidueField R) i F := by
    rw [hspans]
    simp only [RegularCoords.mvPowerSeries, Derivation.restrictScalars_apply, hδX, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have : Φ.symm (c.adicCompletion.pderiv i (Φ F)) = pderiv (R := ResidueField R) i F := hδF
  rw [AlgEquiv.symm_apply_eq] at this
  exact this.symm

include hk in
/-- The first derivative ideal transports along the Cohen isomorphism, `Φ(D(J)) = D(Φ(J))`. -/
theorem D_map_cohenAlgEquivCoords [Algebra.IsAlgebraic k (ResidueField R)]
    (J : Ideal (MvPowerSeries (Fin d) (ResidueField R))) :
    ((RegularCoords.stdMvPowerSeries (ResidueField R) d).D J).map
        (cohenAlgEquivCoords c σ hσ) =
      c.adicCompletion.D (J.map (cohenAlgEquivCoords c σ hσ)) := by
  set Φ := cohenAlgEquivCoords c σ hσ with hΦ
  have hJ : J = Ideal.span (J : Set (MvPowerSeries (Fin d) (ResidueField R))) :=
    (Ideal.span_eq J).symm
  conv_lhs => rw [hJ, RegularCoords.D_span]
  rw [Ideal.map_span, Ideal.map, RegularCoords.D_span, Set.image_union, Set.image_iUnion]
  congr 2
  refine Set.iUnion_congr fun i => ?_
  rw [Set.image_image, Set.image_image]
  congr 1
  funext f
  exact cohenAlgEquivCoords_pderiv c hk σ hσ i f

include hk in
/-- The higher derivative ideals transport along the Cohen isomorphism. -/
theorem Dpow_map_cohenAlgEquivCoords [Algebra.IsAlgebraic k (ResidueField R)] (r : ℕ)
    (J : Ideal (MvPowerSeries (Fin d) (ResidueField R))) :
    ((RegularCoords.stdMvPowerSeries (ResidueField R) d).Dpow r J).map
        (cohenAlgEquivCoords c σ hσ) =
      c.adicCompletion.Dpow r (J.map (cohenAlgEquivCoords c σ hσ)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [RegularCoords.Dpow_succ, RegularCoords.Dpow_succ, D_map_cohenAlgEquivCoords c hk, ih]

include hk in
/-- The maximal contact ideal transports along the Cohen isomorphism, `Φ(MC(J)) = MC(Φ(J))`. -/
theorem MC_map_cohenAlgEquivCoords [Algebra.IsAlgebraic k (ResidueField R)]
    (J : Ideal (MvPowerSeries (Fin d) (ResidueField R))) (m : ℕ) :
    ((RegularCoords.stdMvPowerSeries (ResidueField R) d).MC J m).map
        (cohenAlgEquivCoords c σ hσ) =
      c.adicCompletion.MC (J.map (cohenAlgEquivCoords c σ hσ)) m :=
  Dpow_map_cohenAlgEquivCoords c hk σ hσ (m - 1) J

include hk in
/-- MC-invariance ([Kol07, 53]) of `Î ⊆ R̂` in the completed coordinates transports to
MC-invariance of `Φ⁻¹(Î) ⊆ K⟦X⟧` in the standard coordinates. -/
theorem isMCInvariant_comap_cohenAlgEquivCoords [Algebra.IsAlgebraic k (ResidueField R)]
    (Î : Ideal R̂) (m : ℕ) (h : c.adicCompletion.IsMCInvariant Î m) :
    (RegularCoords.stdMvPowerSeries (ResidueField R) d).IsMCInvariant
      (Î.comap (cohenAlgEquivCoords c σ hσ)) m := by
  set Φ := cohenAlgEquivCoords c σ hσ with hΦ
  set J := Î.comap Φ with hJ
  have hJΦ : J.map Φ = Î := Ideal.map_comap_of_surjective Φ Φ.surjective Î
  change _ * _ ≤ J
  refine Ideal.map_le_iff_le_comap.mp ?_
  rw [Ideal.map_mul, MC_map_cohenAlgEquivCoords c hk, D_map_cohenAlgEquivCoords c hk, hJΦ]
  exact h

include hk in
/-- For `Î ⊆ R̂` MC-invariant with `MC(Î) ⊆ 𝔪R̂`, the ideal `Φ⁻¹(Î)` of `K⟦X⟧` is invariant under
every automorphism of the form `1 + Φ⁻¹(MC(Î))` ([Kol07, Proposition 94], (2) ⇒ (1), as applied
in [Kol07, 95]). -/
theorem isInvariantOnePlus_comap_cohenAlgEquivCoords [Algebra.IsAlgebraic k (ResidueField R)]
    (Î : Ideal R̂) (m : ℕ) (h : c.adicCompletion.IsMCInvariant Î m)
    (hB : c.adicCompletion.MC Î m ≤ maximalIdeal R̂) :
    IsInvariantOnePlus (Î.comap (cohenAlgEquivCoords c σ hσ))
      ((c.adicCompletion.MC Î m).comap (cohenAlgEquivCoords c σ hσ)) := by
  set Φ := cohenAlgEquivCoords c σ hσ with hΦ
  set J := Î.comap Φ with hJ
  have hJΦ : J.map Φ = Î := Ideal.map_comap_of_surjective Φ Φ.surjective Î
  have hMC : (RegularCoords.stdMvPowerSeries (ResidueField R) d).MC J m =
      (c.adicCompletion.MC Î m).comap Φ := by
    rw [← hJΦ, ← MC_map_cohenAlgEquivCoords c hk σ hσ J m,
      Ideal.comap_map_of_bijective Φ Φ.bijective]
  have hB' : (RegularCoords.stdMvPowerSeries (ResidueField R) d).MC J m ≤
      maximalIdeal (MvPowerSeries (Fin d) (ResidueField R)) := by
    rw [hMC, ← comap_maximalIdeal_ringEquiv Φ.toRingEquiv]
    exact Ideal.comap_mono hB
  rw [← hMC]
  exact (isMCInvariant_iff_isInvariantOnePlus J m hB').mp
    (isMCInvariant_comap_cohenAlgEquivCoords c hk σ hσ Î m h)

include hk in
/-- Kollár's "`φ^* Î = Î`" ([Kol07, 95]; [Kol07, Definition 91, (2)]), the equality
form: every automorphism `g` of the form `1 + Φ⁻¹(MC(Î))` satisfies `g(Φ⁻¹ Î) = Φ⁻¹ Î`. -/
theorem map_comap_cohenAlgEquivCoords_eq_of_isOnePlus [Algebra.IsAlgebraic k (ResidueField R)]
    (Î : Ideal R̂) (m : ℕ) (h : c.adicCompletion.IsMCInvariant Î m)
    (hB : c.adicCompletion.MC Î m ≤ maximalIdeal R̂)
    (g : MvPowerSeries (Fin d) (ResidueField R) ≃ₐ[ResidueField R]
      MvPowerSeries (Fin d) (ResidueField R))
    (hg : IsOnePlus ((c.adicCompletion.MC Î m).comap (cohenAlgEquivCoords c σ hσ)) g) :
    (Î.comap (cohenAlgEquivCoords c σ hσ)).map (g : MvPowerSeries (Fin d) (ResidueField R) →+*
      MvPowerSeries (Fin d) (ResidueField R)) = Î.comap (cohenAlgEquivCoords c σ hσ) :=
  Ideal.map_eq_of_map_le g.toRingEquiv _
    (isInvariantOnePlus_comap_cohenAlgEquivCoords c hk σ hσ Î m h hB g hg)

end Cohen

end IsLocalRing
