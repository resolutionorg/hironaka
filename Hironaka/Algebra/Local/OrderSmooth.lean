/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.OrderFlat
public import Mathlib.RingTheory.Smooth.Locus
import Hironaka.Algebra.Local.OrderPolynomial
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# The order under the local maps of étale and smooth algebras

For `R → S` smooth and a prime `q` of `S` over `p`, the local map `R_p → S_q` reflects the powers
of the maximal ideal (`OrdFaithful`, `Hironaka/Algebra/Local/OrderFlat.lean`), hence preserves the
order of every ideal: the local form of the invariance of the order under smooth morphisms stated in
[Hau03, Appendix A].

* The étale case (`ordFaithful_localRingHom_of_etale`): `R_p → S_q` is flat (the localization of a
  flat algebra at a prime lying over a prime), local, and unramified and essentially of finite
  type, so `𝔪_p S_q = 𝔪_q` ([Sta, Tag 00UW], Mathlib's
  `Algebra.FormallyUnramified.map_maximalIdeal`); the flat local lemma
  `ordFaithful_of_flat_of_map_maximalIdeal_eq` applies.
* The smooth case (`ordFaithful_localRingHom_of_isSmoothAt`): a finitely presented algebra smooth
  at `q` is, near `q`, standard étale over a polynomial algebra (Mathlib's
  `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`): `S_q ≅ T_{q'}` for `T = S[1/f]`,
  `f ∉ q`, and `R → T` factors as `R → R[X₁, …, Xₙ] → T` with the second map étale.  `R_p → T_{q'}`
  is then the composite of the polynomial case (`ordFaithful_localRingHom_mvPolynomial_C`,
  `Hironaka/Algebra/Local/OrderPolynomial.lean`) and the étale case, and `OrdFaithful` composes and
  transports along isomorphisms.

Used for the invariance of the order under smooth morphisms of schemes
(`Hironaka/Scheme/IdealSheaf/Order/Smooth.lean`).
-/

public section

namespace IsLocalRing

open IsLocalRing

/-- The étale case: for `R → S` étale and a prime `q` of `S` over `p`, the local map `R_p → S_q`
reflects the powers of the maximal ideal.  It is flat and local with `𝔪_p S_q = 𝔪_q` (unramified
and essentially of finite type, [Sta, Tag 00UW]: Mathlib's
`Algebra.FormallyUnramified.map_maximalIdeal`), so `ordFaithful_of_flat_of_map_maximalIdeal_eq`
applies. -/
theorem ordFaithful_localRingHom_of_etale {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (q : Ideal S) [q.IsPrime] {p : Ideal R} [p.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    OrdFaithful (Localization.localRingHom p q (algebraMap R S) hpq) := by
  have : q.LiesOver p := ⟨hpq⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom p q (algebraMap R S) _
  have : Algebra.EssFiniteType R (Localization.AtPrime q) := Algebra.EssFiniteType.comp R S _
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R _ _
  have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars R _ _
  have h := ordFaithful_of_flat_of_map_maximalIdeal_eq (A := Localization.AtPrime p)
    (B := Localization.AtPrime q) Algebra.FormallyUnramified.map_maximalIdeal
  rwa [Localization.AtPrime.algebraMap_eq] at h

/-- **The order under the local maps of a smooth algebra**: for `R → S` of finite presentation
and smooth at the prime `q` of `S` over `p`, the local map `R_p → S_q` reflects the powers of the
maximal ideal.  Near `q`, `S` is standard étale over a polynomial algebra `R[X₁, …, Xₙ]`:
`S_q ≅ S[1/f]_{q'}` with `f ∉ q`, and `R_p → S[1/f]_{q'}` is the polynomial case followed by the
étale case. -/
theorem ordFaithful_localRingHom_of_isSmoothAt {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    [Algebra.IsSmoothAt R q] {p : Ideal R} [p.IsPrime] (hpq : p = q.comap (algebraMap R S)) :
    OrdFaithful (Localization.localRingHom p q (algebraMap R S) hpq) := by
  obtain ⟨f, hfq, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := q)
  -- `S_q ≅ T_{q'}` for `T = S[1/f]`, `q' = q T`
  have hdisj : Disjoint (Submonoid.powers f : Set S) (q : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hfq (Ideal.IsPrime.mem_of_pow_mem inferInstance k hk)
  have hq' : (q.map (algebraMap S (Localization.Away f))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ q inferInstance hdisj
  have hq'q : (q.map (algebraMap S (Localization.Away f))).comap
      (algebraMap S (Localization.Away f)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) _ inferInstance hdisj
  have : IsLocalization.AtPrime
      (Localization.AtPrime (q.map (algebraMap S (Localization.Away f)))) q := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers f) (S := Localization.Away f)
      (Localization.AtPrime (q.map (algebraMap S (Localization.Away f))))
      (q.map (algebraMap S (Localization.Away f)))
    have hM : ((q.map (algebraMap S (Localization.Away f))).comap
        (algebraMap S (Localization.Away f))).primeCompl = q.primeCompl :=
      Submonoid.ext fun x => by rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hq'q]
    unfold IsLocalization.AtPrime at this ⊢
    rw [hM] at this
    exact this
  let e : Localization.AtPrime q ≃ₐ[S]
      Localization.AtPrime (q.map (algebraMap S (Localization.Away f))) :=
    IsLocalization.algEquiv q.primeCompl _ _
  -- the prime `p'` of `R[X₁, …, Xₙ]` under `q'`, over `p`
  have hp' : p = ((q.map (algebraMap S (Localization.Away f))).comap
      (algebraMap (MvPolynomial (Fin n) R) (Localization.Away f))).comap
      (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) := by
    rw [Ideal.comap_comap, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R S (Localization.Away f), ← Ideal.comap_comap, hq'q]
    exact hpq
  have h₁ := ordFaithful_localRingHom_mvPolynomial_C n _ hp'
  have h₂ := ordFaithful_localRingHom_of_etale (R := MvPolynomial (Fin n) R)
    (q.map (algebraMap S (Localization.Away f)))
    (p := (q.map (algebraMap S (Localization.Away f))).comap
      (algebraMap (MvPolynomial (Fin n) R) (Localization.Away f))) rfl
  refine ((h₁.comp h₂).comp_ringEquiv (e.symm : Localization.AtPrime
    (q.map (algebraMap S (Localization.Away f))) ≃+* Localization.AtPrime q)).congr ?_
  refine (Localization.localRingHom_unique p q _ hpq fun r => ?_).symm
  rw [RingHom.comp_apply, RingHom.comp_apply, Localization.localRingHom_to_map,
    Localization.localRingHom_to_map, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) (Localization.Away f),
    IsScalarTower.algebraMap_apply R S (Localization.Away f),
    ← IsScalarTower.algebraMap_apply S (Localization.Away f)]
  exact e.symm.commutes (algebraMap R S r)

end IsLocalRing
