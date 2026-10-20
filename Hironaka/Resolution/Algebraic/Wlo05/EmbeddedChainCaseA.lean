/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColonRegular
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealCorners
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainLift
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainMonomial
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The chain form when the centre is the component itself

The case of the statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) in which the absorbing centre is the
strict transform `c̃` of the reduced component itself (Step 2 of the proof of [Kol07, Theorem 107]:
the centre of the round of order `1` is the cosupport of the nonmonomial part): a smooth
hypersurface `Γ` having simple normal crossings with the boundary `E` and contained in no member of
`E`, with `J ⊆ Γ` and the nonmonomial part `N(J)` of order `≤ 1` along `Γ`. Then at every point `p`
of `Γ` the ideal `J` is in chain form along `Γ` with the chain `Γ`'s own coordinates and unit level
monomials: `J_p = M(J)_p · Γ_p` (`chainRelativeAt_of_le_isSmoothDivisor`).

The proof is local algebra in the regular local ring `𝒪_{X,p}`. `HasSncWith` provides coordinates
with `Γ_p = (z_j : j ∈ s)`; `NotContainedInMembers` puts no member's coordinate in `s`, so the
enumeration of `s` is a chain avoiding the members; the splitting `J = N(J) · M(J)` with `M(J)_p` a
monomial in the members' coordinates, coprime to the prime `Γ_p`, gives `N(J)_p ⊆ Γ_p`; and the
ring lemma `eq_span_singleton_of_le_of_exists_notMem_sq` (`Γ_p` principal, `N(J)_p ⊄ 𝔪²` from
`ord_p N(J) ≤ 1`) gives `N(J)_p = Γ_p`. The monomial part is restored by
`chainRelativeAt_mul_monomial`. Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Core`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  Hironaka.BMO IsLocalRing

namespace Hironaka.Resolution

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The chain form when the centre is the component itself: on `X` smooth over `k` with `E` snc, a
smooth divisor `Γ` having snc with `E` and contained in no member of `E` near its points, with
`J ≤ Γ` and the nonmonomial part of `J` of order `≤ 1` at the points of `Γ`, carries the chain form
of `J` at every point of `Γ`: `J_p = M(J)_p · Γ_p`, the chain being `Γ`'s own coordinates with unit
level monomials. -/
theorem chainRelativeAt_of_le_isSmoothDivisor (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
    [NoetherianSpace X] {E : DivisorFamily X} (hE : E.IsSnc) {J Γ : X.IdealSheafData}
    (hΓ : IsSmoothDivisor Γ) (hsnc : E.HasSncWith Γ) (hJΓ : J ≤ Γ)
    (hord : ∀ p ∈ Γ.support, (nonmonomialPart J E).ord p ≤ 1)
    (hΓE : NotContainedInMembers E Γ) :
    ∀ p ∈ Γ.support, ChainRelativeAt E J Γ p := by
  intro p hp
  have hLN : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hreg : IsRegularLocalRing (X.presheaf.stalk p) :=
    isRegularLocalRing_stalk f p
  -- the fine split `J = N(J) · M(J)`
  have hsplit : J = nonmonomialPart J E * E.monomial (fun η => (J.ord η).toNat) := by
    rw [← monomialPart_eq_monomial, mul_comm]
    exact (Snc.monomialPart_mul_nonmonomialPart f E hE J).symm
  -- the chain coordinates: `HasSncWith`'s at `p`, `Γ_p = (z_j : j ∈ s)`
  obtain ⟨n, z, ⟨hz, c, hc, hEc⟩, s, hΓs⟩ := hsnc p hp
  have hΓs' : Γ.stalkIdeal p = Ideal.span (z '' ↑s) := hΓs
  have hz' : maximalIdeal (X.presheaf.stalk p) = Ideal.span (Set.range z) := hz.1.symm
  -- `Γ_p = (g)` with `g` a regular parameter
  obtain ⟨g, hg, hg2, hΓg⟩ := hΓ.2 p hp
  -- no member's coordinate is one of `Γ`'s
  have hcs : ∀ j, c j ∉ s := fun j =>
    notMem_of_not_stalkIdeal_le hz hΓs (hEc j) (hΓE p hp j.1 j.2)
  -- `s` is non-empty: `Γ_p ≠ ⊥`
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with hs | hs
    · exfalso
      rw [hs, Finset.coe_empty, Set.image_empty, Ideal.span_empty] at hΓs'
      have hgΓ : g ∈ Γ.stalkIdeal p := hΓg ▸ Ideal.mem_span_singleton_self g
      rw [hΓs', Ideal.mem_bot] at hgΓ
      exact hg2 (hgΓ ▸ (maximalIdeal (X.presheaf.stalk p) ^ 2).zero_mem)
    · exact hs
  obtain ⟨r, hr⟩ : ∃ r, s.card = r + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hne).ne'
  obtain ⟨σ, hσinj, hσrange⟩ : ∃ σ : Fin (r + 1) → Fin n, Function.Injective σ ∧
      Set.range σ = ↑s :=
    ⟨s.orderEmbOfFin hr, (s.orderEmbOfFin hr).injective, Finset.range_orderEmbOfFin s hr⟩
  have hσs : ∀ i, σ i ∈ s := fun i => by
    have := Set.mem_range_self (f := σ) i
    rwa [hσrange, Finset.mem_coe] at this
  have hΓσ : Γ.stalkIdeal p = Ideal.span (Set.range (z ∘ σ)) := by
    rw [Set.range_comp, hσrange, hΓs']
  have hcoords : ChainCoords E Γ p z c σ (fun _ => (0 : Fin n → ℕ)) :=
    ⟨hz, hc, hEc, hσinj, fun i j hij => hcs j (hij ▸ hσs i), fun _ _ h => absurd rfl h, hΓσ⟩
  -- `Γ_p` is prime
  have hprime : (Γ.stalkIdeal p).IsPrime := by
    rw [hΓs']
    exact isPrime_span_image_finset hz' hz.2 s
  -- `N(J)_p ⊆ Γ_p`: the monomial part is coprime to `Γ_p`
  have hNle : (nonmonomialPart J E).stalkIdeal p ≤ Γ.stalkIdeal p := by
    obtain ⟨b, hb⟩ := exists_stalkIdeal_monomial_eq_prod E hE (fun η => (J.ord η).toNat) p
    obtain ⟨b', hb', hMb⟩ := hcoords.prod_pow_stalkIdeal_eq_span b
    have hJp : (nonmonomialPart J E).stalkIdeal p * Ideal.span {monomialOf z b'} ≤
        Γ.stalkIdeal p := by
      rw [← hMb, ← hb, ← IdealSheafData.stalkIdeal_mul, ← hsplit]
      exact IdealSheafData.stalkIdeal_mono hJΓ p
    have hmono : monomialOf z b' ∉ Γ.stalkIdeal p := by
      intro hm
      unfold monomialOf at hm
      obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
      have hbk : b' k ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hk
        exact hprime.ne_top ((Ideal.eq_top_iff_one _).mpr hk)
      have hkΓ : z k ∈ Γ.stalkIdeal p := hprime.mem_of_pow_mem _ hk
      rw [hΓs', ← Ideal.span_singleton_le_iff_mem,
        span_singleton_le_span_image_iff hz' hz.2 s k] at hkΓ
      obtain ⟨j, rfl⟩ := hb' k hbk
      exact hcs j hkΓ
    intro x hx
    have hxm : x * monomialOf z b' ∈ Γ.stalkIdeal p :=
      hJp (Ideal.mul_mem_mul hx (Ideal.mem_span_singleton_self _))
    exact (hprime.mem_or_mem hxm).resolve_right hmono
  -- the ring corner: `N(J)_p = (g) = Γ_p`
  have hN : (nonmonomialPart J E).stalkIdeal p = Γ.stalkIdeal p := by
    rw [hΓg] at hNle ⊢
    refine eq_span_singleton_of_le_of_exists_notMem_sq hg hNle ?_
    have h2 : ¬ ((2 : ℕ) : ℕ∞) ≤ (nonmonomialPart J E).ord p := fun h => by
      have h21 : ((2 : ℕ) : ℕ∞) ≤ 1 := h.trans (hord p hp)
      exact absurd (by exact_mod_cast h21 : (2 : ℕ) ≤ 1) (by norm_num)
    rw [IdealSheafData.le_ord_iff] at h2
    exact IsConcreteLE.not_le_iff_exists.mp h2
  -- the chain form of `N(J)`, then S4 restores `M(J)`
  have hNchain : ChainRelativeAt E (nonmonomialPart J E) Γ p := by
    refine ⟨n, z, c, r, σ, fun _ => (0 : Fin n → ℕ), (0 : Fin n → ℕ), hcoords,
      fun _ h => absurd rfl h, ?_⟩
    rw [hN, hΓσ, monomialOf_zero, Ideal.span_singleton_one, Ideal.top_mul]
    simp only [monomialOf_zero]
    exact (chainIdeal_one _).symm
  rw [hsplit]
  exact chainRelativeAt_mul_monomial hE hNchain _

end Hironaka.Resolution
