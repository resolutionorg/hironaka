/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Algebra.Local.Regular
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Resolution.Algebraic.Wlo05.ChainRelativeLift
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Lifting the chain form across a smooth hypersurface

The scheme form of `exists_chain_lift` (`Hironaka.Resolution.Algebraic.Wlo05.ChainRelativeLift`),
the induction step of the statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): on `X` smooth over `k`, for a smooth
hypersurface `H` (`IsSmoothDivisor`) with `H ≤ J` (the round's ideal contains `H`'s: maximal contact
persists for the nonmonomial part) and `H ≤ Γ` (`Γ ⊆ H`), the chain-relative form of `J|_H` along
`Γ|_H` at a point `w` of `H` gives the chain-relative form of `J` along `Γ` at `ι w` on `X`, with
top monomial `1`. The stalk map of `ι : H ↪ X` is surjective with kernel `H_p`, the generator of
`H_p` is completed to a regular system of parameters, the restricted family's stalks are the images
of the members' stalks (`stalkIdeal_comap`), and the members through `w` on `H` are exactly the
members through `p` on `X` (`AlgebraicGeometry.mem_support_comap_iff_apply`). The coordinates are
those of
[Kol07, Definition 24]; the hypersurfaces of maximal contact are those of [Kol07, Theorem 80], and
the restriction of the ideal to a hypersurface through the centre is that of [Kol07, Lemma 62].
The lift is used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainPushforward`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IsLocalRing Scheme.IdealSheafData
  Ideal

namespace Hironaka.Resolution

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The monomial with zero exponents is `1`. -/
theorem monomialOf_zero {R : Type*} [CommRing R] {n : ℕ} (z : Fin n → R) :
    monomialOf z (0 : Fin n → ℕ) = 1 := by
  simp [monomialOf]

/-- The closed-immersion form of the lift: the chain form lifts along ANY closed immersion
`g : Y ⟶ X` with kernel the smooth hypersurface `H` (a hypersurface of maximal contact,
[Kol07, Theorem 80 (2)], in the application); `chainRelativeAt_of_hypersurface` is the instance
`g := H.subschemeι`, and the pushforward of a run along `H ↪ X` embeds its stages by closed
immersions with kernel the strict transform of `H` (`ker_pushforwardStageHom`). The regularity `hY`
of the source's stalks is derivable (`g` factors through `Y ≅ H.subscheme`) and is carried as a
hypothesis for convenience: `hH.1` for the hypersurface, the stage's smoothness over `k` for a
stage of the pushforward's inner run. -/
theorem chainRelativeAt_of_closedImmersion {Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] {E : DivisorFamily X} (hE : E.IsSnc) {H : X.IdealSheafData} (hH : IsSmoothDivisor H)
    {J Γ : X.IdealSheafData} (hHJ : H ≤ J) (hHΓ : H ≤ Γ) (g : Y ⟶ X) [IsClosedImmersion g]
    (hg : g.ker = H) (hY : ∀ w : Y, IsRegularLocalRing (Y.presheaf.stalk w)) {w : Y}
    (h : ChainRelativeAt (E.comap g) (J.comap g) (Γ.comap g) w) :
    ChainRelativeAt E J Γ (g w) := by
  have hwH : g w ∈ H.support := by
    rw [← hg, ← SetLike.mem_coe, Scheme.Hom.support_ker]
    exact subset_closure ⟨w, rfl⟩
  obtain ⟨n', w', c', r, σ', a', b', hcc, hb', hJ'⟩ := h
  obtain ⟨hw', hc'inj, hc'mem, hσ'inj, hσ'c, ha', hΓ'⟩ := hcc
  -- the stalk map of `H ↪ X` at `w`: surjective, kernel `H_p`
  have hφ : Function.Surjective (g.stalkMap w).hom := g.stalkMap_surjective w
  have hker : RingHom.ker (g.stalkMap w).hom = H.stalkIdeal (g w) := by
    rw [ker_stalkMap_of_isClosedImmersion, hg]
  have hregX := isRegularLocalRing_stalk f (g w)
  have hregH : IsRegularLocalRing (Y.presheaf.stalk w) := hY w
  -- a generator of `H_p`, completed to a regular system of parameters
  obtain ⟨a, ha𝔪, ha2, haH⟩ := hH.2 _ (hwH)
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast
    (X.presheaf.stalk (g w))
  obtain ⟨z, ⟨j₀, hzj₀⟩, hz𝔪⟩ :=
    exists_span_eq_maximalIdeal_of_notMem_sq hn.symm ha𝔪 ha2
  have hz : IsRegularSystemOfParameters z := ⟨hz𝔪.symm, hn.symm⟩
  have hker' : RingHom.ker (g.stalkMap w).hom = span {z j₀} := by
    rw [hker, haH, hzj₀]
  -- the members' generators at `p`
  obtain ⟨m, y, -, cE, -, hcE⟩ := hE.2 (g w)
  -- the members through `w` on `H` are the members through `p` on `X`
  have hmem : ∀ j : {j : E.ι // g w ∈ (E.component j).support},
      w ∈ ((E.comap g).component j.1).support :=
    fun j => (mem_support_comap_iff_apply _ _ _).mpr j.2
  have hce : ∀ j : {j : E.ι // g w ∈ (E.component j).support},
      span {w' (c' ⟨j.1, hmem j⟩)} = span {(g.stalkMap w).hom (y (cE j))} := by
    intro j
    rw [← hc'mem ⟨j.1, hmem j⟩]
    change ((E.component j.1).comap g).stalkIdeal w = _
    have hcE' : (E.component j.1).stalkIdeal (g w) = span {y (cE j)} := hcE j
    rw [IdealSheafData.stalkIdeal_comap, hcE', map_span, Set.image_singleton]
  have hc'' : Function.Injective fun j : {j : E.ι // g w ∈ (E.component j).support} =>
      c' ⟨j.1, hmem j⟩ := by
    intro j j' hjj
    exact Subtype.ext (Subtype.mk.inj (hc'inj hjj))
  have hrange : ∀ k : Fin n', k ∈ Set.range c' → k ∈ Set.range
      fun j : {j : E.ι // g w ∈ (E.component j).support} => c' ⟨j.1, hmem j⟩ := by
    rintro k ⟨⟨j, hj⟩, rfl⟩
    exact ⟨⟨j, (mem_support_comap_iff_apply _ _ _).mp hj⟩, rfl⟩
  -- the two ideals contain `H_p`
  have hJh : z j₀ ∈ J.stalkIdeal (g w) := by
    rw [hzj₀]
    exact IdealSheafData.stalkIdeal_mono hHJ _ (haH ▸ mem_span_singleton_self a)
  have hΓh : z j₀ ∈ Γ.stalkIdeal (g w) := by
    rw [hzj₀]
    exact IdealSheafData.stalkIdeal_mono hHΓ _ (haH ▸ mem_span_singleton_self a)
  have hΓ : (Γ.stalkIdeal (g w)).map (g.stalkMap w).hom =
      span (Set.range (w' ∘ σ')) := by
    rw [← IdealSheafData.stalkIdeal_comap]
    exact hΓ'
  have hJ : (J.stalkIdeal (g w)).map (g.stalkMap w).hom =
      span {monomialOf w' b'} * chainIdeal (w' ∘ σ') fun i => monomialOf w' (a' i) := by
    rw [← IdealSheafData.stalkIdeal_comap]
    exact hJ'
  obtain ⟨zz, c, σ, aa, hzz, hcinj, hcmem, hσinj, hσc, hsupp, hΓX, hJX⟩ :=
    exists_chain_lift (g.stalkMap w).hom hφ hz hker' (fun j => y (cE j)) w' hw' _ hc''
      hce σ' hσ'inj (fun i j => hσ'c i ⟨j.1, hmem j⟩) a' (fun i k hk => hrange k (ha' i k hk)) b'
      (fun k hk => hrange k (hb' k hk)) _ _ hJh hΓh hΓ hJ
  refine ⟨n' + 1, zz, c, r + 1, σ, aa, 0,
    ⟨hzz, hcinj, fun j => (show (E.component j.1).stalkIdeal _ = _ from hcE j).trans (hcmem j),
      hσinj, hσc, hsupp, hΓX⟩,
    fun k h0 => absurd rfl h0, ?_⟩
  rw [hJX, monomialOf_zero, span_singleton_one, Ideal.top_mul]

/-- On `X` smooth over `k`, the chain-relative form of `J|_H` along `Γ|_H` at a point of the smooth
hypersurface `H` lifts to the chain-relative form of `J` along `Γ` at that point of `X`, when
`H ≤ J` and `H ≤ Γ`; the top monomial of the lift is `1` and the level's top monomial becomes the
first chain factor. -/
theorem chainRelativeAt_of_hypersurface (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
    {E : DivisorFamily X} (hE : E.IsSnc) {H : X.IdealSheafData} (hH : IsSmoothDivisor H)
    {J Γ : X.IdealSheafData} (hHJ : H ≤ J) (hHΓ : H ≤ Γ) {w : H.subscheme}
    (h : ChainRelativeAt (E.comap H.subschemeι) (J.comap H.subschemeι) (Γ.comap H.subschemeι) w) :
    ChainRelativeAt E J Γ (H.subschemeι w) :=
  chainRelativeAt_of_closedImmersion f hE hH hHJ hHΓ H.subschemeι
      (IdealSheafData.ker_subschemeι H) hH.1.isRegularAt h

end Hironaka.Resolution
