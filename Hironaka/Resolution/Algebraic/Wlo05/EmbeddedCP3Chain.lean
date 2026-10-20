/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Rebase
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Restrict
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Split
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainLift
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Snc.TrivialTotalTransform
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Hironaka.Scheme.Snc.Defs
import Hironaka.Algebra.Local.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Resolution.Algebraic.Snc.SncOnTransport

/-!
# The pointwise pass along a hypersurface of maximal contact

Step 2.2 of the proof of [Kol07, Theorem 103] applies [Kol07, Lemma 102] to the triple
`(X_r, I_r, H_r + F_r)` with the hypersurface of maximal contact `H_r` as first member. For the
statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) the centres of that run must be
classified for the outer data `(I_r, F_r)`, the boundary without `H_r`. Its first blow-up `Z₋₁` is
the union of the components of `H_r` inside `V(I_r)`; at a point `q` of it the stalk of `I_r` lies
in that of `H_r` (`H_r ≤ I_r` is the maximal contact at the mark `1`, and `H_r ⊆ V(I_r)` along
`Z₋₁`), so a K-shape of `I_r` is impossible — its top generator is a unit times a monomial in chain
coordinates, outside `(h)` — and an I-shape has `Z_q = (f₀) = (h)`, the absorption, the chain of
length one (`centerClassifiedAt_of_stalkIdeal_le_of_isSncAt_append`). At a later centre — the
push-forward of a centre of the inductive run on `H_r` — the pass is the variant for a chain
hypersurface of the pass over a member (`centerClassifiedAt_of_comap_member`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Pass`): in outer chain coordinates the equation `h`
of `H_r` lies in `I_r` and outside `(z_C) + 𝔪²` (so the top exponent `b` is `0`); the flag is
re-based to make `h` a chain coordinate (`exists_update_chainKIdeal_eq`,
`exists_update_chainIdeal_eq`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Rebase`); the
coordinates and the shape descend to `H_r` along the stalk map (`exists_restricted_chain_coords`,
`map_chainKIdeal_succAbove_of_trivial`, `map_chainIdeal_succAbove_of_trivial`); the inner
classification is read there; the stratum lifts (`stratumIn_comap_of_stratumIn_succAbove`,
`terminalIn_comap_of_terminalIn_succAbove`, the absorption through `comap_span_range_succAbove_eq`)
and transfers back to the original flag (`stratumIn_of_stratumIn_update_chainKIdeal`,
`stratumIn_of_stratumIn_update_chainIdeal`, `terminalIn_of_terminalIn_update`,
`span_range_update_eq_of_mem_chainIdeal`). This is `centerClassifiedAt_of_comap_chain`. The
bookkeeping: `IsSncAt` transports along an injection of families with equal members
(`isSncAt_of_injective`), and the embedding of the total transforms of a sub-family has its
complement characterised both ways (`exists_embeds_totalTransformSeq'`). The chain coordinates are
those of [Kol07, Definition 24]. This argument is not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step22`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IsLocalRing IdealSheafData
  BlowUpSequence Scheme.IdealSheafData Hironaka.Snc

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- `IsSncAt` transports along an injection of families with equal members. -/
theorem isSncAt_of_injective {E F : DivisorFamily X} (e : F.ι → E.ι) (he : Function.Injective e)
    (hcomp : ∀ a, E.component (e a) = F.component a) {x : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk x} (h : E.IsSncAt x z) : F.IsSncAt x z := by
  obtain ⟨hz, c, hcinj, hcmem⟩ := h
  refine ⟨hz, fun a => c ⟨e a.1, by rw [hcomp]; exact a.2⟩, ?_, ?_⟩
  · intro a₁ a₂ h12
    exact Subtype.ext (he (Subtype.mk.inj (hcinj h12)))
  · intro a
    rw [← hcomp]
    exact hcmem ⟨e a.1, by rw [hcomp]; exact a.2⟩

/-- `exists_embeds_totalTransformSeq` with the complement characterised both ways: the members of
the total transform of `E₂` outside the range are exactly the transforms of the members of `E₂`
outside the range of `e₀`. -/
theorem exists_embeds_totalTransformSeq' : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    {E₁ E₂ : DivisorFamily X} (e₀ : E₁.ι → E₂.ι) (_ : Function.Injective e₀)
    (_ : ∀ a, E₂.component (e₀ a) = E₁.component a) (i : Fin (S.length + 1)),
    ∃ e : (S.totalTransformSeq E₁ i).ι → (S.totalTransformSeq E₂ i).ι, Function.Injective e ∧
      (∀ b, (S.totalTransformSeq E₂ i).component (e b) =
        (S.totalTransformSeq E₁ i).component b) ∧
      (∀ b, b ∉ Set.range e → ∃ a, a ∉ Set.range e₀ ∧ b = S.originalIdx E₂ i a) ∧
      ∀ a, a ∉ Set.range e₀ → S.originalIdx E₂ i a ∉ Set.range e
  | _, nil _, _, _, e₀, he₀, hcomp₀, _ =>
    ⟨e₀, he₀, hcomp₀, fun b hb => ⟨b, hb, rfl⟩, fun a ha => ha⟩
  | _, cons _ _ _, _, _, e₀, he₀, hcomp₀, ⟨0, _⟩ =>
    ⟨e₀, he₀, hcomp₀, fun b hb => ⟨b, hb, rfl⟩, fun a ha => ha⟩
  | _, cons X D rest, E₁, E₂, e₀, he₀, hcomp₀, ⟨j + 1, h⟩ => by
    let e₁ : (E₁.totalTransform D).ι → (E₂.totalTransform D).ι :=
      fun b => toLex (Sum.map e₀ id (ofLex b))
    have he₁ : Function.Injective e₁ := fun b b' hbb' => by
      have h2 : Sum.map e₀ id (ofLex b) = Sum.map e₀ id (ofLex b') := toLex_inj.mp hbb'
      exact ofLex.injective (Sum.map_injective.mpr ⟨he₀, Function.injective_id⟩ h2)
    have hcomp₁ : ∀ b, (E₂.totalTransform D).component (e₁ b) =
        (E₁.totalTransform D).component b := by
      intro b
      rcases hb : ofLex b with a | u
      · have hb' : b = toLex (Sum.inl a) := by
          rw [← toLex_ofLex b, hb]
          rfl
        subst hb'
        change (E₂.component (e₀ a)).strictTransform D = (E₁.component a).strictTransform D
        rw [hcomp₀]
      · have hb' : b = toLex (Sum.inr u) := by
          rw [← toLex_ofLex b, hb]
          rfl
        subst hb'
        rfl
    obtain ⟨e, he, hcomp, hmiss, hnot⟩ :=
      exists_embeds_totalTransformSeq' rest e₁ he₁ hcomp₁ ⟨j, Nat.lt_of_succ_lt_succ h⟩
    refine ⟨e, he, hcomp, fun b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨a₁, ha₁, rfl⟩ := hmiss b hb
      rcases ha₁' : ofLex a₁ with a | u
      · have ha : a ∉ Set.range e₀ := by
          rintro ⟨a', rfl⟩
          refine ha₁ ⟨toLex (Sum.inl a'), ?_⟩
          rw [← toLex_ofLex a₁, ha₁']
          rfl
        refine ⟨a, ha, ?_⟩
        change rest.originalIdx (E₂.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩ a₁ =
          rest.originalIdx (E₂.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩ (toLex (Sum.inl a))
        rw [← toLex_ofLex a₁, ha₁']
      · exfalso
        refine ha₁ ⟨toLex (Sum.inr u), ?_⟩
        rw [← toLex_ofLex a₁, ha₁']
        rfl
    · -- the transform of a member outside the range stays outside the range
      change rest.originalIdx (E₂.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩
        (toLex (Sum.inl a)) ∉ Set.range e
      refine hnot (toLex (Sum.inl a)) ?_
      rintro ⟨b, hb⟩
      rcases hb' : ofLex b with a' | u
      · have hb'' : b = toLex (Sum.inl a') := by
          rw [← toLex_ofLex b, hb']
          rfl
        subst hb''
        have h3 : Sum.inl (e₀ a') = (Sum.inl a : E₂.ι ⊕ PUnit) := toLex_inj.mp hb
        exact ha ⟨a', Sum.inl.inj h3⟩
      · have hb'' : b = toLex (Sum.inr u) := by
          rw [← toLex_ofLex b, hb']
          rfl
        subst hb''
        exact absurd (toLex_inj.mp hb) Sum.inr_ne_inl


section Ring

variable {R : Type*} [CommRing R]

/-- A coordinate of a regular system lies outside the prime of an element off `(z_C) + 𝔪²`. -/
theorem notMem_span_singleton_of_notMem_sup_sq [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) {C : Set (Fin n)} {x : R}
    (hx2 : x ∉ Ideal.span (z '' C) ⊔ IsLocalRing.maximalIdeal R ^ 2)
    (hxm : x ∈ IsLocalRing.maximalIdeal R) {k : Fin n} (hk : k ∈ C) : z k ∉ Ideal.span {x} := by
  intro hmem
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
  by_cases hdu : IsUnit d
  · apply hx2
    apply Ideal.mem_sup_left
    have h1 : (↑hdu.unit⁻¹ : R) * d = 1 := by
      have := hdu.unit.inv_mul
      rwa [IsUnit.unit_spec] at this
    have hx : x = (↑hdu.unit⁻¹ : R) * z k := by rw [← hd, ← mul_assoc, h1, one_mul]
    rw [hx]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, hk, rfl⟩)
  · have hdm : d ∈ IsLocalRing.maximalIdeal R := by
      by_contra h
      exact hdu (IsLocalRing.notMem_maximalIdeal.mp h)
    have h2 : z k ∈ IsLocalRing.maximalIdeal R ^ 2 := by
      rw [← hd, pow_two]
      exact Ideal.mul_mem_mul hdm hxm
    exact notMem_span_compl_sup_sq hz k (Ideal.mem_sup_right h2)

/-- An element of `(x)` outside `𝔪²` generates `(x)` (for `x ∈ 𝔪`). -/
theorem span_singleton_eq_of_mem_of_notMem_sq [IsLocalRing R] {x f : R}
    (hxm : x ∈ IsLocalRing.maximalIdeal R) (hf : f ∈ Ideal.span {x})
    (hf2 : f ∉ IsLocalRing.maximalIdeal R ^ 2) : Ideal.span {f} = Ideal.span {x} := by
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hf
  have hdu : IsUnit d := by
    by_contra hdu
    have hdm : d ∈ IsLocalRing.maximalIdeal R := by
      by_contra h
      exact hdu (IsLocalRing.notMem_maximalIdeal.mp h)
    apply hf2
    rw [← hd, pow_two]
    exact Ideal.mul_mem_mul hdm hxm
  refine le_antisymm (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf)) ?_
  refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
  have h1 : (↑hdu.unit⁻¹ : R) * d = 1 := by
    have := hdu.unit.inv_mul
    rwa [IsUnit.unit_spec] at this
  have hx : x = (↑hdu.unit⁻¹ : R) * f := by rw [← hd, ← mul_assoc, h1, one_mul]
  rw [hx]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)

/-- A monomial in coordinates outside a prime lies outside the prime. -/
theorem monomialOf_notMem_of_forall_notMem {n : ℕ} {z : Fin n → R} {P : Ideal R}
    (hP : P.IsPrime) {C : Set (Fin n)} {b : Fin n → ℕ} (hb : ∀ κ, b κ ≠ 0 → κ ∈ C)
    (hC : ∀ k ∈ C, z k ∉ P) : monomialOf z b ∉ P := by
  intro hmem
  unfold monomialOf at hmem
  have := hP
  obtain ⟨κ, -, hκ⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
  by_cases h0 : b κ = 0
  · rw [h0, pow_zero] at hκ
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hκ isUnit_one)
  · exact hC κ (hb κ h0) (hP.mem_of_pow_mem _ hκ)

/-- The absorption lifts along the descent to a chain hypersurface: the preimage of the span of
the shortened chain is the span of the full chain. -/
theorem comap_span_range_succAbove_eq {S : Type*} [CommRing S] {n : ℕ} {z : Fin (n + 1) → R}
    {k₀ : Fin (n + 1)} {φ : R →+* S} (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {z k₀}) {r : ℕ} {σ : Fin (r + 2) → Fin (n + 1)}
    {t : Fin (r + 2)} (hk₀ : σ t = k₀) {σ' : Fin (r + 1) → Fin n}
    (hσ : ∀ i, k₀.succAbove (σ' i) = σ (t.succAbove i)) :
    (Ideal.span (Set.range ((fun i => φ (z (k₀.succAbove i))) ∘ σ'))).comap φ =
      Ideal.span (Set.range (z ∘ σ)) := by
  have h1 : Ideal.span (Set.range ((fun i => φ (z (k₀.succAbove i))) ∘ σ')) =
      (Ideal.span (Set.range (z ∘ σ ∘ t.succAbove))).map φ := by
    rw [Ideal.map_span, ← Set.range_comp]
    refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
    simp [Function.comp, hσ]
  have h2 : Set.range (z ∘ σ) = Set.range (z ∘ σ ∘ t.succAbove) ∪ {z (σ t)} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i = t
      · subst hi
        exact Or.inr rfl
      · obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq hi
        exact Or.inl ⟨i', by simp [Function.comp, hi']⟩
    · rintro (⟨i', rfl⟩ | h)
      · exact ⟨t.succAbove i', rfl⟩
      · exact ⟨t, (Set.mem_singleton_iff.mp h).symm⟩
  rw [h1, comap_map_eq_sup_span hφ hker, ← hk₀, h2, Ideal.span_union]

end Ring


/-- **The classification of `Z₋₁` in Step 2.2.** At a point `q` of the hypersurface `H` of maximal
contact where the current ideal lies in the ideal of `H`, no K-shape exists, and an I-shape has
the absorption `Z_q = (f₀)`, the chain of length one; here `Z` has the stalk of `H`. -/
theorem centerClassifiedAt_of_stalkIdeal_le_of_isSncAt_append {E : DivisorFamily X}
    {H K Z : X.IdealSheafData} {q : X} [IsRegularLocalRing (X.presheaf.stalk q)]
    (hq : q ∈ H.support) {m : ℕ} {w : Fin m → X.presheaf.stalk q}
    (hsnc : (E.append H).IsSncAt q w) (hZ : Z.stalkIdeal q = H.stalkIdeal q)
    (hKH : K.stalkIdeal q ≤ H.stalkIdeal q) : CenterClassifiedAt E K Z q := by
  classical
  intro n z c r σ a b hfree hb
  obtain ⟨hz, hcinj, hcmem, hσinj, hσc, ha⟩ := id hfree
  obtain ⟨hw, c₂, hc₂inj, hc₂mem⟩ := id hsnc
  set x := w (c₂ ⟨toLex (Sum.inr PUnit.unit), hq⟩) with hxdef
  have hx : H.stalkIdeal q = Ideal.span {x} := hc₂mem ⟨toLex (Sum.inr PUnit.unit), hq⟩
  have hx2 := notMem_span_sup_sq_of_isSncAt_append hq hsnc hfree hx
  have hprime : (Ideal.span {x}).IsPrime :=
    isPrime_span_singleton_of_parameters hw.1.symm hw.2 _
  have hxm : x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q) :=
    ((mem_support_iff_stalkIdeal_le_maximalIdeal H q).mp hq) (hx ▸ Ideal.mem_span_singleton_self x)
  have hCx : ∀ k ∈ Set.range c, z k ∉ Ideal.span {x} := fun k hk =>
    notMem_span_singleton_of_notMem_sup_sq hz hx2 hxm hk
  have hmon : monomialOf z b ∉ Ideal.span {x} := monomialOf_notMem_of_forall_notMem hprime hb hCx
  have hChain : ∀ C : Ideal (X.presheaf.stalk q),
      K.stalkIdeal q = Ideal.span {monomialOf z b} * C → C ≤ Ideal.span {x} := by
    intro C hK
    have h1 : Ideal.span {monomialOf z b} * C ≤ Ideal.span {x} := by
      rw [← hK, ← hx]
      exact hKH
    exact (hprime.mul_le.mp h1).resolve_left fun h => hmon (h (Ideal.mem_span_singleton_self _))
  refine ⟨fun hK => ?_, fun hI => ?_⟩
  · -- no K-shape: the last generator of the K-shape is a monomial in the member coordinates
    exfalso
    have hle := hChain _ hK
    have hmem : kGen z σ a (Fin.last r) ∈ Ideal.span {x} := by
      apply hle
      rw [chainKIdeal_eq_span_range_kGen]
      exact Ideal.subset_span ⟨Fin.last r, rfl⟩
    unfold kGen at hmem
    rw [Function.update_self, mul_one] at hmem
    have := hprime
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact monomialOf_notMem_of_forall_notMem hprime (ha i) hCx hi
  · -- an I-shape: `f₀ ∈ (x)`, so `(f₀) = (x)`, and the chain has length one
    have hle := hChain _ hI
    have hf0 : z (σ 0) ∈ Ideal.span {x} := by
      apply hle
      rw [chainIdeal_eq_span_range_iGen]
      refine Ideal.subset_span ⟨0, ?_⟩
      exact iGen_eq_of_le z σ a (t₀ := 0) (fun i hi => absurd hi (Nat.not_lt_zero _)) (le_refl _)
    have hf02 : z (σ 0) ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk q) ^ 2 := fun h =>
      notMem_span_compl_sup_sq hz (σ 0) (Ideal.mem_sup_right h)
    have hspan : Ideal.span {z (σ 0)} = Ideal.span {x} :=
      span_singleton_eq_of_mem_of_notMem_sq hxm hf0 hf02
    rcases r with _ | r'
    · refine Or.inr (Or.inr ?_)
      have hrange : Set.range (z ∘ σ) = {z (σ 0)} := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          rw [Fin.fin_one_eq_zero i]
          rfl
        · rintro rfl
          exact ⟨0, rfl⟩
      rw [hZ, hx, ← hspan, hrange]
    · exfalso
      -- the second generator `M₀ f₁` lies in `(f₀)`, a prime containing no other coordinate
      have hprime0 : (Ideal.span {z (σ 0)}).IsPrime :=
        isPrime_span_singleton_of_parameters hz.1.symm hz.2 (σ 0)
      have hmem : iGen z σ a 1 ∈ Ideal.span {z (σ 0)} := by
        rw [hspan]
        apply hle
        rw [chainIdeal_eq_span_range_iGen]
        exact Ideal.subset_span ⟨1, rfl⟩
      unfold iGen at hmem
      have := hprime0
      rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem hprime0).mp hmem with h1 | h1
      · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
        refine monomialOf_notMem_of_forall_notMem hprime0 (ha i) ?_ hi
        intro k hk
        obtain ⟨j, rfl⟩ := hk
        exact notMem_span_singleton_of_ne hz (fun h => hσc 0 j h.symm)
      · exact notMem_span_singleton_of_ne hz (fun h => absurd (hσinj h) Fin.zero_lt_one.ne') h1


/-- The restricted chain coordinates along a chain hypersurface: after the re-basing
`x = z₁ (σ t)`, the coordinates of the members and the chain shortened at `t` restrict along the
stalk map. -/
theorem exists_restricted_chain_coords {Y : Scheme.{u}} (g : Y ⟶ X) [IsClosedImmersion g]
    (E : DivisorFamily X) (F : DivisorFamily Y) (e : F.ι → E.ι) (he : Function.Injective e)
    (hcomp : ∀ a, F.component a = (E.component (e a)).comap g) (hsurj : Function.Surjective e)
    {q' : Y} [IsRegularLocalRing (X.presheaf.stalk (g q'))] {n : ℕ}
    {z : Fin (n + 1) → X.presheaf.stalk (g q')}
    {c : {j : E.ι // g q' ∈ (E.component j).support} → Fin (n + 1)} (hcinj : Function.Injective c)
    (hcmem : ∀ j, (E.component j.1).stalkIdeal (g q') = Ideal.span {z (c j)}) {r : ℕ}
    {σ : Fin (r + 1) → Fin (n + 1)} (hσinj : Function.Injective σ) (hσc : ∀ i j, σ i ≠ c j)
    (t : Fin (r + 1)) {x : X.presheaf.stalk (g q')}
    (hupd : IsRegularSystemOfParameters (Function.update z (σ t) x))
    (hker : RingHom.ker (g.stalkMap q').hom = Ideal.span {x}) :
    ∃ (c' : {a : F.ι // q' ∈ (F.component a).support} → Fin n) (σ' : Fin r → Fin n),
      (∀ i, (σ t).succAbove (σ' i) = σ (t.succAbove i)) ∧
      (∀ κ ∈ Set.range c', (σ t).succAbove κ ∈ Set.range c) ∧
      (∀ κ, (σ t).succAbove κ ∈ Set.range c → κ ∈ Set.range c') ∧
      IsRegularSystemOfParameters
        (fun i : Fin n => (g.stalkMap q').hom (Function.update z (σ t) x ((σ t).succAbove i))) ∧
      Function.Injective c' ∧
      (∀ a, (F.component a.1).stalkIdeal q' =
        Ideal.span {(g.stalkMap q').hom (Function.update z (σ t) x ((σ t).succAbove (c' a)))}) ∧
      Function.Injective σ' ∧ (∀ i a, σ' i ≠ c' a) := by
  classical
  have hφs : Function.Surjective (g.stalkMap q').hom := g.stalkMap_surjective q'
  have hker₁ : RingHom.ker (g.stalkMap q').hom =
      Ideal.span {Function.update z (σ t) x (σ t)} := by
    rw [hker, Function.update_self]
  have hz' := isRegularSystemOfParameters_comp_succAbove hupd (σ t) (g.stalkMap q').hom hφs hker₁
  have hmemF : ∀ a : {a : F.ι // q' ∈ (F.component a).support},
      g q' ∈ (E.component (e a.1)).support := fun a => by
    have := a.2
    rw [hcomp] at this
    exact (mem_support_comap_iff_apply _ _ _).mp this
  have hne : ∀ a : {a : F.ι // q' ∈ (F.component a).support}, c ⟨e a.1, hmemF a⟩ ≠ σ t :=
    fun a h => hσc t ⟨e a.1, hmemF a⟩ h.symm
  choose c' hc' using fun a => Fin.exists_succAbove_eq (hne a)
  have hσne : ∀ i : Fin r, σ (t.succAbove i) ≠ σ t := fun i h => Fin.succAbove_ne t i (hσinj h)
  choose σ' hσ' using fun i => Fin.exists_succAbove_eq (hσne i)
  have hmemE : ∀ j : {j : E.ι // g q' ∈ (E.component j).support},
      ∃ a : {a : F.ι // q' ∈ (F.component a).support}, e a.1 = j.1 := by
    intro j
    obtain ⟨a₀, ha₀⟩ := hsurj j.1
    refine ⟨⟨a₀, ?_⟩, ha₀⟩
    rw [hcomp, mem_support_comap_iff_apply, ha₀]
    exact j.2
  refine ⟨c', σ', hσ', ?_, ?_, hz', ?_, ?_, ?_, ?_⟩
  · rintro κ ⟨a, rfl⟩
    exact ⟨_, (hc' a).symm⟩
  · rintro κ ⟨j, hj⟩
    obtain ⟨a, ha⟩ := hmemE j
    refine ⟨a, Fin.succAbove_right_injective (p := σ t) ?_⟩
    rw [hc' a, ← hj]
    exact congrArg c (Subtype.ext ha)
  · intro a₁ a₂ h12
    have h3 := congrArg (σ t).succAbove h12
    rw [hc' a₁, hc' a₂] at h3
    exact Subtype.ext (he (Subtype.mk.inj (hcinj h3)))
  · intro a
    have h1 : ((E.component (e a.1)).comap g).stalkIdeal q' =
        ((E.component (e a.1)).stalkIdeal (g q')).map (g.stalkMap q').hom :=
      stalkIdeal_comap _ g q'
    rw [hcomp, h1, hcmem ⟨e a.1, hmemF a⟩, Ideal.map_span, Set.image_singleton, hc' a,
      Function.update_of_ne (hne a)]
  · intro i i' hii'
    have h3 := congrArg (σ t).succAbove hii'
    rw [hσ' i, hσ' i'] at h3
    exact Fin.succAbove_right_injective (p := t) (hσinj h3)
  · intro i a heq
    have h3 := congrArg (σ t).succAbove heq
    rw [hσ' i, hc' a] at h3
    exact hσc _ _ h3

/-- **The pointwise pass along the hypersurface of maximal contact** (the variant of
`centerClassifiedAt_of_comap_member` for a chain hypersurface). For a closed immersion `g` with
kernel `H`, `H` snc with the family `E` at `g q'`, and the equation of `H` in the current ideal
`K` (maximal contact at the mark `1`), the classification of a centre `Z'` on `Y` at `q'` for the
restricted ideal and the family `F = E|_Y` (every member restricts) gives the classification of
its push-forward at `g q'`: in every chain-coordinate system the top monomial is `1`, the flag is
re-based so that the equation of `H` is a chain coordinate, the coordinates and the shape
restrict along the descent, and the inner stratum lifts and transfers back. -/
theorem centerClassifiedAt_of_comap_chain {Y : Scheme.{u}} (g : Y ⟶ X) [IsClosedImmersion g]
    (E : DivisorFamily X) (F : DivisorFamily Y) (e : F.ι → E.ι) (he : Function.Injective e)
    (hcomp : ∀ a, F.component a = (E.component (e a)).comap g) (hsurj : Function.Surjective e)
    {H : X.IdealSheafData} (hker : g.ker = H) {K : X.IdealSheafData} {Z' : Y.IdealSheafData}
    {q' : Y} [IsRegularLocalRing (X.presheaf.stalk (g q'))]
    {m : ℕ} {w : Fin m → X.presheaf.stalk (g q')}
    (hsnc : (E.append H).IsSncAt (g q') w) (hHK : H.stalkIdeal (g q') ≤ K.stalkIdeal (g q'))
    (hKq : K.stalkIdeal (g q') ≠ ⊤) (hK0 : (K.comap g).stalkIdeal q' ≠ ⊥)
    (h : CenterClassifiedAt F (K.comap g) Z' q') : CenterClassifiedAt E K (Z'.map g) (g q') := by
  classical
  intro n z c r σ a b hfree hb
  obtain ⟨hz, hcinj, hcmem, hσinj, hσc, ha⟩ := id hfree
  have hqH : g q' ∈ H.support := by
    rw [← hker, ← SetLike.mem_coe, Scheme.Hom.support_ker]
    exact subset_closure ⟨q', rfl⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos (σ 0))).symm⟩
  obtain ⟨hw, c₂, hc₂inj, hc₂mem⟩ := id hsnc
  set x := w (c₂ ⟨toLex (Sum.inr PUnit.unit), hqH⟩) with hxdef
  have hx : H.stalkIdeal (g q') = Ideal.span {x} := hc₂mem ⟨toLex (Sum.inr PUnit.unit), hqH⟩
  have hx2 := notMem_span_sup_sq_of_isSncAt_append hqH hsnc hfree hx
  have hxK : x ∈ K.stalkIdeal (g q') := hHK (hx ▸ Ideal.mem_span_singleton_self x)
  have hxm : x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (g q')) :=
    ((mem_support_iff_stalkIdeal_le_maximalIdeal H (g q')).mp hqH)
      (hx ▸ Ideal.mem_span_singleton_self x)
  have hCσ : ∀ k ∈ Set.range c, k ∉ Set.range σ := by
    rintro k ⟨j, rfl⟩ ⟨i, hi⟩
    exact hσc i j hi
  set φ : X.presheaf.stalk (g q') →+* Y.presheaf.stalk q' := (g.stalkMap q').hom with hφdef
  have hφs : Function.Surjective φ := g.stalkMap_surjective q'
  have hkerφ : RingHom.ker φ = Ideal.span {x} := by
    rw [hφdef, ker_stalkMap_of_isClosedImmersion, hker, hx]
  have hφx : φ x = 0 := by
    rw [← RingHom.mem_ker, hkerφ]
    exact Ideal.mem_span_singleton_self x
  have hK' : (K.comap g).stalkIdeal q' = (K.stalkIdeal (g q')).map φ := stalkIdeal_comap K g q'
  have hZ : (Z'.map g).stalkIdeal (g q') = (Z'.stalkIdeal q').comap φ :=
    stalkIdeal_map_of_isClosedImmersion g Z' q'
  rw [hZ]
  -- the top exponents vanish: otherwise `x ∈ (z_C)`
  have hb0 : ∀ C : Ideal (X.presheaf.stalk (g q')),
      K.stalkIdeal (g q') = Ideal.span {monomialOf z b} * C → b = 0 := by
    intro C hK
    by_contra hne
    obtain ⟨κ, hκ⟩ : ∃ κ, b κ ≠ 0 := by
      by_contra hall
      exact hne (funext fun κ => by_contra fun h0 => hall ⟨κ, h0⟩)
    apply hx2
    apply Ideal.mem_sup_left
    have h1 : K.stalkIdeal (g q') ≤ Ideal.span {z κ} := by
      rw [hK]
      exact Ideal.mul_le_left.trans
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (monomialOf_mem_span_singleton z b hκ)))
    have hsub : ({z κ} : Set (X.presheaf.stalk (g q'))) ⊆ z '' Set.range c :=
      Set.singleton_subset_iff.mpr ⟨κ, hb κ hκ, rfl⟩
    exact Ideal.span_mono hsub (h1 hxK)
  have ha' : ∀ (t : Fin (r + 1)) i κ, a i κ ≠ 0 → κ ≠ σ t :=
    fun t i κ hκ heq => hCσ κ (ha i κ hκ) ⟨t, heq.symm⟩
  refine ⟨fun hK => ?_, fun hI => ?_⟩
  · -- the K-shape
    have hb0' := hb0 _ hK
    subst hb0'
    rw [monomialOf_zero, Ideal.span_singleton_one, Ideal.top_mul] at hK
    have hxC : x ∈ chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) := hK ▸ hxK
    have hne : ∃ i : Fin (r + 1), i.val < r ∧ a i ≠ 0 := by
      by_contra hall
      apply hKq
      rw [hK, chainKIdeal_eq_span_range_kGen]
      have h1 : kGen z σ a (Fin.last r) = 1 := by
        unfold kGen
        rw [Function.update_self, mul_one]
        refine Finset.prod_eq_one fun i hi => ?_
        have hlt := (Finset.mem_filter.mp hi).2
        rw [Fin.lt_def, Fin.val_last] at hlt
        have h0 : a i = 0 := by
          by_contra hne'
          exact hall ⟨i, hlt, hne'⟩
        rw [h0, monomialOf_zero]
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨Fin.last r, h1⟩) isUnit_one
    obtain ⟨t, htr, ht, hupd, heq⟩ :=
      exists_update_chainKIdeal_eq hz σ hσinj (Set.range c) hCσ a ha hne hxC hx2
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨c', σ', hσ', hC, hCback, hz', hc'inj, hstalk, hσ'inj, hσ'c⟩ :=
      exists_restricted_chain_coords g E F e he hcomp hsurj hcinj hcmem hσinj hσc t hupd hkerφ
    have hkerφ₁ : RingHom.ker φ = Ideal.span {Function.update z (σ t) x (σ t)} := by
      rw [Function.update_self]
      exact hkerφ
    have hφk : φ (Function.update z (σ t) x (σ t)) = 0 := by
      rw [Function.update_self]
      exact hφx
    have hres := map_chainKIdeal_succAbove_of_trivial (Function.update z (σ t) x) (σ t) φ hφk σ t
      rfl σ' hσ' a (ha' t) ht
    have hK'' : (K.comap g).stalkIdeal q' =
        Ideal.span
          {monomialOf (fun i => φ (Function.update z (σ t) x ((σ t).succAbove i)))
              (a 0 ∘ (σ t).succAbove)} *
          chainKIdeal ((fun i => φ (Function.update z (σ t) x ((σ t).succAbove i))) ∘ σ')
            (fun i => monomialOf (fun i => φ (Function.update z (σ t) x ((σ t).succAbove i)))
              (a (Fin.succ i) ∘ (σ t).succAbove)) := by
      rw [hK', hK, heq, hres]
    have hfree' : ChainCoordsFree F q'
        (fun i => φ (Function.update z (σ t) x ((σ t).succAbove i))) c' σ'
        (fun i => a (Fin.succ i) ∘ (σ t).succAbove) :=
      ⟨hz', hc'inj, hstalk, hσ'inj, hσ'c, fun i κ hκ => hCback κ (ha _ _ hκ)⟩
    have hb' : ∀ κ, (a 0 ∘ (σ t).succAbove) κ ≠ 0 → κ ∈ Set.range c' :=
      fun κ hκ => hCback κ (ha _ _ hκ)
    have hstrat := (h _ c' σ' _ _ hfree' hb').1 hK''
    have hlift := stratumIn_comap_of_stratumIn_succAbove (b := 0) hφs hkerφ₁ hC rfl hσ' ht hstrat
    exact stratumIn_of_stratumIn_update_chainKIdeal hz σ hσinj (Set.range c) hCσ a 0 hxC t ht hupd
      hlift
  · -- the I-shape
    have hb0' := hb0 _ hI
    subst hb0'
    rw [monomialOf_zero, Ideal.span_singleton_one, Ideal.top_mul] at hI
    have hxC : x ∈ chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) := hI ▸ hxK
    rcases r with _ | r'
    · -- a chain of length one: `K_q = (f₀) = (x)`, so the restricted ideal is zero
      exfalso
      apply hK0
      have hgen : Set.range (iGen z σ a) = {z (σ 0)} := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          rw [Fin.fin_one_eq_zero i]
          exact iGen_eq_of_le z σ a (t₀ := 0) (fun i hi => absurd hi (Nat.not_lt_zero _))
            (le_refl _)
        · rintro rfl
          exact ⟨0, iGen_eq_of_le z σ a (t₀ := 0) (fun i hi => absurd hi (Nat.not_lt_zero _))
            (le_refl _)⟩
      have hI' : chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) = Ideal.span {z (σ 0)} := by
        rw [chainIdeal_eq_span_range_iGen, hgen]
      have hf0m : z (σ 0) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (g q')) := by
        rw [← hz.1]
        exact Ideal.subset_span ⟨σ 0, rfl⟩
      have hx2' : x ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk (g q')) ^ 2 :=
        fun hmem => hx2 (Ideal.mem_sup_right hmem)
      have hspan : Ideal.span {x} = Ideal.span {z (σ 0)} :=
        span_singleton_eq_of_mem_of_notMem_sq hf0m (hI' ▸ hxC) hx2'
      have hφ0 : φ (z (σ 0)) = 0 := by
        rw [← RingHom.mem_ker, hkerφ, hspan]
        exact Ideal.mem_span_singleton_self _
      rw [hK', hI, hI', Ideal.map_span, Set.image_singleton, hφ0,
        Ideal.span_singleton_eq_bot.mpr rfl]
    · obtain ⟨t, ht, hupd, heq⟩ :=
        exists_update_chainIdeal_eq hz σ hσinj (Set.range c) hCσ a ha hxC hx2
      obtain ⟨c', σ', hσ', hC, hCback, hz', hc'inj, hstalk, hσ'inj, hσ'c⟩ :=
        exists_restricted_chain_coords g E F e he hcomp hsurj hcinj hcmem hσinj hσc t hupd hkerφ
      have hkerφ₁ : RingHom.ker φ = Ideal.span {Function.update z (σ t) x (σ t)} := by
        rw [Function.update_self]
        exact hkerφ
      have hφk : φ (Function.update z (σ t) x (σ t)) = 0 := by
        rw [Function.update_self]
        exact hφx
      have hres := map_chainIdeal_succAbove_of_trivial (Function.update z (σ t) x) (σ t) φ hφk σ t
        rfl σ' hσ' a (ha' t) ht
      have hI'' : (K.comap g).stalkIdeal q' =
          Ideal.span
            {monomialOf (fun i => φ (Function.update z (σ t) x ((σ t).succAbove i)))
                (a 0 ∘ (σ t).succAbove)} *
            chainIdeal ((fun i => φ (Function.update z (σ t) x ((σ t).succAbove i))) ∘ σ')
              (fun i => monomialOf (fun i => φ (Function.update z (σ t) x ((σ t).succAbove i)))
                (a (Fin.succ i) ∘ (σ t).succAbove)) := by
        rw [hK', hI, heq, hres]
      have hfree' : ChainCoordsFree F q'
          (fun i => φ (Function.update z (σ t) x ((σ t).succAbove i))) c' σ'
          (fun i => a (Fin.succ i) ∘ (σ t).succAbove) :=
        ⟨hz', hc'inj, hstalk, hσ'inj, hσ'c, fun i κ hκ => hCback κ (ha _ _ hκ)⟩
      have hb' : ∀ κ, (a 0 ∘ (σ t).succAbove) κ ≠ 0 → κ ∈ Set.range c' :=
        fun κ hκ => hCback κ (ha _ _ hκ)
      rcases (h _ c' σ' _ _ hfree' hb').2 hI'' with h1 | h2 | h3
      · exact Or.inl (stratumIn_of_stratumIn_update_chainIdeal hz σ hσinj (Set.range c) hCσ a 0 hxC
          t ht hupd (stratumIn_comap_of_stratumIn_succAbove hφs hkerφ₁ hC rfl hσ' ht h1))
      · exact Or.inr (Or.inl (terminalIn_of_terminalIn_update hz σ hσinj (Set.range c) hCσ a hxC t
          hupd (terminalIn_comap_of_terminalIn_succAbove hφs hkerφ₁ hC rfl hσ' h2)))
      · refine Or.inr (Or.inr ?_)
        rw [h3, comap_span_range_succAbove_eq hφs hkerφ₁ rfl hσ',
          span_range_update_eq_of_mem_chainIdeal hz σ hσinj a hxC t hupd]

end Hironaka.Resolution
