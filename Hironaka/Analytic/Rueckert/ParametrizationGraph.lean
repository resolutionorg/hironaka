/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.NoetherNormalization
public import Hironaka.Analytic.Rueckert.Specialize
public import Hironaka.Analytic.Rueckert.ZeroSet
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Hironaka.Analytic.Rueckert.GraphIdeal
import Hironaka.Analytic.Rueckert.Hypersurface
import Hironaka.Analytic.Rueckert.MinpolyDvd
import Hironaka.Analytic.Rueckert.MonicRelation
import Hironaka.Analytic.Rueckert.ParametrizationDivision
import Hironaka.Analytic.Rueckert.PolyEvalFunction
import Hironaka.Analytic.Rueckert.RootBranch
import Hironaka.Analytic.Rueckert.UFD
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The graph structure of a prime germ off the discriminant

The local parametrization theorem [GR84, Chapter 3, §1] (the graph structure off the
discriminant; [Fre17, Ch. I, 8.2] for a hypersurface): in the coordinates of `σ = substEquiv L`,
with `S` generating `P' = comap σ P`, near every point `x` of the zero-set germ `V(P')` with
`(A · Res(Q, Q'))(x ∘ e) ≠ 0` the zero set is the graph of a map `φ` analytic at `x ∘ e`, a
section of the base projection through `x`.

Proof. Write `u₀ = x ∘ e`, `t₀ = x_{i₀}`. `Q(X_{i₀}) ∈ P'` vanishes on `V(P')` (`VanishesOn`,
`ZeroSet.lean`), so `t₀` is a root of the specialized polynomial `Q(u₀, ·)`; where the resultant
does not vanish the roots are simple (`eventually_isCoprime_specialize`, a Bezout identity), so
`∂_t Q(u₀, t₀) ≠ 0` and the analytic root branch `τ` through `(u₀, t₀)` exists
(`RootBranch.lean`). The graph map is `φ(u) = (u on the base, τ(u) at i₀, B_i(u, τ(u)) / A(u) at
the other fibre coordinates)`. Zero set `⊆` graph: `Q(X_{i₀})` and the relations
`A X_i − B_i(X_{i₀})` vanish on `V(P')`, and the root branch is the unique zero near `(u₀, t₀)`.
Graph `⊆` zero set: the generators of the ideal `J` of `ParametrizationDivision.lean` vanish on
the graph, `Q(X_{i₀})` and the relations by construction, the relation of `X_{i₀}` and the monic
relations `Qf_i(X_i)` (`MonicRelation.lean`) because their "clearing polynomials" `A·T − B_{i₀}(T)`
and `∑_k Qf_{i,k} A^{D-k} B_i(T)^k` vanish at the class of `X_{i₀}` in `𝒪_n/P'`, hence are
multiples of `Q` (`MinpolyDvd.lean`); then the division argument, `A^N F ∈ J` for `F ∈ P'`, gives
the vanishing of every generator of `P'` where `A ≠ 0`. All function-level identities are the
`evalSeries_conv_*_eventually` lemmas and `PolyEvalFunction.lean`. This is the graph structure
that makes the regular points of a prime germ dense (`Hironaka/Space`).
-/

@[expose] public section

open Polynomial Filter Topology

namespace Analytic

variable {n d : ℕ}

section Clearing

/-- The clearing polynomial `∑_{k ≤ D} Qf_k A^{D-k} B^k` of a monic relation `Qf` of degree `D`
along `A · X = B(X_{i₀})`. -/
noncomputable def clearPoly (Qf B : Polynomial (Conv ℂ d)) (A : Conv ℂ d) :
    Polynomial (Conv ℂ d) :=
  ∑ k ∈ Finset.range (Qf.natDegree + 1), C (Qf.coeff k * A ^ (Qf.natDegree - k)) * B ^ k

/-- Where `f(A) ξᵢ = B(ξ)`, the clearing polynomial evaluates to `f(A)^D Qf(ξᵢ)`. -/
theorem eval₂_clearPoly_eq {S : Type*} [CommRing S] (f : Conv ℂ d →+* S)
    (Qf B : Polynomial (Conv ℂ d)) (A : Conv ℂ d) {ξ ξi : S}
    (hrel : f A * ξi = eval₂ f ξ B) :
    eval₂ f ξ (clearPoly Qf B A) = f A ^ Qf.natDegree * eval₂ f ξi Qf := by
  rw [clearPoly, eval₂_finsetSum]
  have : ∀ k ∈ Finset.range (Qf.natDegree + 1),
      eval₂ f ξ (C (Qf.coeff k * A ^ (Qf.natDegree - k)) * B ^ k) =
        f A ^ Qf.natDegree * (f (Qf.coeff k) * ξi ^ k) := by
    intro k hk
    rw [eval₂_mul, eval₂_C, eval₂_pow, ← hrel, mul_pow, map_mul, map_pow]
    have hk' : k ≤ Qf.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    calc f (Qf.coeff k) * f A ^ (Qf.natDegree - k) * (f A ^ k * ξi ^ k)
        = f (Qf.coeff k) * (f A ^ (Qf.natDegree - k) * f A ^ k) * ξi ^ k := by ring
      _ = f A ^ Qf.natDegree * (f (Qf.coeff k) * ξi ^ k) := by
        rw [← pow_add, Nat.sub_add_cancel hk']; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, eval₂_eq_sum_range]

/-- The class of `W(X_i)` in a quotient of `𝒪_n` is `W` evaluated through `mk ∘ convEmbed e` at
the class of `X_i`. -/
theorem mk_eval_map_eq_eval₂ (I : Ideal (Conv ℂ n)) (e : Fin d ↪ Fin n) (i : Fin n)
    (W : Polynomial (Conv ℂ d)) :
    Ideal.Quotient.mk I ((W.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i)) =
      eval₂ ((Ideal.Quotient.mk I).comp (convEmbed ℂ e).toRingHom)
        (Ideal.Quotient.mk I (convX ℂ i)) W := by
  rw [eval_map]
  exact hom_eval₂ W (convEmbed ℂ e).toRingHom (Ideal.Quotient.mk I) (convX ℂ i)

/-- `A^D Qf(X_i) − G(X_{i₀})` lies in the ideal of the single relation `A X_i − B(X_{i₀})`, `G`
the clearing polynomial. -/
theorem pow_mul_eval_sub_clearPoly_mem_span (e : Fin d ↪ Fin n) (i i₀ : Fin n)
    (Qf B : Polynomial (Conv ℂ d)) (A : Conv ℂ d) :
    convEmbed ℂ e A ^ Qf.natDegree * (Qf.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i) -
        ((clearPoly Qf B A).map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈
      Ideal.span {convEmbed ℂ e A * convX ℂ i -
        (B.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀)} := by
  set I : Ideal (Conv ℂ n) := Ideal.span {convEmbed ℂ e A * convX ℂ i -
    (B.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀)} with hI
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, mk_eval_map_eq_eval₂,
    mk_eval_map_eq_eval₂]
  have hrel : ((Ideal.Quotient.mk I).comp (convEmbed ℂ e).toRingHom) A *
      Ideal.Quotient.mk I (convX ℂ i) =
      eval₂ ((Ideal.Quotient.mk I).comp (convEmbed ℂ e).toRingHom) (Ideal.Quotient.mk I (convX ℂ
        i₀))
        B := by
    rw [← mk_eval_map_eq_eval₂, RingHom.comp_apply, ← map_mul]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)
  rw [eval₂_clearPoly_eq _ Qf B A hrel]
  exact sub_eq_zero.mpr rfl

/-- At a root of `p`, if `p` is coprime to its derivative then the derivative does not vanish
(the Bezout identity). -/
theorem eval_derivative_ne_zero_of_isCoprime {p : Polynomial ℂ} {t : ℂ}
    (hcop : IsCoprime p (derivative p)) (ht : p.eval t = 0) : (derivative p).eval t ≠ 0 := by
  obtain ⟨a, b, hab⟩ := hcop
  intro h0
  have := congrArg (eval t) hab
  rw [eval_add, eval_mul, eval_mul, ht, h0, mul_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

end Clearing

/-! ### The elements of `𝒪_n` attached to the data, and the function-level facts -/

section Elements

variable (e : Fin d ↪ Fin n) (i₀ : Fin n)

/-- `W(X_{i₀})` with coefficients embedded along `e`. -/
noncomputable def polyElt (W : Polynomial (Conv ℂ d)) : Conv ℂ n :=
  (W.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀)

/-- The relation `A X_i − B_i(X_{i₀})`. -/
noncomputable def relElt (A : Conv ℂ d) (B : Fin n → Polynomial (Conv ℂ d)) (i : Fin n) :
    Conv ℂ n :=
  convEmbed ℂ e A * convX ℂ i - polyElt e i₀ (B i)

/-- `A^{D_i} Qf_i(X_i) − G_i(X_{i₀})`, `G_i` the clearing polynomial. -/
noncomputable def clearElt (A : Conv ℂ d) (B Qf : Fin n → Polynomial (Conv ℂ d)) (i : Fin n) :
    Conv ℂ n :=
  convEmbed ℂ e A ^ (Qf i).natDegree * polyElt e i (Qf i) - polyElt e i₀ (clearPoly (Qf i) (B i) A)

/-- The generating set of the ideal `J` of `ParametrizationDivision.lean`. -/
def gensSet (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d) (B Qf : Fin n → Polynomial (Conv ℂ d)) :
    Set (Conv ℂ n) :=
  {polyElt e i₀ Q} ∪ Set.range (fun i : {i : Fin n // i ∉ Set.range e} => polyElt e i (Qf i)) ∪
    Set.range (fun i : {i : Fin n // i ∉ Set.range e} => relElt e i₀ A B i)

theorem gensSet_finite (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d)
    (B Qf : Fin n → Polynomial (Conv ℂ d)) : (gensSet e i₀ Q A B Qf).Finite :=
  ((Set.finite_singleton _).union (Set.finite_range _)).union (Set.finite_range _)

/-- The same generating set as a finset. -/
noncomputable def gensFinset (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d)
    (B Qf : Fin n → Polynomial (Conv ℂ d)) : Finset (Conv ℂ n) :=
  (gensSet_finite e i₀ Q A B Qf).toFinset

theorem coe_gensFinset (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d)
    (B Qf : Fin n → Polynomial (Conv ℂ d)) :
    (gensFinset e i₀ Q A B Qf : Set (Conv ℂ n)) = gensSet e i₀ Q A B Qf :=
  Set.Finite.coe_toFinset _

open Classical in
/-- The base coefficient series whose functions must be analytic. -/
noncomputable def coeffFinset (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d)
    (B : Fin n → Polynomial (Conv ℂ d)) : Finset (Conv ℂ d) :=
  insert A ((Finset.range (Q.natDegree + 1)).image Q.coeff ∪
    Finset.univ.biUnion fun i => (Finset.range ((B i).natDegree + 1)).image (B i).coeff)

open Classical in
theorem mem_coeffFinset_A (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d)
    (B : Fin n → Polynomial (Conv ℂ d)) : A ∈ coeffFinset Q A B :=
  Finset.mem_insert_self _ _

open Classical in
theorem mem_coeffFinset_Q (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d)
    (B : Fin n → Polynomial (Conv ℂ d)) {k : ℕ} (hk : k ∈ Finset.range (Q.natDegree + 1)) :
    Q.coeff k ∈ coeffFinset Q A B :=
  Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk))

open Classical in
theorem mem_coeffFinset_B (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d)
    (B : Fin n → Polynomial (Conv ℂ d)) (i : Fin n) {k : ℕ}
    (hk : k ∈ Finset.range ((B i).natDegree + 1)) : (B i).coeff k ∈ coeffFinset Q A B :=
  Finset.mem_insert_of_mem (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hk⟩))

end Elements

/-- The facts about a point `x` near `0` used by the graph argument: the vanishing statements on
the zero-set germs, the function-level identities for the elements attached to the data, the
analyticity of the base coefficient functions at `x ∘ e`, and the coprimality of the specialized
`Q` with its derivative off the resultant. -/
structure GraphFacts (e : Fin d ↪ Fin n) (i₀ : Fin n) (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d)
    (B Qf Hp : Fin n → Polynomial (Conv ℂ d)) (H₀ : Polynomial (Conv ℂ d)) (N : ℕ)
    (S : Finset (Conv ℂ n)) (x : Fin n → ℂ) : Prop where
  vq : x ∈ zeroSet S → evalSeries (polyElt e i₀ Q : MvPowerSeries (Fin n) ℂ) x = 0
  vrel : ∀ i : {i : Fin n // i ∉ Set.range e},
    x ∈ zeroSet S → evalSeries (relElt e i₀ A B i : MvPowerSeries (Fin n) ℂ) x = 0
  vAN : ∀ g ∈ S, x ∈ zeroSet (gensFinset e i₀ Q A B Qf) →
    evalSeries ((convEmbed ℂ e A ^ N * g : Conv ℂ n) : MvPowerSeries (Fin n) ℂ) x = 0
  vcl : ∀ i : {i : Fin n // i ∉ Set.range e}, x ∈ zeroSet {relElt e i₀ A B i} →
    evalSeries (clearElt e i₀ A B Qf i : MvPowerSeries (Fin n) ℂ) x = 0
  eq_q : evalSeries (polyElt e i₀ Q : MvPowerSeries (Fin n) ℂ) x =
    (specialize Q (x ∘ e)).eval (x i₀)
  eq_rel : ∀ i, evalSeries (relElt e i₀ A B i : MvPowerSeries (Fin n) ℂ) x =
    evalSeries (A : MvPowerSeries (Fin d) ℂ) (x ∘ e) * x i - (specialize (B i) (x ∘ e)).eval (x i₀)
  eq_AN : ∀ g ∈ S, evalSeries ((convEmbed ℂ e A ^ N * g : Conv ℂ n) : MvPowerSeries (Fin n) ℂ) x =
    evalSeries (A : MvPowerSeries (Fin d) ℂ) (x ∘ e) ^ N * evalSeries (g : MvPowerSeries (Fin n)
      ℂ) x
  eq_cl : ∀ i, evalSeries (clearElt e i₀ A B Qf i : MvPowerSeries (Fin n) ℂ) x =
    evalSeries (A : MvPowerSeries (Fin d) ℂ) (x ∘ e) ^ (Qf i).natDegree *
      evalSeries (polyElt e i (Qf i) : MvPowerSeries (Fin n) ℂ) x -
        evalSeries (polyElt e i₀ (clearPoly (Qf i) (B i) A) : MvPowerSeries (Fin n) ℂ) x
  eq_g : ∀ i : {i : Fin n // i ∉ Set.range e},
    evalSeries (polyElt e i₀ (clearPoly (Qf i) (B i) A) : MvPowerSeries (Fin n) ℂ) x =
      evalSeries (polyElt e i₀ Q : MvPowerSeries (Fin n) ℂ) x *
        evalSeries (polyElt e i₀ (Hp i) : MvPowerSeries (Fin n) ℂ) x
  eq_rel0 : evalSeries (relElt e i₀ A B i₀ : MvPowerSeries (Fin n) ℂ) x =
    evalSeries (polyElt e i₀ Q : MvPowerSeries (Fin n) ℂ) x *
      evalSeries (polyElt e i₀ H₀ : MvPowerSeries (Fin n) ℂ) x
  an : ∀ c ∈ coeffFinset Q A B, AnalyticAt ℂ (evalSeries (c : MvPowerSeries (Fin d) ℂ)) (x ∘ e)
  cop : evalSeries ((resultant Q (derivative Q) : Conv ℂ d) : MvPowerSeries (Fin d) ℂ) (x ∘ e) ≠ 0 →
    IsCoprime (specialize Q (x ∘ e)) (derivative (specialize Q (x ∘ e)))
  eq_ARes : evalSeries ((A * resultant Q (derivative Q) : Conv ℂ d) : MvPowerSeries (Fin d) ℂ)
      (x ∘ e) =
    evalSeries (A : MvPowerSeries (Fin d) ℂ) (x ∘ e) *
      evalSeries ((resultant Q (derivative Q) : Conv ℂ d) : MvPowerSeries (Fin d) ℂ) (x ∘ e)

section Facts

variable {e : Fin d ↪ Fin n} {i₀ : Fin n}

/-- The function of `−g` near `0`. -/
theorem evalSeries_conv_neg_eventually' (g : Conv ℂ n) :
    evalSeries ((-g : Conv ℂ n) : MvPowerSeries (Fin n) ℂ) =ᶠ[𝓝 (0 : Fin n → ℂ)]
      fun x => -evalSeries (g : MvPowerSeries (Fin n) ℂ) x := by
  filter_upwards [evalSeries_conv_mul_eventually (algebraMap ℂ (Conv ℂ n) (-1)) g] with x hx
  rw [show (-g : Conv ℂ n) = algebraMap ℂ (Conv ℂ n) (-1) * g by rw [map_neg, map_one]; ring, hx,
    evalSeries_algebraMap_conv]
  ring

/-- The function of the relation `A X_i − B_i(X_{i₀})` near `0`. -/
theorem evalSeries_relElt_eventually (A : Conv ℂ d) (B : Fin n → Polynomial (Conv ℂ d)) (i : Fin
  n) :
    evalSeries (relElt e i₀ A B i : MvPowerSeries (Fin n) ℂ) =ᶠ[𝓝 (0 : Fin n → ℂ)] fun x =>
      evalSeries (A : MvPowerSeries (Fin d) ℂ) (x ∘ e) * x i -
        (specialize (B i) (x ∘ e)).eval (x i₀) := by
  filter_upwards [evalSeries_conv_sub_eventually (convEmbed ℂ e A * convX ℂ i) (polyElt e i₀ (B
    i)),
    evalSeries_conv_mul_eventually (convEmbed ℂ e A) (convX ℂ i),
    evalSeries_eval_map_convEmbed_eventually e i₀ (B i)] with x h1 h2 h3
  rw [relElt, h1, h2, evalSeries_convEmbed, evalSeries_convX]
  congr 1

/-- All the facts hold on a neighbourhood of `0`. -/
theorem eventually_graphFacts (Q : Polynomial (Conv ℂ d)) (hQdeg : 0 < Q.natDegree) (A : Conv ℂ d)
    (B Qf Hp : Fin n → Polynomial (Conv ℂ d)) (H₀ : Polynomial (Conv ℂ d)) (N : ℕ)
    (S : Finset (Conv ℂ n)) (P' : Ideal (Conv ℂ n)) (hS : Ideal.span (S : Set (Conv ℂ n)) = P')
    (hQP : polyElt e i₀ Q ∈ P') (hB : ∀ i, i ∉ Set.range e → relElt e i₀ A B i ∈ P')
    (hN : ∀ F ∈ P', convEmbed ℂ e A ^ N * F ∈ Ideal.span (gensSet e i₀ Q A B Qf))
    (hHp : ∀ i, i ∉ Set.range e → clearPoly (Qf i) (B i) A = Q * Hp i)
    (hH₀ : C A * X - B i₀ = Q * H₀) :
    ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), GraphFacts e i₀ Q A B Qf Hp H₀ N S x := by
  -- vanishing statements
  have hV_q : VanishesOn S (polyElt e i₀ Q) := VanishesOn.of_mem_span (by rw [hS]; exact hQP)
  have hV_rel : ∀ i : {i : Fin n // i ∉ Set.range e}, VanishesOn S (relElt e i₀ A B i) := fun i =>
    VanishesOn.of_mem_span (by rw [hS]; exact hB i i.2)
  have hV_AN : ∀ g ∈ S, VanishesOn (gensFinset e i₀ Q A B Qf) (convEmbed ℂ e A ^ N * g) :=
    fun g hg => by
      have hgP : g ∈ P' := by
        have : g ∈ Ideal.span (S : Set (Conv ℂ n)) := Ideal.subset_span hg
        rwa [hS] at this
      exact VanishesOn.of_mem_span (by rw [coe_gensFinset]; exact hN g hgP)
  have hV_cl : ∀ i : {i : Fin n // i ∉ Set.range e},
      VanishesOn {relElt e i₀ A B i} (clearElt e i₀ A B Qf i) := fun i =>
    VanishesOn.of_mem_span (by
      rw [Finset.coe_singleton]
      exact pow_mul_eval_sub_clearPoly_mem_span e i i₀ (Qf i) (B i) A)
  -- function identities
  have hE_q := evalSeries_eval_map_convEmbed_eventually e i₀ Q
  have hE_AN : ∀ g : Conv ℂ n, evalSeries ((convEmbed ℂ e A ^ N * g : Conv ℂ n) :
      MvPowerSeries (Fin n) ℂ) =ᶠ[𝓝 (0 : Fin n → ℂ)] fun x =>
        evalSeries (A : MvPowerSeries (Fin d) ℂ) (x ∘ e) ^ N *
          evalSeries (g : MvPowerSeries (Fin n) ℂ) x := fun g => by
    filter_upwards [evalSeries_conv_mul_eventually (convEmbed ℂ e A ^ N) g,
      evalSeries_conv_pow_eventually (convEmbed ℂ e A) N] with x h1 h2
    rw [h1, h2, evalSeries_convEmbed]
  have hE_cl : ∀ i, evalSeries (clearElt e i₀ A B Qf i : MvPowerSeries (Fin n) ℂ) =ᶠ[𝓝 (0 : Fin n
    → ℂ)]
      fun x => evalSeries (A : MvPowerSeries (Fin d) ℂ) (x ∘ e) ^ (Qf i).natDegree *
        evalSeries (polyElt e i (Qf i) : MvPowerSeries (Fin n) ℂ) x -
          evalSeries (polyElt e i₀ (clearPoly (Qf i) (B i) A) : MvPowerSeries (Fin n) ℂ) x :=
    fun i => by
      filter_upwards [evalSeries_conv_sub_eventually
        (convEmbed ℂ e A ^ (Qf i).natDegree * polyElt e i (Qf i))
        (polyElt e i₀ (clearPoly (Qf i) (B i) A)),
        evalSeries_conv_mul_eventually (convEmbed ℂ e A ^ (Qf i).natDegree) (polyElt e i (Qf i)),
        evalSeries_conv_pow_eventually (convEmbed ℂ e A) (Qf i).natDegree] with x h1 h2 h3
      rw [clearElt, h1, h2, h3, evalSeries_convEmbed]
  have hE_g : ∀ i : {i : Fin n // i ∉ Set.range e},
      evalSeries (polyElt e i₀ (clearPoly (Qf i) (B i) A) : MvPowerSeries (Fin n) ℂ) =ᶠ[𝓝 (0 :
        Fin n → ℂ)]
        fun x => evalSeries (polyElt e i₀ Q : MvPowerSeries (Fin n) ℂ) x *
          evalSeries (polyElt e i₀ (Hp i) : MvPowerSeries (Fin n) ℂ) x := fun i => by
    have : polyElt e i₀ (clearPoly (Qf i) (B i) A) = polyElt e i₀ Q * polyElt e i₀ (Hp i) := by
      rw [polyElt, hHp i i.2, Polynomial.map_mul, eval_mul]; rfl
    rw [this]
    exact evalSeries_conv_mul_eventually _ _
  have hE_rel0 : evalSeries (relElt e i₀ A B i₀ : MvPowerSeries (Fin n) ℂ) =ᶠ[𝓝 (0 : Fin n → ℂ)]
      fun x => evalSeries (polyElt e i₀ Q : MvPowerSeries (Fin n) ℂ) x *
        evalSeries (polyElt e i₀ H₀ : MvPowerSeries (Fin n) ℂ) x := by
    have : relElt e i₀ A B i₀ = polyElt e i₀ Q * polyElt e i₀ H₀ := by
      rw [relElt, polyElt, polyElt, polyElt, ← eval_mul, ← Polynomial.map_mul, ← hH₀,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_sub,
        eval_mul, eval_C, eval_X]
      rfl
    rw [this]
    exact evalSeries_conv_mul_eventually _ _
  -- base facts, pulled back along `x ↦ x ∘ e`
  have hAn : ∀ᶠ u in 𝓝 (0 : Fin d → ℂ), ∀ c ∈ coeffFinset Q A B,
      AnalyticAt ℂ (evalSeries (c : MvPowerSeries (Fin d) ℂ)) u :=
    (eventually_all_finset _).2 fun c _ => (analyticAt_evalSeries_zero c.2).eventually_analyticAt
  have hcop := eventually_isCoprime_specialize (K := ℂ) (W := Q) hQdeg
  have hE_ARes := evalSeries_conv_mul_eventually A (resultant Q (derivative Q))
  have hbase : Tendsto (fun x : Fin n → ℂ => x ∘ e) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x : Fin n → ℂ => x ∘ e) :=
      continuous_pi fun k => continuous_apply (e k)
    have := hc.tendsto 0
    simpa using this
  filter_upwards [hV_q, eventually_all.2 hV_rel, (eventually_all_finset S).2 hV_AN,
    eventually_all.2 hV_cl, hE_q, eventually_all.2 fun i => evalSeries_relElt_eventually A B i,
    (eventually_all_finset S).2 fun g _ => hE_AN g, eventually_all.2 hE_cl, eventually_all.2 hE_g,
    hE_rel0, hbase.eventually hAn, hbase.eventually hcop, hbase.eventually hE_ARes] with x h1 h2
      h3 h4
    h5 h6 h7 h8 h9 h10 h11 h12 h13
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end Facts

/-- The local parametrization theorem [GR84, Chapter 3, §1], the graph structure off the
discriminant: for a prime `P` with the data of the primitive normalization, near every point `x`
of the zero-set germ of `comap σ P` with `(A · Res(Q, Q'))(x ∘ e) ≠ 0` the zero set is the graph
of a map analytic at `x ∘ e`, a section of the base projection through `x`. -/
theorem exists_graph_of_isPrime (P : Ideal (Conv ℂ n)) [P.IsPrime] {d : ℕ} (e : Fin d ↪ Fin n)
    (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) (hinj : Function.Injective (normMap ℂ P e L))
    (hfin : RingHom.Finite (A := Conv ℂ d) (B := Conv ℂ n ⧸ P)
      (normMap ℂ P e L : Conv ℂ d →+* Conv ℂ n ⧸ P))
    (i₀ : Fin n) (hi₀ : i₀ ∉ Set.range e) (Q : Polynomial (Conv ℂ d)) (hQ : Q.Monic)
    (hQirr : Irreducible Q)
    (hQP : (Q.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P)
    (A : Conv ℂ d) (hA : A ≠ 0) (B : Fin n → Polynomial (Conv ℂ d))
    (hB : ∀ i, i ∉ Set.range e → convEmbed ℂ e A * convX ℂ i -
      ((B i).map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P)
    {S : Finset (Conv ℂ n)}
    (hS : Ideal.span (S : Set (Conv ℂ n)) = Ideal.comap (substEquiv L) P) :
    ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), x ∈ zeroSet S →
      evalSeries ((A * resultant Q (derivative Q) : Conv ℂ d) : MvPowerSeries (Fin d) ℂ) (x ∘ e)
        ≠ 0 →
      ∃ φ : (Fin d → ℂ) → (Fin n → ℂ), AnalyticAt ℂ φ (x ∘ e) ∧ φ (x ∘ e) = x ∧
        (∀ u, φ u ∘ e = u) ∧ ∀ᶠ y in 𝓝 x, (y ∈ zeroSet S ↔ y = φ (y ∘ e)) := by
  classical
  -- the monic relations of all coordinates and the division argument
  choose Qf hQfm hQfP using fun i => exists_monic_eval_map_mem_comap P e L hfin i
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_span_of_isPrime P e L hinj i₀ hi₀ Q hQ hQirr hQP A hA B hB
    Qf (fun i _ => hQfm i) (fun i _ => hQfP i)
  -- the domain `𝒪_n / P'`, the base embedded injectively
  have hdom : IsDomain (Conv ℂ n ⧸ Ideal.comap (substEquiv L) P) := Ideal.Quotient.isDomain _
  set f : Conv ℂ d →+* Conv ℂ n ⧸ Ideal.comap (substEquiv L) P :=
    (Ideal.Quotient.mk (Ideal.comap (substEquiv L) P)).comp (convEmbed ℂ e).toRingHom with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    rw [hf, RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq] at hab
    apply hinj
    rw [normMap_apply, normMap_apply, Ideal.Quotient.eq, ← map_sub, ← map_sub]
    have hmem : convEmbed ℂ e (a - b) ∈ Ideal.comap (substEquiv L) P := by rw [map_sub]; exact hab
    exact Ideal.mem_comap.mp hmem
  set ξ : Conv ℂ n ⧸ Ideal.comap (substEquiv L) P :=
    Ideal.Quotient.mk (Ideal.comap (substEquiv L) P) (convX ℂ i₀) with hξ
  have hQξ : eval₂ f ξ Q = 0 := by
    rw [hξ, ← mk_eval_map_eq_eval₂]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hQP
  have hrelξ : ∀ i, i ∉ Set.range e →
      f A * Ideal.Quotient.mk (Ideal.comap (substEquiv L) P) (convX ℂ i) = eval₂ f ξ (B i) :=
    fun i hi => by
      rw [hξ, ← mk_eval_map_eq_eval₂, hf, RingHom.comp_apply, ← map_mul]
      exact Ideal.Quotient.eq.mpr (hB i hi)
  -- `Q` divides the clearing polynomials and `A T − B_{i₀}(T)`
  have hGdvd : ∀ i, i ∉ Set.range e → Q ∣ clearPoly (Qf i) (B i) A := fun i hi => by
    apply dvd_of_eval₂_eq_zero_of_monic_irreducible f hfinj hQ hQirr hQξ
    rw [eval₂_clearPoly_eq f (Qf i) (B i) A (hrelξ i hi), ← mk_eval_map_eq_eval₂,
      Ideal.Quotient.eq_zero_iff_mem.mpr (hQfP i), mul_zero]
  choose! Hp hHp using hGdvd
  have hRdvd : Q ∣ C A * X - B i₀ := by
    apply dvd_of_eval₂_eq_zero_of_monic_irreducible f hfinj hQ hQirr hQξ
    rw [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, hrelξ i₀ hi₀, sub_self]
  obtain ⟨H₀, hH₀⟩ := hRdvd
  have hQdeg : 0 < Q.natDegree := hQ.natDegree_pos.mpr hQirr.ne_one
  -- the facts near `0`
  have hall := eventually_graphFacts (e := e) (i₀ := i₀) Q hQdeg A B Qf Hp H₀ N S _ hS hQP
    (fun i hi => hB i hi) hN hHp hH₀
  filter_upwards [hall, eventually_eventually_nhds.mpr hall] with x hx hxnear
  intro hxS hres
  -- the point: `u₀ = x ∘ e`, `t₀ = x i₀`, a simple root of `Q(u₀, ·)`
  have hAu₀ : evalSeries (A : MvPowerSeries (Fin d) ℂ) (x ∘ e) ≠ 0 := fun h =>
    hres (by rw [hx.eq_ARes, h, zero_mul])
  have hResu₀ : evalSeries ((resultant Q (derivative Q) : Conv ℂ d) : MvPowerSeries (Fin d) ℂ)
      (x ∘ e) ≠ 0 := fun h => hres (by rw [hx.eq_ARes, h, mul_zero])
  have hQ0 : (specialize Q (x ∘ e)).eval (x i₀) = 0 := by rw [← hx.eq_q]; exact hx.vq hxS
  have hder0 : (derivative (specialize Q (x ∘ e))).eval (x i₀) ≠ 0 :=
    eval_derivative_ne_zero_of_isCoprime (hx.cop hResu₀) hQ0
  -- the root branch
  have hΦ₂ : AnalyticAt ℂ (fun p : (Fin d → ℂ) × ℂ => (specialize Q p.1).eval p.2) (x ∘ e, x i₀)
    := by
    have hfun : (fun p : (Fin d → ℂ) × ℂ => (specialize Q p.1).eval p.2) = fun p =>
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          evalSeries (Q.coeff k : MvPowerSeries (Fin d) ℂ) p.1 * p.2 ^ k := by
      funext p; exact eval_specialize Q p.1 p.2
    rw [hfun]
    refine (Finset.analyticAt_sum _ fun k hk =>
      (AnalyticAt.comp (g := evalSeries (Q.coeff k : MvPowerSeries (Fin d) ℂ)) (f := Prod.fst)
        (x := (x ∘ e, x i₀)) (hx.an (Q.coeff k) (mem_coeffFinset_Q Q A B hk)) analyticAt_fst).mul
        (analyticAt_snd.pow k)).congr (Eventually.of_forall fun p => ?_)
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
  have hder : HasDerivAt (fun t => (specialize Q (x ∘ e)).eval t)
      ((derivative (specialize Q (x ∘ e))).eval (x i₀)) (x i₀) :=
    Polynomial.hasDerivAt (specialize Q (x ∘ e)) (x i₀)
  obtain ⟨τ, hτan, hτ0, hτzero, hτuniq⟩ := exists_analytic_root_branch hΦ₂ hQ0 hder hder0
  -- the graph map
  set Bf : Fin n → (Fin d → ℂ) → ℂ := fun i u => (specialize (B i) u).eval (τ u) with hBf
  set Af : (Fin d → ℂ) → ℂ := fun u => evalSeries (A : MvPowerSeries (Fin d) ℂ) u with hAf
  set φ : (Fin d → ℂ) → (Fin n → ℂ) := fun u j =>
    if h : ∃ k, e k = j then u (Classical.choose h) else if j = i₀ then τ u else Bf j u / Af u
    with hφ
  have hφ_base : ∀ u k, φ u (e k) = u k := fun u k => by
    have h : ∃ k', e k' = e k := ⟨k, rfl⟩
    simp only [hφ, dite_eq_left h]
    congr 1
    exact e.injective (Classical.choose_spec h)
  have hφ_i₀ : ∀ u, φ u i₀ = τ u := fun u => by
    have h : ¬ ∃ k, e k = i₀ := fun ⟨k, hk⟩ => hi₀ ⟨k, hk⟩
    simp only [hφ, dite_eq_right h, ite_true]
  have hφ_fib : ∀ u i, i ∉ Set.range e → i ≠ i₀ → φ u i = Bf i u / Af u := fun u i hi hii => by
    have h : ¬ ∃ k, e k = i := fun ⟨k, hk⟩ => hi ⟨k, hk⟩
    simp only [hφ, dite_eq_right h, ite_eq_right hii]
  have hBf_an : ∀ i, AnalyticAt ℂ (Bf i) (x ∘ e) := fun i => by
    have hfun : Bf i = fun u => ∑ k ∈ Finset.range ((B i).natDegree + 1),
        evalSeries ((B i).coeff k : MvPowerSeries (Fin d) ℂ) u * τ u ^ k := by
      funext u; exact eval_specialize (B i) u (τ u)
    rw [hfun]
    refine (Finset.analyticAt_sum _ fun k hk =>
      (hx.an ((B i).coeff k) (mem_coeffFinset_B Q A B i hk)).mul (hτan.pow k)).congr
      (Eventually.of_forall fun u => ?_)
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.pow_apply]
  have hAf_an : AnalyticAt ℂ Af (x ∘ e) := hx.an A (mem_coeffFinset_A Q A B)
  refine ⟨φ, ?_, ?_, fun u => funext fun k => hφ_base u k, ?_⟩
  · -- analyticity of the graph map
    refine AnalyticAt.pi (f := fun j u => φ u j) fun j => ?_
    by_cases hj : ∃ k, e k = j
    · obtain ⟨k, rfl⟩ := hj
      have hfun : (fun u => φ u (e k)) = fun u => u k := funext fun u => hφ_base u k
      rw [hfun]
      exact (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).analyticAt _
    · have hj' : j ∉ Set.range e := fun ⟨k, hk⟩ => hj ⟨k, hk⟩
      by_cases hjj : j = i₀
      · subst hjj
        have hfun : (fun u => φ u j) = τ := funext fun u => hφ_i₀ u
        rw [hfun]
        exact hτan
      · have hfun : (fun u => φ u j) = fun u => Bf j u / Af u :=
          funext fun u => hφ_fib u j hj' hjj
        rw [hfun]
        exact (hBf_an j).div hAf_an hAu₀
  · -- the graph map passes through `x`
    funext j
    by_cases hj : ∃ k, e k = j
    · obtain ⟨k, rfl⟩ := hj
      exact hφ_base (x ∘ e) k
    · have hj' : j ∉ Set.range e := fun ⟨k, hk⟩ => hj ⟨k, hk⟩
      by_cases hjj : j = i₀
      · subst hjj
        rw [hφ_i₀]
        exact hτ0
      · rw [hφ_fib (x ∘ e) j hj' hjj]
        have h1 := hx.vrel ⟨j, hj'⟩ hxS
        rw [hx.eq_rel j] at h1
        have hB0 : Bf j (x ∘ e) = (specialize (B j) (x ∘ e)).eval (x i₀) := by
          rw [hBf]; dsimp only; rw [hτ0]
        rw [hB0, div_eq_iff hAu₀, mul_comm]
        exact (sub_eq_zero.mp h1).symm
  · -- the zero set near `x` is the graph
    have hcontb : Tendsto (fun y : Fin n → ℂ => y ∘ e) (𝓝 x) (𝓝 (x ∘ e)) :=
      (continuous_pi fun k => continuous_apply (e k)).tendsto x
    have hcontp : Tendsto (fun y : Fin n → ℂ => (y ∘ e, y i₀)) (𝓝 x) (𝓝 (x ∘ e, x i₀)) :=
      hcontb.prodMk_nhds ((continuous_apply i₀).tendsto x)
    have hAne : ∀ᶠ u in 𝓝 (x ∘ e), Af u ≠ 0 := hAf_an.continuousAt.eventually_ne hAu₀
    filter_upwards [hxnear, hcontb.eventually hτzero, hcontb.eventually hAne,
      hcontp.eventually hτuniq] with y hy hyτ hyA hyuniq
    constructor
    · -- zero set ⊆ graph
      intro hyS
      funext j
      by_cases hj : ∃ k, e k = j
      · obtain ⟨k, rfl⟩ := hj
        exact (hφ_base (y ∘ e) k).symm
      · have hj' : j ∉ Set.range e := fun ⟨k, hk⟩ => hj ⟨k, hk⟩
        have hyi₀ : y i₀ = τ (y ∘ e) := by
          have h1 := hy.vq hyS
          rw [hy.eq_q] at h1
          exact hyuniq h1
        by_cases hjj : j = i₀
        · subst hjj
          rw [hφ_i₀]
          exact hyi₀
        · rw [hφ_fib (y ∘ e) j hj' hjj]
          have h1 := hy.vrel ⟨j, hj'⟩ hyS
          rw [hy.eq_rel j, hyi₀] at h1
          rw [eq_div_iff hyA, mul_comm]
          exact sub_eq_zero.mp h1
    · -- graph ⊆ zero set
      intro hyφ
      have hyi₀ : y i₀ = τ (y ∘ e) := by
        have h := congrFun hyφ i₀
        rw [h]
        exact hφ_i₀ _
      have hyfib : ∀ i, i ∉ Set.range e → i ≠ i₀ →
          Af (y ∘ e) * y i = (specialize (B i) (y ∘ e)).eval (τ (y ∘ e)) := fun i hi hii => by
        have h := congrFun hyφ i
        rw [h, hφ_fib (y ∘ e) i hi hii, mul_div_cancel₀ _ hyA]
      have hy_q : evalSeries (polyElt e i₀ Q : MvPowerSeries (Fin n) ℂ) y = 0 := by
        rw [hy.eq_q, hyi₀]; exact hyτ
      have hy_rel : ∀ i, i ∉ Set.range e →
          evalSeries (relElt e i₀ A B i : MvPowerSeries (Fin n) ℂ) y = 0 := fun i hi => by
        by_cases hii : i = i₀
        · subst hii
          rw [hy.eq_rel0, hy_q, zero_mul]
        · rw [hy.eq_rel i, hyi₀, hyfib i hi hii, sub_self]
      have hy_qf : ∀ i : {i : Fin n // i ∉ Set.range e},
          evalSeries (polyElt e i (Qf i) : MvPowerSeries (Fin n) ℂ) y = 0 := fun i => by
        have hmem : y ∈ zeroSet {relElt e i₀ A B i} := by
          rw [mem_zeroSet_iff]
          intro g hg
          rw [Finset.mem_singleton] at hg
          rw [hg]
          exact hy_rel i i.2
        have h1 := hy.vcl i hmem
        rw [hy.eq_cl i, hy.eq_g i, hy_q, zero_mul, sub_zero] at h1
        exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hyA)
      have hyG₀ : y ∈ zeroSet (gensFinset e i₀ Q A B Qf) := by
        rw [mem_zeroSet_iff]
        intro g hg
        rw [gensFinset, Set.Finite.mem_toFinset] at hg
        rcases hg with (hg | ⟨⟨i, hi⟩, rfl⟩) | ⟨⟨i, hi⟩, rfl⟩
        · rw [Set.mem_singleton_iff] at hg
          rw [hg]
          exact hy_q
        · exact hy_qf ⟨i, hi⟩
        · exact hy_rel i hi
      rw [mem_zeroSet_iff]
      intro g hg
      have h1 := hy.vAN g hg hyG₀
      rw [hy.eq_AN g hg] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hyA)

end Analytic
