/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Differential
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.AnalyticSpace.RegularStalk
import Hironaka.Manifold.Germ.StalkNoetherian
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Module.SpanRankOperations

/-!
# Germs with independent differentials are part of a regular system of parameters

Germs `h₁, …, h_c ∈ 𝔪_q` of `𝒜_{Kⁿ,q}` are part of a regular system of parameters iff their
differentials `dh_{1,q}, …, dh_{c,q}` are linearly independent — the analytic form of the standard
fact about regular local rings [Sta, Tag 00NQ]. The proof runs through the cotangent space
`𝔪_q/𝔪_q²`: the `K`-linear independence of the differentials is that of the cotangent classes
(`linearIndependent_cotangentClass_iff_linearPart`); the classes live in the `CotangentSpace`, a
vector space over the residue field `κ = 𝒜_{Kⁿ,q}/𝔪_q`, and `K → κ` is an isomorphism (every germ
is a constant modulo `𝔪_q`, a nonzero constant is a unit), so `K`-independence and
`κ`-independence agree (`linearIndependent_residueField_iff_of_algebra`); and a family of `𝔪_q` is
a minimal generating system — a regular system of parameters, `𝒜_{Kⁿ,q}` being regular of
dimension `n` — iff its classes are a `κ`-basis
(`IsLocalRing.span_eq_maximalIdeal_and_card_eq_spanFinrank_iff`,
`IsLocalRing.exists_basis_cotangentSpace_of_span_eq`). Independent classes extend to a basis
(`Module.Basis.sumExtend`), whose new members are lifted to `𝔪_q`. The theorem
`isRegularLocalRing_quotient_span_range_and_ringKrullDim` gives the regularity and the dimension
`n − c` of the quotient of `𝒜_{Kⁿ,q}` by such germs, the algebraic core of the fact that the
common zero set of `c` functions with independent differentials is a
submanifold of codimension `c`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open IsLocalRing Ideal Module
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

section SumExtend

variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V] {v : ι → V}

/-- `Module.Basis.sumExtend` keeps the given vectors at the `inl` indices. -/
theorem _root_.Module.Basis.sumExtend_inl (hs : LinearIndependent F v) (i : ι) :
    Module.Basis.sumExtend hs (Sum.inl i) = v i := by
  simp only [Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.extend_apply_self]
  rfl

end SumExtend

section Transfer

variable {F : Type*} [Field F] {R : Type*} [CommRing R] [IsLocalRing R] [Algebra F R]

/-- Linear independence in the cotangent space `𝔪/𝔪²` over the residue field `κ = R/𝔪` and over a
field of constants `F → R` agree when `F → κ` is an isomorphism (every element of `R` is a constant
modulo `𝔪`, and a constant in `𝔪` is zero). -/
theorem linearIndependent_residueField_iff_of_algebra
    (hsurj : ∀ r : R, ∃ c : F, r - algebraMap F R c ∈ maximalIdeal R)
    (hinj : ∀ c : F, algebraMap F R c ∈ maximalIdeal R → c = 0)
    {ι : Type*} [Finite ι] (v : ι → CotangentSpace R) :
    LinearIndependent (IsLocalRing.ResidueField R) v ↔ LinearIndependent F v := by
  classical
  let _ := Fintype.ofFinite ι
  have hres : ∀ (r : R) (m : CotangentSpace R), residue R r • m = r • m := fun r m =>
    algebraMap_smul (IsLocalRing.ResidueField R) r m
  have halg : ∀ (c : F) (m : CotangentSpace R), algebraMap F R c • m = c • m := fun c m =>
    algebraMap_smul R c m
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro H g hg i
    have h0 : ∑ i, residue R (algebraMap F R (g i)) • v i = 0 := by
      simpa only [hres, halg] using hg
    exact hinj _ ((residue_eq_zero_iff _).mp (H _ h0 i))
  · intro H g hg i
    choose r hr using fun i => Ideal.Quotient.mk_surjective (I := maximalIdeal R) (g i)
    choose c hc using fun i => hsurj (r i)
    have hgc : ∀ i, g i • v i = c i • v i := fun i => by
      rw [← hr i]
      change residue R (r i) • v i = _
      rw [hres, ← halg, ← sub_add_cancel (r i) (algebraMap F R (c i)), add_smul,
        Ideal.Cotangent.smul_eq_zero_of_mem (hc i), zero_add]
    have hsum : ∑ i, c i • v i = 0 := by simpa only [hgc] using hg
    have hci := H c hsum i
    rw [← hr i]
    change residue R (r i) = 0
    rw [residue_eq_zero_iff]
    have := hc i
    rwa [hci, map_zero, sub_zero] at this

end Transfer

variable (K : Type) [RCLike K] (n : ℕ)

/-- Every germ of `𝒜_{Kⁿ,q}` is a constant modulo `𝔪_q` (its value at `q`). -/
theorem exists_sub_algebraMap_mem_maximalIdeal (q : Kn.{u} K n)
    (r : (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) :
    ∃ c : K, r - algebraMap K _ c ∈
      maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) :=
  ⟨Manifold.eval K (Kn.{u} K n) (Kn.{u} K n) q r, (mem_maximalIdeal_iff_eval _ _).mpr (by
    rw [map_sub, algebraMap_stalk_eq, eval_const, sub_self])⟩

/-- A constant of `𝒜_{Kⁿ,q}` lying in `𝔪_q` is zero. -/
theorem algebraMap_mem_maximalIdeal_imp (q : Kn.{u} K n) (c : K)
    (hc : algebraMap K ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) c ∈
      maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)) : c = 0 := by
  have := (mem_maximalIdeal_iff_eval _ _).mp hc
  rwa [algebraMap_stalk_eq, eval_const] at this

/-- Independent cotangent classes of `h₁, …, h_c ∈ 𝔪_q` extend to a regular system of parameters
`x` indexed by `Fin n` through any bijection `e` of `Fin c ⊕ (new indices)` with `Fin n`, with
`x (e (inl j)) = h j`. -/
theorem exists_span_eq_maximalIdeal_of_equiv (q : Kn.{u} K n) {c : ℕ}
    (h : Fin c → (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)
    (hm : ∀ j, h j ∈ maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q))
    (hli : LinearIndependent
      (IsLocalRing.ResidueField ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q))
      (fun j => (maximalIdeal _).toCotangent ⟨h j, hm j⟩))
    (e : Fin c ⊕ Module.Basis.sumExtendIndex hli ≃ Fin n) :
    ∃ x : Fin n → (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q,
      maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) =
        Ideal.span (Set.range x) ∧ ∀ j, x (e (Sum.inl j)) = h j := by
  classical
  have hfin : Finite (Module.Basis.sumExtendIndex hli) := by
    have := FiniteDimensional.fintypeBasisIndex (Module.Basis.sumExtend hli)
    exact Finite.of_injective (Sum.inr : Module.Basis.sumExtendIndex hli →
      Fin c ⊕ Module.Basis.sumExtendIndex hli) Sum.inr_injective
  let _ : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  -- lift the new basis vectors to `𝔪`
  choose y hy using fun k : Module.Basis.sumExtendIndex hli =>
    (maximalIdeal _).toCotangent_surjective (Module.Basis.sumExtend hli (Sum.inr k))
  obtain ⟨x, hxdef⟩ : ∃ x : Fin n → (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q,
      ∀ i, x i = Sum.elim (fun j => h j) (fun k => (y k : _)) (e.symm i) := ⟨_, fun _ => rfl⟩
  have hxm : ∀ i,
      x i ∈ maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) := by
    intro i
    rw [hxdef i]
    obtain ⟨s, hs⟩ : ∃ s, e.symm i = s := ⟨_, rfl⟩
    rw [hs]
    cases s with
    | inl j => exact hm j
    | inr k => exact (y k).2
  have hb : ∀ i, (Module.Basis.sumExtend hli).reindex e i =
      (maximalIdeal _).toCotangent ⟨x i, hxm i⟩ := by
    intro i
    rw [Module.Basis.reindex_apply]
    obtain ⟨s, hs⟩ : ∃ s, e.symm i = s := ⟨_, rfl⟩
    have hxi : x i = Sum.elim (fun j => h j) (fun k => (y k : _)) s := by rw [hxdef i, hs]
    rw [hs]
    cases s with
    | inl j =>
      rw [Basis.sumExtend_inl]
      congr 1
      exact Subtype.ext hxi.symm
    | inr k =>
      rw [← hy k]
      congr 1
      exact Subtype.ext hxi.symm
  refine ⟨x, ((span_eq_maximalIdeal_and_card_eq_spanFinrank_iff x hxm).mpr
    ⟨(Module.Basis.sumExtend hli).reindex e, hb⟩).1, fun j => ?_⟩
  rw [hxdef, Equiv.symm_apply_apply]
  rfl

/-- The count: `c` independent classes plus the new basis vectors make `n = dim 𝔪_q/𝔪_q²`. -/
theorem card_sumExtendIndex (q : Kn.{u} K n) {c : ℕ}
    (h : Fin c → (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)
    (hm : ∀ j, h j ∈ maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q))
    (hli : LinearIndependent
      (IsLocalRing.ResidueField ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q))
      (fun j => (maximalIdeal _).toCotangent ⟨h j, hm j⟩))
    [Fintype (Module.Basis.sumExtendIndex hli)] :
    c + Fintype.card (Module.Basis.sumExtendIndex hli) = n := by
  have hdim : ((n : ℕ) : WithBot ℕ∞) =
      ringKrullDim ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) :=
    (ringKrullDim_stalk_affine K n q).symm
  have := Module.finrank_eq_card_basis (Module.Basis.sumExtend hli)
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    spanFinrank_maximalIdeal_eq_of_natCast_eq hdim, Fintype.card_sum,
    Fintype.card_fin] at this
  exact this.symm

/-- Germs `h₁, …, h_c ∈ 𝔪_q` are part of a regular system of parameters of `𝒜_{Kⁿ,q}` iff their
linear parts are linearly independent, in the structure-sheaf presentation of the stalk. -/
theorem exists_span_eq_maximalIdeal_extending_iff' (q : Kn.{u} K n) {c : ℕ}
    (h : Fin c → (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)
    (hm : ∀ j, h j ∈ maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)) :
    (∃ (x : Fin n → (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)
        (σ : Fin c ↪ Fin n),
        maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) =
          Ideal.span (Set.range x) ∧
        ((n : ℕ) : WithBot ℕ∞) =
          ringKrullDim ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) ∧
        ∀ j, x (σ j) = h j) ↔
      LinearIndependent K (fun j => Manifold.linearPart (Kn.{u} K n) ContinuousLinearEquiv.ulift
        (chartAt (Kn.{u} K n) q) (IsManifold.chart_mem_maximalAtlas q) (mem_chart_source _ q)
        (h j)) := by
  classical
  -- the cotangent classes of the `h j`
  have hcls : (fun j => cotangentClass (Kn.{u} K n) q (h j)) =
      fun j => (maximalIdeal _).toCotangent ⟨h j, hm j⟩ := by
    funext j
    unfold cotangentClass
    congr 1
    exact Subtype.ext (by
      simp only
      rw [(mem_maximalIdeal_iff_eval (Kn.{u} K n) (h j)).mp (hm j), map_zero, sub_zero])
  have hdim : ((n : ℕ) : WithBot ℕ∞) =
      ringKrullDim ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) :=
    (ringKrullDim_stalk_affine K n q).symm
  have hA : LinearIndependent K (fun j => Manifold.linearPart
      (Kn.{u} K n) ContinuousLinearEquiv.ulift
      (chartAt (Kn.{u} K n) q) (IsManifold.chart_mem_maximalAtlas q) (mem_chart_source _ q)
      (h j)) ↔ LinearIndependent K (fun j => (maximalIdeal _).toCotangent ⟨h j, hm j⟩) := by
    rw [← hcls]
    exact (linearIndependent_cotangentClass_iff_linearPart (Kn.{u} K n) ContinuousLinearEquiv.ulift
      (chartAt (Kn.{u} K n) q) (IsManifold.chart_mem_maximalAtlas q) (mem_chart_source _ q) h).symm
  have hB : LinearIndependent K (fun j => (maximalIdeal _).toCotangent ⟨h j, hm j⟩) ↔
      LinearIndependent (IsLocalRing.ResidueField _)
        (fun j => (maximalIdeal _).toCotangent ⟨h j, hm j⟩) :=
    (linearIndependent_residueField_iff_of_algebra (exists_sub_algebraMap_mem_maximalIdeal K n q)
      (algebraMap_mem_maximalIdeal_imp K n q) _).symm
  rw [hA, hB]
  constructor
  · rintro ⟨x, σ, hx, hn, hxσ⟩
    obtain ⟨b, hb⟩ := exists_basis_cotangentSpace_of_span_eq x hx hn
    have hvb : (fun j => (maximalIdeal _).toCotangent ⟨h j, hm j⟩) = b ∘ σ := by
      funext j
      rw [Function.comp_apply, hb (σ j)]
      congr 1
      exact Subtype.ext (hxσ j).symm
    rw [hvb]
    exact b.linearIndependent.comp σ σ.injective
  · intro hli
    have hfin : Finite (Module.Basis.sumExtendIndex hli) := by
      have := FiniteDimensional.fintypeBasisIndex (Module.Basis.sumExtend hli)
      exact Finite.of_injective (Sum.inr : Module.Basis.sumExtendIndex hli →
        Fin c ⊕ Module.Basis.sumExtendIndex hli) Sum.inr_injective
    let _ : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
    have hcard := card_sumExtendIndex K n q h hm hli
    obtain ⟨e, -⟩ : ∃ e : Fin c ⊕ Module.Basis.sumExtendIndex hli ≃ Fin n, True :=
      ⟨Fintype.equivFinOfCardEq (by rw [Fintype.card_sum, Fintype.card_fin]; exact hcard), trivial⟩
    obtain ⟨x, hx, hxe⟩ := exists_span_eq_maximalIdeal_of_equiv K n q h hm hli e
    exact ⟨x, ⟨fun j => e (Sum.inl j), fun a b hab => Sum.inl_injective (e.injective hab)⟩, hx,
      hdim, hxe⟩

/-- Germs `h₁, …, h_c ∈ 𝔪_q` with independent differentials are the initial segment of a regular
system of parameters `x` of `𝒜_{Kⁿ,q}`: `x (castLE j) = h j`. -/
theorem exists_span_eq_maximalIdeal_castLE (q : Kn.{u} K n) {c : ℕ}
    (h : Fin c → (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)
    (hm : ∀ j, h j ∈ maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q))
    (hli : LinearIndependent K (fun j => Manifold.linearPart (Kn.{u} K n)
        ContinuousLinearEquiv.ulift
      (chartAt (Kn.{u} K n) q) (IsManifold.chart_mem_maximalAtlas q) (mem_chart_source _ q)
      (h j))) :
    ∃ (hcn : c ≤ n) (x : Fin n → (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q),
      maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) =
        Ideal.span (Set.range x) ∧ ∀ j, x (Fin.castLE hcn j) = h j := by
  classical
  have hcls : (fun j => cotangentClass (Kn.{u} K n) q (h j)) =
      fun j => (maximalIdeal _).toCotangent ⟨h j, hm j⟩ := by
    funext j
    unfold cotangentClass
    congr 1
    exact Subtype.ext (by
      simp only
      rw [(mem_maximalIdeal_iff_eval (Kn.{u} K n) (h j)).mp (hm j), map_zero, sub_zero])
  have hliκ : LinearIndependent
      (IsLocalRing.ResidueField ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q))
      (fun j => (maximalIdeal _).toCotangent ⟨h j, hm j⟩) := by
    rw [linearIndependent_residueField_iff_of_algebra
      (exists_sub_algebraMap_mem_maximalIdeal K n q) (algebraMap_mem_maximalIdeal_imp K n q),
      ← hcls, linearIndependent_cotangentClass_iff_linearPart (Kn.{u} K n)
        ContinuousLinearEquiv.ulift (chartAt (Kn.{u} K n) q) (IsManifold.chart_mem_maximalAtlas q)
        (mem_chart_source _ q) h]
    exact hli
  have hfin : Finite (Module.Basis.sumExtendIndex hliκ) := by
    have := FiniteDimensional.fintypeBasisIndex (Module.Basis.sumExtend hliκ)
    exact Finite.of_injective (Sum.inr : Module.Basis.sumExtendIndex hliκ →
      Fin c ⊕ Module.Basis.sumExtendIndex hliκ) Sum.inr_injective
  let _ : Fintype (Module.Basis.sumExtendIndex hliκ) := Fintype.ofFinite _
  have hcard := card_sumExtendIndex K n q h hm hliκ
  have hcn : c ≤ n := by omega
  let eJ : Module.Basis.sumExtendIndex hliκ ≃ Fin (n - c) :=
    Fintype.equivFinOfCardEq (by omega)
  let e : Fin c ⊕ Module.Basis.sumExtendIndex hliκ ≃ Fin n :=
    ((Equiv.sumCongr (Equiv.refl (Fin c)) eJ).trans finSumFinEquiv).trans
      (finCongr (Nat.add_sub_cancel' hcn))
  have he : ∀ j, e (Sum.inl j) = Fin.castLE hcn j := fun j => by
    ext
    simp [e, finSumFinEquiv_apply_left]
  obtain ⟨x, hx, hxe⟩ := exists_span_eq_maximalIdeal_of_equiv K n q h hm hliκ e
  refine ⟨hcn, x, hx, fun j => ?_⟩
  rw [← he j]
  exact hxe j

/-- The quotient of `𝒜_{Kⁿ,q}` by `c` germs of `𝔪_q` with independent differentials is a regular
local ring of dimension `n − c`: the germs are an initial segment of a regular system of
parameters, and the quotient of a regular local ring by an initial segment of a regular system of
parameters is regular of the complementary dimension
(`IsLocalRing.isRegularLocalRing_quotient_span_image_lt_and_ringKrullDim`). -/
theorem isRegularLocalRing_quotient_span_range_and_ringKrullDim (q : Kn.{u} K n) {c : ℕ}
    (h : Fin c → (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q)
    (hm : ∀ j, h j ∈ maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q))
    (hli : LinearIndependent K (fun j => Manifold.linearPart (Kn.{u} K n)
        ContinuousLinearEquiv.ulift
      (chartAt (Kn.{u} K n) q) (IsManifold.chart_mem_maximalAtlas q) (mem_chart_source _ q)
      (h j))) :
    IsRegularLocalRing ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q ⧸
        Ideal.span (Set.range h)) ∧
      ringKrullDim ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q ⧸
        Ideal.span (Set.range h)) + (c : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hcn, x, hx, hxc⟩ := exists_span_eq_maximalIdeal_castLE K n q h hm hli
  have hdim : ((n : ℕ) : WithBot ℕ∞) =
      ringKrullDim ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) :=
    (ringKrullDim_stalk_affine K n q).symm
  have himg : x '' {j : Fin n | j.val < c} = Set.range h := by
    ext s
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j.val, hj⟩, by rw [← hxc]; congr 1⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.castLE hcn j, j.2, hxc j⟩
  have := isRegularLocalRing_quotient_span_image_lt_and_ringKrullDim x hx hdim hcn
  rw [himg] at this
  exact ⟨this.1, this.2.trans hdim.symm⟩

/-- Germs `h₁, …, h_c ∈ 𝔪_q` are part of a regular system of parameters of `𝒜_{Kⁿ,q}` iff their
differentials are linearly independent. -/
theorem exists_span_eq_maximalIdeal_extending_iff (q : Kn.{u} K n) {c : ℕ}
    (h : Fin c → (affine K n).toLocallyRingedSpace.presheaf.stalk q)
    (hm : ∀ j,
      h j ∈ IsLocalRing.maximalIdeal ((affine K n).toLocallyRingedSpace.presheaf.stalk q)) :
    (∃ (x : Fin n → (affine K n).toLocallyRingedSpace.presheaf.stalk q) (σ : Fin c ↪ Fin n),
        IsLocalRing.maximalIdeal ((affine K n).toLocallyRingedSpace.presheaf.stalk q) =
          Ideal.span (Set.range x) ∧
        ((n : ℕ) : WithBot ℕ∞) =
          ringKrullDim ((affine K n).toLocallyRingedSpace.presheaf.stalk q) ∧
        ∀ j, x (σ j) = h j) ↔
      LinearIndependent K (fun j => dlin K n q (h j)) :=
  exists_span_eq_maximalIdeal_extending_iff' K n q h hm

end AnalyticSpace
