/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.RealizesBlowUp
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Ideal
import Hironaka.Manifold.BlowUp.Transform.StrictClopen
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.BM97.LedgerBlowUp
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Center
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Chart
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Kernel
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Resolution.Analytic.Principalization.MonomialStep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The stalks of the monomial ideals after a blow-up

The stalk at a point `x` of the monomial ideal `∏_c 𝓘_{piece c}^{a c}` is the product, over the
pieces through `x`, of the powers of the vanishing stalks of their members
(`stalkIdeal_monomialIdeal`). After the blow-up of a centre, the stalk at `p` of the monomial ideal
of the transformed family is the product, over the old pieces through `π p`, of the powers of the
vanishing stalks of their strict transforms, times, over the locus of a face `P`, the vanishing
stalk of the exceptional divisor to the power `total P − m`
(`stalkIdeal_monomialIdeal_blowUpPieces_of_notMem`, `…_of_mem_faceSet`); and the stalk of the total
transform `π^* M` is the same product with the exceptional power `total P` instead
(`stalkIdeal_totalTransform_monomialIdeal_of_notMem`, `…_of_mem_faceSet`). The last statement is the
identity `π^* 𝓘_D = 𝓘_{D'} · 𝓘_F` for a member `D` containing the centre and `π^* 𝓘_D = 𝓘_{D'}` for
the others, read at every stalk: each member's vanishing stalk pulls back to `𝓘_F^ε` times that of
its strict transform, with `ε = 1` exactly for the pieces of the face, and the pieces of `P` through
`π p` are all of `P`. The exponent `total P` is Kollár's coefficient of the new divisor before the
division by `m` in [Kol07, 111, Step 3] and [Kol07, Definition 60].
-/

public section

open Set Topology Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO.PieceFamily

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {N : AnalyticManifold.{u} 𝕜 E} {Φ : PieceFamily N}
  {F : HypersurfaceFamily N} {e : Fin Φ.nextLabel ↪o F.ι} {m : ℕ} {hV : Φ.IsValid n m}
  {S : Finset (Finset ℕ)}

/-! ### The stalk of the monomial ideal -/

/-- At one of its points, the vanishing stalk of a piece is that of its member. -/
theorem Realizes.vanishingStalk_piece_eq (hΦ : Φ.Realizes F e) {c : Fin Φ.nextComp} {x : N}
    (hx : x ∈ Φ.piece c) :
    vanishingStalk (𝕜 := 𝕜) (E := E) (Φ.piece c) x =
      vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp (e ⟨Φ.label c, Φ.label_lt c c.2⟩)) x := by
  obtain ⟨O, hO, hpiece⟩ := hΦ.exists_isOpen_piece_eq c.2
  have hxO : x ∈ O := (hpiece ▸ hx).2
  rw [hpiece]
  exact vanishingStalk_inter_of_mem_nhds (hO.mem_nhds hxO)

/-- The stalk of the ideal sheaf of a piece is the vanishing stalk of the piece. -/
theorem stalkIdeal_pieceIdeal (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (c : Fin Φ.nextComp)
    (x : N) :
    (Φ.pieceIdeal hF hΦ c).stalkIdeal x = vanishingStalk (𝕜 := 𝕜) (E := E) (Φ.piece c) x :=
  (hΦ.isClosedSubmanifold_piece hF c).stalkIdeal_idealSheaf_eq_vanishingStalk x

open scoped Classical in
/-- The stalk of the monomial ideal at `x` is the product, over the pieces through `x`, of the
powers of the vanishing stalks of their members. -/
theorem stalkIdeal_monomialIdeal (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) (x : N) :
    (Φ.monomialIdeal hF hΦ).stalkIdeal x =
      ∏ c : {c : Fin Φ.nextComp // x ∈ Φ.piece c},
        vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp (e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩)) x ^
          Φ.a c.1 := by
  classical
  rw [monomialIdeal, IdealSheaf.stalkIdeal_finset_prod, ← Finset.prod_filter_mul_prod_filter_not
    Finset.univ (fun c : Fin Φ.nextComp => x ∈ Φ.piece c)]
  have h2 : ∏ c ∈ (Finset.univ.filter fun c : Fin Φ.nextComp => ¬ x ∈ Φ.piece c),
      (Φ.pieceIdeal hF hΦ c ^ Φ.a c.1).stalkIdeal x = 1 := by
    refine Finset.prod_eq_one fun c hc => ?_
    rw [IdealSheaf.stalkIdeal_pow,
      Φ.stalkIdeal_pieceIdeal_of_notMem hF hΦ (Finset.mem_filter.mp hc).2, Ideal.top_pow,
      Ideal.one_eq_top]
  rw [h2, mul_one, Finset.prod_subtype (Finset.univ.filter fun c : Fin Φ.nextComp => x ∈ Φ.piece c)
    (p := fun c : Fin Φ.nextComp => x ∈ Φ.piece c) (fun c => by simp)]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [IdealSheaf.stalkIdeal_pow, Φ.stalkIdeal_pieceIdeal hF hΦ, hΦ.vanishingStalk_piece_eq c.2]

/-! ### The stalks after the blow-up -/

/-- The boundary family after the blow-up of a centre has simple normal crossings, the centre having
simple normal crossings with the family. -/
theorem isSnc_totalTransform_centerOf (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S)) :
    (F.totalTransform (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)).IsSnc ψ₀ :=
  HypersurfaceFamily.isSnc_totalTransform hZ (isBlowUp_blowUpπ ψ₀ hZ) hF
    (hΦ.hasSncWith_centerOf hF hS)

/-- At a point over a piece, the vanishing stalk of the strict transform of the piece is that of the
strict transform of its member: the strict transform of a clopen part of a set is the corresponding
clopen part of the strict transform. -/
theorem Realizes.vanishingStalk_strictTransformSet_piece_eq (hΦ : Φ.Realizes F e) {r : ℕ}
    (hZ' : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r) {c : Fin Φ.nextComp}
        {p : Manifold.blowUp ψ₀ hZ'}
    (hp : Manifold.blowUpπ ψ₀ hZ' p ∈ Φ.piece c) :
    vanishingStalk (𝕜 := 𝕜) (E := E)
        (strictTransformSet (Manifold.blowUpπ ψ₀ hZ') (Φ.centerOf S) (Φ.piece c)) p =
      vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet (Manifold.blowUpπ ψ₀ hZ') (Φ.centerOf S)
        (F.hyp (e ⟨Φ.label c, Φ.label_lt c c.2⟩))) p := by
  have hπ : Continuous (Manifold.blowUpπ ψ₀ hZ') := (isBlowUp_blowUpπ ψ₀ hZ').contMDiff.continuous
  obtain ⟨O, hO, hpiece⟩ := hΦ.exists_isOpen_piece_eq c.2
  have hpO : Manifold.blowUpπ ψ₀ hZ' p ∈ O := (hpiece ▸ hp).2
  have hcl : IsClosed (F.hyp (e ⟨Φ.label c, Φ.label_lt c c.2⟩) ∩ O) := hpiece ▸ Φ.isClosed_piece c
  rw [hpiece, strictTransformSet_inter_of_isOpen hπ _ hO hcl]
  exact vanishingStalk_inter_of_mem_nhds ((hO.preimage hπ).mem_nhds hpO)

/-- The stalk of the monomial ideal of the transformed family at `p`, as a product over all indices
below `nextComp + |S|` of the powers of the vanishing stalks of the new pieces. -/
theorem stalkIdeal_monomialIdeal_blowUpPieces_eq_prod_range (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S))
    (p : Manifold.blowUp ψ₀ hZ) :
    ((Φ.blowUpPieces S m hZ).monomialIdeal (Φ.isSnc_totalTransform_centerOf hF hΦ hS hZ)
        (hΦ.realizes_blowUpPieces hS hZ)).stalkIdeal p =
      ∏ c ∈ Finset.range (Φ.nextComp + S.card),
        vanishingStalk (𝕜 := 𝕜) (E := E) ((Φ.blowUpPieces S m hZ).piece c) p ^
          (Φ.blowUpPieces S m hZ).a c := by
  unfold monomialIdeal
  rw [IdealSheaf.stalkIdeal_finset_prod,
    ← Fin.prod_univ_eq_prod_range (fun c => vanishingStalk (𝕜 := 𝕜) (E := E)
      ((Φ.blowUpPieces S m hZ).piece c) p ^ (Φ.blowUpPieces S m hZ).a c) (Φ.nextComp + S.card)]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [IdealSheaf.stalkIdeal_pow]
  congr 1
  exact (Φ.blowUpPieces S m hZ).stalkIdeal_pieceIdeal _ _ c p

open scoped Classical in
/-- The old part of the product: the strict transforms of the old pieces through `π p`. -/
theorem prod_range_nextComp_vanishingStalk_blowUpPieces (hΦ : Φ.Realizes F e)
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S)) (p : Manifold.blowUp ψ₀ hZ) :
    ∏ c ∈ Finset.range Φ.nextComp,
        vanishingStalk (𝕜 := 𝕜) (E := E) ((Φ.blowUpPieces S m hZ).piece c) p ^
          (Φ.blowUpPieces S m hZ).a c =
      ∏ c : {c : Fin Φ.nextComp // Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c},
        vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)
          (F.hyp (e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩))) p ^ Φ.a c.1 := by
  classical
  have hπ : Continuous (Manifold.blowUpπ ψ₀ hZ) := (isBlowUp_blowUpπ ψ₀ hZ).contMDiff.continuous
  rw [← Fin.prod_univ_eq_prod_range, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun c : Fin Φ.nextComp => Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c)]
  have h2 : ∏ c ∈ (Finset.univ.filter fun c : Fin Φ.nextComp =>
      ¬ Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c),
      vanishingStalk (𝕜 := 𝕜) (E := E) ((Φ.blowUpPieces S m hZ).piece c.1) p ^
        (Φ.blowUpPieces S m hZ).a c.1 = 1 := by
    refine Finset.prod_eq_one fun c hc => ?_
    have hnot : p ∉ (Φ.blowUpPieces S m hZ).piece c.1 := fun hp =>
      (Finset.mem_filter.mp hc).2 (Φ.π_mem_piece_of_mem_blowUpPieces_piece hZ c.2 hp)
    rw [vanishingStalk_eq_top_of_notMem ((Φ.blowUpPieces S m hZ).isClosed_piece c.1) hnot,
      Ideal.top_pow, Ideal.one_eq_top]
  rw [h2, mul_one, Finset.prod_subtype (Finset.univ.filter fun c : Fin Φ.nextComp =>
    Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c) (p := fun c : Fin Φ.nextComp =>
        Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c)
    (fun c => by simp)]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Φ.blowUpPieces_piece_of_lt S m hZ c.1.2, Φ.blowUpPieces_a_of_lt S m hZ c.1.2,
    hΦ.vanishingStalk_strictTransformSet_piece_eq hZ c.2]

/-- Off the exceptional divisor the new part of the product is trivial: no new piece passes through
`p`. -/
theorem prod_range_card_vanishingStalk_blowUpPieces_of_notMem
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S)) {p : Manifold.blowUp ψ₀ hZ}
    (hp : Manifold.blowUpπ ψ₀ hZ p ∉ Φ.centerOf S) :
    ∏ c ∈ Finset.range S.card,
        vanishingStalk (𝕜 := 𝕜) (E := E) ((Φ.blowUpPieces S m hZ).piece (Φ.nextComp + c)) p ^
          (Φ.blowUpPieces S m hZ).a (Φ.nextComp + c) = 1 := by
  refine Finset.prod_eq_one fun c _ => ?_
  have hnot : p ∉ (Φ.blowUpPieces S m hZ).piece (Φ.nextComp + c) := fun hp' => by
    obtain ⟨P, hP, -, hxP⟩ := (Φ.mem_blowUpPieces_piece_of_le hZ (Nat.le_add_right _ _)).mp hp'
    exact hp (Φ.faceSet_subset_centerOf hP hxP)
  rw [vanishingStalk_eq_top_of_notMem ((Φ.blowUpPieces S m hZ).isClosed_piece _) hnot,
    Ideal.top_pow, Ideal.one_eq_top]

/-- Over the locus of `P`, only the new piece of `P` passes through `p`; its vanishing stalk is that
of the exceptional divisor and its exponent is `total P − m`. -/
theorem prod_range_card_vanishingStalk_blowUpPieces_of_mem_faceSet (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S)
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S)) {P : Finset ℕ} (hP : P ∈ S)
    {p : Manifold.blowUp ψ₀ hZ} (hxP : Manifold.blowUpπ ψ₀ hZ p ∈ Φ.faceSet P) :
    ∏ c ∈ Finset.range S.card,
        vanishingStalk (𝕜 := 𝕜) (E := E) ((Φ.blowUpPieces S m hZ).piece (Φ.nextComp + c)) p ^
          (Φ.blowUpPieces S m hZ).a (Φ.nextComp + c) =
      vanishingStalk (𝕜 := 𝕜) (E := E) ((Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.centerOf S) p ^
          (Φ.total P - m) := by
  classical
  have hπ : Continuous (Manifold.blowUpπ ψ₀ hZ) := (isBlowUp_blowUpπ ψ₀ hZ).contMDiff.continuous
  rw [Finset.prod_eq_single (MonomialState.rank S P)]
  · have hc : Φ.nextComp + MonomialState.rank S P = Φ.newComp S P := rfl
    rw [hc, Φ.blowUpPieces_piece_newComp S m hZ hP, Φ.blowUpPieces_a_newComp S m hZ hP]
    congr 1
    -- near `p` the preimage of the locus of `P` is the exceptional divisor
    obtain ⟨U, hU, hUP⟩ := hΦ.exists_mem_nhds_centerOf_inter_subset hS hP hxP
    have hU' : (Manifold.blowUpπ ψ₀ hZ) ⁻¹' U ∈ 𝓝 p := hπ.continuousAt.preimage_mem_nhds hU
    rw [← vanishingStalk_inter_of_mem_nhds (Z := (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.faceSet P) hU',
      ← vanishingStalk_inter_of_mem_nhds (Z := (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.centerOf S) hU']
    congr 1
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hq, hqU⟩
      exact ⟨Φ.faceSet_subset_centerOf hP hq, hqU⟩
    · rintro ⟨hq, hqU⟩
      exact ⟨hUP ⟨hq, hqU⟩, hqU⟩
  · intro c _ hc
    have hnot : p ∉ (Φ.blowUpPieces S m hZ).piece (Φ.nextComp + c) := fun hp' => by
      obtain ⟨Q, hQ, hQc, hxQ⟩ :=
        (Φ.mem_blowUpPieces_piece_of_le hZ (Nat.le_add_right _ _)).mp hp'
      have hQP : Q = P := hΦ.eq_of_mem_faceSet_of_isCenter hS hQ hP hxQ hxP
      subst hQP
      have hQc' : Φ.nextComp + MonomialState.rank S Q = Φ.nextComp + c := hQc
      exact hc (Nat.add_left_cancel hQc').symm
    rw [vanishingStalk_eq_top_of_notMem ((Φ.blowUpPieces S m hZ).isClosed_piece _) hnot,
      Ideal.top_pow, Ideal.one_eq_top]
  · intro h
    exact absurd (Finset.mem_range.mpr (MonomialState.rank_lt_card hP)) h

open scoped Classical in
/-- The stalk of the monomial ideal of the transformed family at a point off the exceptional
divisor: the strict transforms of the old pieces through `π p`, with their exponents. -/
theorem stalkIdeal_monomialIdeal_blowUpPieces_of_notMem (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard
      S)) {p : Manifold.blowUp ψ₀ hZ}
    (hp : Manifold.blowUpπ ψ₀ hZ p ∉ Φ.centerOf S) :
    ((Φ.blowUpPieces S m hZ).monomialIdeal (Φ.isSnc_totalTransform_centerOf hF hΦ hS hZ)
        (hΦ.realizes_blowUpPieces hS hZ)).stalkIdeal p =
      ∏ c : {c : Fin Φ.nextComp // Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c},
        vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)
          (F.hyp (e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩))) p ^ Φ.a c.1 := by
  rw [Φ.stalkIdeal_monomialIdeal_blowUpPieces_eq_prod_range hF hΦ hS hZ, Finset.prod_range_add,
    Φ.prod_range_card_vanishingStalk_blowUpPieces_of_notMem hZ hp, mul_one,
    Φ.prod_range_nextComp_vanishingStalk_blowUpPieces hΦ hZ]

open scoped Classical in
/-- The stalk of the monomial ideal of the transformed family at a point over the locus of the face
`P`: the strict transforms of the old pieces through `π p`, times the exceptional divisor to the
power `total P − m`. -/
theorem stalkIdeal_monomialIdeal_blowUpPieces_of_mem_faceSet (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S))
    {P : Finset ℕ} (hP : P ∈ S)
    {p : Manifold.blowUp ψ₀ hZ} (hxP : Manifold.blowUpπ ψ₀ hZ p ∈ Φ.faceSet P) :
    ((Φ.blowUpPieces S m hZ).monomialIdeal (Φ.isSnc_totalTransform_centerOf hF hΦ hS hZ)
        (hΦ.realizes_blowUpPieces hS hZ)).stalkIdeal p =
      (∏ c : {c : Fin Φ.nextComp // Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c},
        vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)
          (F.hyp (e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩))) p ^ Φ.a c.1) *
        vanishingStalk (𝕜 := 𝕜) (E := E) ((Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.centerOf S) p ^
          (Φ.total P - m) := by
  rw [Φ.stalkIdeal_monomialIdeal_blowUpPieces_eq_prod_range hF hΦ hS hZ, Finset.prod_range_add,
    Φ.prod_range_card_vanishingStalk_blowUpPieces_of_mem_faceSet hΦ hS hZ hP hxP,
    Φ.prod_range_nextComp_vanishingStalk_blowUpPieces hΦ hZ]

/-! ### The stalks of the total transform -/

open scoped Classical in
/-- The exponent sum over the pieces of `P` through a point of its locus is `total P`. -/
theorem sum_ite_mem_eq_total {P : Finset ℕ} (hPn : ∀ c ∈ P, c < Φ.nextComp) {x : N}
    (hxP : x ∈ Φ.faceSet P) :
    ∑ c : {c : Fin Φ.nextComp // x ∈ Φ.piece c}, (if c.1.1 ∈ P then Φ.a c.1 else 0) =
      Φ.total P := by
  classical
  rw [← Finset.sum_filter]
  have himg : (Finset.univ.filter fun c : {c : Fin Φ.nextComp // x ∈ Φ.piece c} => c.1.1 ∈ P).image
      (fun c => c.1.1) = P := by
    ext c
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact hd
    · intro hc
      exact ⟨⟨⟨c, hPn c hc⟩, Φ.mem_faceSet.mp hxP c hc⟩, hc, rfl⟩
  rw [total]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image fun d _ d' _ h => Subtype.ext (Fin.ext h)]

open scoped Classical in
/-- The stalk of the total transform of the monomial ideal at a point off the exceptional divisor:
the pull-back of the vanishing stalk of a member not containing the centre is that of its strict
transform. -/
theorem stalkIdeal_totalTransform_monomialIdeal_of_notMem (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S)) {p : Manifold.blowUp ψ₀ hZ}
    (hp : Manifold.blowUpπ ψ₀ hZ p ∉ Φ.centerOf S) :
    ((Φ.monomialIdeal hF hΦ).pullback _ (isBlowUp_blowUpπ ψ₀ hZ).contMDiff).stalkIdeal p =
      ∏ c : {c : Fin Φ.nextComp // Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c},
        vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)
          (F.hyp (e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩))) p ^ Φ.a c.1 := by
  rw [IdealSheaf.stalkIdeal_pullback, Φ.stalkIdeal_monomialIdeal hF hΦ, Ideal.map_finset_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Ideal.map_pow,
    map_germMap_vanishingStalk_hyp_of_notMem hZ (isBlowUp_blowUpπ ψ₀ hZ) hF hp _]
  rfl

open scoped Classical in
/-- The stalk of the total transform of the monomial ideal at a point over the locus of the face
`P`: the strict transforms of the old pieces through `π p`, times the exceptional divisor to the
power `total P`. The pieces of `P` are exactly the pieces through `π p` whose coordinates lie in the
block of the centre, and only for those does the pull-back of the member's vanishing stalk acquire
the exceptional factor. -/
theorem stalkIdeal_totalTransform_monomialIdeal_of_mem_faceSet (hF : F.IsSnc ψ₀)
    (hΦ : Φ.Realizes F e) (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀
      (Φ.centerOf S) (faceCard S))
    {P : Finset ℕ} (hP : P ∈ S)
    {p : Manifold.blowUp ψ₀ hZ} (hxP : Manifold.blowUpπ ψ₀ hZ p ∈ Φ.faceSet P) :
    ((Φ.monomialIdeal hF hΦ).pullback _ (isBlowUp_blowUpπ ψ₀ hZ).contMDiff).stalkIdeal p =
      (∏ c : {c : Fin Φ.nextComp // Manifold.blowUpπ ψ₀ hZ p ∈ Φ.piece c},
        vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)
          (F.hyp (e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩))) p ^ Φ.a c.1) *
        vanishingStalk (𝕜 := 𝕜) (E := E) ((Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.centerOf S) p ^ Φ.total P
            := by
  classical
  set x := Manifold.blowUpπ ψ₀ hZ p with hx
  have hPn : ∀ c ∈ P, c < Φ.nextComp := fun c hc =>
    Φ.lt_nextComp_of_mem_nerve (subset_nerve_of_isCenter hS hP) hc
  have hxZ : x ∈ Φ.centerOf S := Φ.faceSet_subset_centerOf hP hxP
  obtain ⟨φ, σ, κ, hxφ, hφad, hκ, hcoord, hmiss, hPσ, hσP, cidx, hsnc, hκc⟩ :=
    hΦ.exists_chart_of_mem_faceSet hF hS hP hxP
  obtain ⟨i, Φ', hΦ', hpΦ⟩ := (isBlowUp_blowUpπ ψ₀ hZ).cover φ σ hφad p hxφ
  rw [IdealSheaf.stalkIdeal_pullback, Φ.stalkIdeal_monomialIdeal hF hΦ, Ideal.map_finset_prod]
  -- each member's vanishing stalk pulls back to `I_F^ε` times its strict transform's
  have hterm : ∀ c : {c : Fin Φ.nextComp // x ∈ Φ.piece c},
      Ideal.map (germMap (Manifold.blowUpπ ψ₀ hZ) (isBlowUp_blowUpπ ψ₀ hZ).contMDiff p)
          (vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp (e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩)) x ^
            Φ.a c.1) =
        (vanishingStalk (𝕜 := 𝕜) (E := E) ((Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.centerOf S) p ^
            (if c.1.1 ∈ P then Φ.a c.1 else 0)) *
          vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet (Manifold.blowUpπ ψ₀ hZ)
              (Φ.centerOf S)
            (F.hyp (e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩))) p ^ Φ.a c.1 := by
    intro c
    rw [Ideal.map_pow, germMap_vanishingStalk_hyp ψ₀ hZ (isBlowUp_blowUpπ ψ₀ hZ) hF hφad hsnc hΦ'
      hpΦ ⟨e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩, hΦ.piece_subset_hyp c.1.2 c.2⟩, mul_pow,
      ← pow_mul]
    congr 2
    have hiff : (∃ k, σ k = κ c) ↔ c.1.1 ∈ P := by
      rw [hPσ c]
      exact ⟨fun ⟨k, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, hk⟩⟩
    rw [hκc c] at hiff
    by_cases hc : c.1.1 ∈ P
    · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc, one_mul]
    · rw [ite_eq_right (fun h => hc (hiff.mp h)), ite_eq_right hc, zero_mul]
  rw [Finset.prod_congr rfl fun c _ => hterm c, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Φ.sum_ite_mem_eq_total hPn hxP, mul_comm]

end Hironaka.Manifold.BMO.PieceFamily
