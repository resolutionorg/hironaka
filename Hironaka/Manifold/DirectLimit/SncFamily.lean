/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.DirectLimit.Manifold
public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
public import Hironaka.Manifold.Snc.Basic
public import Mathlib.Data.Sigma.Order
import Hironaka.Manifold.Chart.Transport

/-!
# Hypersurface families glued along an open-embedding chain

Włodarczyk's exceptional divisor `E` on the glued space `M̃` of a locally finite embedded
desingularization [Wlo09, Theorem 2.0.2] is the union of the exceptional divisors of the
successions over the members of an exhaustion, which agree on the overlaps up to the empty blow-ups
([Wlo09, Theorem 2.0.3 (4)]; [Kol07, Proposition 37, (37.2)]: the subschemes of the pieces glue).
This module glues a chain of hypersurface families, one on each piece `X m` of an open-embedding
chain `c` (`OpenEmbeddingChain`), into one family on the limit `c.Limit`, given order embeddings
`ε m` of the index sets matching the members of consecutive levels (`FamilyChain`): the trace on
`X m` of the member `ε m j` of level `m + 1` is the member `j`, and a member of level `m + 1` not in
the range of `ε m` has empty trace on `X m`.

* `FamilyChain.iter`: the composite embeddings of the index sets, with their traces
  (`preimage_iter_hyp_iter`, `preimage_iter_hyp_eq_empty`).
* `FamilyChain.Born`: a member of level `m` is *born* at `m` when it is not the image of a member
  of level `m - 1`; every member has a unique born ancestor (`exists_born`,
  `eq_of_born_of_iter_eq`, `birth`).
* `FamilyChain.glue`: the glued family, indexed by the pairs `(m, j)` in the lexicographic order,
  the member of a born `j` being the union over the higher levels of the images of its
  descendants (and empty otherwise). Its trace on every piece is a member of that piece's family
  or empty (`preimage_toLimit_glueHyp`), its members are closed when those of the pieces are
  (`isClosed_glueHyp`), its support traces to the supports of the pieces
  (`preimage_toLimit_support_glue`), and it is a simple normal crossings family when every
  piece's family is (`isSnc_glue`): the adapted and snc charts of a piece, read on the limit
  through the inclusion of the piece (`limitChart`, `limitChart_mem_maximalAtlas`), serve for the
  glued family, whose members through a point correspond to the members of the piece through the
  point by the birth correspondence.

Not in the sources beyond the statements cited; bookkeeping.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Filter
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold.OpenEmbeddingChain

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (c : OpenEmbeddingChain.{u} 𝕜 E)

/-! ### Closed sets of the limit, and charts of the pieces read on the limit -/

/-- A subset of the limit is closed iff its preimage in every piece is (the quotient topology of
the sigma type). -/
theorem isClosed_iff_forall_preimage_toLimit (s : Set c.Limit) :
    IsClosed s ↔ ∀ n, IsClosed (c.toLimit n ⁻¹' s) := by
  constructor
  · intro hs n
    exact hs.preimage (c.continuous_toLimit n)
  · intro h
    have hsat : IsClosed (Quotient.mk c.setoid ⁻¹' s) := by
      rw [isClosed_sigma_iff]
      exact h
    exact (isQuotientMap_quotient_mk' (s := c.setoid)).isClosed_preimage.mp hsat

/-- A chart of the maximal atlas of a piece, read on the limit through the inclusion of the piece,
is a chart of the maximal atlas of the limit (`mem_maximalAtlas_of_contMDiffOn`: analytic with
analytic inverse). -/
theorem limitChart_mem_maximalAtlas (n : ℕ) [Nonempty (c.X n)]
    {φ : OpenPartialHomeomorph (c.X n) E} (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω (c.X n)) :
    c.limitChart n φ ∈ maximalAtlas 𝓘(𝕜, E) ω c.Limit := by
  refine mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · rw [c.limitChart_source]
    exact (contMDiffOn_of_mem_maximalAtlas hφ).comp
      ((c.contMDiffOn_pieceOpenEmb_symm n).mono inter_subset_left) fun _ hx => hx.2
  · rw [c.limitChart_target]
    refine ((c.contMDiff_toLimit n).comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas hφ)).congr fun v _ => ?_
    exact (c.limitChart_symm_apply n φ v).symm

/-- A point of the limit over a piece lies in the source of the limit chart of a chart of the
piece containing its preimage. -/
theorem toLimit_mem_limitChart_source (n : ℕ) [Nonempty (c.X n)]
    (φ : OpenPartialHomeomorph (c.X n) E) {x : c.X n} (hx : x ∈ φ.source) :
    c.toLimit n x ∈ (c.limitChart n φ).source := by
  rw [c.limitChart_source]
  refine ⟨⟨x, rfl⟩, ?_⟩
  change (c.pieceOpenEmb n).symm (c.toLimit n x) ∈ φ.source
  rw [c.pieceOpenEmb_symm_toLimit]
  exact hx

/-- A point of the source of a limit chart is the image of a point of the chart's source. -/
theorem exists_eq_toLimit_of_mem_limitChart_source (n : ℕ) [Nonempty (c.X n)]
    (φ : OpenPartialHomeomorph (c.X n) E) {q : c.Limit} (hq : q ∈ (c.limitChart n φ).source) :
    ∃ x ∈ φ.source, c.toLimit n x = q := by
  rw [c.limitChart_source] at hq
  obtain ⟨⟨x, rfl⟩, hx⟩ := hq
  refine ⟨x, ?_, rfl⟩
  change (c.pieceOpenEmb n).symm (c.toLimit n x) ∈ φ.source at hx
  rwa [c.pieceOpenEmb_symm_toLimit] at hx

/-- The limit chart at the image of a point of the piece is the chart at the point. -/
theorem limitChart_toLimit (n : ℕ) [Nonempty (c.X n)] (φ : OpenPartialHomeomorph (c.X n) E)
    (x : c.X n) : c.limitChart n φ (c.toLimit n x) = φ x := by
  rw [c.limitChart_apply, c.pieceOpenEmb_symm_toLimit]

/-! ### A chain of hypersurface families -/

/-- A chain of hypersurface families on the pieces of `c`, with order embeddings of the index sets
matching the members of consecutive levels: the trace on `X m` of the member `ε m j` of level
`m + 1` is the member `j` of level `m`, and a member of level `m + 1` outside the range of `ε m`
has empty trace on `X m` ([Kol07, Proposition 37, (37.2)]; the empty blow-ups arising from
restriction, [Kol07, 34.1]). -/
structure FamilyChain where
  /-- The family on the piece `X m`. -/
  H : ∀ m : ℕ, HypersurfaceFamily (c.X m)
  /-- The matching of the members of level `m` with members of level `m + 1`. -/
  ε : ∀ m : ℕ, (H m).ι ↪o (H (m + 1)).ι
  /-- The trace of a matched member is the member. -/
  preimage_hyp_ε : ∀ (m : ℕ) (j : (H m).ι), ⇑(c.ι m) ⁻¹' (H (m + 1)).hyp (ε m j) = (H m).hyp j
  /-- An unmatched member of level `m + 1` has empty trace on level `m`. -/
  preimage_hyp_eq_empty : ∀ (m : ℕ) (b : (H (m + 1)).ι), b ∉ Set.range (ε m) →
    ⇑(c.ι m) ⁻¹' (H (m + 1)).hyp b = ∅

namespace FamilyChain

variable {c} (D : c.FamilyChain)

/-! ### The composite embeddings of the index sets -/

/-- The composite embedding `(H m).ι ↪o (H m').ι` for `m ≤ m'`, `ε (m'-1) ∘ ⋯ ∘ ε m`
(`Nat.leRecOn`, as `OpenEmbeddingChain.iter`). -/
def iter : ∀ {m m' : ℕ}, m ≤ m' → (D.H m).ι ↪o (D.H m').ι := fun {m _} h =>
  Nat.leRecOn (C := fun k => (D.H m).ι ↪o (D.H k).ι) h (fun {k} f => f.trans (D.ε k))
    (RelEmbedding.refl _)

theorem iter_self (m : ℕ) : D.iter (le_refl m) = RelEmbedding.refl _ := Nat.leRecOn_self _

theorem iter_self_apply (m : ℕ) (h : m ≤ m) (j : (D.H m).ι) : D.iter h j = j := by
  rw [iter_self]
  rfl

theorem iter_succ {m m' : ℕ} (h : m ≤ m') (h' : m ≤ m' + 1) :
    D.iter h' = (D.iter h).trans (D.ε m') := Nat.leRecOn_succ h _

theorem iter_succ_apply {m m' : ℕ} (h : m ≤ m') (h' : m ≤ m' + 1) (j : (D.H m).ι) :
    D.iter h' j = D.ε m' (D.iter h j) := by
  rw [D.iter_succ h h']
  rfl

theorem iter_trans {m m' k : ℕ} (h₁ : m ≤ m') (h₂ : m' ≤ k) (j : (D.H m).ι) :
    D.iter h₂ (D.iter h₁ j) = D.iter (h₁.trans h₂) j := by
  induction k, h₂ using Nat.le_induction with
  | base => rw [iter_self_apply]
  | succ k hmk ih =>
    rw [D.iter_succ_apply hmk (Nat.le_succ_of_le hmk), ih,
      D.iter_succ_apply (h₁.trans hmk) (h₁.trans (Nat.le_succ_of_le hmk))]

/-- The trace on `X m` of the descendant at level `m'` of a member of level `m` is the member. -/
theorem preimage_iter_hyp_iter {m m' : ℕ} (h : m ≤ m') (j : (D.H m).ι) :
    ⇑(c.iter h) ⁻¹' (D.H m').hyp (D.iter h j) = (D.H m).hyp j := by
  induction m', h using Nat.le_induction with
  | base =>
    rw [D.iter_self_apply, c.iter_self]
    rfl
  | succ k hmk ih =>
    rw [D.iter_succ_apply hmk (Nat.le_succ_of_le hmk), c.iter_succ hmk (Nat.le_succ_of_le hmk)]
    change ⇑(c.iter hmk) ⁻¹' (⇑(c.ι k) ⁻¹' (D.H (k + 1)).hyp (D.ε k (D.iter hmk j))) = _
    rw [D.preimage_hyp_ε, ih]

/-- A member of level `m'` which is not the descendant of a member of level `m` has empty trace
on `X m`. -/
theorem preimage_iter_hyp_eq_empty {m m' : ℕ} (h : m ≤ m') (b : (D.H m').ι)
    (hb : b ∉ Set.range (D.iter h)) : ⇑(c.iter h) ⁻¹' (D.H m').hyp b = ∅ := by
  induction m', h using Nat.le_induction with
  | base => exact absurd ⟨b, D.iter_self_apply m _ b⟩ hb
  | succ k hmk ih =>
    rw [c.iter_succ hmk (Nat.le_succ_of_le hmk)]
    change ⇑(c.iter hmk) ⁻¹' (⇑(c.ι k) ⁻¹' (D.H (k + 1)).hyp b) = ∅
    by_cases hbr : b ∈ Set.range (D.ε k)
    · obtain ⟨b', rfl⟩ := hbr
      have hb' : b' ∉ Set.range (D.iter hmk) := fun ⟨j, hj⟩ =>
        hb ⟨j, by rw [D.iter_succ_apply hmk (Nat.le_succ_of_le hmk), hj]⟩
      rw [D.preimage_hyp_ε, ih b' hb']
    · rw [D.preimage_hyp_eq_empty k b hbr, preimage_empty]

/-! ### Birth -/

/-- A member of level `m` is born at `m` when it is not the image of a member of level `m - 1`
(every member of level `0` is born at `0`). -/
def Born : ∀ m : ℕ, (D.H m).ι → Prop
  | 0, _ => True
  | m + 1, j => j ∉ Set.range (D.ε m)

theorem born_zero (j : (D.H 0).ι) : D.Born 0 j := trivial

theorem born_succ_iff (m : ℕ) (j : (D.H (m + 1)).ι) : D.Born (m + 1) j ↔ j ∉ Set.range (D.ε m) :=
  Iff.rfl

/-- Every member has a born ancestor. -/
theorem exists_born : ∀ (m' : ℕ) (b : (D.H m').ι),
    ∃ (m : ℕ) (h : m ≤ m') (j : (D.H m).ι), D.Born m j ∧ D.iter h j = b
  | 0, b => ⟨0, le_rfl, b, trivial, D.iter_self_apply 0 le_rfl b⟩
  | m' + 1, b => by
    by_cases hb : b ∈ Set.range (D.ε m')
    · obtain ⟨b', rfl⟩ := hb
      obtain ⟨m, h, j, hj, hjb⟩ := exists_born m' b'
      exact ⟨m, h.trans (Nat.le_succ m'), j, hj,
        by rw [D.iter_succ_apply h (h.trans (Nat.le_succ m')), hjb]⟩
    · exact ⟨m' + 1, le_rfl, b, hb, D.iter_self_apply _ le_rfl b⟩

/-- A born member is no descendant of a member of a lower level. -/
theorem not_lt_of_born_of_iter_eq {m₁ m₂ m' : ℕ} (h₁ : m₁ ≤ m') (h₂ : m₂ ≤ m')
    {j₁ : (D.H m₁).ι} {j₂ : (D.H m₂).ι} (hb₂ : D.Born m₂ j₂)
    (heq : D.iter h₁ j₁ = D.iter h₂ j₂) : ¬ m₁ < m₂ := by
  intro hlt
  obtain ⟨k, rfl⟩ : ∃ k, m₂ = k + 1 := ⟨m₂ - 1, by omega⟩
  have hk : m₁ ≤ k := Nat.lt_succ_iff.mp hlt
  have h3 : D.iter h₂ (D.iter (Nat.le_succ_of_le hk) j₁) = D.iter h₂ j₂ := by
    rw [D.iter_trans]
    exact heq
  have e := (D.iter h₂).injective h3
  exact hb₂ ⟨D.iter hk j₁, by rw [← D.iter_succ_apply hk (Nat.le_succ_of_le hk)]; exact e⟩

/-- The born ancestor of a member is unique. -/
theorem eq_of_born_of_iter_eq {m₁ m₂ m' : ℕ} (h₁ : m₁ ≤ m') (h₂ : m₂ ≤ m')
    {j₁ : (D.H m₁).ι} {j₂ : (D.H m₂).ι} (hb₁ : D.Born m₁ j₁) (hb₂ : D.Born m₂ j₂)
    (heq : D.iter h₁ j₁ = D.iter h₂ j₂) :
    (⟨m₁, j₁⟩ : Σ m, (D.H m).ι) = ⟨m₂, j₂⟩ := by
  rcases lt_trichotomy m₁ m₂ with hlt | hm | hgt
  · exact absurd hlt (D.not_lt_of_born_of_iter_eq h₁ h₂ hb₂ heq)
  · subst hm
    rw [(D.iter h₁).injective heq]
  · exact absurd hgt (D.not_lt_of_born_of_iter_eq h₂ h₁ hb₁ heq.symm)

/-- The born ancestor of a member (chosen). -/
def birth (m' : ℕ) (b : (D.H m').ι) : Σ m, (D.H m).ι :=
  ⟨(D.exists_born m' b).choose, (D.exists_born m' b).choose_spec.choose_spec.choose⟩

theorem birth_le (m' : ℕ) (b : (D.H m').ι) : (D.birth m' b).1 ≤ m' :=
  (D.exists_born m' b).choose_spec.choose

theorem born_birth (m' : ℕ) (b : (D.H m').ι) : D.Born (D.birth m' b).1 (D.birth m' b).2 :=
  (D.exists_born m' b).choose_spec.choose_spec.choose_spec.1

theorem iter_birth (m' : ℕ) (b : (D.H m').ι) : D.iter (D.birth_le m' b) (D.birth m' b).2 = b :=
  (D.exists_born m' b).choose_spec.choose_spec.choose_spec.2

/-- The composite embedding read on equal pairs. -/
theorem iter_congr_sigma {m' : ℕ} {p q : Σ m, (D.H m).ι} (hp : p.1 ≤ m') (hq : q.1 ≤ m')
    (h : p = q) : D.iter hp p.2 = D.iter hq q.2 := by
  subst h
  rfl

/-- The birth map is injective. -/
theorem eq_of_birth_eq {m' : ℕ} {b₁ b₂ : (D.H m').ι} (h : D.birth m' b₁ = D.birth m' b₂) :
    b₁ = b₂ := by
  rw [← D.iter_birth m' b₁, ← D.iter_birth m' b₂]
  exact D.iter_congr_sigma _ _ h

/-- The birth of the descendant of a born member is the member. -/
theorem birth_iter_of_born {m m' : ℕ} (h : m ≤ m') {j : (D.H m).ι} (hj : D.Born m j) :
    D.birth m' (D.iter h j) = ⟨m, j⟩ :=
  D.eq_of_born_of_iter_eq (D.birth_le m' _) h (D.born_birth m' _) hj (D.iter_birth m' _)

/-! ### The glued family -/

open Classical in
/-- The glued member of the pair `(m, j)`: for `j` born at `m`, the union over the levels `m' ≥ m`
of the images in the limit of its descendants; empty otherwise. -/
def glueHyp (m : ℕ) (j : (D.H m).ι) : Set c.Limit :=
  if D.Born m j then ⋃ (m' : ℕ) (h : m ≤ m'), c.toLimit m' '' (D.H m').hyp (D.iter h j) else ∅

/-- **The glued hypersurface family** on the limit, indexed by the pairs `(m, j)` in the
lexicographic order. -/
def glue : HypersurfaceFamily c.Limit where
  ι := Σₗ m : ℕ, (D.H m).ι
  countable := inferInstanceAs (Countable (Σ m : ℕ, (D.H m).ι))
  hyp p := D.glueHyp (ofLex p).1 (ofLex p).2

theorem glue_hyp (p : Σₗ m : ℕ, (D.H m).ι) : D.glue.hyp p = D.glueHyp (ofLex p).1 (ofLex p).2 :=
  rfl

theorem glueHyp_of_not_born {m : ℕ} {j : (D.H m).ι} (hj : ¬ D.Born m j) : D.glueHyp m j = ∅ := by
  classical
  unfold glueHyp
  rw [ite_eq_right hj]

/-- **The trace of a glued member on a piece**: the descendant of the member at that level, if the
level is at or above the birth level, and empty below it. -/
theorem preimage_toLimit_glueHyp {m : ℕ} {j : (D.H m).ι} (hj : D.Born m j) (m'' : ℕ) :
    c.toLimit m'' ⁻¹' D.glueHyp m j =
      if h : m ≤ m'' then (D.H m'').hyp (D.iter h j) else ∅ := by
  classical
  ext x
  unfold glueHyp
  rw [ite_eq_left hj]
  simp only [mem_preimage, mem_iUnion, mem_image]
  constructor
  · rintro ⟨m', h, y, hy, hxy⟩
    have hx₀ : c.iter (le_max_right m' m'') x = c.iter (le_max_left m' m'') y :=
      (c.toLimit_eq_iff_iter (le_max_right m' m'') (le_max_left m' m'')).mp hxy.symm
    have hy₀ : c.iter (le_max_left m' m'') y ∈
        (D.H (max m' m'')).hyp (D.iter (h.trans (le_max_left m' m'')) j) := by
      rw [← D.iter_trans h (le_max_left m' m''), ← mem_preimage, D.preimage_iter_hyp_iter]
      exact hy
    rw [← hx₀] at hy₀
    by_cases hmm : m ≤ m''
    · rw [dite_eq_left hmm]
      have e := D.iter_trans hmm (le_max_right m' m'') j
      rw [← e, ← mem_preimage, D.preimage_iter_hyp_iter] at hy₀
      exact hy₀
    · exfalso
      have hnot : D.iter (h.trans (le_max_left m' m'')) j ∉ Set.range (D.iter (le_max_right m' m''))
          := by
        rintro ⟨ν, hν⟩
        have hlt : m'' < m := Nat.lt_of_not_le hmm
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hk : m'' ≤ k := Nat.lt_succ_iff.mp hlt
        have h3 : D.iter (h.trans (le_max_left m' m'')) (D.iter (Nat.le_succ_of_le hk) ν) =
            D.iter (h.trans (le_max_left m' m'')) j := by
          rw [D.iter_trans]
          exact hν
        have e := (D.iter (h.trans (le_max_left m' m''))).injective h3
        exact hj ⟨D.iter hk ν, by rw [← D.iter_succ_apply hk (Nat.le_succ_of_le hk)]; exact e⟩
      have := D.preimage_iter_hyp_eq_empty (le_max_right m' m'') _ hnot
      rw [← mem_preimage, this] at hy₀
      exact hy₀
  · intro hx
    by_cases hmm : m ≤ m''
    · rw [dite_eq_left hmm] at hx
      exact ⟨m'', hmm, x, hx, rfl⟩
    · rw [dite_eq_right hmm] at hx
      exact absurd hx (notMem_empty x)

/-- The trace of the glued member of the birth of a member `b` of a piece is `b`. -/
theorem preimage_toLimit_glueHyp_birth (m' : ℕ) (b : (D.H m').ι) :
    c.toLimit m' ⁻¹' D.glueHyp (D.birth m' b).1 (D.birth m' b).2 = (D.H m').hyp b := by
  rw [D.preimage_toLimit_glueHyp (D.born_birth m' b), dite_eq_left (D.birth_le m' b), D.iter_birth]

/-- The membership of a point of the limit over a piece in a glued member. -/
theorem toLimit_mem_glueHyp_iff (m : ℕ) (j : (D.H m).ι) (m'' : ℕ) (x : c.X m'') :
    c.toLimit m'' x ∈ D.glueHyp m j ↔
      D.Born m j ∧ ∃ h : m ≤ m'', x ∈ (D.H m'').hyp (D.iter h j) := by
  by_cases hj : D.Born m j
  · rw [← mem_preimage, D.preimage_toLimit_glueHyp hj]
    by_cases hmm : m ≤ m''
    · rw [dite_eq_left hmm]
      exact ⟨fun hx => ⟨hj, hmm, hx⟩, fun ⟨_, _, hx⟩ => hx⟩
    · rw [dite_eq_right hmm]
      exact ⟨fun hx => absurd hx (notMem_empty x), fun ⟨_, h, _⟩ => absurd h hmm⟩
  · rw [D.glueHyp_of_not_born hj]
    exact ⟨fun hx => absurd hx (notMem_empty _), fun ⟨h, _⟩ => absurd h hj⟩

/-- The glued members are closed when the members of the pieces are. -/
theorem isClosed_glueHyp (hcl : ∀ (m : ℕ) (j : (D.H m).ι), IsClosed ((D.H m).hyp j)) (m : ℕ)
    (j : (D.H m).ι) : IsClosed (D.glueHyp m j) := by
  rw [c.isClosed_iff_forall_preimage_toLimit]
  intro n
  by_cases hj : D.Born m j
  · rw [D.preimage_toLimit_glueHyp hj]
    split_ifs
    · exact hcl _ _
    · exact isClosed_empty
  · rw [D.glueHyp_of_not_born hj, preimage_empty]
    exact isClosed_empty

/-- **The support of the glued family traces to the supports of the pieces.** -/
theorem preimage_toLimit_support_glue (m'' : ℕ) :
    c.toLimit m'' ⁻¹' D.glue.support = (D.H m'').support := by
  ext x
  simp only [HypersurfaceFamily.support, mem_preimage, mem_iUnion]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨-, h, hx⟩ := (D.toLimit_mem_glueHyp_iff _ _ m'' x).mp hp
    exact ⟨_, hx⟩
  · rintro ⟨b, hb⟩
    refine ⟨toLex (D.birth m'' b), ?_⟩
    change c.toLimit m'' x ∈ D.glueHyp (D.birth m'' b).1 (D.birth m'' b).2
    rw [D.toLimit_mem_glueHyp_iff]
    exact ⟨D.born_birth m'' b, D.birth_le m'' b, by rw [D.iter_birth]; exact hb⟩

/-! ### Charts of a piece read on the limit -/

variable {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

omit D in
/-- A chart of a piece adapted to the trace of a subset `Y'` of the limit, read on the limit, is
adapted to `Y'`. -/
theorem _root_.Manifold.OpenEmbeddingChain.isAdaptedChart_limitChart (m : ℕ) [Nonempty (c.X m)]
    {Y' : Set c.Limit} {Y : Set (c.X m)} (hY : c.toLimit m ⁻¹' Y' = Y)
    {φ : OpenPartialHomeomorph (c.X m) E} {k : ℕ} {σ : Fin k ↪ Fin n}
    (hφ : IsAdaptedChart ψ Y φ σ) : IsAdaptedChart ψ Y' (c.limitChart m φ) σ := by
  refine ⟨c.limitChart_mem_maximalAtlas m hφ.1, fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := c.exists_eq_toLimit_of_mem_limitChart_source m φ hy
  rw [c.limitChart_toLimit, ← hφ.2 z hz, ← hY]
  rfl

/-- The glued member of a born pair is a closed submanifold of codimension one when the members
of the pieces are: the adapted chart of the trace, read on the limit. -/
theorem isClosedSubmanifold_glueHyp (hH : ∀ m, (D.H m).IsSnc ψ) (m : ℕ) (j : (D.H m).ι) :
    IsClosedSubmanifold ψ (D.glueHyp m j) 1 := by
  refine ⟨D.isClosed_glueHyp (fun m j => ((hH m).1 j).isClosed) m j, fun q hq => ?_⟩
  obtain ⟨m'', x, rfl⟩ := c.toLimit_surjective q
  have : Nonempty (c.X m'') := ⟨x⟩
  obtain ⟨hj, h, hx⟩ := (D.toLimit_mem_glueHyp_iff m j m'' x).mp hq
  obtain ⟨φ, σ, hxφ, hadapt⟩ := ((hH m'').1 (D.iter h j)).exists_adaptedChart x hx
  refine ⟨c.limitChart m'' φ, σ, c.toLimit_mem_limitChart_source m'' φ hxφ,
    c.isAdaptedChart_limitChart ψ m'' ?_ hadapt⟩
  rw [D.preimage_toLimit_glueHyp hj, dite_eq_left h]

/-- The member of a piece through `x` corresponding to a glued member through the image of `x`:
its descendant at that level (`toLimit_mem_glueHyp_iff`). -/
def glueIdx {m'' : ℕ} {x : c.X m''} (p : {p // c.toLimit m'' x ∈ D.glue.hyp p}) :
    {b : (D.H m'').ι // x ∈ (D.H m'').hyp b} :=
  ⟨D.iter ((D.toLimit_mem_glueHyp_iff _ _ m'' x).mp p.2).2.choose (ofLex p.1).2,
    ((D.toLimit_mem_glueHyp_iff _ _ m'' x).mp p.2).2.choose_spec⟩

theorem glueIdx_injective {m'' : ℕ} {x : c.X m''} :
    Function.Injective (D.glueIdx (m'' := m'') (x := x)) := by
  intro p₁ p₂ hp
  have born : ∀ p : {p // c.toLimit m'' x ∈ D.glue.hyp p}, D.Born (ofLex p.1).1 (ofLex p.1).2 :=
    fun p => ((D.toLimit_mem_glueHyp_iff _ _ m'' x).mp p.2).1
  have e := D.eq_of_born_of_iter_eq _ _ (born p₁) (born p₂) (congrArg Subtype.val hp)
  apply Subtype.ext
  change p₁.1 = p₂.1
  exact ofLex.injective (e : ofLex p₁.1 = ofLex p₂.1)

/-- An snc chart of a piece's family at `x`, read on the limit, is an snc chart of the glued
family at the image of `x`, with the indices of the glued members through the point those of
their descendants in the piece (`glueIdx`). -/
theorem isSncChartAt_glue_limitChart {m'' : ℕ} [Nonempty (c.X m'')] {x : c.X m''}
    {φ : OpenPartialHomeomorph (c.X m'') E} {cidx : {j // x ∈ (D.H m'').hyp j} → Fin n}
    (hc : (D.H m'').IsSncChartAt ψ φ x cidx) :
    D.glue.IsSncChartAt ψ (c.limitChart m'' φ) (c.toLimit m'' x) fun p => cidx (D.glueIdx p) := by
  refine ⟨c.limitChart_mem_maximalAtlas m'' hc.mem_maximalAtlas,
    c.toLimit_mem_limitChart_source m'' φ hc.mem_source, fun p y hy => ?_,
    fun p₁ p₂ hp => D.glueIdx_injective (hc.injective hp)⟩
  obtain ⟨z, hz, rfl⟩ := c.exists_eq_toLimit_of_mem_limitChart_source m'' φ hy
  rw [c.limitChart_toLimit]
  change c.toLimit m'' z ∈ D.glueHyp (ofLex p.1).1 (ofLex p.1).2 ↔
    ψ (φ z) (cidx (D.glueIdx p)) = 0
  rw [D.toLimit_mem_glueHyp_iff, ← hc.mem_iff (D.glueIdx p) hz]
  constructor
  · rintro ⟨-, h', hz'⟩
    exact hz'
  · intro hz'
    exact ⟨((D.toLimit_mem_glueHyp_iff _ _ m'' x).mp p.2).1, _, hz'⟩

/-- The glued family is locally finite when the families of the pieces are: a neighbourhood of a
point of a piece meeting finitely many members of the piece, read on the limit, meets only the
glued members of their born ancestors. -/
theorem locallyFinite_glue (hH : ∀ m, LocallyFinite (D.H m).hyp) : LocallyFinite D.glue.hyp := by
  intro q
  obtain ⟨m'', x, rfl⟩ := c.toLimit_surjective q
  obtain ⟨t, ht, hfin⟩ := hH m'' x
  refine ⟨c.toLimit m'' '' t, (c.isOpenEmbedding_toLimit m'').isOpenMap.image_mem_nhds ht, ?_⟩
  refine ((hfin.image (fun b => toLex (D.birth m'' b))).subset fun p hp => ?_)
  obtain ⟨_, hpq, ⟨y, hy, rfl⟩⟩ := hp
  rw [glue_hyp, D.toLimit_mem_glueHyp_iff] at hpq
  obtain ⟨hb, h, hy'⟩ := hpq
  refine ⟨D.iter h (ofLex p).2, ⟨y, hy', hy⟩, ?_⟩
  change toLex (D.birth m'' (D.iter h (ofLex p).2)) = p
  rw [D.birth_iter_of_born h hb]
  rfl

/-- **The glued family of a chain of simple normal crossings families has simple normal
crossings**: closed smooth hypersurfaces (`isClosedSubmanifold_glueHyp`), locally finite
(`locallyFinite_glue`), and the snc chart of a piece at a point, read on the limit, is an snc chart
of the glued family, the members through the point corresponding to those of the piece through it
by the birth correspondence. -/
theorem isSnc_glue (hH : ∀ m, (D.H m).IsSnc ψ) : D.glue.IsSnc ψ := by
  refine ⟨fun p => D.isClosedSubmanifold_glueHyp ψ hH _ _,
    D.locallyFinite_glue fun m => (hH m).2.1, fun q => ?_⟩
  obtain ⟨m'', x, rfl⟩ := c.toLimit_surjective q
  have : Nonempty (c.X m'') := ⟨x⟩
  obtain ⟨φ, cidx, hc⟩ := (hH m'').2.2 x
  exact ⟨c.limitChart m'' φ, _, D.isSncChartAt_glue_limitChart ψ hc⟩

end FamilyChain

end Manifold.OpenEmbeddingChain

end
