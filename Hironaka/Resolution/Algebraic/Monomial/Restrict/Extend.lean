/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Restrict.Rename

/-!
# The renumbering across one blow-up

When the direct state `D` blows up its centre `S_D` and the pulled-back state `P` blows up the
centre `S` of `N`, whose faces in `P` are exactly the `ρ`-images of the faces of `S_D`, the
renumbering `Rel ρ σ D P` of `Hironaka/Resolution/Algebraic/Monomial/Restrict/Rename.lean` extends:
the new component of `Q ∈ S_D` goes to the new component of `ρ(Q) ∈ S` (`extendComp`), the new label
of `D` to the new label of `P` (`extendLabel`), and `Rel` persists (`Rel.blowUp`). The order of the
new components is preserved because the faces of a centre are numbered by their sorted lists of
components and `ρ` is strictly monotone (`lex_map_iff`). Not in the sources; this is the step
of the induction of `Hironaka/Resolution/Algebraic/Monomial/Restrict/Phase.lean`, and `extendComp`
is also the renumbering along which the geometric run is pulled back in
`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackRun.lean` and
`Hironaka/Resolution/Algebraic/Monomial/Geometric/ChainRun.lean`.
-/

@[expose] public section

namespace Hironaka.Monomial.MonomialState

open Finset

section Defs

variable (ρ σ : ℕ → ℕ) (D P : MonomialState) (S_D S : Finset (Finset ℕ))

/-- The renumbering of components after a blow-up: old components by `ρ`, the new component of
the face `Q` of `S_D` to the new component of `ρ(Q)` in `S`. -/
def extendComp (c : ℕ) : ℕ :=
  if c < D.nextComp then ρ c
  else (S_D.filter fun Q => D.newComp S_D Q = c).sup fun Q => P.newComp S (Q.image ρ)

/-- The renumbering of labels after a blow-up: old labels by `σ`, the new label to the new
label. -/
def extendLabel (ℓ : ℕ) : ℕ := if ℓ < D.nextLabel then σ ℓ else P.nextLabel

theorem extendComp_of_lt {c : ℕ} (hc : c < D.nextComp) : extendComp ρ D P S_D S c = ρ c :=
  ite_eq_left hc

theorem extendComp_newComp {Q : Finset ℕ} (hQ : Q ∈ S_D) :
    extendComp ρ D P S_D S (D.newComp S_D Q) = P.newComp S (Q.image ρ) := by
  rw [extendComp, ite_eq_right (not_lt.mpr (D.nextComp_le_newComp S_D Q))]
  have : (S_D.filter fun Q' => D.newComp S_D Q' = D.newComp S_D Q) = {Q} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hQ, rfl⟩,
      fun Q' hQ' =>
        D.newComp_injOn S_D (Finset.mem_filter.mp hQ').1 hQ (Finset.mem_filter.mp hQ').2⟩
  rw [this, Finset.sup_singleton]

theorem extendLabel_of_lt {ℓ : ℕ} (hℓ : ℓ < D.nextLabel) : extendLabel σ D P ℓ = σ ℓ :=
  ite_eq_left hℓ

theorem extendLabel_nextLabel : extendLabel σ D P D.nextLabel = P.nextLabel :=
  ite_eq_right (lt_irrefl _)

theorem image_extendComp_of_lt {T : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp) :
    T.image (extendComp ρ D P S_D S) = T.image ρ :=
  Finset.image_congr fun c hc => extendComp_of_lt ρ D P S_D S (hT c hc)

end Defs

/-! ### Ranks under the renumbering -/

theorem rank_lt_rank_iff {S : Finset (Finset ℕ)} {P Q : Finset ℕ} (hP : P ∈ S) (hQ : Q ∈ S) :
    rank S P < rank S Q ↔ faceList P < faceList Q := by
  refine ⟨fun h => ?_, rank_lt_rank hP⟩
  by_contra hn
  rcases (not_lt.mp hn).lt_or_eq with hlt | heq
  · exact lt_asymm h (rank_lt_rank hQ hlt)
  · exact lt_irrefl _ (faceList_injective heq ▸ h)

/-- The new components allocated by a blow-up are exactly `nextComp, …, nextComp + |S_D| - 1`. -/
theorem exists_newComp_eq (D : MonomialState) (S_D : Finset (Finset ℕ)) {c : ℕ}
    (hc : D.nextComp ≤ c) (hc' : c < D.nextComp + S_D.card) : ∃ Q ∈ S_D, D.newComp S_D Q = c := by
  have himg : S_D.image (rank S_D) = Finset.range S_D.card := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (rank_lt_card hQ)
    · rw [Finset.card_range, Finset.card_image_of_injOn (rank_injOn S_D)]
  have : c - D.nextComp ∈ S_D.image (rank S_D) := by
    rw [himg, Finset.mem_range]; omega
  obtain ⟨Q, hQ, hr⟩ := Finset.mem_image.mp this
  exact ⟨Q, hQ, by rw [newComp, hr]; omega⟩

namespace Rel

variable {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P)
include h

theorem faceList_image {Q : Finset ℕ} (hQ : ∀ c ∈ Q, c < D.nextComp) :
    faceList (Q.image ρ) = (faceList Q).map ρ :=
  sortedList_image fun a ha b hb hab => h.mono (hQ a ha) (hQ b hb) hab

theorem faceList_image_lt_iff {Q Q' : Finset ℕ} (hQ : ∀ c ∈ Q, c < D.nextComp)
    (hQ' : ∀ c ∈ Q', c < D.nextComp) :
    faceList (Q.image ρ) < faceList (Q'.image ρ) ↔ faceList Q < faceList Q' := by
  rw [h.faceList_image hQ, h.faceList_image hQ']
  exact map_lt_map_iff h.mono (fun c hc => hQ c (mem_sortedList.mp hc))
    (fun c hc => hQ' c (mem_sortedList.mp hc))

/-- Images of subsets of faces compare like the subsets. -/
theorem image_subset_image_iff {A B : Finset ℕ} (hA : ∀ c ∈ A, c < D.nextComp)
    (hB : ∀ c ∈ B, c < D.nextComp) : A.image ρ ⊆ B.image ρ ↔ A ⊆ B := by
  rw [← Finset.coe_subset, Finset.coe_image, Finset.coe_image,
    h.mono.injOn.image_subset_image_iff (fun c hc => hA c hc) (fun c hc => hB c hc),
    Finset.coe_subset]

theorem image_eq_image_iff {A B : Finset ℕ} (hA : ∀ c ∈ A, c < D.nextComp)
    (hB : ∀ c ∈ B, c < D.nextComp) : A.image ρ = B.image ρ ↔ A = B := by
  rw [← Finset.coe_inj, Finset.coe_image, Finset.coe_image,
    h.mono.injOn.image_eq_image_iff (fun c hc => hA c hc) (fun c hc => hB c hc), Finset.coe_inj]

end Rel

section Center

variable {ρ : ℕ → ℕ} {D P : MonomialState} {S S_D : Finset (Finset ℕ)}

theorem lt_of_mem_center (hSD : S_D ⊆ D.nerve) {Q : Finset ℕ} (hQ : Q ∈ S_D) :
    ∀ c ∈ Q, c < D.nextComp :=
  fun _ hc => D.lt_nextComp_of_mem (hSD hQ) hc

theorem image_mem_center (hfilter : S.filter (· ∈ P.nerve) = S_D.image (Finset.image ρ))
    {Q : Finset ℕ} (hQ : Q ∈ S_D) : Q.image ρ ∈ S := by
  have : Q.image ρ ∈ S.filter (· ∈ P.nerve) := by
    rw [hfilter]; exact Finset.mem_image_of_mem _ hQ
  exact (Finset.mem_filter.mp this).1

/-- A face of `S` lying in `P`'s nerve is the image of a face of `S_D`. -/
theorem exists_of_mem_center (hfilter : S.filter (· ∈ P.nerve) = S_D.image (Finset.image ρ))
    {Q : Finset ℕ} (hQ : Q ∈ S) (hQP : Q ∈ P.nerve) : ∃ Q₀ ∈ S_D, Q₀.image ρ = Q := by
  have : Q ∈ S_D.image (Finset.image ρ) := by
    rw [← hfilter]; exact Finset.mem_filter.mpr ⟨hQ, hQP⟩
  exact Finset.mem_image.mp this

/-- A component below the new counter is old or the new component of a face of the centre. -/
theorem lt_or_exists_newComp (D : MonomialState) (S_D : Finset (Finset ℕ)) {c : ℕ}
    (hc : c < D.nextComp + S_D.card) : c < D.nextComp ∨ ∃ Q ∈ S_D, D.newComp S_D Q = c := by
  by_cases h : c < D.nextComp
  · exact Or.inl h
  · exact Or.inr (exists_newComp_eq D S_D (not_lt.mp h) hc)

end Center

namespace Rel

variable {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P)
include h

section Extend

variable {S S_D : Finset (Finset ℕ)} (hSD : S_D ⊆ D.nerve)
  (hfilter : S.filter (· ∈ P.nerve) = S_D.image (Finset.image ρ))
include hSD hfilter

theorem newComp_image_lt {Q₁ Q₂ : Finset ℕ} (hQ₁ : Q₁ ∈ S_D) (hQ₂ : Q₂ ∈ S_D)
    (hlt : D.newComp S_D Q₁ < D.newComp S_D Q₂) :
    P.newComp S (Q₁.image ρ) < P.newComp S (Q₂.image ρ) := by
  rw [newComp, newComp] at hlt ⊢
  refine Nat.add_lt_add_left (rank_lt_rank (image_mem_center hfilter hQ₁) ?_) _
  rw [h.faceList_image_lt_iff (lt_of_mem_center hSD hQ₁) (lt_of_mem_center hSD hQ₂)]
  exact (rank_lt_rank_iff hQ₁ hQ₂).mp (Nat.lt_of_add_lt_add_left hlt)

/-- No face of the centre `S` lies inside the image of a set of old components unless it is the
image of a face of `S_D` inside that set. -/
theorem not_subset_image (hS0 : ∀ Q ∈ S, Q.Nonempty) {T : Finset ℕ} (hT : T ∈ D.nerve)
    (hTS : ∀ Q₀ ∈ S_D, ¬ Q₀ ⊆ T) : ∀ Q ∈ S, ¬ Q ⊆ T.image ρ := fun Q hQ hQT => by
  have hQP : Q ∈ P.nerve := P.mem_nerve_of_subset (h.image_mem_nerve hT) hQT (hS0 Q hQ)
  obtain ⟨Q₀, hQ₀, rfl⟩ := exists_of_mem_center hfilter hQ hQP
  exact hTS Q₀ hQ₀ ((h.image_subset_image_iff (lt_of_mem_center hSD hQ₀)
    fun _ hc => D.lt_nextComp_of_mem hT hc).mp hQT)

theorem extendComp_strictMonoOn :
    StrictMonoOn (extendComp ρ D P S_D S) (Set.Iio (D.nextComp + S_D.card)) := by
  intro a ha b hb hab
  rcases lt_or_exists_newComp D S_D ha with ha' | ⟨Q₁, hQ₁, rfl⟩
  · rcases lt_or_exists_newComp D S_D hb with hb' | ⟨Q₂, hQ₂, rfl⟩
    · rw [extendComp_of_lt ρ D P S_D S ha', extendComp_of_lt ρ D P S_D S hb']
      exact h.mono ha' hb' hab
    · rw [extendComp_of_lt ρ D P S_D S ha', extendComp_newComp ρ D P S_D S hQ₂]
      exact (h.lt a ha').trans_le (P.nextComp_le_newComp S _)
  · rcases lt_or_exists_newComp D S_D hb with hb' | ⟨Q₂, hQ₂, rfl⟩
    · exact absurd (hab.trans hb') (not_lt.mpr (D.nextComp_le_newComp S_D Q₁))
    · rw [extendComp_newComp ρ D P S_D S hQ₁, extendComp_newComp ρ D P S_D S hQ₂]
      exact h.newComp_image_lt hSD hfilter hQ₁ hQ₂ hab

omit hSD in
theorem extendComp_lt : ∀ c, c < D.nextComp + S_D.card →
    extendComp ρ D P S_D S c < P.nextComp + S.card := fun c hc => by
  rcases lt_or_exists_newComp D S_D hc with hc' | ⟨Q, hQ, rfl⟩
  · rw [extendComp_of_lt ρ D P S_D S hc']
    exact (h.lt c hc').trans_le (Nat.le_add_right _ _)
  · rw [extendComp_newComp ρ D P S_D S hQ]
    exact P.newComp_lt (image_mem_center hfilter hQ)

theorem blowUp_a_extend : ∀ c, c < D.nextComp + S_D.card →
    (P.blowUp S).a (extendComp ρ D P S_D S c) = (D.blowUp S_D).a c := fun c hc => by
  rcases lt_or_exists_newComp D S_D hc with hc' | ⟨Q, hQ, rfl⟩
  · rw [extendComp_of_lt ρ D P S_D S hc', P.blowUp_a_of_lt S (h.lt c hc'), D.blowUp_a_of_lt S_D hc',
      h.a_eq c hc']
  · rw [extendComp_newComp ρ D P S_D S hQ, P.blowUp_a_newComp S (image_mem_center hfilter hQ),
      D.blowUp_a_newComp S_D hQ, h.total_image (lt_of_mem_center hSD hQ), h.m_eq]

omit hSD hfilter in
theorem blowUp_label_extend : ∀ c, c < D.nextComp + S_D.card →
    (P.blowUp S).label (extendComp ρ D P S_D S c) =
      extendLabel σ D P ((D.blowUp S_D).label c) := fun c hc => by
  rcases lt_or_exists_newComp D S_D hc with hc' | ⟨Q, hQ, rfl⟩
  · rw [extendComp_of_lt ρ D P S_D S hc', P.blowUp_label_of_lt S (h.lt c hc'),
      D.blowUp_label_of_lt S_D hc', h.label_eq c hc', extendLabel_of_lt σ D P (D.label_lt c hc')]
  · rw [extendComp_newComp ρ D P S_D S hQ, P.blowUp_label_newComp S, D.blowUp_label_newComp S_D,
      extendLabel_nextLabel]

omit hSD hfilter in
theorem extendLabel_strictMonoOn :
    StrictMonoOn (extendLabel σ D P) (Set.Iio (D.nextLabel + 1)) := by
  intro a ha b hb hab
  have hb' : b ≤ D.nextLabel := Nat.lt_succ_iff.mp hb
  have ha' : a < D.nextLabel := lt_of_lt_of_le hab hb'
  rw [extendLabel_of_lt σ D P ha']
  rcases hb'.lt_or_eq with hb'' | rfl
  · rw [extendLabel_of_lt σ D P hb'']
    exact h.σmono ha' hb'' hab
  · rw [extendLabel_nextLabel]
    exact h.σlt a ha'

omit hSD hfilter in
theorem extendLabel_lt : ∀ ℓ, ℓ < D.nextLabel + 1 → extendLabel σ D P ℓ < P.nextLabel + 1 :=
  fun ℓ hℓ => by
  rcases (Nat.lt_succ_iff.mp hℓ).lt_or_eq with hℓ' | rfl
  · rw [extendLabel_of_lt σ D P hℓ']
    exact (h.σlt ℓ hℓ').trans (Nat.lt_succ_self _)
  · rw [extendLabel_nextLabel]
    exact Nat.lt_succ_self _

/-- The nerve rule commutes with the renumbering. -/
theorem blowUp_nerve_extend (hS0 : ∀ Q ∈ S, Q.Nonempty) :
    (P.blowUp S).nerve = (D.blowUp S_D).nerve.image (Finset.image (extendComp ρ D P S_D S)) := by
  ext T'
  rw [Finset.mem_image, P.blowUp_nerve]
  constructor
  · intro hT'
    rcases mem_blowUpNerve.mp hT' with ⟨h1, h2⟩ | ⟨Q, hQ, T₁, h1, h2, h3, rfl⟩
    · obtain ⟨T, hT, rfl⟩ := h.exists_of_mem_nerve h1
      refine ⟨T, ?_, image_extendComp_of_lt ρ D P S_D S fun _ hc => D.lt_nextComp_of_mem hT hc⟩
      rw [D.blowUp_nerve]
      refine mem_blowUpNerve.mpr (Or.inl ⟨hT, fun Q₀ hQ₀ hQ₀T => ?_⟩)
      exact h2 (Q₀.image ρ) (image_mem_center hfilter hQ₀) (Finset.image_subset_image hQ₀T)
    · have hQP : Q ∈ P.nerve := P.mem_nerve_of_subset h2 Finset.subset_union_right (hS0 Q hQ)
      obtain ⟨Q₀, hQ₀, rfl⟩ := exists_of_mem_center hfilter hQ hQP
      obtain ⟨T₂, hT₂, hT₂e⟩ := h.exists_of_mem_nerve h2
      have hT₂c : ∀ c ∈ T₂, c < D.nextComp := fun _ hc => D.lt_nextComp_of_mem hT₂ hc
      have hT₁₀c : ∀ c ∈ T₂.filter (fun c => ρ c ∈ T₁), c < D.nextComp := fun c hc =>
        hT₂c c (Finset.mem_filter.mp hc).1
      have hT₁e : (T₂.filter fun c => ρ c ∈ T₁).image ρ = T₁ := by
        ext x
        constructor
        · intro hx
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_filter.mp hc).2
        · intro hx
          have : x ∈ T₂.image ρ := hT₂e ▸ Finset.mem_union_left _ hx
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp this
          exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hc, hx⟩)
      have hQ₀T₂ : Q₀ ⊆ T₂ := (h.image_subset_image_iff (lt_of_mem_center hSD hQ₀) hT₂c).mp
        (hT₂e ▸ Finset.subset_union_right)
      have hQ₀ne : Q₀.Nonempty := Finset.image_nonempty.mp (hS0 _ hQ)
      have hunion : T₂.filter (fun c => ρ c ∈ T₁) ∪ Q₀ ∈ D.nerve :=
        D.mem_nerve_of_subset hT₂ (Finset.union_subset (Finset.filter_subset _ _) hQ₀T₂)
          (hQ₀ne.mono Finset.subset_union_right)
      refine ⟨insert (D.newComp S_D Q₀) (T₂.filter fun c => ρ c ∈ T₁), ?_, ?_⟩
      · rw [D.blowUp_nerve]
        refine mem_blowUpNerve.mpr (Or.inr ⟨Q₀, hQ₀, _, ?_, hunion, fun Q' hQ' hQ'T => ?_, rfl⟩)
        · by_cases he : T₂.filter (fun c => ρ c ∈ T₁) = ∅
          · exact Or.inl he
          · exact Or.inr (D.mem_nerve_of_subset hT₂ (Finset.filter_subset _ _)
              (Finset.nonempty_iff_ne_empty.mpr he))
        · exact h3 (Q'.image ρ) (image_mem_center hfilter hQ')
            (hT₁e ▸ Finset.image_subset_image hQ'T)
      · rw [Finset.image_insert, extendComp_newComp ρ D P S_D S hQ₀,
          image_extendComp_of_lt ρ D P S_D S hT₁₀c, hT₁e]
  · rintro ⟨T, hT, rfl⟩
    rw [D.blowUp_nerve] at hT
    rcases mem_blowUpNerve.mp hT with ⟨h1, h2⟩ | ⟨Q₀, hQ₀, T₁₀, h1, h2, h3, rfl⟩
    · rw [image_extendComp_of_lt ρ D P S_D S fun _ hc => D.lt_nextComp_of_mem h1 hc]
      exact mem_blowUpNerve.mpr (Or.inl ⟨h.image_mem_nerve h1,
        h.not_subset_image hSD hfilter hS0 h1 h2⟩)
    · have hT₁₀c : ∀ c ∈ T₁₀, c < D.nextComp := fun _ hc =>
        D.lt_nextComp_of_mem h2 (Finset.mem_union_left _ hc)
      rw [Finset.image_insert, extendComp_newComp ρ D P S_D S hQ₀,
        image_extendComp_of_lt ρ D P S_D S hT₁₀c]
      refine mem_blowUpNerve.mpr (Or.inr ⟨Q₀.image ρ, image_mem_center hfilter hQ₀, T₁₀.image ρ,
        ?_, ?_, fun Q hQ hQT => ?_, rfl⟩)
      · rcases h1 with h1 | h1
        · exact Or.inl (by rw [h1, Finset.image_empty])
        · exact Or.inr (h.image_mem_nerve h1)
      · rw [← Finset.image_union]
        exact h.image_mem_nerve h2
      · have hQP : Q ∈ P.nerve := P.mem_nerve_of_subset (h.image_mem_nerve h2)
          (hQT.trans (Finset.image_subset_image Finset.subset_union_left)) (hS0 Q hQ)
        obtain ⟨Q', hQ', rfl⟩ := exists_of_mem_center hfilter hQ hQP
        exact h3 Q' hQ' ((h.image_subset_image_iff (lt_of_mem_center hSD hQ') hT₁₀c).mp hQT)

/-- The renumbering extends across a blow-up: `D` along its centre `S_D`, `P` along the centre
`S` whose faces in `P` are the images of those of `S_D`. -/
theorem blowUp (hS0 : ∀ Q ∈ S, Q.Nonempty) :
    Rel (extendComp ρ D P S_D S) (extendLabel σ D P) (D.blowUp S_D) (P.blowUp S) where
  n_eq := by rw [blowUp_n, blowUp_n, h.n_eq]
  m_eq := by rw [blowUp_m, blowUp_m, h.m_eq]
  mono := by rw [blowUp_nextComp]; exact h.extendComp_strictMonoOn hSD hfilter
  lt := by rw [blowUp_nextComp, blowUp_nextComp]; exact h.extendComp_lt hfilter
  a_eq := by rw [blowUp_nextComp]; exact h.blowUp_a_extend hSD hfilter
  label_eq := by rw [blowUp_nextComp]; exact h.blowUp_label_extend
  σmono := by rw [blowUp_nextLabel]; exact h.extendLabel_strictMonoOn
  σlt := by rw [blowUp_nextLabel, blowUp_nextLabel]; exact h.extendLabel_lt
  nerve_eq := h.blowUp_nerve_extend hSD hfilter hS0

end Extend

end Rel

end Hironaka.Monomial.MonomialState
