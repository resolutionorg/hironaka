/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Restrict
public import Hironaka.Resolution.Algebraic.Monomial.Restrict.Rename
public import Hironaka.Resolution.Algebraic.Monomial.Step3Phases
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Extend
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Invariant

/-!
# Functoriality under restriction: the induction along the run

Kollár's Step 3 on the monomial state commutes with restriction to a subnerve: for `Sub L N`
(`Hironaka/Resolution/Algebraic/Monomial/Restrict.lean`) the run on `L` is the run on `N` pulled
back, with the empty blow-ups deleted and the components and labels reindexed by order embeddings
(`step3_restrict`). This is the second clause of [Kol07, 34.1] for the combinatorial procedure;
the proof is not in the sources.

Three states are carried along the run on `N`: the direct state `D` (the run on the subnerve
`L`), the pulled-back state `P` (the centres of `N` applied to `L`, dead components and unused
labels included) and `N` itself, with `Rel ρ σ D P` (`P` is `D` renumbered,
`Hironaka/Resolution/Algebraic/Monomial/Restrict/Rename.lean`) and `Sub P N`
(`Hironaka/Resolution/Algebraic/Monomial/Restrict/Invariant.lean`). Along phase `r` of `N`
(`phase_restrict`, by the functional induction principle of `phase`): a centre of `N` disjoint from
`P`'s nerve does not change `P`'s nerve or `D` (`Rel.of_blowUp_disjoint`); a centre meeting it
restricts to Kollár's centre of `P` (`Sub.choice_eq_of_mem`), which is the image of Kollár's centre
of `D` (`Rel.choice_eq`), and the three states advance together with the renumbering extended
(`Rel.blowUp` of `Hironaka/Resolution/Algebraic/Monomial/Restrict/Extend.lean`); when `N`'s phase
ends, `D`'s has ended too. The phases compose (`phases_restrict`), and `step3_restrict` reads the
result off with the renumberings packaged as order embeddings (`exists_orderEmbedding_extend`).

Together with `step3_refine` of `Hironaka/Resolution/Algebraic/Monomial/Restrict/RefinePhase.lean`
this gives the functoriality of the geometric Step 3 under smooth morphisms
(`Hironaka/Resolution/Algebraic/Monomial/Geometric/ChainRunErase.lean`).
-/

public section

namespace Hironaka.Monomial.MonomialState

open Finset

/-! ### The pulled-back run, unfolded -/

theorem restrictRun_nil (st : MonomialState) : restrictRun st [] = [] := rfl

theorem restrictRun_cons_of_eq_empty (st : MonomialState) {S : Finset (Finset ℕ)}
    (Ns : List (Finset (Finset ℕ))) (h : S.filter (· ∈ st.nerve) = ∅) :
    restrictRun st (S :: Ns) = restrictRun (st.blowUp S) Ns := by
  simp [restrictRun, h]

theorem restrictRun_cons_of_ne_empty (st : MonomialState) {S : Finset (Finset ℕ)}
    (Ns : List (Finset (Finset ℕ))) (h : S.filter (· ∈ st.nerve) ≠ ∅) :
    restrictRun st (S :: Ns) = S.filter (· ∈ st.nerve) :: restrictRun (st.blowUp S) Ns := by
  simp [restrictRun, h]

theorem restrictRun_append (st : MonomialState) (L₁ L₂ : List (Finset (Finset ℕ))) :
    restrictRun st (L₁ ++ L₂) = restrictRun st L₁ ++ restrictRun (L₁.foldl blowUp st) L₂ := by
  induction L₁ generalizing st with
  | nil => rfl
  | cons S L₁ ih =>
    rw [List.cons_append, List.foldl_cons]
    by_cases h : S.filter (· ∈ st.nerve) = ∅
    · rw [restrictRun_cons_of_eq_empty st _ h, restrictRun_cons_of_eq_empty st _ h, ih]
    · rw [restrictRun_cons_of_ne_empty st _ h, restrictRun_cons_of_ne_empty st _ h, ih,
        List.cons_append]

/-! ### Counters and centers along a phase -/

theorem nextComp_le_blowUp (st : MonomialState) (S : Finset (Finset ℕ)) :
    st.nextComp ≤ (st.blowUp S).nextComp :=
  Nat.le_add_right _ _

theorem nextLabel_le_blowUp (st : MonomialState) (S : Finset (Finset ℕ)) :
    st.nextLabel ≤ (st.blowUp S).nextLabel :=
  Nat.le_succ _

variable {r : ℕ}

theorem phase_nextComp_le (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    st.nextComp ≤ (phase r st hs).1.nextComp := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih =>
    rw [phase_of_nonempty st hs h]
    exact (nextComp_le_blowUp st _).trans ih
  | case2 st hs h => rw [phase_of_not_nonempty st hs h]

theorem phase_nextLabel_le (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    st.nextLabel ≤ (phase r st hs).1.nextLabel := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih =>
    rw [phase_of_nonempty st hs h]
    exact (nextLabel_le_blowUp st _).trans ih
  | case2 st hs h => rw [phase_of_not_nonempty st hs h]

/-- Every component of a centre of a phase lies below the final counter. -/
theorem phase_centers_lt (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    ∀ S ∈ (phase r st hs).2, ∀ Q ∈ S, ∀ c ∈ Q, c < (phase r st hs).1.nextComp := by
  induction st, hs using phase.induct r with
  | case1 st hs h ih =>
    rw [phase_of_nonempty st hs h]
    intro S hS Q hQ c hc
    rcases List.mem_cons.mp hS with rfl | hS
    · exact (st.lt_nextComp_of_mem (st.mem_nerve_of_mem_choice hQ) hc).trans_le
        ((nextComp_le_blowUp st _).trans (phase_nextComp_le _ _))
    · exact ih S hS Q hQ c hc
  | case2 st hs h =>
    rw [phase_of_not_nonempty st hs h]
    intro S hS
    exact absurd hS (List.not_mem_nil)

/-! ### A center disjoint from the subnerve -/

theorem Sub.star_of_star {L N : MonomialState} (h : Sub L N) {s : ℕ} (hs : N.Star s) : L.Star s :=
  fun T hT => by
  rw [h.total_eq, h.m_eq]
  exact hs T (h.mem_faces hT)

theorem Sub.choice_eq_empty_of {L N : MonomialState} (h : Sub L N) {r : ℕ}
    (hN : N.choice r = ∅) : L.choice r = ∅ :=
  L.choice_eq_empty_iff.mpr (h.star_of_star (N.choice_eq_empty_iff.mp hN))

/-- A blow-up of `P` along nonempty faces none of which is a face of `P` keeps `Rel`: the nerve
is unchanged and the old components keep their exponents and labels. -/
theorem Rel.of_blowUp_disjoint {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P)
    {S : Finset (Finset ℕ)} (hS0 : ∀ Q ∈ S, Q.Nonempty) (hdis : ∀ Q ∈ S, Q ∉ P.nerve) :
    Rel ρ σ D (P.blowUp S) where
  n_eq := h.n_eq
  m_eq := h.m_eq
  mono := h.mono
  lt c hc := (h.lt c hc).trans_le (nextComp_le_blowUp P S)
  a_eq c hc := by rw [P.blowUp_a_of_lt S (h.lt c hc), h.a_eq c hc]
  label_eq c hc := by rw [P.blowUp_label_of_lt S (h.lt c hc), h.label_eq c hc]
  σmono := h.σmono
  σlt ℓ hℓ := (h.σlt ℓ hℓ).trans_le (nextLabel_le_blowUp P S)
  nerve_eq := by rw [blowUp_nerve_of_forall_notMem P hS0 hdis, h.nerve_eq]

/-! ### The induction along a phase -/

/-- The image of a family of faces under a renumbering that agrees with `ρ` on the components
involved. -/
theorem image_image_congr {ρ ρ' : ℕ → ℕ} {K : ℕ} (hρ : ∀ c, c < K → ρ' c = ρ c)
    {S : Finset (Finset ℕ)} (hS : ∀ Q ∈ S, ∀ c ∈ Q, c < K) :
    S.image (Finset.image ρ') = S.image (Finset.image ρ) :=
  Finset.image_congr fun Q hQ => Finset.image_congr fun c hc => hρ c (hS Q hQ c hc)

/-- Phase `r` of the run on `N`, with the direct state `D` and the pulled-back state `P` carried
along: the renumbering extends, `Rel` and `Sub` persist, and the centres of `D`'s phase are the
nonempty restrictions of the centres of `N`'s phase. -/
theorem phase_restrict (r : ℕ) : ∀ (N : MonomialState) (hsN : ∀ s < r, N.Star s)
    (D P : MonomialState) (ρ σ : ℕ → ℕ), Rel ρ σ D P → Sub P N →
    ∀ hsD : ∀ s < r, D.Star s,
    ∃ ρ' σ' : ℕ → ℕ, (∀ c, c < D.nextComp → ρ' c = ρ c) ∧ (∀ ℓ, ℓ < D.nextLabel → σ' ℓ = σ ℓ) ∧
      Rel ρ' σ' (phase r D hsD).1 ((phase r N hsN).2.foldl blowUp P) ∧
      Sub ((phase r N hsN).2.foldl blowUp P) (phase r N hsN).1 ∧
      (phase r D hsD).2.map (fun S => S.image (Finset.image ρ')) =
        restrictRun P (phase r N hsN).2 := by
  intro N hsN
  induction N, hsN using phase.induct r with
  | case1 N hsN hne ih =>
    intro D P ρ σ hrel hsub hsD
    rw [phase_of_nonempty N hsN hne]
    simp only [List.foldl_cons]
    have hS0 : ∀ Q ∈ N.choice r, Q.Nonempty := fun Q hQ =>
      N.nerve_nonempty Q (N.mem_nerve_of_mem_choice hQ)
    have hsub' : Sub (P.blowUp (N.choice r)) (N.blowUp (N.choice r)) := hsub.blowUp _
    by_cases hdis : (N.choice r).filter (· ∈ P.nerve) = ∅
    · have hdis' : ∀ Q ∈ N.choice r, Q ∉ P.nerve := fun Q hQ hQP =>
        Finset.notMem_empty Q (hdis ▸ Finset.mem_filter.mpr ⟨hQ, hQP⟩)
      obtain ⟨ρ', σ', hρ', hσ', hrel', hsub'', hmap⟩ :=
        ih D (P.blowUp (N.choice r)) ρ σ (hrel.of_blowUp_disjoint hS0 hdis') hsub' hsD
      refine ⟨ρ', σ', hρ', hσ', hrel', hsub'', ?_⟩
      rw [hmap, restrictRun_cons_of_eq_empty P _ hdis]
    · obtain ⟨Q, hQ⟩ := Finset.nonempty_iff_ne_empty.mpr hdis
      obtain ⟨hQN, hQP⟩ := Finset.mem_filter.mp hQ
      have hPc : P.choice r = (N.choice r).filter (· ∈ P.nerve) := hsub.choice_eq_of_mem hQN hQP
      have hfilter : (N.choice r).filter (· ∈ P.nerve) = (D.choice r).image (Finset.image ρ) := by
        rw [← hPc, hrel.choice_eq]
      have hDne : (D.choice r).Nonempty := by
        rw [← Finset.image_nonempty (f := Finset.image ρ), ← hfilter]
        exact ⟨Q, hQ⟩
      have hSD : D.choice r ⊆ D.nerve := (D.isCenter_choice r).1
      rw [phase_of_nonempty D hsD hDne]
      simp only [List.map_cons]
      obtain ⟨ρ', σ', hρ', hσ', hrel', hsub'', hmap⟩ :=
        ih (D.blowUp (D.choice r)) (P.blowUp (N.choice r)) _ _
          (hrel.blowUp hSD hfilter hS0) hsub' (fun _ hsr => D.star_blowUp hsD hsr)
      refine ⟨ρ', σ', fun c hc => ?_, fun ℓ hℓ => ?_, hrel', hsub'', ?_⟩
      · rw [hρ' c (hc.trans_le (nextComp_le_blowUp D _)), extendComp_of_lt ρ D P _ _ hc]
      · rw [hσ' ℓ (hℓ.trans_le (nextLabel_le_blowUp D _)), extendLabel_of_lt σ D P hℓ]
      · rw [hmap, restrictRun_cons_of_ne_empty P _ hdis, hfilter]
        congr 1
        have hlt : ∀ Q ∈ D.choice r, ∀ c ∈ Q, c < D.nextComp := fun Q hQ c hc =>
          D.lt_nextComp_of_mem (hSD hQ) hc
        rw [image_image_congr hρ'
          (fun Q hQ c hc => (hlt Q hQ c hc).trans_le (nextComp_le_blowUp D _)),
          image_image_congr (fun c hc => extendComp_of_lt ρ D P _ _ hc) hlt]
  | case2 N hsN hne =>
    intro D P ρ σ hrel hsub hsD
    rw [phase_of_not_nonempty N hsN hne]
    have hD : D.choice r = ∅ := (hrel.choice_eq_empty_iff r).mp
      (hsub.choice_eq_empty_of (Finset.not_nonempty_iff_eq_empty.mp hne))
    rw [phase_of_not_nonempty D hsD (Finset.not_nonempty_iff_eq_empty.mpr hD)]
    exact ⟨ρ, σ, fun _ _ => rfl, fun _ _ => rfl, hrel, hsub, rfl⟩

/-! ### The phases and Step 3 -/

theorem phases_restrict (k : ℕ) : ∀ (r : ℕ) (N : MonomialState) (hsN : ∀ s < r, N.Star s)
    (D P : MonomialState) (ρ σ : ℕ → ℕ), Rel ρ σ D P → Sub P N → ∀ hsD : ∀ s < r, D.Star s,
    ∃ ρ' σ' : ℕ → ℕ, (∀ c, c < D.nextComp → ρ' c = ρ c) ∧ (∀ ℓ, ℓ < D.nextLabel → σ' ℓ = σ ℓ) ∧
      Rel ρ' σ' (phases k r D hsD).1 ((phases k r N hsN).2.foldl blowUp P) ∧
      Sub ((phases k r N hsN).2.foldl blowUp P) (phases k r N hsN).1 ∧
      (phases k r D hsD).2.map (fun S => S.image (Finset.image ρ')) =
        restrictRun P (phases k r N hsN).2 := by
  induction k with
  | zero =>
    intro r N hsN D P ρ σ hrel hsub hsD
    exact ⟨ρ, σ, fun _ _ => rfl, fun _ _ => rfl, hrel, hsub, rfl⟩
  | succ k ih =>
    intro r N hsN D P ρ σ hrel hsub hsD
    rw [phases_succ, phases_succ]
    simp only [List.foldl_append, List.map_append]
    obtain ⟨ρ₁, σ₁, hρ₁, hσ₁, hrel₁, hsub₁, hmap₁⟩ :=
      phase_restrict r N hsN D P ρ σ hrel hsub hsD
    obtain ⟨ρ', σ', hρ', hσ', hrel', hsub', hmap'⟩ := ih (r + 1) _ (phase_star_succ N hsN) _ _
      ρ₁ σ₁ hrel₁ hsub₁ (phase_star_succ D hsD)
    refine ⟨ρ', σ', fun c hc => ?_, fun ℓ hℓ => ?_, hrel', hsub', ?_⟩
    · rw [hρ' c (hc.trans_le (phase_nextComp_le D hsD)), hρ₁ c hc]
    · rw [hσ' ℓ (hℓ.trans_le (phase_nextLabel_le D hsD)), hσ₁ ℓ hℓ]
    · rw [restrictRun_append, ← hmap', ← hmap₁]
      congr 1
      exact List.map_congr_left fun S hS => image_image_congr hρ' (phase_centers_lt D hsD S hS)

theorem IsRun.nextComp_le {st st' : MonomialState} {L : List (Finset (Finset ℕ))}
    (h : IsRun st L st') : st.nextComp ≤ st'.nextComp := by
  induction h with
  | nil => exact le_rfl
  | cons r _ _ _ _ ih => exact (nextComp_le_blowUp _ _).trans ih

theorem IsRun.nextLabel_le {st st' : MonomialState} {L : List (Finset (Finset ℕ))}
    (h : IsRun st L st') : st.nextLabel ≤ st'.nextLabel := by
  induction h with
  | nil => exact le_rfl
  | cons r _ _ _ _ ih => exact (nextLabel_le_blowUp _ _).trans ih

/-- Every component of a centre of a run lies below the final counter. -/
theorem IsRun.centers_lt {st st' : MonomialState} {L : List (Finset (Finset ℕ))}
    (h : IsRun st L st') : ∀ S ∈ L, ∀ Q ∈ S, ∀ c ∈ Q, c < st'.nextComp := by
  induction h with
  | nil => intro S hS; exact absurd hS List.not_mem_nil
  | cons r _ _ _ hL ih =>
    intro S hS Q hQ c hc
    rcases List.mem_cons.mp hS with rfl | hS
    · exact (lt_nextComp_of_mem _ (mem_nerve_of_mem_choice _ hQ) hc).trans_le
        ((nextComp_le_blowUp _ _).trans hL.nextComp_le)
    · exact ih S hS Q hQ c hc

/-- A map strictly monotone below `K` extends to an order embedding of `ℕ`. -/
theorem exists_orderEmbedding_extend (f : ℕ → ℕ) (K : ℕ) (hf : StrictMonoOn f (Set.Iio K)) :
    ∃ g : ℕ ↪o ℕ, ∀ c, c < K → g c = f c := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact ⟨OrderEmbedding.ofStrictMono id strictMono_id, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
  · have hg : StrictMono fun c => if c < K then f c else f (K - 1) + 1 + (c - K) := by
      intro a b hab
      dsimp only
      split_ifs with ha hb hb
      · exact hf ha hb hab
      · have h1 : f a ≤ f (K - 1) :=
          (hf.le_iff_le ha (Nat.sub_lt hK Nat.one_pos)).mpr (by omega)
        omega
      · omega
      · omega
    exact ⟨OrderEmbedding.ofStrictMono _ hg, fun c hc => by
      rw [OrderEmbedding.coe_ofStrictMono]; exact ite_eq_left hc⟩

theorem step3_restrict_aux {L N : MonomialState} (h : Sub L N) :
    ∃ ρ' σ' : ℕ → ℕ, (∀ c, c < L.nextComp → ρ' c = c) ∧ (∀ ℓ, ℓ < L.nextLabel → σ' ℓ = ℓ) ∧
      Rel ρ' σ' (step3 L).1 ((step3 N).2.foldl blowUp L) ∧
      (step3 L).2.map (fun S => S.image (Finset.image ρ')) = restrictRun L (step3 N).2 := by
  have e : step3 L = phases N.n 1 L (star_of_lt_one L) := by rw [step3, h.n_eq]
  rw [e, step3]
  obtain ⟨ρ', σ', hρ', hσ', hrel, -, hmap⟩ :=
    phases_restrict N.n 1 N (star_of_lt_one N) L L id id (Rel.refl L) h (star_of_lt_one L)
  exact ⟨ρ', σ', hρ', hσ', hrel, hmap⟩

/-- Functoriality of Step 3 under restriction to a down-closed subnerve, the second clause of
[Kol07, 34.1] on the state: for `Sub L N` there are order embeddings `ρ` of components and `σ`
of labels, the identity on those of `L`, such that the pulled-back run on `L` is the direct run
on `L` renumbered by `ρ` and `σ`, with the same nerve up to `ρ`, and the centres of the direct
run, renumbered, are the pulled-back centres with the empty ones deleted. -/
theorem step3_restrict {L N : MonomialState} (h : Sub L N) :
    ∃ ρ : ℕ ↪o ℕ, (∀ c, c < L.nextComp → ρ c = c) ∧
      ∃ σ : ℕ ↪o ℕ, (∀ ℓ, ℓ < L.nextLabel → σ ℓ = ℓ) ∧
        (∀ c, c < (step3 L).1.nextComp →
          ((step3 N).2.foldl blowUp L).a (ρ c) = (step3 L).1.a c ∧
          ((step3 N).2.foldl blowUp L).label (ρ c) = σ ((step3 L).1.label c)) ∧
        ((step3 N).2.foldl blowUp L).nerve = (step3 L).1.nerve.image (Finset.image ρ) ∧
        (step3 L).2.map (fun S : Finset (Finset ℕ) => S.image (Finset.image ρ)) =
          restrictRun L (step3 N).2 := by
  obtain ⟨ρ', σ', hρ', hσ', hrel, hmap⟩ := step3_restrict_aux h
  obtain ⟨ρ, hρ⟩ := exists_orderEmbedding_extend ρ' (step3 L).1.nextComp hrel.mono
  obtain ⟨σ, hσ⟩ := exists_orderEmbedding_extend σ' (step3 L).1.nextLabel hrel.σmono
  have hLD : L.nextComp ≤ (step3 L).1.nextComp := (step3_isRun L).nextComp_le
  have hLD' : L.nextLabel ≤ (step3 L).1.nextLabel := (step3_isRun L).nextLabel_le
  refine ⟨ρ, fun c hc => by rw [hρ c (hc.trans_le hLD), hρ' c hc], σ,
    fun ℓ hℓ => by rw [hσ ℓ (hℓ.trans_le hLD'), hσ' ℓ hℓ], fun c hc => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hρ c hc]; exact hrel.a_eq c hc
  · rw [hρ c hc, hσ _ ((step3 L).1.label_lt c hc)]; exact hrel.label_eq c hc
  · rw [hrel.nerve_eq]
    exact (image_image_congr hρ fun Q hQ c hc => (step3 L).1.lt_nextComp_of_mem hQ hc).symm
  · rw [← hmap]
    exact List.map_congr_left fun S hS => image_image_congr hρ ((step3_isRun L).centers_lt S hS)

end Hironaka.Monomial.MonomialState
