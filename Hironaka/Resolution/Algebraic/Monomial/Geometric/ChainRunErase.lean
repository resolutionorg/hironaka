/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Restrict
public import Hironaka.Resolution.Algebraic.Monomial.Restrict.Extend
public import Hironaka.Resolution.Algebraic.Monomial.Step3Phases
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Invariant
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Phase
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Refine
import Hironaka.Resolution.Algebraic.Monomial.Restrict.RefinePhase

/-!
# The run of a partially refining state as an explicit chain with skips

The second clause of [Kol07, 34.1] compares the run of Step 3 on `Y` with the run on `X` when
`h : Y ⟶ X` is not surjective: a centre of `X` none of whose faces has a face of `Y` over it is an
empty blow-up of `Y` and is skipped. The combinatorial modules describe this in two steps:
`step3_restrict` of `Hironaka/Resolution/Algebraic/Monomial/Restrict/Phase.lean` (the run on the
restricted state `D` is the run on `X` with the empty steps deleted and the surviving centres
filtered, up to a renumbering `Rel ρ' σ' D P` against a state `P` that is `Sub` the state of `X`
with the same counters) and `step3_refine` of
`Hironaka/Resolution/Algebraic/Monomial/Restrict/RefinePhase.lean` (the run on `Y` is the
`ρ`-preimage run of the run on `D`). The geometric fold of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackErase.lean` needs the composite parent map
`Y → X` explicitly at every stage, so this module re-runs both lockstep inductions at once, with the
explicit chain:

* `chainRunE ρ Y N Ns`: the run on `Y` induced by the run `Ns` on `N` along `ρ`, with the empty
  steps skipped; `chainMapE`, `chainStateYE` the parent map and the state of `Y` after the chain;
* `IsChainE ρ Y N Ns`: the run `Ns` on `N` is a chain run for `(ρ, Y)`, every step being a skip
  (no face of `Y` over the centre) or a blow-up of `Y` along the faces over the centre, a centre
  of `Y`;
* `phase_chainE`, `phases_chainE`, `step3_chainE`: *the run of Step 3 on `Y` is the chain run
  with skips of the run of Step 3 on `N`*, given `Refines ρ_Y Y D`, `Rel ρ' σ' D P`, `Sub P N`
  with `ρ = ρ' ∘ ρ_Y` on the components of `Y`.

The proofs are `phase_restrict` and `phase_chain`
(`Hironaka/Resolution/Algebraic/Monomial/Geometric/ChainRun.lean`) run side by side. Not in the
sources; bookkeeping for the deletion of empty blow-ups of [Kol07, 32] and [Kol07, 34.1].
-/

@[expose] public section

namespace Hironaka.Monomial.MonomialState

open Finset

/-! ### The chain run with skips -/

/-- The run on `Y` induced by a run on `N` along the parent map `ρ`, with the empty steps
deleted: a centre `S` of `N` with no face of `Y` over it is skipped (`Y` unchanged, `N` blown up);
otherwise the faces of `Y` over `S` are blown up and the parent map extended by `extendComp`. -/
def chainRunE (ρ : ℕ → ℕ) : MonomialState → MonomialState → List (Finset (Finset ℕ)) →
    List (Finset (Finset ℕ))
  | _, _, [] => []
  | Y, N, S :: Ns =>
    if (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅ then chainRunE ρ Y (N.blowUp S) Ns
    else (Y.nerve.filter fun Q => Q.image ρ ∈ S) ::
      chainRunE (extendComp ρ Y N (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
        (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (N.blowUp S) Ns

/-- The parent map after the chain with skips. -/
def chainMapE (ρ : ℕ → ℕ) : MonomialState → MonomialState → List (Finset (Finset ℕ)) → (ℕ → ℕ)
  | _, _, [] => ρ
  | Y, N, S :: Ns =>
    if (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅ then chainMapE ρ Y (N.blowUp S) Ns
    else chainMapE (extendComp ρ Y N (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
      (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (N.blowUp S) Ns

/-- The state of `Y` after the chain with skips. -/
def chainStateYE (ρ : ℕ → ℕ) : MonomialState → MonomialState → List (Finset (Finset ℕ)) →
    MonomialState
  | Y, _, [] => Y
  | Y, N, S :: Ns =>
    if (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅ then chainStateYE ρ Y (N.blowUp S) Ns
    else chainStateYE (extendComp ρ Y N (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
      (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (N.blowUp S) Ns

variable (ρ : ℕ → ℕ) (Y N : MonomialState) {S : Finset (Finset ℕ)} (Ns : List (Finset (Finset ℕ)))

theorem chainRunE_nil : chainRunE ρ Y N [] = [] := rfl

theorem chainRunE_cons_of_eq_empty (h : (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅) :
    chainRunE ρ Y N (S :: Ns) = chainRunE ρ Y (N.blowUp S) Ns := by
  rw [chainRunE, ite_eq_left h]

theorem chainRunE_cons_of_ne_empty (h : (Y.nerve.filter fun Q => Q.image ρ ∈ S) ≠ ∅) :
    chainRunE ρ Y N (S :: Ns) = (Y.nerve.filter fun Q => Q.image ρ ∈ S) ::
      chainRunE (extendComp ρ Y N (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
        (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (N.blowUp S) Ns := by
  rw [chainRunE, ite_eq_right h]

theorem chainMapE_nil : chainMapE ρ Y N [] = ρ := rfl

theorem chainMapE_cons_of_eq_empty (h : (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅) :
    chainMapE ρ Y N (S :: Ns) = chainMapE ρ Y (N.blowUp S) Ns := by
  rw [chainMapE, ite_eq_left h]

theorem chainMapE_cons_of_ne_empty (h : (Y.nerve.filter fun Q => Q.image ρ ∈ S) ≠ ∅) :
    chainMapE ρ Y N (S :: Ns) =
      chainMapE (extendComp ρ Y N (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
        (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (N.blowUp S) Ns := by
  rw [chainMapE, ite_eq_right h]

theorem chainStateYE_nil : chainStateYE ρ Y N [] = Y := rfl

theorem chainStateYE_cons_of_eq_empty (h : (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅) :
    chainStateYE ρ Y N (S :: Ns) = chainStateYE ρ Y (N.blowUp S) Ns := by
  rw [chainStateYE, ite_eq_left h]

theorem chainStateYE_cons_of_ne_empty (h : (Y.nerve.filter fun Q => Q.image ρ ∈ S) ≠ ∅) :
    chainStateYE ρ Y N (S :: Ns) =
      chainStateYE (extendComp ρ Y N (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
        (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (N.blowUp S) Ns := by
  rw [chainStateYE, ite_eq_right h]

/-- The chain with skips along a concatenation. -/
theorem chainRunE_append (ρ : ℕ → ℕ) : ∀ (Y N : MonomialState) (N₁ N₂ : List (Finset (Finset ℕ))),
    chainRunE ρ Y N (N₁ ++ N₂) =
      chainRunE ρ Y N N₁ ++
        chainRunE (chainMapE ρ Y N N₁) (chainStateYE ρ Y N N₁) (N₁.foldl blowUp N) N₂
  | _, _, [], _ => rfl
  | Y, N, S :: N₁, N₂ => by
    rw [List.cons_append, List.foldl_cons]
    by_cases h : (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅
    · rw [chainRunE_cons_of_eq_empty _ _ _ _ h, chainRunE_cons_of_eq_empty _ _ _ _ h,
        chainMapE_cons_of_eq_empty _ _ _ _ h, chainStateYE_cons_of_eq_empty _ _ _ _ h]
      exact chainRunE_append ρ Y (N.blowUp S) N₁ N₂
    · rw [chainRunE_cons_of_ne_empty _ _ _ _ h, chainRunE_cons_of_ne_empty _ _ _ _ h,
        chainMapE_cons_of_ne_empty _ _ _ _ h, chainStateYE_cons_of_ne_empty _ _ _ _ h,
        List.cons_append]
      exact congrArg _ (chainRunE_append _ _ _ N₁ N₂)

theorem chainMapE_append (ρ : ℕ → ℕ) : ∀ (Y N : MonomialState) (N₁ N₂ : List (Finset (Finset ℕ))),
    chainMapE ρ Y N (N₁ ++ N₂) =
      chainMapE (chainMapE ρ Y N N₁) (chainStateYE ρ Y N N₁) (N₁.foldl blowUp N) N₂
  | _, _, [], _ => rfl
  | Y, N, S :: N₁, N₂ => by
    rw [List.cons_append, List.foldl_cons]
    by_cases h : (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅
    · rw [chainMapE_cons_of_eq_empty _ _ _ _ h, chainMapE_cons_of_eq_empty _ _ _ _ h,
        chainStateYE_cons_of_eq_empty _ _ _ _ h]
      exact chainMapE_append ρ Y (N.blowUp S) N₁ N₂
    · rw [chainMapE_cons_of_ne_empty _ _ _ _ h, chainMapE_cons_of_ne_empty _ _ _ _ h,
        chainStateYE_cons_of_ne_empty _ _ _ _ h]
      exact chainMapE_append _ _ _ N₁ N₂

theorem chainStateYE_append (ρ : ℕ → ℕ) :
    ∀ (Y N : MonomialState) (N₁ N₂ : List (Finset (Finset ℕ))),
    chainStateYE ρ Y N (N₁ ++ N₂) =
      chainStateYE (chainMapE ρ Y N N₁) (chainStateYE ρ Y N N₁) (N₁.foldl blowUp N) N₂
  | _, _, [], _ => rfl
  | Y, N, S :: N₁, N₂ => by
    rw [List.cons_append, List.foldl_cons]
    by_cases h : (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅
    · rw [chainStateYE_cons_of_eq_empty _ _ _ _ h, chainStateYE_cons_of_eq_empty _ _ _ _ h,
        chainMapE_cons_of_eq_empty _ _ _ _ h]
      exact chainStateYE_append ρ Y (N.blowUp S) N₁ N₂
    · rw [chainStateYE_cons_of_ne_empty _ _ _ _ h, chainStateYE_cons_of_ne_empty _ _ _ _ h,
        chainMapE_cons_of_ne_empty _ _ _ _ h]
      exact chainStateYE_append _ _ _ N₁ N₂

/-! ### The chain predicate -/

/-- *The run `Ns` on `N` is a chain run with skips for `(ρ, Y)`*: every step is a skip (no face of
`Y` over the centre, `Y` unchanged) or a blow-up of `Y` along the (nonempty) set of faces over the
centre, which is a centre of `Y`, with the parent map extended. The geometric fold consumes
exactly these facts. -/
inductive IsChainE : (ℕ → ℕ) → MonomialState → MonomialState → List (Finset (Finset ℕ)) → Prop
  | nil (ρ : ℕ → ℕ) (Y N : MonomialState) : IsChainE ρ Y N []
  | skip {ρ : ℕ → ℕ} {Y N : MonomialState} (S : Finset (Finset ℕ)) {Ns : List (Finset (Finset ℕ))}
      (hno : (Y.nerve.filter fun Q => Q.image ρ ∈ S) = ∅) (hnext : IsChainE ρ Y (N.blowUp S) Ns) :
      IsChainE ρ Y N (S :: Ns)
  | step {ρ : ℕ → ℕ} {Y N : MonomialState} (S : Finset (Finset ℕ)) {Ns : List (Finset (Finset ℕ))}
      (hne : (Y.nerve.filter fun Q => Q.image ρ ∈ S).Nonempty)
      (hY : Y.IsCenter (Y.nerve.filter fun Q => Q.image ρ ∈ S))
      (hnext : IsChainE (extendComp ρ Y N (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
        (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (N.blowUp S) Ns) :
      IsChainE ρ Y N (S :: Ns)

theorem IsChainE.append {ρ : ℕ → ℕ} {Y N : MonomialState} {N₁ N₂ : List (Finset (Finset ℕ))}
    (h₁ : IsChainE ρ Y N N₁)
    (h₂ : IsChainE (chainMapE ρ Y N N₁) (chainStateYE ρ Y N N₁) (N₁.foldl blowUp N) N₂) :
    IsChainE ρ Y N (N₁ ++ N₂) := by
  induction h₁ with
  | nil ρ Y N => exact h₂
  | skip S hno _ ih =>
    rw [chainMapE_cons_of_eq_empty _ _ _ _ hno, chainStateYE_cons_of_eq_empty _ _ _ _ hno,
      List.foldl_cons] at h₂
    exact IsChainE.skip S hno (ih h₂)
  | step S hne hY _ ih =>
    have hne' := Finset.nonempty_iff_ne_empty.mp hne
    rw [chainMapE_cons_of_ne_empty _ _ _ _ hne', chainStateYE_cons_of_ne_empty _ _ _ _ hne',
      List.foldl_cons] at h₂
    exact IsChainE.step S hne hY (ih h₂)

/-! ### A renumbering is injective on the faces -/

/-- The image under a renumbering of a face of `D` lies in the image of a family of faces of `D`
iff the face does (the renumbering is injective on the components of `D`). -/
theorem Rel.image_mem_image_iff {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P)
    {T : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp) {A : Finset (Finset ℕ)} (hA : A ⊆ D.nerve) :
    T.image ρ ∈ A.image (Finset.image ρ) ↔ T ∈ A := by
  refine ⟨fun hi => ?_, fun hT' => Finset.mem_image_of_mem _ hT'⟩
  obtain ⟨T₀, hT₀, he⟩ := Finset.mem_image.mp hi
  have h1 : (↑(T₀.image ρ) : Set ℕ) = ↑(T.image ρ) := by rw [he]
  rw [Finset.coe_image, Finset.coe_image] at h1
  have : T₀ = T := Finset.coe_inj.mp ((h.mono.injOn.image_eq_image_iff
    (fun _ hc => D.lt_nextComp_of_mem (hA hT₀) hc) (fun c hc => hT c hc)).mp h1)
  exact this ▸ hT₀

/-! ### The lockstep with skips -/

/-- `phase_restrict` and `phase_chain` together, with the explicit chain with skips: along the
phase-`r` run of `N`, the restricted state `D` and the state `Y` refining it advance exactly at
the centres with a face of `Y` over them; the phase-`r` run of `Y` is the chain run with skips,
and the composite parent map `Y → N` is the chain map. -/
theorem phase_chainE (r : ℕ) : ∀ (N : MonomialState) (hsN : ∀ s < r, N.Star s)
    (Y D P : MonomialState) (ρY ρ' σ' ρ : ℕ → ℕ), Refines ρY Y D → Rel ρ' σ' D P → Sub P N →
    (∀ c, c < Y.nextComp → ρ c = ρ' (ρY c)) →
    ∀ (hsD : ∀ s < r, D.Star s) (hsY : ∀ s < r, Y.Star s),
    ∃ ρY' ρ'' σ'' : ℕ → ℕ,
      Refines ρY' (phase r Y hsY).1 (phase r D hsD).1 ∧
      Rel ρ'' σ'' (phase r D hsD).1 ((phase r N hsN).2.foldl blowUp P) ∧
      Sub ((phase r N hsN).2.foldl blowUp P) (phase r N hsN).1 ∧
      (∀ c, c < (phase r Y hsY).1.nextComp →
        chainMapE ρ Y N (phase r N hsN).2 c = ρ'' (ρY' c)) ∧
      IsChainE ρ Y N (phase r N hsN).2 ∧
      (phase r Y hsY).2 = chainRunE ρ Y N (phase r N hsN).2 ∧
      (phase r Y hsY).1 = chainStateYE ρ Y N (phase r N hsN).2 := by
  intro N hsN
  induction N, hsN using phase.induct r with
  | case1 N hsN hne ih =>
    intro Y D P ρY ρ' σ' ρ hrefY hrel hsub hρ hsD hsY
    rw [phase_of_nonempty N hsN hne]
    simp only [List.foldl_cons]
    have hS0 : ∀ Q ∈ N.choice r, Q.Nonempty := fun Q hQ =>
      N.nerve_nonempty Q (N.mem_nerve_of_mem_choice hQ)
    have hsub' : Sub (P.blowUp (N.choice r)) (N.blowUp (N.choice r)) := hsub.blowUp _
    -- the image of a face of `Y` under the composite map
    have himg : ∀ Q ∈ Y.nerve, Q.image ρ = (Q.image ρY).image ρ' := fun Q hQ => by
      rw [Finset.image_image]
      exact Finset.image_congr fun c hc => hρ c (Y.lt_nextComp_of_mem hQ hc)
    have himgP : ∀ Q ∈ Y.nerve, Q.image ρ ∈ P.nerve := fun Q hQ => by
      rw [himg Q hQ]
      exact hrel.image_mem_nerve (hrefY.image_mem Q hQ)
    by_cases hdis : (N.choice r).filter (· ∈ P.nerve) = ∅
    · -- a skip: no face of the shadow (hence of `Y`) over the center
      have hdis' : ∀ Q ∈ N.choice r, Q ∉ P.nerve := fun Q hQ hQP =>
        Finset.notMem_empty Q (hdis ▸ Finset.mem_filter.mpr ⟨hQ, hQP⟩)
      have hno : (Y.nerve.filter fun Q => Q.image ρ ∈ N.choice r) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun Q hQ hQS => hdis' _ hQS (himgP Q hQ)
      obtain ⟨ρY', ρ'', σ'', h1, h2, h3, h4, h5, h6, h7⟩ :=
        ih Y D (P.blowUp (N.choice r)) ρY ρ' σ' ρ hrefY (hrel.of_blowUp_disjoint hS0 hdis') hsub'
          hρ hsD hsY
      rw [chainRunE_cons_of_eq_empty _ _ _ _ hno, chainMapE_cons_of_eq_empty _ _ _ _ hno,
        chainStateYE_cons_of_eq_empty _ _ _ _ hno]
      exact ⟨ρY', ρ'', σ'', h1, h2, h3, h4, IsChainE.skip _ hno h5, h6, h7⟩
    · -- a step: the center of `Y` is the set of faces over the center of `N`
      obtain ⟨Q₀, hQ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hdis
      obtain ⟨hQ₀N, hQ₀P⟩ := Finset.mem_filter.mp hQ₀
      have hPc : P.choice r = (N.choice r).filter (· ∈ P.nerve) := hsub.choice_eq_of_mem hQ₀N hQ₀P
      have hfilter : (N.choice r).filter (· ∈ P.nerve) = (D.choice r).image (Finset.image ρ') := by
        rw [← hPc, hrel.choice_eq]
      have hDne : (D.choice r).Nonempty := by
        rw [← Finset.image_nonempty (f := Finset.image ρ'), ← hfilter]
        exact ⟨Q₀, hQ₀⟩
      have hYne : (Y.choice r).Nonempty := (hrefY.choice_nonempty_iff r).mpr hDne
      have hSD : D.choice r ⊆ D.nerve := (D.isCenter_choice r).1
      have hSY : Y.choice r ⊆ Y.nerve := (Y.isCenter_choice r).1
      have hSL : D.choice r = (Y.choice r).image (Finset.image ρY) := hrefY.choice_image r
      have hpre : ∀ Q ∈ Y.nerve, Q.image ρY ∈ D.choice r → Q ∈ Y.choice r := fun Q hQ hQD => by
        rw [hrefY.choice_eq]; exact Finset.mem_filter.mpr ⟨hQ, hQD⟩
      -- the faces of `Y` over the center of `N` are Kollár's choice on `Y`
      have hfil : (Y.nerve.filter fun Q => Q.image ρ ∈ N.choice r) = Y.choice r := by
        rw [hrefY.choice_eq r]
        refine Finset.filter_congr fun Q hQ => ?_
        have hQρ : Q.image ρ ∈ N.choice r ↔ Q.image ρ ∈ (N.choice r).filter (· ∈ P.nerve) := by
          rw [Finset.mem_filter]
          exact ⟨fun h => ⟨h, himgP Q hQ⟩, fun h => h.1⟩
        rw [hQρ, hfilter, himg Q hQ]
        exact hrel.image_mem_image_iff (fun c hc => D.lt_nextComp_of_mem (hrefY.image_mem Q hQ) hc)
          hSD
      have hne' : (Y.nerve.filter fun Q => Q.image ρ ∈ N.choice r) ≠ ∅ := by
        rw [hfil]; exact Finset.nonempty_iff_ne_empty.mp hYne
      rw [phase_of_nonempty Y hsY hYne, phase_of_nonempty D hsD hDne]
      -- the composite parent map after the blow-ups
      have hρ₁ : ∀ c, c < (Y.blowUp (Y.choice r)).nextComp →
          extendComp ρ Y N (Y.choice r) (N.choice r) c =
            extendComp ρ' D P (D.choice r) (N.choice r)
              (extendComp ρY Y D (Y.choice r) (D.choice r) c) := by
        intro c hc
        rw [blowUp_nextComp] at hc
        rcases lt_or_exists_newComp Y (Y.choice r) hc with hc' | ⟨Q, hQ, rfl⟩
        · rw [extendComp_of_lt ρ Y N _ _ hc', extendComp_of_lt ρY Y D _ _ hc',
            extendComp_of_lt ρ' D P _ _ (hrefY.lt c hc')]
          exact hρ c hc'
        · have hQD : Q.image ρY ∈ D.choice r := by
            rw [hSL]; exact Finset.mem_image_of_mem _ hQ
          rw [extendComp_newComp ρ Y N _ _ hQ, extendComp_newComp ρY Y D _ _ hQ,
            extendComp_newComp ρ' D P _ _ hQD, ← hsub.newComp_eq, himg Q (hSY hQ)]
      obtain ⟨ρY', ρ'', σ'', h1, h2, h3, h4, h5, h6, h7⟩ :=
        ih (Y.blowUp (Y.choice r)) (D.blowUp (D.choice r)) (P.blowUp (N.choice r)) _ _ _ _
          (hrefY.blowUp hSY hSL hpre) (hrel.blowUp hSD hfilter hS0) hsub' hρ₁
          (fun _ hsr => D.star_blowUp hsD hsr) (fun _ hsr => Y.star_blowUp hsY hsr)
      rw [chainRunE_cons_of_ne_empty _ _ _ _ hne', chainMapE_cons_of_ne_empty _ _ _ _ hne',
        chainStateYE_cons_of_ne_empty _ _ _ _ hne', hfil]
      refine ⟨ρY', ρ'', σ'', h1, h2, h3, h4, ?_, by rw [h6], h7⟩
      refine IsChainE.step (N.choice r) ?_ ?_ ?_
      · rw [hfil]; exact hYne
      · rw [hfil]; exact Y.isCenter_choice r
      · rw [hfil]; exact h5
  | case2 N hsN hne =>
    intro Y D P ρY ρ' σ' ρ hrefY hrel hsub hρ hsD hsY
    rw [phase_of_not_nonempty N hsN hne]
    have hNe : N.choice r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hDe : D.choice r = ∅ := (hrel.choice_eq_empty_iff r).mp (hsub.choice_eq_empty_of hNe)
    have hYe : ¬ (Y.choice r).Nonempty := fun hY => by
      have := (hrefY.choice_nonempty_iff r).mp hY
      rw [hDe] at this
      exact Finset.not_nonempty_empty this
    rw [phase_of_not_nonempty D hsD (Finset.not_nonempty_iff_eq_empty.mpr hDe),
      phase_of_not_nonempty Y hsY hYe]
    exact ⟨ρY, ρ', σ', hrefY, hrel, hsub, hρ, IsChainE.nil _ _ _, rfl, rfl⟩

/-- The phases, with the chain with skips. -/
theorem phases_chainE (k : ℕ) : ∀ (r : ℕ) (N : MonomialState) (hsN : ∀ s < r, N.Star s)
    (Y D P : MonomialState) (ρY ρ' σ' ρ : ℕ → ℕ), Refines ρY Y D → Rel ρ' σ' D P → Sub P N →
    (∀ c, c < Y.nextComp → ρ c = ρ' (ρY c)) →
    ∀ (hsD : ∀ s < r, D.Star s) (hsY : ∀ s < r, Y.Star s),
    ∃ ρY' ρ'' σ'' : ℕ → ℕ,
      Refines ρY' (phases k r Y hsY).1 (phases k r D hsD).1 ∧
      Rel ρ'' σ'' (phases k r D hsD).1 ((phases k r N hsN).2.foldl blowUp P) ∧
      Sub ((phases k r N hsN).2.foldl blowUp P) (phases k r N hsN).1 ∧
      (∀ c, c < (phases k r Y hsY).1.nextComp →
        chainMapE ρ Y N (phases k r N hsN).2 c = ρ'' (ρY' c)) ∧
      IsChainE ρ Y N (phases k r N hsN).2 ∧
      (phases k r Y hsY).2 = chainRunE ρ Y N (phases k r N hsN).2 ∧
      (phases k r Y hsY).1 = chainStateYE ρ Y N (phases k r N hsN).2 := by
  induction k with
  | zero =>
    intro r N hsN Y D P ρY ρ' σ' ρ hrefY hrel hsub hρ hsD hsY
    exact ⟨ρY, ρ', σ', hrefY, hrel, hsub, hρ, IsChainE.nil _ _ _, rfl, rfl⟩
  | succ k ih =>
    intro r N hsN Y D P ρY ρ' σ' ρ hrefY hrel hsub hρ hsD hsY
    rw [phases_succ, phases_succ, phases_succ]
    obtain ⟨ρY₁, ρ₁'', σ₁'', h1, h2, h3, h4, h5, h6, h7⟩ :=
      phase_chainE r N hsN Y D P ρY ρ' σ' ρ hrefY hrel hsub hρ hsD hsY
    obtain ⟨ρY', ρ'', σ'', g1, g2, g3, g4, g5, g6, g7⟩ := ih (r + 1) _ (phase_star_succ N hsN) _ _ _
      ρY₁ ρ₁'' σ₁'' _ h1 h2 h3 h4 (phase_star_succ D hsD) (phase_star_succ Y hsY)
    have hfoldN : (phase r N hsN).1 = (phase r N hsN).2.foldl blowUp N := phase_fst_eq_foldl N hsN
    simp only [List.foldl_append]
    rw [chainRunE_append, chainMapE_append, chainStateYE_append, ← h7, ← hfoldN]
    refine ⟨ρY', ρ'', σ'', g1, g2, g3, g4, IsChainE.append h5 ?_, by rw [h6, g6], g7⟩
    rw [← h7, ← hfoldN]
    exact g5

/-- *The run of Step 3 on `Y` is the chain run with skips of the run of Step 3 on `N`*: for `Y`
refining the restricted state `D` (`Refines ρ_Y Y D`), `D` renumbered against `P`
(`Rel ρ' σ' D P`), `P` a sub-state of `N` (`Sub P N`), and `ρ = ρ' ∘ ρ_Y` on the components of
`Y`. -/
theorem step3_chainE {Y D P N : MonomialState} {ρY ρ' σ' ρ : ℕ → ℕ} (hrefY : Refines ρY Y D)
    (hrel : Rel ρ' σ' D P) (hsub : Sub P N) (hρ : ∀ c, c < Y.nextComp → ρ c = ρ' (ρY c)) :
    IsChainE ρ Y N (step3 N).2 ∧ (step3 Y).2 = chainRunE ρ Y N (step3 N).2 := by
  have e : step3 Y = phases N.n 1 Y (star_of_lt_one Y) := by
    rw [step3, hrefY.n_eq, hrel.n_eq, hsub.n_eq]
  rw [e, step3]
  obtain ⟨_, _, _, _, _, _, _, h5, h6, _⟩ := phases_chainE N.n 1 N (star_of_lt_one N) Y D P ρY ρ' σ'
    ρ hrefY hrel hsub hρ (star_of_lt_one D) (star_of_lt_one Y)
  exact ⟨h5, h6⟩

end Hironaka.Monomial.MonomialState
