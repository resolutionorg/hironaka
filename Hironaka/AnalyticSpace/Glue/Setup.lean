/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Tame
import Hironaka.AnalyticSpace.Glue.Cover
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ShrinkingLemma

/-!
# The local data: cover, shrinking, complexifications, tame transitions

`LocalData X` bundles the choices of the proof of the gluing theorem for complexifications [BW59,
Proposition 1]: a countable locally finite cover `U i` of `X` by relatively compact open subsets,
each with a complexification `C i` of `X | U i`; a shrinking `V i` (`closure (V i) ⊆ U i`, still
covering); and for every pair a tame normalized transition datum `P i j` over `U i ⊓ U j`
(`Hironaka.AnalyticSpace.Glue.Normalize`, `Hironaka.AnalyticSpace.Glue.Tame`), the identity on the
diagonal. `exists_localData` produces one from the hypotheses `hloc` (local existence of
complexifications) and `hiso` (local isomorphisms near the real points) of the gluing theorem: the
cover by `exists_locallyFinite_cover` (the property of admitting a complexification is stable under
`Complexification.restrictLe`), the shrinking by the shrinking lemma (`X` is paracompact and
Hausdorff, hence normal), the transitions by `PairIso.ofHiso` and `PairIso.exists_tame`. The two
covers are the pair of locally finite covers `V_i ⊆ U_i` of the proof of [Car57, §3, Proposition 2].

Conventions. The diagonal datum is `PairIso.refl` transported along `U i = U i ⊓ U i`
(`PairIso.ofEq`); it is tame because its `outer` set is empty. For `X = ∅` any countable index type
works (the empty cover; `LocalData.countable` asks for countability); for a finite index type the
local finiteness is automatic.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {X : AnalyticSpace.{u} ℝ}

namespace PairIso

variable {Ui Uj : Opens X} {Ci : Complexification (X.restrictOpen Ui)}
  {Cj : Complexification (X.restrictOpen Uj)} {V : Opens X} {hVi : V ≤ Ui} {hVj : V ≤ Uj}

/-- Transport of a datum along an equality of the base open `V = V'`. -/
noncomputable def ofEq (P : PairIso Ci Cj V hVi hVj) {V' : Opens X} (h : V = V') (hVi' : V' ≤ Ui)
    (hVj' : V' ≤ Uj) : PairIso Ci Cj V' hVi' hVj' where
  Ωi := P.Ωi
  Ωj := P.Ωj
  e := P.e
  mem_Ωi := fun v => P.mem_Ωi ⟨v.1, h.symm ▸ v.2⟩
  mem_Ωj := fun v => P.mem_Ωj ⟨v.1, h.symm ▸ v.2⟩
  Ωi_le := by subst h; exact P.Ωi_le
  Ωj_le := by subst h; exact P.Ωj_le
  compat := by subst h; exact P.compat

/-- The diagonal datum is tame: its `outer` set is empty. -/
theorem tame_refl_ofEq {Ui : Opens X} (Ci : Complexification (X.restrictOpen Ui))
    (h : Ui = Ui ⊓ Ui) : ((PairIso.refl Ci).ofEq h inf_le_left inf_le_right).Tame := by
  rw [Tame, Set.disjoint_right]
  rintro ⟨y, z⟩ ⟨hy, -⟩ -
  obtain ⟨u, hu, -⟩ := Ci.mem_imageDiff.mp hy
  exact hu ⟨u.2, u.2⟩

end PairIso

/-- The diagonal datum `P i i`, the identity transition transported to the pair type. -/
noncomputable def diagDatum {J : Type u} (U : J → Opens X)
    (C : ∀ i, Complexification (X.restrictOpen (U i))) (i j : J) (h : i = j) :
    PairIso (C i) (C j) (U i ⊓ U j) inf_le_left inf_le_right := by
  subst h
  exact (PairIso.refl (C i)).ofEq (inf_idem (U i)).symm inf_le_left inf_le_right

theorem diagDatum_rfl {J : Type u} (U : J → Opens X)
    (C : ∀ i, Complexification (X.restrictOpen (U i))) (i : J) :
    diagDatum U C i i rfl =
      (PairIso.refl (C i)).ofEq (inf_idem (U i)).symm inf_le_left inf_le_right :=
  rfl

/-- The local data of the proof of the gluing theorem for complexifications. -/
structure LocalData (X : AnalyticSpace.{u} ℝ) where
  /-- The index type of the cover. -/
  J : Type u
  countable : Countable J
  /-- The cover. -/
  U : J → Opens X
  lf : LocallyFinite fun i => (U i : Set X)
  cpt : ∀ i, IsCompact (closure (U i : Set X))
  cover : ⋃ i, (U i : Set X) = Set.univ
  /-- The local complexifications. -/
  C : ∀ i, Complexification (X.restrictOpen (U i))
  /-- The shrinking. -/
  V : J → Opens X
  closure_V_subset : ∀ i, closure (V i : Set X) ⊆ U i
  V_cover : ⋃ i, (V i : Set X) = Set.univ
  /-- The tame transition data, the identity on the diagonal. -/
  P : ∀ i j, PairIso (C i) (C j) (U i ⊓ U j) inf_le_left inf_le_right
  tame : ∀ i j, (P i j).Tame
  P_diag : ∀ i, P i i = (PairIso.refl (C i)).ofEq (inf_idem (U i)).symm inf_le_left inf_le_right

attribute [instance] LocalData.countable

/-- The existence of the local data from the hypotheses `hloc` and `hiso` of the gluing theorem. -/
theorem exists_localData
    (hloc : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ Nonempty (Complexification (X.restrictOpen U)))
    (hiso : ∀ (V : Opens X) (C C' : Complexification (X.restrictOpen V)),
      ∃ (W : Opens C.Y) (W' : Opens C'.Y) (hW : ∀ x, KLocallyRingedSpace.Hom.toFun C.f x ∈ W)
        (hW' : ∀ x, KLocallyRingedSpace.Hom.toFun C'.f x ∈ W')
        (e : KIso (C.Y.toKLocallyRingedSpace.restrictOpen W)
          (C'.Y.toKLocallyRingedSpace.restrictOpen W')),
        Hom.restrictTo C.f ⊤ W (fun x _ => hW x) ≫ e.hom =
          Hom.restrictTo C'.f ⊤ W' (fun x _ => hW' x)) :
    Nonempty (LocalData X) := by
  classical
  -- the cover
  obtain ⟨J, hJ, U, hP, hcpt, hlf, hcover⟩ := exists_locallyFinite_cover X
    (fun U => Nonempty (Complexification (X.restrictOpen U)))
    (fun {U V} hVU ⟨C⟩ => ⟨C.restrictLe V hVU⟩) hloc
  -- the shrinking (the shrinking lemma; `X` is normal as a paracompact Hausdorff space)
  obtain ⟨Vs, hVs_cover, hVs_open, hVs_closure⟩ := exists_subset_iUnion_closure_subset
    (s := (Set.univ : Set X)) (u := fun i => (U i : Set X)) isClosed_univ (fun i => (U i).2)
    (fun x _ => hlf.point_finite x) (by rw [hcover])
  -- the transitions
  let C : ∀ i, Complexification (X.restrictOpen (U i)) := fun i => (hP i).some
  have hpair : ∀ i j, ∃ P : PairIso (C i) (C j) (U i ⊓ U j) inf_le_left inf_le_right, P.Tame := by
    intro i j
    obtain ⟨W, W', hW, hW', e, heq⟩ := hiso (U i ⊓ U j) ((C i).restrictLe (U i ⊓ U j) inf_le_left)
      ((C j).restrictLe (U i ⊓ U j) inf_le_right)
    exact PairIso.exists_tame (PairIso.ofHiso W W' hW hW' e heq)
  let P : ∀ i j, PairIso (C i) (C j) (U i ⊓ U j) inf_le_left inf_le_right := fun i j =>
    if h : i = j then diagDatum U C i j h else (hpair i j).choose
  refine ⟨⟨J, hJ, U, hlf, hcpt, hcover, C, fun i => ⟨Vs i, hVs_open i⟩, hVs_closure,
    Set.eq_univ_of_univ_subset hVs_cover, P, ?_, ?_⟩⟩
  · intro i j
    by_cases h : i = j
    · subst h
      change (if h : i = i then diagDatum U C i i h else (hpair i i).choose).Tame
      rw [dite_eq_left rfl, diagDatum_rfl]
      exact PairIso.tame_refl_ofEq _ _
    · change (if h : i = j then diagDatum U C i j h else (hpair i j).choose).Tame
      rw [dite_eq_right h]
      exact (hpair i j).choose_spec
  · intro i
    change (if h : i = i then diagDatum U C i i h else (hpair i i).choose) = _
    rw [dite_eq_left rfl]
    exact diagDatum_rfl U C i

end AnalyticSpace.Glue
