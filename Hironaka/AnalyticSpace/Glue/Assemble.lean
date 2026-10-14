/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.TripleSet
public import Hironaka.AnalyticSpace.Glue.Data
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The gluing data of the shrunk pieces

From the shrunk pieces `A_i` (`Hironaka.AnalyticSpace.Glue.TripleSet`), the `K`-gluing core of the
gluing theorem for complexifications: pieces `Y_i | A_i`; gluing open subsets
`W_ij = A_i ∩ Ω_ij ∩ φ_ij⁻¹(A_j)` (everything on the diagonal, nothing for non-relevant pairs);
transitions `t_ij` lifted from `φ_ij` along the inclusions (the identity on the diagonal). The
shrinking constraints give: a point of `W_ij ∩ W_ik` lies in the trimmed cocycle neighbourhood
`N'_ijk` (`mem_nhd'_of_mem`), so `t_ij` lands in `W_ji` (through the triple `(i, j, i)`), and `t_ij`
carries `W_ij ∩ W_ik` into `W_jk` (`t_inter`, through the triple `(i, j, k)` and the pointwise
cocycle). This module builds the `KGlueCore` (`Shrunk.core`); the cocycle identity, making it
`KGlueData`, is `Hironaka.AnalyticSpace.Glue.CocycleData`.

Conventions. `WOpen i j ⊆ Y_i` is the gluing open subset in `Y_i`; `W i j` is its preimage in the
piece `Y_i | A_i`. The diagonal transition is the identity transported along `i = j` (`diagTrans`,
with `diagTrans_rfl`). For `j ∉ rel i` with `j ≠ i`, `W i j = ⊥` and every identity about it holds
trivially, by `⊥ ≤ _`; for `U_i ∩ U_j ∩ U_k = ∅` with `j, k ∈ rel i`, `N'_ijk = ⊥`, so
`W_ij ∩ W_ik = ∅`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {X : AnalyticSpace.{u} ℝ} {D : LocalData X} {huniq : Huniq X}

/-! ### The diagonal datum, unfolded -/

namespace LocalData

theorem Ωi_P_diag (i : D.J) : (D.P i i).Ωi = ⊤ := by
  rw [D.P_diag i]
  rfl

theorem mem_Ωi_P_diag (i : D.J) (y : (D.C i).Y) : y ∈ (D.P i i).Ωi := by
  rw [D.Ωi_P_diag i]
  exact Set.mem_univ y

theorem toFun_e_P_diag (i : D.J) :
    ∀ z : (D.C i).Y.toKLocallyRingedSpace.restrictOpen (D.P i i).Ωi,
      (KLocallyRingedSpace.Hom.toFun (D.P i i).e.hom z).1 = z.1 := by
  rw [D.P_diag i]
  intro z
  rfl

end LocalData

namespace Shrunk

variable (S : Shrunk D huniq)

/-! ### The pieces and the gluing opens -/

/-- The shrunk piece `Y_i | A_i`, as a `K`-space. -/
noncomputable abbrev piece (i : D.J) : KLocallyRingedSpace.{u} ℂ :=
  (D.C i).Y.toKLocallyRingedSpace.restrictOpen (S.A i)

open Classical in
/-- The gluing open `A_i ∩ Ω_ij ∩ φ_ij⁻¹(A_j) ⊆ Y_i` (everything on the diagonal, nothing for a
non-relevant pair). -/
noncomputable def WOpen (i j : D.J) : Opens (D.C i).Y :=
  if i = j then ⊤ else if j ∈ D.rel i then S.A i ⊓ (D.P i j).Ωi ⊓ (D.P i j).pullOpens (S.A j) else ⊥

/-- The gluing open as an open of the piece. -/
noncomputable def W (i j : D.J) : Opens (S.piece i) :=
  (Opens.map (ofRestrict (D.C i).Y.toKLocallyRingedSpace (S.A i)).1.base).obj (S.WOpen i j)

theorem mem_W {i j : D.J} (x : S.piece i) : x ∈ S.W i j ↔ x.1 ∈ S.WOpen i j := Iff.rfl

theorem WOpen_self (i : D.J) : S.WOpen i i = ⊤ := by
  unfold WOpen
  rw [ite_eq_left rfl]

theorem WOpen_of_ne_of_mem {i j : D.J} (h : i ≠ j) (hj : j ∈ D.rel i) :
    S.WOpen i j = S.A i ⊓ (D.P i j).Ωi ⊓ (D.P i j).pullOpens (S.A j) := by
  unfold WOpen
  rw [ite_eq_right h, ite_eq_left hj]

theorem WOpen_of_notMem {i j : D.J} (h : i ≠ j) (hj : j ∉ D.rel i) : S.WOpen i j = ⊥ := by
  unfold WOpen
  rw [ite_eq_right h, ite_eq_right hj]

theorem W_self (i : D.J) : S.W i i = ⊤ := by
  apply Opens.ext
  exact Set.eq_univ_of_forall fun x => by
    change x.1 ∈ S.WOpen i i
    rw [S.WOpen_self]
    trivial

theorem mem_rel_of_mem_WOpen {i j : D.J} (h : i ≠ j) {y : (D.C i).Y} (hy : y ∈ S.WOpen i j) :
    j ∈ D.rel i := by
  by_contra hj
  rw [S.WOpen_of_notMem h hj] at hy
  exact hy

theorem mem_A_of_mem_WOpen {i j : D.J} (h : i ≠ j) {y : (D.C i).Y} (hy : y ∈ S.WOpen i j) :
    y ∈ S.A i := by
  rw [S.WOpen_of_ne_of_mem h (S.mem_rel_of_mem_WOpen h hy)] at hy
  exact hy.1.1

theorem mem_Ω_of_mem_WOpen {i j : D.J} {y : (D.C i).Y} (hy : y ∈ S.WOpen i j) :
    y ∈ (D.P i j).Ωi := by
  by_cases h : i = j
  · subst h
    exact D.mem_Ωi_P_diag i y
  · rw [S.WOpen_of_ne_of_mem h (S.mem_rel_of_mem_WOpen h hy)] at hy
    exact hy.1.2

theorem toFun_e_mem_A_of_mem_WOpen {i j : D.J} (h : i ≠ j) {y : (D.C i).Y}
    (hy : y ∈ S.WOpen i j) :
    (KLocallyRingedSpace.Hom.toFun (D.P i j).e.hom ⟨y, S.mem_Ω_of_mem_WOpen hy⟩).1 ∈ S.A j := by
  have hy' := hy
  rw [S.WOpen_of_ne_of_mem h (S.mem_rel_of_mem_WOpen h hy)] at hy'
  obtain ⟨hΩ, hmem⟩ := ((D.P i j).mem_pullOpens (S.A j) y).mp hy'.2
  exact hmem

/-! ### The shrinking constraints on points -/

/-- A point of `A_i ∩ Ω_ij ∩ Ω_ik` whose two images lie in `A_j`, `A_k` lies in the trimmed cocycle
neighbourhood `N'_ijk` (the triple constraint of the shrinking). -/
theorem mem_nhd'_of_mem {i j k : D.J} (hj : j ∈ D.rel' i) (hk : k ∈ D.rel' i) {y : (D.C i).Y}
    (hy : y ∈ S.A i) (hΩj : y ∈ (D.P i j).Ωi) (hΩk : y ∈ (D.P i k).Ωi)
    (hAj : (KLocallyRingedSpace.Hom.toFun (D.P i j).e.hom ⟨y, hΩj⟩).1 ∈ S.A j)
    (hAk : (KLocallyRingedSpace.Hom.toFun (D.P i k).e.hom ⟨y,
        hΩk⟩).1 ∈ S.A k) : y ∈ D.nhd' huniq i j k := by
  by_contra hN
  exact (S.triple i j k hj hk).notMem_of_mem_left ⟨hy, hAj, hAk⟩
    (subset_closure ⟨y, hΩj, hΩk, hN, rfl⟩)

/-- The trimmed neighbourhood is either the cocycle neighbourhood (nonempty triple overlap) or
empty. -/
theorem nhd'_cases (i j k : D.J) :
    D.nhd' huniq i j k = D.cocycleNhd huniq i j k ∧
        ((D.U i ⊓ D.U j ⊓ D.U k : Opens X) : Set X).Nonempty ∨
      D.nhd' huniq i j k = ⊥ := by
  unfold LocalData.nhd'
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr rfl

/-- A point of the trimmed neighbourhood lies in the cocycle neighbourhood, and the triple overlap
is nonempty. -/
theorem mem_cocycleNhd_of_mem_nhd' {i j k : D.J} {y : (D.C i).Y} (hy : y ∈ D.nhd' huniq i j k) :
    y ∈ D.cocycleNhd huniq i j k ∧ ((D.U i ⊓ D.U j ⊓ D.U k : Opens X) : Set X).Nonempty := by
  rcases nhd'_cases (D := D) (huniq := huniq) i j k with ⟨h, hne⟩ | h
  · rw [h] at hy
    exact ⟨hy, hne⟩
  · rw [h] at hy
    exact absurd hy (by simp)

/-- The pointwise cocycle on the cocycle neighbourhood: `φ_jk (φ_ij y) = φ_ik y`. -/
theorem toFun_e_e_eq {i j k : D.J} {y : (D.C i).Y} (hy : y ∈ D.cocycleNhd huniq i j k) :
    (KLocallyRingedSpace.Hom.toFun (D.P j k).e.hom
      ⟨(KLocallyRingedSpace.Hom.toFun (D.P i j).e.hom
          ⟨y, tripleDomain_le_Ωij _ _ _ (D.cocycleNhd_le huniq i j k hy)⟩).1,
        mem_pullOpens_of_mem_tripleDomain _ _ _ (D.cocycleNhd_le huniq i j k hy)⟩).1 =
      (KLocallyRingedSpace.Hom.toFun (D.P i k).e.hom
        ⟨y, tripleDomain_le_Ωik _ _ _ (D.cocycleNhd_le huniq i j k hy)⟩).1 := by
  let z : (D.C i).Y.toKLocallyRingedSpace.restrictOpen (D.cocycleNhd huniq i j k) := ⟨y, hy⟩
  have h : KLocallyRingedSpace.Hom.toFun (compTrans (D.P i j) (D.P j k) (D.P i k))
      (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl _ (D.cocycleNhd_le huniq i j k)) z) =
    KLocallyRingedSpace.Hom.toFun (directTrans (D.P i j) (D.P j k) (D.P i k))
      (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl _ (D.cocycleNhd_le huniq i j k)) z) :=
    congrFun (congrArg KLocallyRingedSpace.Hom.toFun (D.cocycleNhd_eq huniq i j k)) z
  have hz := toFun_restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (D.cocycleNhd_le huniq i j k) z
  have h' : KLocallyRingedSpace.Hom.toFun (compTrans (D.P i j) (D.P j k) (D.P i k))
      ⟨y, D.cocycleNhd_le huniq i j k hy⟩ =
      KLocallyRingedSpace.Hom.toFun (directTrans (D.P i j) (D.P j k) (D.P i k)) ⟨y,
          D.cocycleNhd_le huniq i j k hy⟩ :=
    (congrArg (KLocallyRingedSpace.Hom.toFun (compTrans (D.P i j) (D.P j k)
        (D.P i k))) hz).symm.trans
      (h.trans (congrArg (KLocallyRingedSpace.Hom.toFun (directTrans (D.P i j) (D.P j k)
          (D.P i k))) hz))
  exact (toFun_compTrans_val _ _ _ ⟨y, D.cocycleNhd_le huniq i j k hy⟩).symm.trans
    (h'.trans (toFun_directTrans_val _ _ _ ⟨y, D.cocycleNhd_le huniq i j k hy⟩))

/-! ### The transition lands in the gluing open of the other piece -/

theorem mem_nhd'_of_mem_WOpen {i j : D.J} (h : i ≠ j) {y : (D.C i).Y} (hy : y ∈ S.WOpen i j) :
    y ∈ D.nhd' huniq i j i := by
  exact S.mem_nhd'_of_mem (D.mem_rel'_of_mem_rel (S.mem_rel_of_mem_WOpen h hy))
    (D.self_mem_rel' i) (S.mem_A_of_mem_WOpen h hy) (S.mem_Ω_of_mem_WOpen hy)
    (D.mem_Ωi_P_diag i y) (S.toFun_e_mem_A_of_mem_WOpen h hy)
    (Set.mem_of_eq_of_mem (D.toFun_e_P_diag i ⟨y, D.mem_Ωi_P_diag i y⟩)
      (S.mem_A_of_mem_WOpen h hy))

/-- The image of a point of `W_ij` under `φ_ij` lies in `W_ji`. -/
theorem toFun_e_mem_WOpen {i j : D.J} (h : i ≠ j) {y : (D.C i).Y} (hy : y ∈ S.WOpen i j) :
    (KLocallyRingedSpace.Hom.toFun (D.P i j).e.hom ⟨y, S.mem_Ω_of_mem_WOpen hy⟩).1 ∈ S.WOpen j i :=
        by
  have hN := (mem_cocycleNhd_of_mem_nhd' (S.mem_nhd'_of_mem_WOpen h hy)).1
  have hD := D.cocycleNhd_le huniq i j i hN
  have hji : i ∈ D.rel j := D.rel_comm (S.mem_rel_of_mem_WOpen h hy)
  rw [S.WOpen_of_ne_of_mem (Ne.symm h) hji]
  refine ⟨⟨S.toFun_e_mem_A_of_mem_WOpen h hy, mem_pullOpens_of_mem_tripleDomain _ _ _ hD⟩, ?_⟩
  refine ((D.P j i).mem_pullOpens (S.A i) _).mpr ⟨mem_pullOpens_of_mem_tripleDomain _ _ _ hD, ?_⟩
  have hc := toFun_e_e_eq hN
  exact Set.mem_of_eq_of_mem (hc.trans (D.toFun_e_P_diag i _)) (S.mem_A_of_mem_WOpen h hy)

/-! ### The transitions -/

theorem range_incl₂_subset_Ω (i j : D.J) :
    Set.range (KLocallyRingedSpace.Hom.toFun (incl₂ (D.C i).Y.toKLocallyRingedSpace (S.A i)
        (S.W i j))) ⊆
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict (D.C i).Y.toKLocallyRingedSpace
          (D.P i j).Ωi)) := by
  rintro _ ⟨x, rfl⟩
  rw [range_toFun_ofRestrict]
  exact S.mem_Ω_of_mem_WOpen x.2

/-- The inclusion of the gluing open into the transition domain `Y_i | Ω_ij`. -/
noncomputable def ι (i j : D.J) :
    (S.piece i).restrictOpen (S.W i j) ⟶
      (D.C i).Y.toKLocallyRingedSpace.restrictOpen (D.P i j).Ωi :=
  liftAlong (ofRestrict (D.C i).Y.toKLocallyRingedSpace (D.P i j).Ωi)
    (incl₂ (D.C i).Y.toKLocallyRingedSpace (S.A i) (S.W i j)) (S.range_incl₂_subset_Ω i j)

theorem ι_comp_ofRestrict (i j : D.J) :
    S.ι i j ≫ ofRestrict (D.C i).Y.toKLocallyRingedSpace (D.P i j).Ωi =
      incl₂ (D.C i).Y.toKLocallyRingedSpace (S.A i) (S.W i j) :=
  liftAlong_comp _ _ _

theorem toFun_ι_val (i j : D.J) (x : (S.piece i).restrictOpen (S.W i j)) :
    (KLocallyRingedSpace.Hom.toFun (S.ι i j) x).1 = x.1.1 :=
  toFun_liftAlong (ofRestrict (D.C i).Y.toKLocallyRingedSpace (D.P i j).Ωi)
    (incl₂ (D.C i).Y.toKLocallyRingedSpace (S.A i) (S.W i j)) (S.range_incl₂_subset_Ω i j) x

/-- The transition into `Y_j`. -/
noncomputable def tW (i j : D.J) :
    (S.piece i).restrictOpen (S.W i j) ⟶ (D.C j).Y.toKLocallyRingedSpace :=
  S.ι i j ≫ (D.P i j).e.hom ≫ ofRestrict (D.C j).Y.toKLocallyRingedSpace (D.P i j).Ωj

theorem toFun_tW (i j : D.J) (x : (S.piece i).restrictOpen (S.W i j)) :
    KLocallyRingedSpace.Hom.toFun (S.tW i j) x =
      (KLocallyRingedSpace.Hom.toFun (D.P i j).e.hom ⟨x.1.1, S.mem_Ω_of_mem_WOpen x.2⟩).1 := by
  have h : KLocallyRingedSpace.Hom.toFun (S.ι i j) x = ⟨x.1.1, S.mem_Ω_of_mem_WOpen x.2⟩ :=
    Subtype.ext (S.toFun_ι_val i j x)
  change (KLocallyRingedSpace.Hom.toFun (D.P i j).e.hom (KLocallyRingedSpace.Hom.toFun
      (S.ι i j) x)).1 = _
  rw [h]

theorem range_tW_subset {i j : D.J} (h : i ≠ j) :
    Set.range (KLocallyRingedSpace.Hom.toFun (S.tW i j)) ⊆
      Set.range (KLocallyRingedSpace.Hom.toFun (incl₂ (D.C j).Y.toKLocallyRingedSpace (S.A j)
          (S.W j i))) := by
  rintro _ ⟨x, rfl⟩
  rw [mem_range_toFun_incl₂, S.toFun_tW]
  have hmem := S.toFun_e_mem_WOpen h x.2
  refine ⟨?_, hmem⟩
  by_cases hji : j = i
  · exact absurd hji.symm h
  · exact S.mem_A_of_mem_WOpen hji hmem

/-- The identity transition on the diagonal, transported along `i = j`. -/
noncomputable def diagTrans (i j : D.J) (h : i = j) :
    (S.piece i).restrictOpen (S.W i j) ⟶ (S.piece j).restrictOpen (S.W j i) := by
  subst h
  exact 𝟙 _

theorem diagTrans_rfl (i : D.J) : S.diagTrans i i rfl = 𝟙 _ := rfl

open Classical in
/-- The transition `t_ij : W_ij ⟶ W_ji`. -/
noncomputable def t (i j : D.J) :
    (S.piece i).restrictOpen (S.W i j) ⟶ (S.piece j).restrictOpen (S.W j i) :=
  if h : i = j then S.diagTrans i j h
  else liftAlong (incl₂ (D.C j).Y.toKLocallyRingedSpace (S.A j) (S.W j i)) (S.tW i j)
    (S.range_tW_subset h)

theorem t_self (i : D.J) : S.t i i = 𝟙 _ := by
  unfold t
  rw [dite_eq_left rfl]
  exact S.diagTrans_rfl i

theorem t_comp_incl₂ {i j : D.J} (h : i ≠ j) :
    S.t i j ≫ incl₂ (D.C j).Y.toKLocallyRingedSpace (S.A j) (S.W j i) = S.tW i j := by
  unfold t
  rw [dite_eq_right h]
  exact liftAlong_comp _ _ _

theorem toFun_t_val {i j : D.J} (h : i ≠ j) (x : (S.piece i).restrictOpen (S.W i j)) :
    (KLocallyRingedSpace.Hom.toFun (S.t i j) x).1.1 =
      (KLocallyRingedSpace.Hom.toFun (D.P i j).e.hom ⟨x.1.1, S.mem_Ω_of_mem_WOpen x.2⟩).1 := by
  have h₁ := congrFun (congrArg KLocallyRingedSpace.Hom.toFun (S.t_comp_incl₂ h)) x
  change (KLocallyRingedSpace.Hom.toFun (S.t i j) x).1.1 = KLocallyRingedSpace.Hom.toFun
      (S.tW i j) x at h₁
  rw [h₁, S.toFun_tW]

/-! ### The gluing core -/

/-- The `K`-gluing core of the shrunk pieces. -/
noncomputable abbrev core : KGlueCore.{u} ℂ where
  J := D.J
  Y := S.piece
  W := S.W
  W_id := S.W_self
  t := S.t
  t_id := S.t_self
  t_inter := by
    intro i j k x hx
    by_cases hij : i = j
    · subst hij
      rw [S.t_self]
      exact hx
    · change (KLocallyRingedSpace.Hom.toFun (S.t i j) x).1.1 ∈ S.WOpen j k
      rw [S.toFun_t_val hij]
      by_cases hjk : j = k
      · subst hjk
        rw [S.WOpen_self]
        trivial
      · have hxij : x.1.1 ∈ S.WOpen i j := x.2
        have hxik : x.1.1 ∈ S.WOpen i k := hx
        have hj : j ∈ D.rel i := S.mem_rel_of_mem_WOpen hij hxij
        have hk : k ∈ D.rel i := by
          by_cases hik : i = k
          · subst hik
            obtain ⟨x₀, hx₀⟩ := hj
            exact ⟨x₀, hx₀.1, hx₀.1⟩
          · by_contra hk
            rw [S.WOpen_of_notMem hik hk] at hxik
            exact hxik
        have hAk : (KLocallyRingedSpace.Hom.toFun (D.P i k).e.hom ⟨x.1.1,
            S.mem_Ω_of_mem_WOpen hxik⟩).1 ∈ S.A k := by
          by_cases hik : i = k
          · subst hik
            exact Set.mem_of_eq_of_mem (D.toFun_e_P_diag i _) (S.mem_A_of_mem_WOpen hij hxij)
          · exact S.toFun_e_mem_A_of_mem_WOpen hik hxik
        have hN := S.mem_nhd'_of_mem (D.mem_rel'_of_mem_rel hj) (D.mem_rel'_of_mem_rel hk)
          (S.mem_A_of_mem_WOpen hij hxij) (S.mem_Ω_of_mem_WOpen hxij) (S.mem_Ω_of_mem_WOpen hxik)
          (S.toFun_e_mem_A_of_mem_WOpen hij hxij) hAk
        obtain ⟨hNc, hne⟩ := mem_cocycleNhd_of_mem_nhd' hN
        have hD := D.cocycleNhd_le huniq i j k hNc
        have hjk' : k ∈ D.rel j := by
          obtain ⟨x₀, hx₀⟩ := hne
          exact ⟨x₀, hx₀.1.2, hx₀.2⟩
        rw [S.WOpen_of_ne_of_mem hjk hjk']
        refine ⟨⟨S.toFun_e_mem_A_of_mem_WOpen hij hxij,
          mem_pullOpens_of_mem_tripleDomain _ _ _ hD⟩, ?_⟩
        refine ((D.P j k).mem_pullOpens (S.A k) _).mpr
          ⟨mem_pullOpens_of_mem_tripleDomain _ _ _ hD, ?_⟩
        exact Set.mem_of_eq_of_mem (toFun_e_e_eq hNc) hAk

end Shrunk

end AnalyticSpace.Glue
