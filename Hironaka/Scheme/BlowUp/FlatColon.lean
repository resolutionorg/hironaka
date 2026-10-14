/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The colon by a finitely generated ideal commutes with flat base change

Włodarczyk's resolution commutes with smooth morphisms [Wlo05, Theorem 1.0.2 (d)], the
functoriality proved in [Wlo05, §4.1]. The embedded resolution of
`Hironaka.Resolution.Algebraic.Wlo05.Embedded` replaces, at each step, the ideal `I` by the colon
`(I : I_Γ)` by the reduced, finitely generated, in general not invertible, ideal `I_Γ` of the union
of the strict transforms of the components already contained in a centre (`isolatedTriple`).
Transporting the construction along a smooth morphism `h` therefore needs the colon to commute with
the pull-back along `h`: `(I : K).comap h = (I.comap h : K.comap h)`. The lemma
`colon_comap_of_flat` of `Hironaka.Scheme.BlowUpSequence.PullbackInduced` proves this for an
invertible `K` (a principal stalk); this module proves it for every ideal sheaf on a locally
Noetherian scheme (every `K` is coherent, hence finitely generated on affines and on stalks). It is
used by the pull-back of the embedded resolution along smooth morphisms
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullback`).

The algebra is [Mat89, Theorem 7.4 (iii)]: for a flat `R`-algebra `S` and a finitely generated
`J = (j_1, …, j_r)`, `(I : J) S = (I S : J S)`. The colon by `J` is the intersection of the colons
by the `j_i` (`Ideal.colon_span`, `Submodule.colon_iUnion`), each of which commutes with flat base
change (`map_colon_singleton_of_flat` of `Hironaka.Scheme.BlowUpSequence.PullbackInduced`), and a
finite intersection commutes with flat base change (`Ideal.map_inf_of_flat` below, by the equational
criterion for flatness [Sta, Tag 00HK]: an element of `I S ∩ J S` has two expressions whose
difference is a trivial relation).

## Main declarations

* `Ideal.map_inf_of_flat`: `(I ⊓ J) S = I S ⊓ J S` for flat `S`.
* `Ideal.map_colon_of_fg_of_flat`: `(I : J) S = (I S : J S)` for flat `S` and finitely generated
  `J`.
* `stalkIdeal_colon_of_isLocallyNoetherian`: the stalk of a colon is the colon of the stalks.
* `colon_comap_of_flat_of_isLocallyNoetherian`: the colon commutes with flat pull-back.
-/

public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

section Ring

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- The equational criterion for flatness [Sta, Tag 00HK], read on an element of `I S ∩ J S`: a
finite intersection of ideals commutes with flat base change. Given
`x = Σ φ(a_i) s_i = Σ φ(b_j) t_j`
with `a_i ∈ I`, `b_j ∈ J`, the relation `Σ φ(a_i) s_i − Σ φ(b_j) t_j = 0` is trivial, `s_i = Σ_l
c_{il} y_l`, `t_j = Σ_l d_{jl} y_l` with `Σ_i a_i c_{il} = Σ_j b_j d_{jl}` for every `l`; the common
value `e_l` lies in `I ⊓ J` and `x = Σ_l φ(e_l) y_l`. -/
theorem _root_.Ideal.map_inf_of_flat (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) = I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  classical
  refine le_antisymm (Ideal.map_inf_le _) fun x hx => ?_
  obtain ⟨hxI, hxJ⟩ := Submodule.mem_inf.mp hx
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp
    (show x ∈ Submodule.span S (algebraMap R S '' (I : Set R)) from hxI)
  obtain ⟨m, d, g', hg'⟩ := Submodule.mem_span_set'.mp
    (show x ∈ Submodule.span S (algebraMap R S '' (J : Set R)) from hxJ)
  have hgI : ∀ i, ∃ a ∈ I, algebraMap R S a = (g i : S) := fun i => (g i).2
  have hgJ : ∀ j, ∃ b ∈ J, algebraMap R S b = (g' j : S) := fun j => (g' j).2
  choose a haI ha using hgI
  choose b hbJ hb using hgJ
  -- the relation `Σ a_i • c_i − Σ b_j • d_j = 0` in `S`, over the index type `Fin n ⊕ Fin m`
  let f : Fin n ⊕ Fin m → R := Sum.elim a fun j => -b j
  let z : Fin n ⊕ Fin m → S := Sum.elim c d
  have hrel : ∑ k, f k • z k = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [f, z, Sum.elim_inl, Sum.elim_inr, Algebra.smul_def, map_neg, neg_mul,
      Finset.sum_neg_distrib]
    have e1 : ∑ i, algebraMap R S (a i) * c i = x := by
      rw [← hg]; exact Finset.sum_congr rfl fun i _ => by rw [ha, smul_eq_mul, mul_comm]
    have e2 : ∑ j, algebraMap R S (b j) * d j = x := by
      rw [← hg']; exact Finset.sum_congr rfl fun j _ => by rw [hb, smul_eq_mul, mul_comm]
    rw [e1, e2, add_neg_cancel]
  obtain ⟨p, α, y, hz, hα⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S) hrel
  -- the coefficient of `y l` in `x` is `Σ_i a_i α_{i l}`, which is also `Σ_j b_j α_{j l}`
  have hx' : x = ∑ l, algebraMap R S (∑ i, a i * α (Sum.inl i) l) * y l := by
    calc x = ∑ i, c i • (g i : S) := hg.symm
      _ = ∑ i, algebraMap R S (a i) * c i := Finset.sum_congr rfl fun i _ => by
        rw [ha, smul_eq_mul, mul_comm]
      _ = ∑ i, algebraMap R S (a i) * ∑ l, α (Sum.inl i) l • y l := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show c i = z (Sum.inl i) from rfl, hz (Sum.inl i)]
      _ = ∑ l, algebraMap R S (∑ i, a i * α (Sum.inl i) l) * y l := by
        simp only [Finset.mul_sum, map_sum, map_mul, Finset.sum_mul, Algebra.smul_def]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
  have hcoef : ∀ l, ∑ i, a i * α (Sum.inl i) l = ∑ j, b j * α (Sum.inr j) l := by
    intro l
    have h := hα l
    rw [Fintype.sum_sum_type] at h
    simp only [f, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at h
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h)
  rw [hx']
  refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  refine Submodule.mem_inf.mpr ⟨Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (haI i), ?_⟩
  rw [hcoef l]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hbJ j)

/-- A finite infimum of ideals commutes with flat base change. -/
theorem _root_.Ideal.map_finset_inf_of_flat {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    (s.inf I).map (algebraMap R S) = s.inf fun i => (I i).map (algebraMap R S) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert i s hi ih => rw [Finset.inf_insert, Finset.inf_insert, Ideal.map_inf_of_flat, ih]

/-- The colon by the span of a finite set is the finite infimum of the colons by its elements
(`Ideal.colon_span`, `Submodule.colon_iUnion`). -/
theorem _root_.Ideal.colon_span_finset {T : Type*} [CommRing T] (K : Ideal T) (t : Finset T) :
    K.colon (Ideal.span (t : Set T) : Set T) = t.inf fun x => K.colon {x} := by
  classical
  rw [Ideal.colon_span, show (t : Set T) = ⋃ x ∈ t, {x} from (Set.biUnion_of_singleton _).symm,
    Submodule.colon_iUnion, Finset.inf_eq_iInf]
  exact iInf_congr fun x => by rw [Submodule.colon_iUnion]

/-- The colon by a finitely generated ideal commutes with flat base change,
`(I : J) S = (I S : J S)` [Mat89, Theorem 7.4 (iii)]. -/
theorem _root_.Ideal.map_colon_of_fg_of_flat (I J : Ideal R) (hJ : J.FG) :
    (I.colon (J : Set R)).map (algebraMap R S) =
      (I.map (algebraMap R S)).colon (J.map (algebraMap R S) : Set S) := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  rw [Ideal.colon_span_finset, Ideal.map_finset_inf_of_flat, Ideal.map_span, ← Finset.coe_image,
    Ideal.colon_span_finset, Finset.inf_image]
  exact Finset.inf_congr rfl fun x _ => map_colon_singleton_of_flat I x

end Ring

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- On a locally Noetherian scheme every ideal sheaf is finitely generated on affine opens, so the
stalk of a colon is the colon of the stalks (`ideal_colon_of_fg` of
`Hironaka.Scheme.BlowUp.Transform`, the colon commuting with localization for a finitely generated
divisor). -/
theorem stalkIdeal_colon_of_isLocallyNoetherian [IsLocallyNoetherian X] (I K : X.IdealSheafData)
    (x : X) :
    (I.colon K).stalkIdeal x =
      (I.stalkIdeal x).colon (K.stalkIdeal x : Set (X.presheaf.stalk x)) := by
  obtain ⟨U, hx⟩ := exists_affineOpens_mem x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := U.2.isLocalization_stalk ⟨x, hx⟩
  have hfg : ∀ V : X.affineOpens, (K.ideal V).FG := fun V => by
    have := IsLocallyNoetherian.component_noetherian (X := X) V
    exact IsNoetherian.noetherian (K.ideal V)
  rw [stalkIdeal_eq_map_germ _ U hx, stalkIdeal_eq_map_germ I U hx, stalkIdeal_eq_map_germ K U hx,
    ideal_colon_of_fg I K hfg U]
  exact map_colon_of_fg (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _ (hfg U)

/-- On locally Noetherian schemes the colon commutes with flat pull-back,
`(J : K).comap h = (J.comap h : K.comap h)` ([Mat89, Theorem 7.4 (iii)] on stalks): the lemma
`colon_comap_of_flat` of `Hironaka.Scheme.BlowUpSequence.PullbackInduced` without the invertibility
of `K`. -/
theorem colon_comap_of_flat_of_isLocallyNoetherian (h : Y ⟶ X) [Flat h] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (J K : X.IdealSheafData) :
    (J.colon K).comap h = (J.comap h).colon (K.comap h) := by
  apply ext_stalkIdeal
  intro y
  have hφ : (h.stalkMap y).hom.Flat := Flat.stalkMap h y
  let _ : Algebra (X.presheaf.stalk (h y)) (Y.presheaf.stalk y) := (h.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (h y)) (Y.presheaf.stalk y) := hφ
  obtain ⟨U, hx⟩ := exists_affineOpens_mem (h y)
  have hfg : (K.stalkIdeal (h y)).FG := by
    have := IsLocallyNoetherian.component_noetherian (X := X) U
    rw [stalkIdeal_eq_map_germ K U hx]
    exact Ideal.FG.map (IsNoetherian.noetherian (K.ideal U)) _
  rw [stalkIdeal_comap, stalkIdeal_colon_of_isLocallyNoetherian,
    stalkIdeal_colon_of_isLocallyNoetherian, stalkIdeal_comap, stalkIdeal_comap]
  exact Ideal.map_colon_of_fg_of_flat (S := Y.presheaf.stalk y) _ _ hfg

end AlgebraicGeometry.Scheme.IdealSheafData
