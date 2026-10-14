/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Completion
public import Hironaka.Algebra.Local.Order
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Hironaka.Algebra.Local.Coords
import Hironaka.Algebra.Local.RegularSystem
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# The completion `R̂` and its relation to `R`

`R` is a Noetherian local ring, `R̂ = AdicCompletion (maximalIdeal R) R` and `ι : R → R̂` the
canonical map: the completion of [Kol07, Definition 55].  This file collects what the rest of the
library needs about the passage from `R` to `R̂`: `R̂` is local with the same residue field, the
order of an element or an ideal is preserved, ideals extend faithfully, and the coordinate
derivations extend, so that a coordinate structure on `R` induces one on `R̂`.

## The completion is local with the same residue field

Mathlib supplies everything: `R̂` is local with maximal ideal `𝔪R̂`
(`AdicCompletion.maximalIdeal_eq_map`), the residue map `R/𝔪 → R̂/𝔪R̂` is bijective
(`AdicCompletion.residueField_map_bijective`) and `R̂` is `𝔪R̂`-adically complete.  The four
statements are restated here under the names used later.

## Order is preserved

`(𝔪R̂)ᵃ` is the kernel of the evaluation `R̂ → R/𝔪ᵃ` at level `a`
(`AdicCompletion.pow_smul_top_eq_ker_eval`, read through `Ideal.smul_top_eq_map`), and the
evaluation of `ι f` is `f mod 𝔪ᵃ`; so `ι f ∈ (𝔪R̂)ᵃ ↔ f ∈ 𝔪ᵃ`.  Since the order of an element is
`sup {a : f ∈ 𝔪ᵃ}` (`Hironaka/Algebra/Local/Order.lean`), `ord (ι f) = ord f`, and for ideals both
inequalities `ord I ≤ ord (I R̂)` (`ι` is a local homomorphism) and `ord (I R̂) ≤ ord I`
(generators) follow.

## Ideals extend faithfully

`R → R̂` is flat (`AdicCompletion.flat_of_isNoetherian`) and local
(`AdicCompletion.algebraMap_isLocalHom_of_fg`), hence faithfully flat
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`, [Sta, Tag 00MC]), and for a faithfully flat
extension `I R̂ ∩ R = I` (`Ideal.comap_map_eq_self_of_faithfullyFlat`); so `I R̂ = J R̂` forces
`I = J`.  Finally `I R̂` is the image of the completion `Î` of the module `I`: the image
contains each `ι i` (`AdicCompletion.map_of`), and it is contained in `I R̂` because `Î` is the
image of `R̂ ⊗ I` (`ofTensorProduct_surjective_of_finite`, `I` finitely generated) and, by
naturality of `ofTensorProduct`, an elementary tensor `r ⊗ i` maps to `r · ι i`.

## The coordinate derivations extend

`∂̂ᵢ := (∂ᵢ).adicCompletion 𝔪` (`Hironaka/Algebra/Local/Completion.lean`) restricts to `∂ᵢ` along
`ι`, so `∂̂ᵢ (ι xⱼ) = ι (δᵢⱼ) = δᵢⱼ`, and it kills the coefficient field when `∂ᵢ` does.
Commutation is checked level by level: the level-`n` component of `∂̂ᵢ (∂̂ⱼ f)` is `∂ᵢ ∂ⱼ h mod 𝔪ⁿ`
for any lift `h` of the level-`n + 2` component of `f`, symmetric in `i, j` by `c.pderiv_comm`.
With the regularity of `R̂` supplied as an instance (it follows from the Cohen structure theorem,
`Hironaka/Algebra/Local/CohenIso.lean`), the pair `(ι x, ∂̂)` is a `RegularCoords` structure on
`R̂`: the `ι xᵢ` generate `𝔪R̂` (`maximalIdeal_eq_map`, `Ideal.map_span`), and the dimension field
follows from `spanFinrank (𝔪R̂) = spanFinrank 𝔪` (`AdicCompletion.spanFinrank_maximalIdeal_eq`) and
regularity of both rings.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

universe u v

variable {R : Type u} [CommRing R]

section Local

variable [IsLocalRing R] [IsNoetherianRing R]

/-- `R̂` is a local ring (Mathlib's instance, restated). -/
theorem isLocalRing_adicCompletion : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
  inferInstance

/-- The maximal ideal of `R̂` is `𝔪R̂`. -/
theorem maximalIdeal_adicCompletion :
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
      (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  AdicCompletion.maximalIdeal_eq_map

/-- The residue field of `R̂` is `K`. -/
theorem residueField_map_adicCompletion_bijective :
    Function.Bijective
      (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) :=
  AdicCompletion.residueField_map_bijective R

/-- `R̂` is `𝔪R̂`-adically complete. -/
theorem isAdicComplete_adicCompletion :
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion (maximalIdeal R) R) :=
  inferInstance

/-- `ι f ∈ (𝔪R̂)ᵃ ↔ f ∈ 𝔪ᵃ`, through the kernel of the evaluation at level `a`. -/
theorem algebraMap_mem_maximalIdeal_pow_iff (f : R) (a : ℕ) :
    algebraMap R (AdicCompletion (maximalIdeal R) R) f ∈
        maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ a ↔
      f ∈ maximalIdeal R ^ a := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing,
    LinearMap.mem_ker]
  change AdicCompletion.eval (maximalIdeal R) R a (AdicCompletion.of (maximalIdeal R) R f) = 0 ↔ _
  rw [AdicCompletion.eval_of, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.smul_eq_mul,
    Ideal.mul_top]

/-- `f ∈ 𝔪ᵃ ↔ ι f ∈ (𝔪R̂)ᵃ`. -/
theorem mem_maximalIdeal_pow_iff_algebraMap_mem (f : R) (a : ℕ) :
    f ∈ maximalIdeal R ^ a ↔
      algebraMap R (AdicCompletion (maximalIdeal R) R) f ∈
        maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ a :=
  (algebraMap_mem_maximalIdeal_pow_iff f a).symm

/-- The order of an element is preserved under completion. -/
theorem ordElem_algebraMap_adicCompletion (f : R) :
    ordElem (algebraMap R (AdicCompletion (maximalIdeal R) R) f) = ordElem f := by
  apply _root_.ENat.eq_of_forall_natCast_le_iff
  intro r
  rw [← mem_maximalIdeal_pow_iff_le_ordElem, ← mem_maximalIdeal_pow_iff_le_ordElem,
    algebraMap_mem_maximalIdeal_pow_iff]

/-- The order of an ideal is preserved under completion. -/
theorem ord_map_adicCompletion (I : Ideal R) :
    ord (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) = ord I := by
  apply _root_.ENat.eq_of_forall_natCast_le_iff
  intro r
  rw [le_ord_iff, le_ord_iff]
  constructor
  · intro h f hf
    exact (algebraMap_mem_maximalIdeal_pow_iff f r).mp (h (Ideal.mem_map_of_mem _ hf))
  · intro h
    calc I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))
        ≤ (maximalIdeal R ^ r).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
          Ideal.map_mono h
      _ = (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ^ r :=
          Ideal.map_pow _ _ _
      _ = maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ r := by
          rw [AdicCompletion.maximalIdeal_eq_map]

/-- `R → R̂` is faithfully flat (flat and local, [Sta, Tag 00MC]). -/
theorem faithfullyFlat_adicCompletion :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- `I R̂ ∩ R = I` (Krull's intersection theorem in the form recalled in [Kol07, Definition 55],
here from faithful flatness). -/
theorem comap_map_adicCompletion (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) = I := by
  have := faithfullyFlat_adicCompletion (R := R)
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- Extension of ideals to `R̂` is injective: two subschemes with the same completion at a point
agree near it ([Kol07, Definition 55]). -/
theorem map_adicCompletion_injective :
    Function.Injective
      (fun I : Ideal R => I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  intro I J h
  have := congrArg (Ideal.comap (algebraMap R (AdicCompletion (maximalIdeal R) R))) h
  simpa only [comap_map_adicCompletion] using this

/-- `I R̂ = Î`, the image in `R̂` of the completion of the module `I`. -/
theorem range_adicCompletion_map_subtype (I : Ideal R) :
    LinearMap.range (AdicCompletion.map (maximalIdeal R) I.subtype) =
      I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have : Module.Finite R I := Module.Finite.iff_fg.mpr I.fg_of_isNoetherianRing
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite (maximalIdeal R) I z
    rw [← LinearMap.comp_apply, AdicCompletion.ofTensorProduct_naturality, LinearMap.comp_apply]
    induction t using TensorProduct.inductionOn with
    | tmul r i =>
      rw [TensorProduct.AlgebraTensorModule.map_tmul, AdicCompletion.ofTensorProduct_tmul]
      exact Ideal.mul_mem_left _ r (Ideal.mem_map_of_mem _ i.2)
    | add x y hx hy =>
      rw [map_add, map_add]
      exact add_mem hx hy
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨AdicCompletion.of (maximalIdeal R) I ⟨i, hi⟩, by rw [AdicCompletion.map_of]; rfl⟩

end Local

section Derivations

variable [IsLocalRing R]

/-- The extended derivation restricts to `D` along `ι` (the completed derivations of
[Kol07, Lemma 74(5)]). -/
theorem adicCompletion_algebraMap_maximalIdeal {k : Type v} [CommRing k] [Algebra k R]
    (D : Derivation k R R) (f : R) :
    D.adicCompletion (maximalIdeal R) (algebraMap R (AdicCompletion (maximalIdeal R) R) f) =
      algebraMap R (AdicCompletion (maximalIdeal R) R) (D f) :=
  D.adicCompletion_algebraMap _ f

/-- The extension kills the coefficient field whenever `D` does. -/
theorem adicCompletion_algebraMap_eq_zero {k : Type v} [CommRing k] [Algebra k R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (hD : ∀ a : k, D (algebraMap k R a) = 0) (a : k) :
    D.adicCompletion (maximalIdeal R) (algebraMap k (AdicCompletion (maximalIdeal R) R) a) = 0 := by
  rw [AdicCompletion.algebraMap_apply, D.adicCompletion_of, hD, map_zero]

end Derivations

namespace RegularCoords

variable [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ} (c : RegularCoords R n)

/-- `∂̂ᵢ (ι xⱼ) = δᵢⱼ`. -/
theorem adicCompletion_pderiv_x (i j : Fin n) :
    (c.pderiv i).adicCompletion (maximalIdeal R)
        (algebraMap R (AdicCompletion (maximalIdeal R) R) (c.x j)) =
      if i = j then 1 else 0 := by
  rw [Derivation.adicCompletion_algebraMap, c.pderiv_x]
  split_ifs <;> simp

/-- The extended coordinate derivations commute. -/
theorem adicCompletion_pderiv_comm (i j : Fin n) (f : AdicCompletion (maximalIdeal R) R) :
    (c.pderiv i).adicCompletion (maximalIdeal R)
        ((c.pderiv j).adicCompletion (maximalIdeal R) f) =
      (c.pderiv j).adicCompletion (maximalIdeal R)
        ((c.pderiv i).adicCompletion (maximalIdeal R) f) := by
  apply AdicCompletion.ext
  intro m
  obtain ⟨h, hh⟩ := Submodule.Quotient.mk_surjective _ (f.val (m + 2))
  simp only [Derivation.adicCompletion_val]
  rw [← hh, Derivation.adicLevel_mk, Derivation.adicLevel_mk, Derivation.adicLevel_mk,
    Derivation.adicLevel_mk, c.pderiv_comm]

/-- The coordinate structure on `R̂` with parameters `ι xᵢ` and derivations `∂̂ᵢ`, given the
regularity of `R̂` as an instance argument. -/
noncomputable def adicCompletion [IsRegularLocalRing (AdicCompletion (maximalIdeal R) R)] :
    RegularCoords (AdicCompletion (maximalIdeal R) R) n where
  x i := algebraMap R (AdicCompletion (maximalIdeal R) R) (c.x i)
  pderiv i := (c.pderiv i).adicCompletion (maximalIdeal R)
  span_x := by
    rw [AdicCompletion.maximalIdeal_eq_map, c.span_x, Ideal.map_span, ← Set.range_comp]
    rfl
  card := by
    have h1 : ((maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (AdicCompletion (maximalIdeal R) R) :=
      IsRegularLocalRing.spanFinrank_maximalIdeal (R := AdicCompletion (maximalIdeal R) R)
    rw [← h1, AdicCompletion.spanFinrank_maximalIdeal_eq,
      spanFinrank_maximalIdeal_eq_of_natCast_eq c.card]
  pderiv_x i j := c.adicCompletion_pderiv_x i j
  pderiv_comm i j f := c.adicCompletion_pderiv_comm i j f

/-- `R̂` carries a `RegularCoords` structure with parameters `ι xᵢ` and derivations `∂̂ᵢ`, given
the regularity of `R̂`. -/
theorem exists_adicCompletion_coords [IsRegularLocalRing (AdicCompletion (maximalIdeal R) R)] :
    ∃ ĉ : RegularCoords (AdicCompletion (maximalIdeal R) R) n,
      ĉ.x = (fun i => algebraMap R (AdicCompletion (maximalIdeal R) R) (c.x i)) ∧
      ĉ.pderiv = fun i => (c.pderiv i).adicCompletion (maximalIdeal R) :=
  ⟨c.adicCompletion, rfl, rfl⟩

end RegularCoords

end IsLocalRing
