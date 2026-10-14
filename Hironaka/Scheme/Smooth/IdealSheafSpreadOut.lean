/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Algebra.Local.CompletionCoords
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.Adapted
import Hironaka.Scheme.Smooth.EtaleCoordinates

/-!
# From formal to Zariski-local equality of ideal sheaves

Kollár's remark on Krull's intersection theorem in [Kol07, Definition 55]: in a Noetherian local
ring `(R, 𝔪)` every ideal `I` equals `∩_s (I + 𝔪^s)`, so two subschemes `Z, W ⊂ X` with the same
completion at `x` agree on an open neighbourhood `U` of `x` ("such that `Z ∩ U = W ∩ U`"). Kollár
uses it to pass from the identities (91.1′–4′) between completions to an open neighbourhood
`U(p) ∋ (p, p)` ([Kol07, 95], the proof of Theorem 92).

* `stalkIdeal_eq_of_map_adicCompletion_eq`: on a locally Noetherian scheme, two ideal sheaves with
  equal completions at `q` have equal stalks at `q`: `R → R̂` is faithfully flat for a Noetherian
  local ring, so extension of ideals to the completion is injective
  (`IsLocalRing.map_adicCompletion_injective`).
* `exists_comap_eq_of_stalkIdeal_eq`: two ideal sheaves with equal stalks at `q` agree on an open
  neighbourhood of `q`: on an affine `V ∋ q` the ideals `J(V), J'(V)` are finitely generated
  (Noetherian) and have the same localization at the prime of `q`, so they agree after inverting
  some `s ∉ 𝔭_q` (`exists_mem_map_eq_map_of_localization`, `Adapted.lean`), i.e. on the basic open
  `D(s) ∋ q`; ideal sheaves on `D(s)` are determined by their stalks (`ext_stalkIdeal`).
* `exists_comap_eq_of_map_adicCompletion_eq`: the composite, Kollár's statement.

Used to pass from the formal equivalence of two hypersurfaces of maximal contact to their
equivalence on an étale neighbourhood
(`Hironaka/Resolution/Algebraic/MaximalContact/AgreeOnSpread.lean`).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing TopologicalSpace AlgebraicGeometry

universe u

variable {W : Scheme.{u}} [IsLocallyNoetherian W] (J J' : W.IdealSheafData) (q : W)

/-- Two ideal sheaves with equal completions at `q` have equal stalks at `q` (Krull's intersection
theorem, [Kol07, Definition 55], through the faithful flatness of `R → R̂`). -/
theorem stalkIdeal_eq_of_map_adicCompletion_eq
    (h : (J.stalkIdeal q).map (algebraMap _
        (AdicCompletion (maximalIdeal (W.presheaf.stalk q)) (W.presheaf.stalk q))) =
      (J'.stalkIdeal q).map (algebraMap _
        (AdicCompletion (maximalIdeal (W.presheaf.stalk q)) (W.presheaf.stalk q)))) :
    J.stalkIdeal q = J'.stalkIdeal q :=
  map_adicCompletion_injective h

/-- Two ideal sheaves on a locally Noetherian scheme with equal stalks at `q` agree on an open
neighbourhood of `q` (the geometric form of Krull's intersection theorem in
[Kol07, Definition 55]; spreading out finitely many generators). -/
theorem exists_comap_eq_of_stalkIdeal_eq (h : J.stalkIdeal q = J'.stalkIdeal q) :
    ∃ V : W.Opens, q ∈ V ∧ J.comap V.ι = J'.comap V.ι := by
  obtain ⟨V, hqV⟩ := exists_affineOpens_mem q
  let _ := W.presheaf.algebra_section_stalk ⟨q, hqV⟩
  have hloc := V.2.isLocalization_stalk ⟨q, hqV⟩
  set p := (V.2.primeIdealOf ⟨q, hqV⟩).asIdeal with hpdef
  have hI : (J.ideal V).map (algebraMap Γ(W, V.1) (W.presheaf.stalk q)) =
      (J'.ideal V).map (algebraMap Γ(W, V.1) (W.presheaf.stalk q)) := by
    change (J.ideal V).map (W.presheaf.germ V.1 q hqV).hom =
      (J'.ideal V).map (W.presheaf.germ V.1 q hqV).hom
    rw [← stalkIdeal_eq_map_germ J V hqV, ← stalkIdeal_eq_map_germ J' V hqV, h]
  have hnoeth : IsNoetherianRing Γ(W, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨s, hsp, hs⟩ := exists_mem_map_eq_map_of_localization p.primeCompl (J.ideal V)
    (J'.ideal V) (IsNoetherian.noetherian _) (IsNoetherian.noetherian _) hI
  set U : W.Opens := W.basicOpen s with hUdef
  have hU : IsAffineOpen U := V.2.basicOpen s
  set Ua : W.affineOpens := ⟨U, hU⟩ with hUadef
  have hUV : U ≤ V.1 := W.basicOpen_le s
  have hqU : q ∈ U := (mem_basicOpen_iff_notMem_primeIdealOf V.2 hqV s).mpr hsp
  let _ := restrictAlgebra (X := W) hUV
  have hloc' : IsLocalization.Away s Γ(W, U) :=
    V.2.isLocalization_of_eq_basicOpen s (homOfLE hUV) rfl
  have hideal : J.ideal Ua = J'.ideal Ua := by
    rw [← map_ideal J (U := Ua) (V := V) hUV, ← map_ideal J' (U := Ua) (V := V) hUV]
    exact hs Γ(W, U)
  refine ⟨U, hqU, ext_stalkIdeal fun u => ?_⟩
  have hu : Ua.1.ι u ∈ Ua.1 := u.2
  rw [stalkIdeal_comap, stalkIdeal_comap, stalkIdeal_eq_map_germ J Ua hu,
    stalkIdeal_eq_map_germ J' Ua hu, hideal]

/-- Two ideal sheaves with equal completions at `q` agree on an open neighbourhood of `q`
([Kol07, Definition 55]; used as "(91.1′–4′) also hold in an open neighborhood `U(p)` by (55)" in
[Kol07, 95]). -/
theorem exists_comap_eq_of_map_adicCompletion_eq
    (h : (J.stalkIdeal q).map (algebraMap _
        (AdicCompletion (maximalIdeal (W.presheaf.stalk q)) (W.presheaf.stalk q))) =
      (J'.stalkIdeal q).map (algebraMap _
        (AdicCompletion (maximalIdeal (W.presheaf.stalk q)) (W.presheaf.stalk q)))) :
    ∃ V : W.Opens, q ∈ V ∧ J.comap V.ι = J'.comap V.ι :=
  exists_comap_eq_of_stalkIdeal_eq J J' q (stalkIdeal_eq_of_map_adicCompletion_eq J J' q h)

end AlgebraicGeometry.Scheme.IdealSheafData
