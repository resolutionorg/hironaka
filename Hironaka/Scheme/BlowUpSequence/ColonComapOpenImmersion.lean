/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional
import Hironaka.Scheme.BlowUpSequence.Remark33Iso
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Inverse image along an open immersion and the colon by any ideal sheaf

`comap_colon_of_isOpenImmersion` (`Hironaka/Scheme/BlowUpSequence/Remark33Iso.lean`, affine source)
and `comap_colon_of_isOpenImmersion'` (`Hironaka/Scheme/BlowUpSequence/Remark33Exceptional.lean`,
any source) show that the inverse image along an open immersion commutes with the colon by an
invertible ideal sheaf; this is the compatibility of the controlled transform with smooth pull-back
in the proof of [Wlo05, Proposition 2.4.2]. On a locally Noetherian scheme every ideal of sections
is finitely generated, so `ideal_colon_of_fg` (`Hironaka/Scheme/BlowUp/Transform.lean`) gives the
sections of a colon sheaf on every affine open for any divisor `K`, and the same two proofs go
through: `comap_colon_of_isOpenImmersion_of_isAffine` and
`comap_colon_of_isOpenImmersion_of_isLocallyNoetherian`. The embedded desingularization uses them
to read the ideal of the marked triple after isolating some components, a colon by the reduced
ideal of the strict transforms already isolated (the proof of [Wlo05, Theorem 4.7.1]), through an
open window. The invertible forms are the special case; they are not restated here.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData

namespace AlgebraicGeometry.Remark33

variable {M : Scheme.{u}}


/-- On a locally Noetherian scheme every ideal sheaf is finitely generated on every affine open;
the locally Noetherian form of `ideal_fg`
(`Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicSheaf.lean`, finite type over a field). -/
theorem ideal_fg_of_isLocallyNoetherian [IsLocallyNoetherian M] (K : M.IdealSheafData)
    (U : M.affineOpens) : (K.ideal U).FG := by
  have : IsNoetherianRing Γ(M, U) := IsLocallyNoetherian.component_noetherian U
  exact IsNoetherian.noetherian _

/-- On a locally Noetherian scheme the sections of a colon sheaf on an affine open are the colon
of the sections (`ideal_colon_of_fg`). -/
theorem ideal_colon_of_isLocallyNoetherian [IsLocallyNoetherian M] (I K : M.IdealSheafData)
    (U : M.affineOpens) :
    (I.colon K).ideal U = (I.ideal U).colon (K.ideal U : Set Γ(M, U)) :=
  Scheme.IdealSheafData.ideal_colon_of_fg I K (fun U => ideal_fg_of_isLocallyNoetherian K U) U

/-- The generalisation of `comap_colon_of_isOpenImmersion` (`Remark33Iso.lean`; invertible `K`) to
any `K` on a locally Noetherian scheme: inverse image along an open immersion from an affine
scheme commutes with the colon; the same proof with `ideal_colon_of_isLocallyNoetherian` (finitely
generated sections, `ideal_colon_of_fg`) in place of `ideal_colon_of_isInvertible`. -/
theorem comap_colon_of_isOpenImmersion_of_isAffine [IsLocallyNoetherian M] {Y : Scheme.{u}}
    [IsAffine Y] (c : Y ⟶ M) [IsOpenImmersion c] (I K : M.IdealSheafData) :
    (I.colon K).comap c = (I.comap c).colon (K.comap c) := by
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion c
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  have hθ : Function.Surjective ⇑((c.appIso ⊤).inv.hom) :=
    (c.appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (I.colon K) c ⟨⊤,
      isAffineOpen_top Y⟩
  have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I c ⟨⊤, isAffineOpen_top Y⟩
  have h3 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion K c ⟨⊤, isAffineOpen_top Y⟩
  rw [h1, ideal_colon_of_isLocallyNoetherian I K, Ideal.comap_colon_of_surjective _ hθ, ← h2,
    ← h3, ideal_colon_of_isLocallyNoetherian]

/-- The generalisation of `comap_colon_of_isOpenImmersion'` (`Remark33Exceptional.lean`; invertible
`K`) to any `K` on a locally Noetherian scheme: inverse image along any open immersion commutes
with the colon; from the affine case by the same covering argument
`le_of_comap_le_of_forall_exists`. -/
theorem comap_colon_of_isOpenImmersion_of_isLocallyNoetherian [IsLocallyNoetherian M]
    {Y : Scheme.{u}} (c : Y ⟶ M) [IsOpenImmersion c] (I K : M.IdealSheafData) :
    (I.colon K).comap c = (I.comap c).colon (K.comap c) := by
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion c
  have key : ∀ V : Y.affineOpens,
      ((I.colon K).comap c).comap V.1.ι = ((I.comap c).colon (K.comap c)).comap V.1.ι := by
    intro V
    have : IsAffine (V.1 : Scheme.{u}) := V.2
    rw [← Scheme.IdealSheafData.comap_comp, comap_colon_of_isOpenImmersion_of_isAffine
        (V.1.ι ≫ c) I K,
      comap_colon_of_isOpenImmersion_of_isAffine V.1.ι (I.comap c) (K.comap c),
          Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp]
  have hcov : ∀ x : Y, ∃ (V : Y.affineOpens) (y : (V.1 : Scheme.{u})), V.1.ι y = x := by
    intro x
    have hx : x ∈ (⊤ : Y.Opens) := trivial
    rw [← iSup_affineOpens_eq_top Y] at hx
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨V, ⟨x, hV⟩, rfl⟩
  exact le_antisymm
    (le_of_comap_le_of_forall_exists (fun V : Y.affineOpens => V.1.ι)
      hcov fun V => (key V).le)
    (le_of_comap_le_of_forall_exists (fun V : Y.affineOpens => V.1.ι)
      hcov fun V => (key V).ge)

end AlgebraicGeometry.Remark33
