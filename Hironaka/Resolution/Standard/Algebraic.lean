/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Restrict
public import Hironaka.Scheme.BlowUp.BlowUpAlong.Defs
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Algebra.RegularSmooth.SingularLocus
import Hironaka.Resolution.Algebraic.Hir64.MainTheoremI
import Hironaka.Scheme.BlowUp.Glue.BlowUp
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.BlowUpAlong

/-!
# Resolution of a variety by a single blow-up, in Mathlib's terms

Hironaka's Main Theorem I [Hir64, p. 132] (`AlgebraicGeometry.exists_isBlowUpAlong_smooth`): an
integral scheme `X`, separated and of finite type over a field `k` of characteristic zero, has a
blow-up `π : X' → X` along an ideal sheaf supported exactly on the singular locus, with `X'` smooth
over `k`; `π` is proper and an isomorphism over the smooth locus of `X`. It is stated with Mathlib's
definitions and two that Mathlib lacks, effective Cartier ideal sheaves and blow-ups given by their
universal property, defined from Mathlib's alone (`Scheme.IdealSheafData.IsEffectiveCartier`,
`Scheme.Hom.IsBlowUpAlong`, in `Hironaka.Scheme.BlowUp.BlowUpAlong.Defs`, a module importing Mathlib
only), so that the challenge file `Challenge/Standard.lean` imports Mathlib only and repeats the two
definitions word for word. They are the library's `Scheme.IdealSheafData.IsInvertible` and
`IsBlowUp` (`Scheme.Hom.isBlowUpAlong_iff_isBlowUp`).

It is the library's Main Theorem I,
`AlgebraicGeometry.exists_support_eq_singularLocus_isRegular_blowUp`, for `X` with its structure
morphism as an algebraic `k`-scheme, read in Mathlib's terms: the resolution is the blow-up
`D.blowUp → X` along an ideal sheaf `D` supported on the singular locus, which has the universal
property of the blow-up (`Scheme.IdealSheafData.blowUp.isBlowUp`, read through
`Scheme.Hom.isBlowUpAlong_iff_isBlowUp`). It is proper because `X` is locally Noetherian
(`Scheme.IdealSheafData.blowUp.isProper_π`) and an isomorphism over the complement of the support of
`D` (`Scheme.IdealSheafData.blowUp.isIso_π_restrict_compl_support`), which is the smooth locus of
`X` since over the perfect field `k` the singular locus is the complement of the smooth locus
(`Scheme.singularLocus_eq_compl_smoothLocus`, [Sta, Tag 00TV]); and `D.blowUp` is regular, hence
smooth over `k` (`Scheme.smooth_iff_isRegular`).
-/

public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/-- **Resolution of singularities** [Hir64, Main Theorem I, p. 132]. Every integral scheme `X`,
separated and of finite type over a field `k` of characteristic zero, is resolved by a single
blow-up: there is a blow-up `π : X' → X` along an ideal sheaf supported exactly on the singular
locus of `X`, with `X'` smooth over `k`. In particular `π` is proper and an isomorphism over the
smooth locus.

Relation to the source.
* **Translation.** Hironaka's "non-singular" (every local ring regular) is read as smooth over `k`,
  `Smooth (π ≫ f)`, and his singular locus as the complement of the smooth locus `f.smoothLocus`:
  for schemes locally of finite type over a field of characteristic zero the two notions agree
  [Sta, Tag 00TV].
* **Interpretation.** Hironaka's "say reduced and irreducible" is read as the hypothesis
  `IsIntegral X`.

Source statement: [Hir64, Main Theorem I, p. 132] -/
theorem exists_isBlowUpAlong_smooth {k : Type u} [Field k] [CharZero k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] [IsIntegral X] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (I : X.IdealSheafData),
      -- `π` is a blow-up of `X` along `I`
      π.IsBlowUpAlong I ∧
      -- the centre `I` is supported exactly on the singular locus of `X`
      (I.support : Set X) = (f.smoothLocus : Set X)ᶜ ∧
      -- `X'` is smooth over `k`
      Smooth (π ≫ f) ∧
      -- `π` is proper
      IsProper π ∧
      -- `π⁻¹(X_sm) → X_sm` is an isomorphism, `X_sm` the smooth locus of `X` over `k`
      IsIso (π ∣_ f.smoothLocus) := by
  let Xk : AlgScheme k := MorphismProperty.Over.mk ⊤ f ⟨inferInstance, inferInstance⟩
  have : IsIntegral Xk.left := ‹IsIntegral X›
  obtain ⟨D, hsupp, hreg⟩ : ∃ D : X.IdealSheafData,
      (D.support : Set X) = X.singularLocus ∧ IsRegular D.blowUp :=
    exists_support_eq_singularLocus_isRegular_blowUp Xk
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hprop : IsProper D.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π (X := X) D
  -- the centre is the complement of the smooth locus
  have hsupp' : (D.support : Set X) = (f.smoothLocus : Set X)ᶜ :=
    hsupp.trans (Scheme.singularLocus_eq_compl_smoothLocus f)
  have hU : D.support.compl = f.smoothLocus := by
    ext x
    change x ∉ (D.support : Set X) ↔ x ∈ (f.smoothLocus : Set X)
    rw [hsupp']
    exact not_not
  have hiso := Scheme.IdealSheafData.blowUp.isIso_π_restrict_compl_support D
  rw [hU] at hiso
  refine ⟨D.blowUp, D.blowUpπ, D, (D.blowUpπ.isBlowUpAlong_iff_isBlowUp D).mpr
    (Scheme.IdealSheafData.blowUp.isBlowUp D), hsupp', ?_, hprop, hiso⟩
  have : LocallyOfFiniteType (D.blowUpπ ≫ f) :=
    @locallyOfFiniteType_comp _ _ _ D.blowUpπ f hprop.toLocallyOfFiniteType ‹_›
  exact (Scheme.smooth_iff_isRegular (D.blowUpπ ≫ f)).mpr hreg

end AlgebraicGeometry
