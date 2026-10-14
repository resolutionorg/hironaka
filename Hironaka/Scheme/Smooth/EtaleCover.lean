/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale pairs in the image form and their disjoint unions

Kollár's étale equivalence of two hypersurfaces of maximal contact takes "étale surjections
`ψ, ψ' : U ⇉ X`" [Kol07, Definition 91]. Here surjectivity is replaced by the image form: the
images of `ψ` and `ψ'` each contain the relevant closed set (the cosupport of the marked ideal),
because surjective pairs need not exist. Kollár's construction ends with "The images of finitely
many of the `U(p)` cover `X`. We can take `U` to be their disjoint union" ([Kol07, 95], the proof
of Theorem 92).

* `EtaleImagePair X S`: étale `ψ, ψ' : U ⟶ X` whose images both contain `S`, the pair of
  [Kol07, Definition 91] in the image form. The étale equivalence of
  `Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquiv.lean` adds the conditions (91.1′)–(91.4′)
  to this pair.
* `EtaleImagePair.sigma`: the disjoint union `∐ W_i` of a finite family of pairs with
  `ψ := Sigma.desc ψ_i`, `ψ' := Sigma.desc ψ'_i`, étale because étaleness is local at the source
  (`IsZariskiLocalAtSource.sigmaDesc`), covering because each `ψ_i` factors through `ψ`.
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- Étaleness is Zariski-local at the source (Mathlib's
`HasRingHomProperty.instIsZariskiLocalAtSource` for `RingHom.Etale`); instance search does not
find this instance by itself, so it is registered here. -/
instance instIsZariskiLocalAtSourceEtale : IsZariskiLocalAtSource @Etale.{u} :=
  HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)

/-- The image of the coproduct map `∐ g_i : ∐ W_i ⟶ X` contains every set covered by the images
of the `g_i`. -/
theorem subset_range_sigmaDesc_of_subset_iUnion {X : Scheme.{u}} {ι : Type u} (W : ι → Scheme.{u})
    (g : ∀ i, W i ⟶ X) {S : Set X} (h : S ⊆ ⋃ i, Set.range (g i).base) :
    S ⊆ Set.range (Sigma.desc g).base :=
  h.trans (Set.iUnion_subset fun i => by
    rintro _ ⟨y, rfl⟩
    exact ⟨(Sigma.ι W i).base y, by rw [← Sigma.ι_comp_desc g i]; rfl⟩)

/-- A pair of étale morphisms `ψ, ψ' : U ⟶ X` whose images both contain the set `S` (in the
application, the cosupport of a marked ideal): the "étale surjections `ψ, ψ' : U ⇉ X`" of
[Kol07, Definition 91], in the image form. -/
structure EtaleImagePair (X : Scheme.{u}) (S : Set X) where
  /-- The étale neighbourhood. -/
  U : Scheme.{u}
  /-- The first étale map. -/
  ψ : U ⟶ X
  /-- The second étale map. -/
  ψ' : U ⟶ X
  etale_ψ : Etale ψ
  etale_ψ' : Etale ψ'
  /-- The image of `ψ` contains `S` (the replacement for surjectivity). -/
  covers : S ⊆ Set.range ψ.base
  /-- The image of `ψ'` contains `S`. -/
  covers' : S ⊆ Set.range ψ'.base

attribute [instance] EtaleImagePair.etale_ψ EtaleImagePair.etale_ψ'

/-- The disjoint union of a family of étale pairs `ψ_i, ψ'_i : W_i ⟶ X` whose images cover `S`,
with `ψ := ∐ ψ_i`, `ψ' := ∐ ψ'_i` ("we can take `U` to be their disjoint union", [Kol07, 95]). -/
noncomputable def EtaleImagePair.sigma {X : Scheme.{u}} {S : Set X} {ι : Type u}
    (W : ι → Scheme.{u}) (ψ ψ' : ∀ i, W i ⟶ X) [∀ i, Etale (ψ i)] [∀ i, Etale (ψ' i)]
    (h : S ⊆ ⋃ i, Set.range (ψ i).base) (h' : S ⊆ ⋃ i, Set.range (ψ' i).base) :
    EtaleImagePair X S where
  U := ∐ W
  ψ := Sigma.desc ψ
  ψ' := Sigma.desc ψ'
  etale_ψ := IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  etale_ψ' := IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  covers := subset_range_sigmaDesc_of_subset_iUnion W ψ h
  covers' := subset_range_sigmaDesc_of_subset_iUnion W ψ' h'

theorem EtaleImagePair.sigma_ψ {X : Scheme.{u}} {S : Set X} {ι : Type u}
    (W : ι → Scheme.{u}) (ψ ψ' : ∀ i, W i ⟶ X) [∀ i, Etale (ψ i)] [∀ i, Etale (ψ' i)]
    (h : S ⊆ ⋃ i, Set.range (ψ i).base) (h' : S ⊆ ⋃ i, Set.range (ψ' i).base) :
    (EtaleImagePair.sigma W ψ ψ' h h').ψ = Sigma.desc ψ ∧
      (EtaleImagePair.sigma W ψ ψ' h h').ψ' = Sigma.desc ψ' :=
  ⟨rfl, rfl⟩

end AlgebraicGeometry
