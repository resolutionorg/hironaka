/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.ProjectiveBundle.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The vocabulary of the algebraic main theorems

The notions in which the algebraic main theorems are stated: [Hironaka's Main Theorems II and II(N)
and Corollaries 1 and 3][Hir64], [Kollár's Theorems 35 and 36][Kol07] and Włodarczyk's embedded
desingularization [Wlo05, Theorem 1.0.2]. The functorial theorems assert the existence of a
*blow-up sequence functor* [Kol07, Definition 31] with a property of each value and a
functoriality package [Kol07, 34]; they differ in the inputs of the functor and in the property of
the values. Hironaka's theorems assert the existence of a single succession of blow-ups with
clauses on its centres, weak transforms and boundaries.

Inputs.
* `AlgScheme k`: algebraic `k`-schemes (separated and of finite type over `Spec k`) with the
  `k`-morphisms, as Mathlib's `MorphismProperty.Over`.
* `ReducedEquidimensionalScheme k`: the full subcategory of the reduced, equidimensional algebraic
  `k`-schemes (`Scheme.IsReducedEquidimensional`), the inputs of Theorem 36.
* `Triple k`: Kollár's triples `(X, I, E)` [Kol07, Notation 64], the inputs of Theorem 35; a
  morphism is a `k`-morphism along which `I` and `E` pull back.
* `EmbeddedPair k`: a reduced closed subscheme `Y` of a smooth equidimensional algebraic
  `k`-scheme `X`, the inputs of Włodarczyk's theorem; a morphism is a `k`-morphism along which `Y`
  pulls back.
* `HasUnderlyingScheme C k`: a category `C` with a functor to `AlgScheme k`, the underlying scheme
  of an input. `HasChangeOfFields C`: for a family of such categories, one per field, the notion of
  a base change of an input along a field extension.

Blow-up sequence functors and functoriality.
* `BlowUpSequenceFunctor C`: a succession of blow-ups of the underlying scheme of every input
  [Kol07, Definition 31].
* `CommutesWithSmoothMorphisms` [Kol07, 34.1],
  `CommutesWithChangeOfFields` [Kol07, 34.2], and, for triples,
  `CommutesWithClosedEmbeddingsOfEmptyBoundary` [Kol07, 34.3 with `E = ∅`].
* For embedded pairs, `CommutesWithSmoothMorphismsMeetingComponents` [Wlo05, Theorem 1.0.2 (d)].

Properties of a succession of blow-ups.
* `BlowUpSequence.HasRegularIrreducibleCenters`, `BlowUpSequence.HasSncBoundaries` and
  `BlowUpSequence.HasConstantPositiveOrderAlongCenters`: clauses of Hironaka's Main Theorems II
  and II(N) and of his Corollary 1.
* `Scheme.IsSncDivisor`: a closed set is the support of a simple normal crossing divisor.
* `BlowUpSequence.IsResolution` [Kol07, (2)] and `BlowUpSequence.IsStrongResolution`
  [Kol07, (3); Theorem 36 (1)–(3)].
* `BlowUpSequence.HasSmoothSncCenters` and `Triple.IsPrincipalizedBy`
  [Kol07, Theorem 35 (1)–(3)].
* `EmbeddedPair.IsDesingularizedBy` [Wlo05, Theorem 1.0.2 (a)–(c), (e)].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-! ### Algebraic `k`-schemes -/

/-- The category of algebraic `k`-schemes, the schemes separated and of finite type over
`Spec k`, with the `k`-morphisms: Mathlib's `MorphismProperty.Over`. An object `X` has the
underlying scheme `X.left` and the structure morphism `X.hom : X.left ⟶ Spec k`; a morphism
`h : Y ⟶ X` has the underlying morphism of schemes `h.left`.

Relation to the source.
* **Translation.** `X : AlgScheme k` is Hironaka's algebraic $B$-scheme over the field $B = k$, a
  scheme (separated) of finite type over $\operatorname{Spec} B$ [Hir64, Ch. 0, §1, pp. 118–119].
* **Interpretation.** Kollár's schemes of finite type over a field and Włodarczyk's varieties are
  taken separated, as Hironaka's algebraic schemes are. -/
abbrev AlgScheme (k : Type u) [Field k] : Type (u + 1) :=
  (@FiniteType ⊓ @IsSeparated : MorphismProperty Scheme.{u}).Over ⊤ (Spec (.of k))

namespace AlgScheme

variable {k : Type u} [Field k] (X : AlgScheme k)

instance over : X.left.Over (Spec (.of k)) := ⟨X.hom⟩

instance finiteType : FiniteType (X.left ↘ Spec (.of k)) := X.prop.1

end AlgScheme

/-- `X` is *reduced and equidimensional* over `k`: `X` is reduced and its smooth locus over `k` is
smooth of a single relative dimension `d` [Kol07, Notation 64]. Over a perfect field (in the
theorems `k` has characteristic zero) the smooth locus of a reduced scheme of finite type is dense
and contains every generic point, so this says that the irreducible components of `X` all have
dimension `d`; for a smooth `X` it says that `X` is smooth of relative dimension `d`. Over an
imperfect field the smooth locus of a reduced scheme can be empty or not dense, and the condition
says less. -/
def Scheme.IsReducedEquidimensional (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] : Prop :=
  IsReduced X ∧
    ∃ d : ℕ, SmoothOfRelativeDimension d ((X ↘ Spec (.of k)).smoothLocus.ι ≫ (X ↘ Spec (.of k)))

/-- The inputs of Theorem 36: the algebraic `k`-schemes that are reduced and equidimensional
(`Scheme.IsReducedEquidimensional`: reduced, with smooth locus over `k` smooth of a single relative
dimension), with the `k`-morphisms. The irreducible components of an input may meet, so the two
axes `xy = 0` in the plane and every reduced simple normal crossing scheme are inputs. An object
`X` has `X.obj : AlgScheme k`. -/
abbrev ReducedEquidimensionalScheme (k : Type u) [Field k] : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun X : AlgScheme k => X.left.IsReducedEquidimensional k

/-! ### Triples -/

/-- A *triple* `(X, I, E)` [Kol07, Notation 64], the input of Theorem 35: `X` a smooth,
equidimensional algebraic `k`-scheme (smooth of a single relative dimension over `k`), `I` an ideal
sheaf nonzero at every point (so on every irreducible component), and `E` a simple normal crossing
divisor family with ordered index set. -/
structure Triple (k : Type u) [Field k] where
  /-- The smooth ambient scheme. -/
  X : AlgScheme k
  /-- `X` is smooth of a single relative dimension over `k` (smooth and equidimensional). -/
  smoothOfRelativeDimension : ∃ n : ℕ, SmoothOfRelativeDimension n (X.left ↘ Spec (.of k))
  /-- The ideal sheaf. -/
  I : X.left.IdealSheafData
  /-- `I` is nonzero at every point. -/
  isNonzeroEverywhere : Scheme.IdealSheafData.IsNonzeroEverywhere I
  /-- The boundary. -/
  E : Scheme.DivisorFamily X.left
  /-- `E` is a simple normal crossing family. -/
  isSnc : E.IsSnc

private theorem divisorFamily_comap_id {X : Scheme.{u}} (E : Scheme.DivisorFamily X) :
    E.comap (𝟙 X) = E := by
  cases E
  simp [Scheme.DivisorFamily.comap]

private theorem divisorFamily_comap_comp {X Y Z : Scheme.{u}} (E : Scheme.DivisorFamily Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) : E.comap (f ≫ g) = (E.comap g).comap f := by
  cases E
  simp only [Scheme.DivisorFamily.comap, Scheme.IdealSheafData.comap_comp]
  rfl

namespace Triple

variable {k : Type u} [Field k]

/-- A morphism of triples `(Y, J, F) ⟶ (X, I, E)`: a `k`-morphism `h : Y ⟶ X` with `J = h^* I` and
`F = h⁻¹ E`, so that the source is the pull-back of the target [Kol07, 34.1]. -/
instance : Category.{u} (Triple k) where
  Hom T T' := { h : T.X ⟶ T'.X // T.I = T'.I.comap h.left ∧ T.E = T'.E.comap h.left }
  id T := ⟨𝟙 T.X, by simp [Scheme.IdealSheafData.comap_id],
    by simp [divisorFamily_comap_id]⟩
  comp f g := ⟨f.1 ≫ g.1,
    by simp [f.2.1, g.2.1, Scheme.IdealSheafData.comap_comp],
    by simp [f.2.2, g.2.2, divisorFamily_comap_comp]⟩

end Triple

/-! ### Embedded pairs -/

/-- An *embedded pair* `(X, Y)`, the input of Włodarczyk's theorem [Wlo05, Theorem 1.0.2]: `X` a
smooth, equidimensional algebraic `k`-scheme (smooth of a single relative dimension over `k`) and
`Y` a reduced closed subscheme of `X`, given by its ideal sheaf. -/
structure EmbeddedPair (k : Type u) [Field k] where
  /-- The smooth ambient scheme. -/
  X : AlgScheme k
  /-- `X` is smooth of a single relative dimension over `k` (smooth and equidimensional). -/
  smoothOfRelativeDimension : ∃ n : ℕ, SmoothOfRelativeDimension n (X.left ↘ Spec (.of k))
  /-- The ideal sheaf of the embedded subscheme. -/
  Y : X.left.IdealSheafData
  /-- The embedded subscheme is reduced. -/
  isReduced : IsReduced Y.subscheme

namespace EmbeddedPair

variable {k : Type u} [Field k]

/-- A morphism of embedded pairs `(X', Y') ⟶ (X, Y)`: a `k`-morphism `h : X' ⟶ X` with
`Y' = h⁻¹(Y)`, the ideal sheaf of `Y'` the pull-back of that of `Y`. -/
instance : Category.{u} (EmbeddedPair k) where
  Hom P Q := { h : P.X ⟶ Q.X // P.Y = Q.Y.comap h.left }
  id P := ⟨𝟙 P.X, by simp [Scheme.IdealSheafData.comap_id]⟩
  comp f g := ⟨f.1 ≫ g.1, by simp [f.2, g.2, Scheme.IdealSheafData.comap_comp]⟩

end EmbeddedPair

/-! ### Blow-up sequence functors -/

/-- A category `C` of inputs with an underlying algebraic `k`-scheme, given by a functor to
`AlgScheme k`. -/
class HasUnderlyingScheme (C : Type*) [Category.{u} C] (k : outParam (Type u)) [Field k] where
  /-- The underlying algebraic `k`-scheme. -/
  forget : C ⥤ AlgScheme k

namespace HasUnderlyingScheme

variable {C : Type*} [Category.{u} C] {k : Type u} [Field k] [HasUnderlyingScheme C k]

/-- The underlying scheme of an input. -/
abbrev scheme (X : C) : Scheme.{u} := (forget.obj X).left

/-- The underlying morphism of schemes of a morphism of inputs. -/
abbrev hom {X Y : C} (h : X ⟶ Y) : scheme X ⟶ scheme Y := (forget.map h).left

end HasUnderlyingScheme

open HasUnderlyingScheme

instance ReducedEquidimensionalScheme.hasUnderlyingScheme (k : Type u) [Field k] :
    HasUnderlyingScheme (ReducedEquidimensionalScheme k) k where
  forget := ObjectProperty.ι _

instance Triple.hasUnderlyingScheme (k : Type u) [Field k] : HasUnderlyingScheme (Triple k) k where
  forget :=
    { obj T := T.X
      map h := h.1 }

instance EmbeddedPair.hasUnderlyingScheme (k : Type u) [Field k] :
    HasUnderlyingScheme (EmbeddedPair k) k where
  forget :=
    { obj P := P.X
      map h := h.1 }

/-- A *blow-up sequence functor* on the inputs `C` [Kol07, Definition 31]: a succession of blow-ups
of the underlying scheme of every input. Kollár's inputs are triples `(X, I, E)`; for Theorem 36
they are schemes. -/
abbrev BlowUpSequenceFunctor (C : Type*) [Category.{u} C] {k : Type u} [Field k]
    [HasUnderlyingScheme C k] : Type _ :=
  ∀ X : C, Scheme.BlowUpSequence (scheme X)

section Functoriality

variable {C : Type*} [Category.{u} C] {k : Type u} [Field k] [HasUnderlyingScheme C k]

/-- `B` *commutes with smooth morphisms* [Kol07, 34.1]: for a morphism of inputs `h : Y ⟶ X` whose
underlying morphism is smooth, `B(Y)` is the pull-back `h^* B(X)` if `h` is surjective, and is
obtained from `h^* B(X)` by deleting every blow-up with empty centre in general. (The first
condition follows from the second when `B` has no empty blow-ups; Kollár states both.) -/
@[mk_iff]
structure CommutesWithSmoothMorphisms (B : BlowUpSequenceFunctor C) : Prop where
  /-- For smooth surjective `h`, `B(Y)` is `h^* B(X)` (the first condition of 34.1). -/
  eq_pullback_of_surjective ⦃X Y : C⦄ (h : Y ⟶ X) :
    Smooth (hom h) → Function.Surjective (hom h) → B Y = (B X).pullback (hom h)
  /-- For smooth `h`, `B(Y)` is `h^* B(X)` with the empty blow-ups deleted (the second
  condition). -/
  eq_eraseEmpty_pullback ⦃X Y : C⦄ (h : Y ⟶ X) :
    Smooth (hom h) → B Y = ((B X).pullback (hom h)).eraseEmpty

end Functoriality

/-- For a family `C` of categories of inputs, one for each field, the notion of a *base change* of
an input along a field extension [Kol07, 34.2]: `IsFieldBaseChange σ p` for inputs `X` over `k` and
`XL` over `L`, a field extension `σ : k → L` and a morphism `p` of underlying schemes, says that `p`
exhibits `XL` as the base change `X ×_{Spec k} Spec L` together with its extra structure. -/
class HasChangeOfFields (C : ∀ (k : Type u) [Field k], Type*)
    [∀ (k : Type u) [Field k], Category.{u} (C k)]
    [∀ (k : Type u) [Field k], HasUnderlyingScheme (C k) k] where
  /-- `p` exhibits `XL` as the base change of `X` along `σ`. -/
  IsFieldBaseChange {k L : Type u} [Field k] [Field L] (σ : k →+* L) {X : C k} {XL : C L}
    (p : scheme XL ⟶ scheme X) : Prop

/-- For reduced equidimensional schemes, a base change is a cartesian square over `Spec σ`. -/
instance ReducedEquidimensionalScheme.hasChangeOfFields :
    HasChangeOfFields ReducedEquidimensionalScheme where
  IsFieldBaseChange {_ _} _ _ σ X XL p :=
    IsPullback p XL.obj.hom X.obj.hom (Spec.map (CommRingCat.ofHom σ))

/-- For triples, a base change is a cartesian square over `Spec σ` along which the ideal sheaf and
the boundary pull back. -/
instance Triple.hasChangeOfFields : HasChangeOfFields Triple where
  IsFieldBaseChange {_ _} _ _ σ X XL p :=
    IsPullback p XL.X.hom X.X.hom (Spec.map (CommRingCat.ofHom σ)) ∧
      XL.I = X.I.comap p ∧ XL.E = X.E.comap p

/-- A family of blow-up sequence functors, one for each field of characteristic zero, *commutes
with change of fields* [Kol07, 34.2]: for a field extension `σ : k → L` and an input `XL` over `L`
exhibited as the base change of an input `X` over `k` by `p`, `B_L(XL)` is the pull-back
`p^* B_k(X)`. The ring map `σ` may be an automorphism (`L = k`), so the condition includes
invariance under the automorphisms of `k`, as Kollár's does. -/
def CommutesWithChangeOfFields {C : ∀ (k : Type u) [Field k], Type*}
    [∀ (k : Type u) [Field k], Category.{u} (C k)]
    [∀ (k : Type u) [Field k], HasUnderlyingScheme (C k) k] [HasChangeOfFields C]
    (B : ∀ (k : Type u) [Field k] [CharZero k], BlowUpSequenceFunctor (C k)) : Prop :=
  ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L) (X : C k)
    (XL : C L) (p : scheme XL ⟶ scheme X), HasChangeOfFields.IsFieldBaseChange σ p →
      B L XL = (B k X).pullback p

/-- A blow-up sequence functor on triples *commutes with closed embeddings* when the boundary is
empty [Kol07, 34.3, for `E = ∅`]: for a closed embedding `j : Y ↪ X` of smooth schemes and triples
`(Y, I_Y, ∅)` and `(X, j_* I_Y, ∅)`, `B(X, j_* I_Y, ∅)` is the push-forward `j_* B(Y, I_Y, ∅)`.
A boundary is empty when it has no components (its index type is empty), however it is indexed.
Kollár states 34.3 for a boundary with simple normal crossings with `Y`; Theorem 35 (5) asserts it
only for `E = ∅`. -/
def CommutesWithClosedEmbeddingsOfEmptyBoundary {k : Type u} [Field k]
    (B : BlowUpSequenceFunctor (Triple k)) : Prop :=
  ∀ (T Y : Triple k) (j : Y.X ⟶ T.X) [IsClosedImmersion j.left],
    IsEmpty T.E.ι → IsEmpty Y.E.ι → T.I = Y.I.map j.left → B T = (B Y).pushforward j.left

/-- A blow-up sequence functor on embedded pairs *commutes with smooth morphisms meeting the
components* [Wlo05, Theorem 1.0.2 (d)]: for a morphism of embedded pairs `h : (X', Y') ⟶ (X, Y)`
whose underlying morphism is smooth, `B(X', Y')` is the pull-back `h^* B(X, Y)` if `h` is
surjective, and is obtained from `h^* B(X, Y)` by deleting every blow-up with empty centre if the
image of `h` meets every irreducible component of `Y`. Włodarczyk's (d), read through his
Definition 2.1.5 (extensions by isomorphisms) and Proposition 2.4.2, asserts the second condition
for every smooth `h`; here it is asserted only when the image meets every component of `Y`. -/
@[mk_iff]
structure CommutesWithSmoothMorphismsMeetingComponents {k : Type u} [Field k]
    (B : BlowUpSequenceFunctor (EmbeddedPair k)) : Prop where
  /-- For smooth surjective `h`, `B(X', Y')` is `h^* B(X, Y)`. -/
  eq_pullback_of_surjective ⦃P Q : EmbeddedPair k⦄ (h : Q ⟶ P) :
    Smooth (hom h) → Function.Surjective (hom h) → B Q = (B P).pullback (hom h)
  /-- For smooth `h` whose image meets every irreducible component of `Y`, `B(X', Y')` is
  `h^* B(X, Y)` with the empty blow-ups deleted. -/
  eq_eraseEmpty_pullback ⦃P Q : EmbeddedPair k⦄ (h : Q ⟶ P) : Smooth (hom h) →
    (∀ Z ∈ irreducibleComponents P.Y.subscheme,
      (Set.range (hom h) ∩ P.Y.subschemeι '' Z).Nonempty) →
    B Q = ((B P).pullback (hom h)).eraseEmpty

/-! ### Properties of the values -/

/-- `Z` is the support of a simple normal crossing divisor on `X` [Kol07, Definition 24]. -/
def Scheme.IsSncDivisor {X : Scheme.{u}} (Z : Set X) : Prop :=
  ∃ F : Scheme.DivisorFamily X, F.IsSnc ∧ (F.support : Set X) = Z

namespace Scheme.BlowUpSequence

section Hironaka

variable {X : Scheme.{u}}

/-- Every centre of the succession is non-singular (every local ring is regular) and irreducible
[Hir64, Main Theorem II (i), Main Theorem II(N) (1); Corollary 1, "non-singular irreducible
centers D(i)", p. 143]. -/
def HasRegularIrreducibleCenters (S : BlowUpSequence X) : Prop :=
  ∀ i : Fin S.length, IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme

/-- Starting from `E`, every boundary `E_i` has only normal crossings with the centre `D_i`, and
the last boundary `E_r` has only normal crossings [Hir64, Main Theorem II (iii) and the first half
of (iv); Main Theorem II(N) (3) and the first half of (4)]. The boundaries are `S.boundarySeq E`:
`E_0 = E` and `E_{i+1} = red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`; "has only normal crossings (with)" is
Hironaka's Definition 2 (`IsSncBoundary`, `IsSncBoundaryWith`). -/
@[mk_iff]
structure HasSncBoundaries (S : BlowUpSequence X) (E : X.IdealSheafData) : Prop where
  /-- `E_i` has only normal crossings with `D_i` [Hir64, Main Theorem II (iii); Main Theorem II(N)
  (3)]. -/
  isSncBoundaryWith_center : ∀ i : Fin S.length,
    (S.boundarySeq E i.castSucc).IsSncBoundaryWith (S.center i)
  /-- `E_r` has only normal crossings [Hir64, Main Theorem II (iv), Main Theorem II(N) (4), first
  half]. -/
  isSncBoundary_last : (S.boundarySeq E (Fin.last S.length)).IsSncBoundary

/-- The weak transform of `J` has a constant positive order along every centre: for every `i`
there is a positive integer `c` such that the weak transform `J_i` on the stage `X_i` has order `c`
at every point of the centre `D_i` [Hir64, Corollary 1 (1)]. -/
def HasConstantPositiveOrderAlongCenters (S : BlowUpSequence X) (J : X.IdealSheafData) : Prop :=
  ∀ i : Fin S.length, ∃ c : ℕ, 0 < c ∧ ∀ y ∈ (S.center i).support,
    (S.weakTransformSeq J i.castSucc).ord y = c

end Hironaka

variable {k : Type u} [Field k] {X : AlgScheme k}

/-- A succession of blow-ups `Π : X_r → X` is a *resolution* of `X` [Kol07, (2)]: `X_r` is smooth
over `k`, `Π` is projective (`IsProjective`, hence proper), and `Π` is birational, an isomorphism
over a dense open subset of `X`. Reading birationality as an isomorphism over a dense open subset is
right for a reduced `X`, the case of the theorems. -/
@[mk_iff]
structure IsResolution (S : BlowUpSequence X.left) : Prop where
  /-- `X_r` is smooth over `k`. -/
  smooth : Smooth (S.composite ≫ X.hom)
  /-- `Π` is projective [Kol07, (2)]. -/
  isProjective : IsProjective S.composite
  /-- `Π` is an isomorphism over a dense open subset. -/
  exists_dense_isIso : ∃ U : X.left.Opens, Dense (U : Set X.left) ∧ IsIso (S.composite ∣_ U)

/-- A succession of blow-ups `Π : X_r → X` is a *strong resolution* of `X` [Kol07, (3)], clauses
(1)–(3) of Theorem 36: a resolution (smooth over `k`, projective, birational) that is an isomorphism
over the smooth locus `X^{ns}` of `X`, and such that `Π⁻¹(Sing X)`, `Sing X` the complement of the
smooth locus, is the support of a simple normal crossing divisor. -/
@[mk_iff]
structure IsStrongResolution (S : BlowUpSequence X.left) : Prop extends IsResolution S where
  /-- `Π` is an isomorphism over `X^{ns}`. -/
  isIso_restrict_smoothLocus : IsIso (S.composite ∣_ (X.left ↘ Spec (.of k)).smoothLocus)
  /-- `Π⁻¹(Sing X)` is the support of a simple normal crossing divisor. -/
  isSncDivisor_preimage : Scheme.IsSncDivisor
    (S.composite ⁻¹' ((X.left ↘ Spec (.of k)).smoothLocus : Set X.left)ᶜ)

/-- Every centre of the succession is smooth over `k` and has simple normal crossings with the total
transform of the divisor family `E` at its stage [Kol07, Theorem 35 (1)]. -/
def HasSmoothSncCenters (S : BlowUpSequence X.left) (E : Scheme.DivisorFamily X.left) : Prop :=
  ∀ i : Fin S.length,
    Smooth ((S.center i).subschemeι ≫ S.stageMap i.castSucc ≫ X.hom) ∧
      (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i)

end Scheme.BlowUpSequence

variable {k : Type u} [Field k] in
/-- The triple `T = (X, I, E)` is *principalized* by a succession of blow-ups `Π : X_r → X`
[Kol07, Theorem 35 (1)–(3)]: its centres are smooth with simple normal crossings with the total
transforms of `E`, the pull-back `Π^* I` is the ideal sheaf of a simple normal crossing divisor,
and `Π` is an isomorphism over `X ∖ (cosupp I ∪ Sing E)`. (Kollár prints `X ∖ cosupp I`; his
construction first blows up intersections of components of `E`, which need not lie in
`cosupp I`.) -/
@[mk_iff]
structure Triple.IsPrincipalizedBy (T : Triple k) (S : Scheme.BlowUpSequence T.X.left) : Prop where
  /-- (1) Smooth centres with simple normal crossings with the boundary. -/
  hasSmoothSncCenters : S.HasSmoothSncCenters T.E
  /-- (2) `Π^* I` is the ideal sheaf of a simple normal crossing divisor. -/
  isIdealOfSncDivisor : (T.I.comap S.composite).IsIdealOfSncDivisor
  /-- (3) `Π` is an isomorphism over `X ∖ (cosupp I ∪ Sing E)`. -/
  isIso_restrict : IsIso (S.composite ∣_ (T.I.support ⊔ T.E.singularLocus).compl)

variable {k : Type u} [Field k] in
/-- The embedded pair `P = (X, Y)` is *desingularized* by a succession of blow-ups `σ : X_r → X`
[Wlo05, Theorem 1.0.2 (a)–(c), (e)]. With exceptional divisors `E_i` (the total transforms of the
empty divisor family) and strict transforms `Y_i` of `Y`: every centre `C_i` is smooth over `k`
and has simple normal crossings with `E_i`; every `E_i` is a simple normal crossing family; no
point of `C_i ∩ Y_i` lies over a point of `Reg(Y)`, the image in `X` of the smooth locus of `Y`
over `k`; `Ỹ = Y_r` is smooth over `k` and has simple normal crossings with `E_r`; and
`σ^*(I_Y) = I_Ỹ · J` for the ideal sheaf `J` of a simple normal crossing divisor supported in
`E_r`. -/
@[mk_iff]
structure EmbeddedPair.IsDesingularizedBy (P : EmbeddedPair k)
    (S : Scheme.BlowUpSequence P.X.left) : Prop where
  /-- Every centre `C_i` is smooth over `k` and has simple normal crossings with `E_i`
  [Wlo05, Theorem 1.0.2, the smoothness of the centres and the second half of (a)]. -/
  hasSmoothSncCenters : S.HasSmoothSncCenters (Scheme.DivisorFamily.empty P.X.left)
  /-- (a) Every `E_i`, the last included, is a simple normal crossing family. -/
  isSnc_totalTransformSeq : ∀ i : Fin (S.length + 1),
    (S.totalTransformSeq (Scheme.DivisorFamily.empty P.X.left) i).IsSnc
  /-- (b) No point of `C_i ∩ Y_i` lies over a point of `Reg(Y)`, the image in `X` of the smooth
  locus of `Y → Spec k`. -/
  stageMap_notMem_smoothLocus : ∀ i : Fin S.length, ∀ x ∈ (S.center i).support,
    x ∈ (S.strictTransformSeq P.Y i.castSucc).support →
      S.stageMap i.castSucc x ∉
        P.Y.subschemeι '' ((P.Y.subschemeι ≫ (P.X.left ↘ Spec (.of k))).smoothLocus : Set _)
  /-- (c) The strict transform `Ỹ = Y_r` is smooth over `k`. -/
  smooth_strictTransformSeq_last :
    Smooth ((S.strictTransformSeq P.Y (Fin.last S.length)).subschemeι ≫ S.composite ≫ P.X.hom)
  /-- (c) `Ỹ` has simple normal crossings with `E_r`. -/
  hasSncWith_strictTransformSeq_last :
    (S.totalTransformSeq (Scheme.DivisorFamily.empty P.X.left) (Fin.last S.length)).HasSncWith
      (S.strictTransformSeq P.Y (Fin.last S.length))
  /-- (e) `σ^*(I_Y) = I_Ỹ · J` for the ideal sheaf `J` of a simple normal crossing divisor
  supported in `E_r`. -/
  exists_comap_composite_eq_mul : ∃ J : (S.stage (Fin.last S.length)).IdealSheafData,
    J.IsIdealOfSncDivisor ∧
      J.support ≤
        (S.totalTransformSeq (Scheme.DivisorFamily.empty P.X.left) (Fin.last S.length)).support ∧
      P.Y.comap S.composite = S.strictTransformSeq P.Y (Fin.last S.length) * J

end AlgebraicGeometry
