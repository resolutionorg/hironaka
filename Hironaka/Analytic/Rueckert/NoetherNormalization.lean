/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Embed
public import Hironaka.Analytic.Rueckert.Subst
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Hironaka.Analytic.Rueckert.Basic
import Hironaka.Analytic.Rueckert.Noetherian
import Hironaka.Analytic.Weierstrass.Division
import Hironaka.Analytic.Weierstrass.FunctionLevel
import Hironaka.Analytic.Weierstrass.Poly
import Hironaka.Analytic.Weierstrass.Tail
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Noether normalization for analytic algebras

For a proper ideal `I` of the ring `𝒪_n = Conv K n` of convergent power series there are
`d ≤ n`, an injection `e : Fin d ↪ Fin n` of the coordinates and a `K`-linear change of
coordinates `L` such that the composite `𝒪_d → 𝒪_n → 𝒪_n → 𝒪_n / I` (embed along `e`,
substitute `L`, reduce modulo `I`) is injective and finite
(`exists_noetherNormalization_analytic`). The proof follows [Fre17, Ch. I, §7]:

* Lemma 7.1 with its additional remark (`finite_mk_comp_convTail`): if `I` contains a series `P`
  regular of order `d` in `x_0` (a `z_n`-general series in Freitag's terms), then `𝒪_{n} / I` is
  generated as an `𝒪_{n-1}`-module by the images of `1, x_0, …, x_0^{d-1}`, an immediate
  consequence of the Weierstrass division theorem (`exists_unique_weierstrassDivision`): a
  series `F` is `F = Q·P + R` with `R` a polynomial of degree `< d` in `x_0` over `𝒪_{n-1}`, and
  the coefficients of `R` are convergent (`coeff_splitFirst_mem_conv`).
* Theorem 7.2 (`exists_noetherNormalization_analytic`), by induction on `n` through repeated
  application of 7.1: for `I ≠ ⊥` choose `0 ≠ f ∈ I` and a linear change `L` making `f` regular
  in `x_0` (`exists_substEquiv_isRegularIn`, the `z_n`-general reduction of [Fre17, Ch. I, §3]);
  the map `g : 𝒪_{n-1} → 𝒪_n / L(I)` is finite by 7.1; its kernel `b = L(I) ∩ 𝒪_{n-1}` is proper,
  so the induction hypothesis gives `𝒪_d → 𝒪_{n-1} / b` injective and finite, and
  `𝒪_{n-1} / b → 𝒪_n / L(I)` is injective and finite (`RingHom.kerLift`,
  `RingHom.Finite.of_comp_finite`); finite over finite is finite (`RingHom.Finite.comp`);
  transport back along `L⁻¹` (`Ideal.quotientEquiv`). The uniqueness of `d` (the Krull
  dimension) is not stated here; see `Parameters.lean`.

Freitag works over `ℂ`. The proof is carried out over any `K` with `[RCLike K]`, the Weierstrass
division and the linear changes of coordinates being stated over `K`. The map `𝒪_d → 𝒪_n` is
`convEmbed K e` (`Embed.lean`) composed with `substEquiv L` (`Subst.lean`); the induction
composes the block-diagonal change `x ↦ (x_0, L' (x_1, …, x_{n-1}))` (`consCLE L'`) with `L⁻¹` so
that the tail embedding `convTail` intertwines the two substitutions
(`substConv_consCLE_convTail`). The normalization is the starting point of the local
parametrization of a prime germ (`ParametrizationPrimitive.lean`) and of the theory of dimension
(`Parameters.lean`); the dimension theory of analytic spaces
(`Hironaka/AnalyticSpace/ConvDimension.lean`, `Hironaka/AnalyticSpace/Semicontinuity.lean`)
applies it to the stalks.
-/

@[expose] public section

open scoped ENNReal NNReal
open MvPowerSeries Filter Topology

namespace Analytic

variable {K : Type*} [RCLike K] {m n d : ℕ}

/-! ### Finiteness over the tail ring -/

/-- A series whose coefficients vanish in degree `≥ d` in `x_0` is the polynomial
`∑_{i < d} r_i(x_1, …, x_m) x_0^i` in `x_0` with coefficients `r_i` the slices `splitFirst`,
lifted by `liftTail`. -/
theorem eq_sum_liftTail_coeff_mul_X_pow {r : MvPowerSeries (Fin (m + 1)) K} {d : ℕ}
    (hr : ∀ ν : Fin (m + 1) →₀ ℕ, d ≤ ν 0 → coeff ν r = 0) :
    r = ∑ i ∈ Finset.range d, liftTail (PowerSeries.coeff i (splitFirst K m r)) * X 0 ^ i := by
  ext ν
  obtain ⟨k, x, rfl⟩ : ∃ (k : ℕ) (x : Fin m →₀ ℕ), ν = Finsupp.cons k x :=
    ⟨ν 0, ν.tail, (Finsupp.cons_tail ν).symm⟩
  rw [map_sum (MvPowerSeries.coeff (R := K) (Finsupp.cons k x))]
  simp_rw [coeff_cons_liftTail_mul_X_pow]
  by_cases hk : k < d
  · rw [Finset.sum_eq_single k]
    · rw [ite_eq_left rfl, coeff_coeff_finSuccEquiv]
    · intro i _ hi
      rw [ite_eq_right (Ne.symm hi)]
    · intro h
      exact absurd (Finset.mem_range.mpr hk) h
  · rw [hr _ (by rw [Finsupp.cons_zero]; exact not_lt.mp hk)]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    rw [ite_eq_right]
    rintro rfl
    exact hk (Finset.mem_range.mp hi)

/-- [Fre17, Ch. I, Lemma 7.1] with its additional remark: if the ideal `I ⊆ 𝒪_{m+1}` contains a
series `P` regular of order `d` in `x_0`, then `𝒪_{m+1} / I` is a finite `𝒪_m`-module, generated
by the images of `1, x_0, …, x_0^{d-1}`, along the tail embedding `𝒪_m → 𝒪_{m+1}`. Proof:
Weierstrass division of a representative by `P` (`exists_unique_weierstrassDivision`) gives a
remainder polynomial of degree `< d` in `x_0` with convergent coefficients. -/
theorem finite_mk_comp_convTail {I : Ideal (Conv K (m + 1))} {P : Conv K (m + 1)} (hP : P ∈ I)
    {d : ℕ} (hreg : IsRegularIn (P : MvPowerSeries (Fin (m + 1)) K) d) :
    RingHom.Finite (A := Conv K m) (B := Conv K (m + 1) ⧸ I)
      ((Ideal.Quotient.mk I).comp (convTail K).toRingHom) := by
  classical
  let alg : Algebra (Conv K m) (Conv K (m + 1) ⧸ I) := RingHom.toAlgebra (R := Conv K m)
    (S := Conv K (m + 1) ⧸ I) ((Ideal.Quotient.mk I).comp (convTail K).toRingHom)
  let hmod : Module (Conv K m) (Conv K (m + 1) ⧸ I) := @Algebra.toModule _ _ _ _ alg
  refine ⟨⟨(Finset.range d).image fun i => Ideal.Quotient.mk I (convX K 0 ^ i), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨qq, r, hq, hr, hrd, hF, -⟩ := exists_unique_weierstrassDivision F.2 P.2 hreg
  have hFr : Ideal.Quotient.mk I F = Ideal.Quotient.mk I ⟨r, hr⟩ := by
    rw [Ideal.Quotient.eq]
    have : F - ⟨r, hr⟩ = ⟨qq, hq⟩ * P := Subtype.ext (by
      change (F : MvPowerSeries (Fin (m + 1)) K) - r = qq * P
      rw [hF]; ring)
    rw [this]
    exact I.mul_mem_left _ hP
  have hsum : (⟨r, hr⟩ : Conv K (m + 1)) = ∑ i ∈ Finset.range d,
      convTail K ⟨PowerSeries.coeff i (splitFirst K m r), coeff_splitFirst_mem_conv hr i⟩ *
        convX K 0 ^ i := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change r = ∑ i ∈ Finset.range d, _
    conv_lhs => rw [eq_sum_liftTail_coeff_mul_X_pow hrd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_convTail, coe_convX]
  rw [hFr, hsum, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [map_mul]
  change algebraMap (Conv K m) (Conv K (m + 1) ⧸ I)
    ⟨PowerSeries.coeff i (splitFirst K m r), coeff_splitFirst_mem_conv hr i⟩ *
      Ideal.Quotient.mk I (convX K 0 ^ i) ∈ _
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hi))

/-! ### The block-diagonal linear change `id ⊕ L'` and the tail embedding -/

/-- The linear change `x ↦ (x_0, L' (x_1, …, x_m))` of `K^{m+1}`: the identity on the regular
variable `x_0`, the induction hypothesis's change `L'` on the tail variables (the induction step
of [Fre17, Ch. I, 7.2]). -/
noncomputable def consCLE (L' : (Fin m → K) ≃L[K] (Fin m → K)) :
    (Fin (m + 1) → K) ≃L[K] (Fin (m + 1) → K) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => Fin.cons (x 0) (L' (Fin.tail x))
      invFun := fun y => Fin.cons (y 0) (L'.symm (Fin.tail y))
      map_add' := fun x y => by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · rw [show Fin.tail (x + y) = Fin.tail x + Fin.tail y from rfl, map_add]
          simp
      map_smul' := fun c x => by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · rw [show Fin.tail (c • x) = c • Fin.tail x from rfl, map_smul]
          simp
      left_inv := fun x => by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp [Fin.tail]
      right_inv := fun y => by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp [Fin.tail] }

/-- `consCLE L' x = (x_0, L' (x_1, …, x_m))`. -/
theorem consCLE_apply (L' : (Fin m → K) ≃L[K] (Fin m → K)) (x : Fin (m + 1) → K) :
    consCLE L' x = Fin.cons (x 0) (L' (Fin.tail x)) := rfl

/-- The tail of `consCLE L' x` is `L'` of the tail of `x`. -/
theorem tail_consCLE (L' : (Fin m → K) ≃L[K] (Fin m → K)) (x : Fin (m + 1) → K) :
    Fin.tail (consCLE L' x) = L' (Fin.tail x) := by
  rw [consCLE_apply, Fin.tail_cons]

/-- Substituting `consCLE L'` into a series lifted from the tail variables is the lift of the
substitution of `L'`: the tail embedding `convTail` intertwines the two linear changes. Proved on
the function level through `evalSeries_substConv` and `evalSeries_liftTail`. -/
theorem substConv_consCLE_convTail (L' : (Fin m → K) ≃L[K] (Fin m → K)) (c : Conv K m) :
    substConv ((consCLE L' : (Fin (m + 1) → K) ≃L[K] (Fin (m + 1) → K)) :
        (Fin (m + 1) → K) →L[K] (Fin (m + 1) → K)) (convTail K c) =
      convTail K (substConv (L' : (Fin m → K) →L[K] (Fin m → K)) c) := by
  refine Conv.ext_of_evalSeries_eventuallyEq ?_
  have htail : Tendsto (Fin.tail : (Fin (m + 1) → K) → (Fin m → K)) (𝓝 0) (𝓝 0) := by
    have : Continuous (Fin.tail : (Fin (m + 1) → K) → (Fin m → K)) :=
      continuous_pi fun j => continuous_apply j.succ
    have h0 := this.tendsto 0
    rwa [show Fin.tail (0 : Fin (m + 1) → K) = 0 from rfl] at h0
  have h1 := evalSeries_substConv ((consCLE L' : (Fin (m + 1) → K) ≃L[K] (Fin (m + 1) → K)) :
    (Fin (m + 1) → K) →L[K] (Fin (m + 1) → K)) (convTail K c)
  have h2 := (evalSeries_substConv (L' : (Fin m → K) →L[K] (Fin m → K)) c).comp_tendsto htail
  refine h1.trans ?_
  filter_upwards [h2] with x hx
  simp only [Function.comp_apply] at hx
  change evalSeries (convTail K c : MvPowerSeries (Fin (m + 1)) K) (consCLE L' x) =
    evalSeries (convTail K (substConv (L' : (Fin m → K) →L[K] (Fin m → K)) c) :
      MvPowerSeries (Fin (m + 1)) K) x
  rw [coe_convTail, coe_convTail, evalSeries_liftTail, evalSeries_liftTail, tail_consCLE]
  exact hx.symm

/-! ### Noether normalization -/

variable (K) in
/-- The normalization map `𝒪_d → 𝒪_n → 𝒪_n → 𝒪_n / I`: embed along the injection `e` of the
coordinates (`convEmbed K e`), substitute the linear change `L` (`substEquiv L`), reduce modulo
`I`. The abbreviation unfolds definitionally to this composite. -/
noncomputable def normMap (I : Ideal (Conv K n)) (e : Fin d ↪ Fin n)
    (L : (Fin n → K) ≃L[K] (Fin n → K)) : Conv K d →ₐ[K] Conv K n ⧸ I :=
  (Ideal.Quotient.mkₐ K I).comp ((substEquiv L).toAlgHom.comp (convEmbed K e))

/-- `normMap K I e L c = [substEquiv L (convEmbed K e c)]`. -/
theorem normMap_apply (I : Ideal (Conv K n)) (e : Fin d ↪ Fin n)
    (L : (Fin n → K) ≃L[K] (Fin n → K)) (c : Conv K d) :
    normMap K I e L c = Ideal.Quotient.mk I (substEquiv L (convEmbed K e c)) := rfl

/-- Embedding along the identity injection is the identity. -/
theorem convEmbed_refl (c : Conv K n) : convEmbed K (Function.Embedding.refl (Fin n)) c = c := by
  apply Subtype.ext
  rw [coe_convEmbed]
  exact rename_id_apply _

/-- The tail embedding `convTail` is the case `e = Fin.succ` of `convEmbed`. -/
theorem convEmbed_succ (c : Conv K m) :
    convEmbed K ⟨Fin.succ, Fin.succ_injective m⟩ c = convTail K c :=
  Subtype.ext (by rw [coe_convEmbed, coe_convTail]; rfl)

/-- The tail embedding of an embedding along `e` is the embedding along `Fin.succ ∘ e`
(`convEmbed_succ` composed with the renaming along `e`). -/
theorem convTail_convEmbed (e : Fin d ↪ Fin m) (c : Conv K d) :
    convTail K (convEmbed K e c) = convEmbed K (e.trans ⟨Fin.succ, Fin.succ_injective m⟩) c := by
  apply Subtype.ext
  rw [coe_convTail, coe_convEmbed, coe_convEmbed]
  change rename Fin.succ (rename e (c : MvPowerSeries (Fin d) K)) =
    rename (Fin.succ ∘ e) (c : MvPowerSeries (Fin d) K)
  rw [rename_rename]

/-- The case `I = 0` of [Fre17, Ch. I, 7.2]: for the zero ideal, `d = n` with the identity
injection and the identity linear change, `𝒪_n → 𝒪_n / 0` being an isomorphism. -/
theorem exists_normMap_bot (I : Ideal (Conv K n)) (hI : I = ⊥) :
    ∃ (d : ℕ) (e : Fin d ↪ Fin n) (L : (Fin n → K) ≃L[K] (Fin n → K)),
      Function.Injective (normMap K I e L) ∧
        RingHom.Finite (A := Conv K d) (B := Conv K n ⧸ I)
          (normMap K I e L : Conv K d →+* Conv K n ⧸ I) := by
  subst hI
  refine ⟨n, Function.Embedding.refl _, ContinuousLinearEquiv.refl K _, ?_, ?_⟩
  · have hmk : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal (Conv K n))) :=
      (RingHom.injective_iff_ker_eq_bot _).mpr Ideal.mk_ker
    intro c c' h
    rw [normMap_apply, normMap_apply, convEmbed_refl, convEmbed_refl] at h
    have := hmk h
    simpa [substEquiv_apply, substConv_id] using this
  · refine RingHom.Finite.of_surjective _ fun q => ?_
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨c, ?_⟩
    change normMap K ⊥ _ _ c = _
    rw [normMap_apply, convEmbed_refl]
    simp [substEquiv_apply, substConv_id]

/-- Noether normalization for analytic algebras, existence clause [Fre17, Ch. I, Theorem 7.2]
(the source works over `ℂ`; the proof here is over any `K` with `[RCLike K]`): for a proper ideal
`I ⊆ 𝒪_n` there are `d`, an injection `e : Fin d ↪ Fin n` and a linear change `L` with the
normalization map `𝒪_d → 𝒪_n / I` (`normMap K I e L`) injective and finite. Induction on `n` by
repeated application of Lemma 7.1 (`finite_mk_comp_convTail`) after the `z_n`-general reduction
(`exists_substEquiv_isRegularIn`), with `RingHom.kerLift` for the induced map on `𝒪_{n-1} / b`,
`RingHom.Finite.comp` for the transitivity of finiteness, and `Ideal.quotientEquiv` to transport
back along `L⁻¹`. -/
theorem exists_noetherNormalization_analytic {n : ℕ} (I : Ideal (Conv K n)) (hI : I ≠ ⊤) :
    ∃ (d : ℕ) (e : Fin d ↪ Fin n) (L : (Fin n → K) ≃L[K] (Fin n → K)),
      Function.Injective (normMap K I e L) ∧
        RingHom.Finite (A := Conv K d) (B := Conv K n ⧸ I)
          (normMap K I e L : Conv K d →+* Conv K n ⧸ I) := by
  induction n with
  | zero =>
    apply exists_normMap_bot
    by_contra hne
    obtain ⟨f, hfI, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact hI (I.eq_top_of_isUnit_mem hfI (isUnit_of_ne_zero_conv_zero hf0))
  | succ m ih =>
    by_cases hbot : I = ⊥
    · exact exists_normMap_bot I hbot
    obtain ⟨f, hfI, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨L, hreg⟩ := exists_substEquiv_isRegularIn hf0
    obtain ⟨σ, hσ⟩ : ∃ σ : Conv K (m + 1) ≃+* Conv K (m + 1), σ = (substEquiv L).toRingEquiv :=
      ⟨_, rfl⟩
    have hσapp : ∀ x, σ x = substEquiv L x := fun x => by rw [hσ]; rfl
    obtain ⟨I', hI'def⟩ : ∃ I' : Ideal (Conv K (m + 1)),
        I' = I.map (σ : Conv K (m + 1) →+* Conv K (m + 1)) := ⟨_, rfl⟩
    have hI' : I' ≠ ⊤ := by
      rw [hI'def, Ideal.map_comap_of_equiv]
      exact Ideal.comap_ne_top _ hI
    have hPI : substEquiv L f ∈ I' := by
      rw [hI'def, ← hσapp]
      exact Ideal.mem_map_of_mem _ hfI
    obtain ⟨g, hgdef⟩ : ∃ g : Conv K m →+* Conv K (m + 1) ⧸ I',
        g = (Ideal.Quotient.mk I').comp (convTail K).toRingHom := ⟨_, rfl⟩
    have hg : RingHom.Finite (A := Conv K m) (B := Conv K (m + 1) ⧸ I') g := by
      rw [hgdef]
      exact finite_mk_comp_convTail hPI hreg
    have : Nontrivial (Conv K (m + 1) ⧸ I') := Ideal.Quotient.nontrivial_iff.mpr hI'
    have hJ : RingHom.ker g ≠ ⊤ := RingHom.ker_ne_top g
    obtain ⟨d, e', L', hinj', hfin'⟩ := ih (RingHom.ker g) hJ
    have hkl : ((RingHom.kerLift g).comp (Ideal.Quotient.mk (RingHom.ker g))) = g :=
      RingHom.ext fun x => RingHom.kerLift_mk g x
    have hkl' : RingHom.Finite (A := Conv K m) (B := Conv K (m + 1) ⧸ I')
        ((RingHom.kerLift g).comp (Ideal.Quotient.mk (RingHom.ker g))) := by
      rw [hkl]
      exact hg
    have hklfin : RingHom.Finite (A := Conv K m ⧸ RingHom.ker g) (B := Conv K (m + 1) ⧸ I')
        (RingHom.kerLift g) := RingHom.Finite.of_comp_finite hkl'
    -- the total map on `Conv K d`
    set eT : Fin d ↪ Fin (m + 1) := e'.trans ⟨Fin.succ, Fin.succ_injective m⟩ with heT
    set LT : (Fin (m + 1) → K) ≃L[K] (Fin (m + 1) → K) := L.symm.trans (consCLE L') with hLT
    have hLTL : ((LT : (Fin (m + 1) → K) →L[K] (Fin (m + 1) → K)) ∘L
        (L : (Fin (m + 1) → K) →L[K] (Fin (m + 1) → K))) =
        ((consCLE L' : (Fin (m + 1) → K) ≃L[K] (Fin (m + 1) → K)) :
          (Fin (m + 1) → K) →L[K] (Fin (m + 1) → K)) := by
      ext x
      simp [hLT]
    have hqe : I' = I.map (σ : Conv K (m + 1) →+* Conv K (m + 1)) := hI'def
    have key : ∀ c : Conv K d, (RingHom.kerLift g) (normMap K (RingHom.ker g) e' L' c) =
        Ideal.quotientEquiv I I' σ hqe (normMap K I eT LT c) := by
      intro c
      rw [normMap_apply, RingHom.kerLift_mk, hgdef, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, normMap_apply, Ideal.quotientEquiv_mk, hσapp]
      congr 1
      rw [substEquiv_apply, substEquiv_apply, ← substConv_consCLE_convTail, convTail_convEmbed,
        substEquiv_apply, substConv_substConv, hLTL]
    have hTinj : Function.Injective ((RingHom.kerLift g).comp (normMap K (RingHom.ker g) e' L' :
        Conv K d →+* Conv K m ⧸ RingHom.ker g)) :=
      (RingHom.kerLift_injective g).comp hinj'
    have hTfin : RingHom.Finite (A := Conv K d) (B := Conv K (m + 1) ⧸ I')
        ((RingHom.kerLift g).comp (normMap K (RingHom.ker g) e' L' :
          Conv K d →+* Conv K m ⧸ RingHom.ker g)) := hklfin.comp hfin'
    have hT : ((RingHom.kerLift g).comp (normMap K (RingHom.ker g) e' L' :
        Conv K d →+* Conv K m ⧸ RingHom.ker g)) =
        ((Ideal.quotientEquiv I I' σ hqe : Conv K (m + 1) ⧸ I →+* Conv K (m + 1) ⧸ I').comp
          (normMap K I eT LT : Conv K d →+* Conv K (m + 1) ⧸ I)) :=
      RingHom.ext fun c => key c
    refine ⟨d, eT, LT, ?_, ?_⟩
    · have := hTinj
      rw [hT, RingHom.coe_comp] at this
      exact Function.Injective.of_comp this
    · have h2 : (normMap K I eT LT : Conv K d →+* Conv K (m + 1) ⧸ I) =
          ((Ideal.quotientEquiv I I' σ hqe).symm : Conv K (m + 1) ⧸ I' →+* Conv K (m + 1) ⧸ I).comp
            ((RingHom.kerLift g).comp (normMap K (RingHom.ker g) e' L' :
              Conv K d →+* Conv K m ⧸ RingHom.ker g)) := by
        rw [hT]
        ext c
        exact (RingEquiv.symm_apply_apply (Ideal.quotientEquiv I I' σ hqe)
          (normMap K I eT LT c)).symm
      have hes : RingHom.Finite (A := Conv K (m + 1) ⧸ I') (B := Conv K (m + 1) ⧸ I)
          ((Ideal.quotientEquiv I I' σ hqe).symm : Conv K (m + 1) ⧸ I' →+* Conv K (m + 1) ⧸ I) :=
        RingHom.Finite.of_surjective _ (Ideal.quotientEquiv I I' σ hqe).symm.surjective
      have hcomp := RingHom.Finite.comp hes hTfin
      rw [← h2] at hcomp
      exact hcomp

end Analytic
