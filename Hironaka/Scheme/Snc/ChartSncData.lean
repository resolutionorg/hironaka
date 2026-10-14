/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.TotalTransformData
public import Hironaka.Scheme.Smooth.ChartDefs
import Hironaka.Scheme.Smooth.ChartEtale
import Hironaka.Scheme.Smooth.StandardChart
import Hironaka.Scheme.Snc.Coordinates
import Hironaka.Scheme.Snc.EtaleParameters
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The total transform in the chart coordinates

Hauser's computation (the proof of [Hau14, Proposition 5.3]; [Hau14, Proposition 5.4 (6)–(7)];
[Hau03, Appendix C]): on the chart of `x_j` of the blow-up of `Z = (x_1 = ⋯ = x_r = 0)`, the chart
functions are `y_i = x_i/x_j` for `i < r`, `i ≠ j`, and `y_i = x_i` otherwise
[Kol07, Definition 60]; the exceptional divisor is `(y_j)`, a component `(x_c = 0)` containing the
centre has total transform `(x_c) = (y_c y_j)` — or `(y_j)` when `c = j` — and a transversal
component `(x_c = 0)` has total transform `(y_c)`. At a point `p` of the chart the chart functions
are étale coordinates (`Hironaka.Scheme.Smooth.ChartEtale`), so by
`Hironaka.Scheme.Snc.EtaleParameters` the local ring is regular and the chart functions vanishing at
`p` are part of a regular system of parameters; a chart function not vanishing at `p` is a unit
there. Reading the total transforms through this regular system of parameters gives exactly the four
shapes of `TotalTransformData`.

**Why the lemma holds.** In the chart ring `Γ(U)[J/x_j]` one has `x_i = y_i · x_j` for `i < r`
(`algebraMap_eq_ratio_mul`) and `x_j = y_j`; the ideal `J Γ(U)[J/x_j]` is `(x_j)`. Localizing at
`p`, a coordinate `y_c ∈ p` becomes the parameter `z_{σ c}`, a coordinate `y_c ∉ p` a unit:
`(y_c y_j)` is `(z_{σ c} z_{σ j})` or `(z_{σ j})`, `(y_c)` is `(z_{σ c})` or `(1)`. The indices
`σ c` are distinct and differ from `σ j` for `c ≠ j`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal affineBlowUpAlgebra

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n r : ℕ}
  {Z : X.IdealSheafData} {x₀ : X} (E : EtaleCoordinatesAdapted f n r Z x₀) {j : Fin n}
  (hj : j.val < r)

/-- The chart functions `y_i = x_i/x_j` (`i < r`, `i ≠ j`) and `y_i = x_i` (otherwise) of the chart
of `x_j` [Kol07, Definition 60], as in `etale_aeval_chartCoordinates`. -/
noncomputable def chartCoord : Fin n → affineBlowUpAlgebra E.centerIdeal (E.coord j hj) :=
  fun i => if h : i.val < r ∧ i ≠ j then
    (ratio E.centerIdeal (E.coord j hj) (E.coord i h.1) :
      affineBlowUpAlgebra E.centerIdeal (E.v j))
  else algebraMap Γ(X, E.U) _ (E.v i)

theorem chartCoord_self : chartCoord E hj j = algebraMap Γ(X, E.U) _ (E.v j) := by
  simp [chartCoord]

theorem chartCoord_of_not_lt {i : Fin n} (hi : ¬ i.val < r) :
    chartCoord E hj i = algebraMap Γ(X, E.U) _ (E.v i) := by
  simp [chartCoord, hi]

/-- `x_i = y_i y_j` in the chart of `x_j`, for `i < r`, `i ≠ j` [Kol07, Definition 60]. -/
theorem algebraMap_v_eq_chartCoord_mul {i : Fin n} (hi : i.val < r) (hij : i ≠ j) :
    algebraMap Γ(X, E.U) (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) (E.v i) =
      chartCoord E hj i * chartCoord E hj j := by
  rw [chartCoord_self, algebraMap_eq_ratio_mul E hj hi]
  simp [chartCoord, hi, hij]

/-- The chart functions are étale coordinates of the chart ring over `k` (the `k`-algebra structures
through `f`). -/
theorem etale_aeval_chartCoord :
    letI := f.sectionsAlgebra E.U.1
    letI : Algebra k (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) :=
      ((algebraMap Γ(X, E.U) _).comp (algebraMap k Γ(X, E.U))).toAlgebra
    (MvPolynomial.aeval (R := k) (chartCoord E hj)).toRingHom.Etale :=
  etale_aeval_chartCoordinates E hj

section Shape

variable (q : Ideal (affineBlowUpAlgebra E.centerIdeal (E.coord j hj))) [q.IsPrime]

/-- The chart computation (the proof of [Hau14, Proposition 5.3]; [Hau14, Proposition 5.4 (6)–(7)];
[Hau03, Appendix C]): at a prime `q` of the chart ring of `x_j` lying on the exceptional divisor
(`y_j ∈ q`), for a family of ideal sheaves `D i` of `X` whose members through `x₀` are the
coordinate hyperplanes `(x_{c' i} = 0)` on the chart (`c'` injective) and whose other members miss
the chart, the exceptional ideal `(x_j)` and the total transforms `(x_{c' i})` (and `(1)`), extended
to the local ring at `q`, have the shape `TotalTransformData`: the local ring is regular with a
regular system of parameters containing the vanishing chart functions, `F = (y_j)`, and each total
transform is `(y_c y_j)`, `(y_c)`, `(y_j)` or `(1)`. -/
theorem totalTransformData_chart (hjq : chartCoord E hj j ∈ q) {ι : Type*}
    (D : ι → X.IdealSheafData) (c' : {i : ι // x₀ ∈ (D i).support} → Fin n)
    (hc'inj : Function.Injective c') (T : ι → Ideal (Localization.AtPrime q))
    (hT : ∀ i (h : x₀ ∈ (D i).support), T i = span {algebraMap
      (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) (Localization.AtPrime q)
      (algebraMap Γ(X, E.U) (affineBlowUpAlgebra E.centerIdeal (E.coord j hj))
        (E.v (c' ⟨i, h⟩)))})
    (hT' : ∀ i, x₀ ∉ (D i).support → T i = ⊤) :
    TotalTransformData (span {algebraMap (affineBlowUpAlgebra E.centerIdeal (E.coord j hj))
      (Localization.AtPrime q)
      (algebraMap Γ(X, E.U) (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) (E.v j))}) T ∧
    ∀ i (h : x₀ ∈ (D i).support), T i ≤ span {algebraMap
      (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) (Localization.AtPrime q)
      (algebraMap Γ(X, E.U) (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) (E.v j))} →
      (c' ⟨i, h⟩).val < r := by
  classical
  let _ := f.sectionsAlgebra E.U.1
  let _ : Algebra k (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) :=
    ((algebraMap Γ(X, E.U) _).comp (algebraMap k Γ(X, E.U))).toAlgebra
  have hy : (MvPolynomial.aeval (R := k) (chartCoord E hj)).toRingHom.Etale :=
    etale_aeval_chartCoord E hj
  have hex := exists_span_eq_maximalIdeal_of_etale_coordinates (chartCoord E hj) hy q
  obtain ⟨hreg, m, z, hz, σ, hσinj, hσ⟩ := hex
  let alg := algebraMap (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)) (Localization.AtPrime q)
  have hunit : ∀ c : Fin n, chartCoord E hj c ∉ q → IsUnit (alg (chartCoord E hj c)) := fun c hc =>
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).mpr hc
  let j' : Fin m := σ ⟨j, hjq⟩
  let a : ι → Fin m := fun i =>
    if h : x₀ ∈ (D i).support then
      if hq : chartCoord E hj (c' ⟨i, h⟩) ∈ q then σ ⟨c' ⟨i, h⟩, hq⟩ else j'
    else j'
  have ha_of : ∀ i (h : x₀ ∈ (D i).support) (hq : chartCoord E hj (c' ⟨i, h⟩) ∈ q),
      a i = σ ⟨c' ⟨i, h⟩, hq⟩ := fun i h hq => by
    change (if h : x₀ ∈ (D i).support then
      (if hq : chartCoord E hj (c' ⟨i, h⟩) ∈ q then σ ⟨c' ⟨i, h⟩, hq⟩ else j') else j') = _
    rw [dite_eq_left h, dite_eq_left hq]
  have ha_of_not : ∀ i (h : x₀ ∈ (D i).support), chartCoord E hj (c' ⟨i, h⟩) ∉ q → a i = j' :=
    fun i h hq => by
      change (if h : x₀ ∈ (D i).support then
        (if hq : chartCoord E hj (c' ⟨i, h⟩) ∈ q then σ ⟨c' ⟨i, h⟩, hq⟩ else j') else j') = _
      rw [dite_eq_left h, dite_eq_right hq]
  have ha_notMem : ∀ i, x₀ ∉ (D i).support → a i = j' := fun i h => by
    change (if h : x₀ ∈ (D i).support then
      (if hq : chartCoord E hj (c' ⟨i, h⟩) ∈ q then σ ⟨c' ⟨i, h⟩, hq⟩ else j') else j') = _
    rw [dite_eq_right h]
  have ha_not : ∀ i, a i ≠ j' → ∃ (h : x₀ ∈ (D i).support) (hq : chartCoord E hj (c' ⟨i, h⟩) ∈ q),
      c' ⟨i, h⟩ ≠ j ∧ a i = σ ⟨c' ⟨i, h⟩, hq⟩ := by
    intro i hi
    by_cases h : x₀ ∈ (D i).support
    · by_cases hq : chartCoord E hj (c' ⟨i, h⟩) ∈ q
      · refine ⟨h, hq, fun hcj => hi ?_, ha_of i h hq⟩
        rw [ha_of i h hq]
        exact congrArg σ (Subtype.ext hcj)
      · exact absurd (ha_of_not i h hq) hi
    · exact absurd (ha_notMem i h) hi
  have hzj' : z j' = alg (chartCoord E hj j) := hσ ⟨j, hjq⟩
  -- `(x_j)` read in the localization is `(z_{j'})`
  have hF : span {alg (algebraMap Γ(X, E.U) _ (E.v j))} = span {z j'} :=
    (congrArg (fun t => span {alg t}) (chartCoord_self E hj).symm).trans
      (congrArg (fun t => span {t}) hzj'.symm)
  -- a component whose total transform lies in `(y_j)` has a coordinate `< r` (it contains `Z`)
  have hle : ∀ i (h : x₀ ∈ (D i).support),
      T i ≤ span {alg (algebraMap Γ(X, E.U) _ (E.v j))} → (c' ⟨i, h⟩).val < r := by
    intro i h hTle
    by_contra hlt
    have hTi : T i = span {alg (chartCoord E hj (c' ⟨i, h⟩))} :=
      (hT i h).trans (congrArg (fun t => span {alg t}) (chartCoord_of_not_lt E hj hlt).symm)
    have hTle' : span {alg (chartCoord E hj (c' ⟨i, h⟩))} ≤ span {z j'} :=
      hTi.symm.le.trans (hTle.trans hF.le)
    by_cases hq : chartCoord E hj (c' ⟨i, h⟩) ∈ q
    · have hcj : c' ⟨i, h⟩ ≠ j := fun hcj => hlt (hcj ▸ hj)
      have hne : σ ⟨c' ⟨i, h⟩, hq⟩ ≠ j' := fun heq =>
        hcj (congrArg Subtype.val (hσinj heq))
      have hmem : z (σ ⟨c' ⟨i, h⟩, hq⟩) ∈ span {z j'} :=
        (hσ ⟨_, hq⟩).symm ▸ hTle' (mem_span_singleton_self _)
      exact notMem_span_singleton_of_ne hz.1 hz.2 hne.symm hmem
    · have hu := hunit _ hq
      have htop : span {alg (chartCoord E hj (c' ⟨i, h⟩))} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
      have hle' : (⊤ : Ideal (Localization.AtPrime q)) ≤ span {z j'} := htop.symm.le.trans hTle'
      have hunit' : IsUnit (z j') := Ideal.span_singleton_eq_top.mp (top_le_iff.mp hle')
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
        (mem_maximalIdeal_and_notMem_sq_of_span_eq hz j').1) hunit'
  refine ⟨⟨hreg, m, z, hz, j', a, hF, ?_, ?_⟩, hle⟩
  · -- injectivity off `j'`
    intro i i' hi hi' heq
    have hi₁ := ha_not i hi
    have hi₂ := ha_not i' hi'
    obtain ⟨h, hq, -, ha⟩ := hi₁
    obtain ⟨h', hq', -, ha'⟩ := hi₂
    have heq' : σ ⟨c' ⟨i, h⟩, hq⟩ = σ ⟨c' ⟨i', h'⟩, hq'⟩ := ha.symm.trans (heq.trans ha')
    have := congrArg Subtype.val (hσinj heq')
    exact congrArg Subtype.val (hc'inj this)
  · -- the four shapes
    intro i
    by_cases h : x₀ ∈ (D i).support
    · have hTi := hT i h
      by_cases hcj : c' ⟨i, h⟩ = j
      · -- the component of the chart coordinate
        rw [hcj] at hTi
        exact Or.inr (Or.inl (hTi.trans hF))
      · by_cases hq : chartCoord E hj (c' ⟨i, h⟩) ∈ q
        · have ha : a i = σ ⟨c' ⟨i, h⟩, hq⟩ := ha_of i h hq
          have hne : a i ≠ j' := fun heq => by
            have heq' : σ ⟨c' ⟨i, h⟩, hq⟩ = σ ⟨j, hjq⟩ := ha.symm.trans heq
            exact hcj (congrArg Subtype.val (hσinj heq'))
          have hz' : z (a i) = alg (chartCoord E hj (c' ⟨i, h⟩)) :=
            (congrArg z ha).trans (hσ ⟨_, hq⟩)
          by_cases hlt : (c' ⟨i, h⟩).val < r
          · refine Or.inl ⟨hne, Or.inl (hTi.trans ?_)⟩
            exact (congrArg (fun t => span {alg t})
              (algebraMap_v_eq_chartCoord_mul E hj hlt hcj)).trans
              ((congrArg (fun t => span {t}) (map_mul alg _ _)).trans
                (congrArg (fun t => span {t}) (congrArg₂ (· * ·) hz'.symm hzj'.symm)))
          · refine Or.inl ⟨hne, Or.inr (hTi.trans ?_)⟩
            exact (congrArg (fun t => span {alg t}) (chartCoord_of_not_lt E hj hlt).symm).trans
              (congrArg (fun t => span {t}) hz'.symm)
        · have hu := hunit _ hq
          by_cases hlt : (c' ⟨i, h⟩).val < r
          · refine Or.inr (Or.inl (hTi.trans ?_))
            exact (congrArg (fun t => span {alg t})
              (algebraMap_v_eq_chartCoord_mul E hj hlt hcj)).trans
              ((congrArg (fun t => span {t}) (map_mul alg _ _)).trans
                ((Ideal.span_singleton_mul_left_unit hu _).trans
                  (congrArg (fun t => span {t}) hzj'.symm)))
          · refine Or.inr (Or.inr (hTi.trans ?_))
            exact (congrArg (fun t => span {alg t}) (chartCoord_of_not_lt E hj hlt).symm).trans
              (Ideal.span_singleton_eq_top.mpr hu)
    · exact Or.inr (Or.inr (hT' i h))

end Shape

end AlgebraicGeometry
