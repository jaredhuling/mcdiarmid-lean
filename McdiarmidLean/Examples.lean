/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import McdiarmidLean.Statement

/-!
# Examples of the bounded-differences inequality

These examples apply the library results to Bernoulli coordinates, strict tail events,
zero coordinate bounds, and empty products.
-/

public section

open MeasureTheory ProbabilityTheory

namespace McdiarmidLean.Examples

/-- One coordinate and the indicator of a measurable set: bounded differences hold with
`c = 1`, so `P{1_A(x₀) ≥ P(A) + t} ≤ exp(-2t²)`. -/
example {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {A : Set X} (hA : MeasurableSet A) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin 1 => ν)
        {x | (∫ y, A.indicator 1 (y 0) ∂(Measure.pi fun _ : Fin 1 => ν)) + t
          ≤ A.indicator (1 : X → ℝ) (x 0)}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ _i : Fin 1, (1 : ℝ) ^ 2)) := by
  refine mcdiarmid_upper_tail_pi (fun _ => ν) (fun x => A.indicator 1 (x 0)) (fun _ => 1)
    ((measurable_one.indicator hA).comp (measurable_pi_apply 0)) ?_ t ht
  intro x y i _
  by_cases hx : x 0 ∈ A <;> by_cases hy : y 0 ∈ A <;> simp [hx, hy]

/-- The bound in the one-coordinate example is `exp(-2t²)`. -/
example (t : ℝ) : -(2 * t ^ 2) / ∑ _i : Fin 1, (1 : ℝ) ^ 2 = -2 * t ^ 2 := by
  simp

/-- Empty index type: `Σᵢ cᵢ² = 0`, so the bound is `ofReal (exp 0) = 1`. -/
example (c : Empty → ℝ) (t : ℝ) :
    ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) = 1 := by
  simp

-- The strict textbook upper-tail event follows from the stronger public closed event.
theorem strict_upper {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : McdiarmidLean.BoundedDiff F c) (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t < F x - ∫ y, F y ∂Measure.pi μ}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) := by
  apply le_trans (measure_mono (t := {x | (∫ y, F y ∂Measure.pi μ) + t ≤ F x}) ?_)
    (McdiarmidLean.mcdiarmid_upper_tail_pi μ F c hFm hF t ht)
  intro x hx
  change t < F x - _ at hx
  change _ + t ≤ F x
  linarith

-- Zero coordinate bounds imply that the statistic is constant and its centered tail is zero.
theorem zero_diff_tail {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (hF : McdiarmidLean.BoundedDiff F (fun _ => 0))
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ |F x - ∫ y, F y ∂Measure.pi μ|} = 0 := by
  have hne : Nonempty (ι → X) := nonempty_of_isProbabilityMeasure (Measure.pi μ)
  obtain ⟨x₀⟩ := hne
  have hconst : F = fun _ => F x₀ := by
    funext x
    have h := McdiarmidLean.Induction.abs_sub_le_sum hF x₀ x
    have hz : F x - F x₀ = 0 := by simpa using h
    exact sub_eq_zero.mp hz
  rw [hconst]
  simp [not_le.mpr ht]

-- Both coordinate and observation types may be empty; there is still one empty vector.
theorem empty_index_tail (F : (Empty → Empty) → ℝ) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun i : Empty => nomatch i)
      {x | t ≤ |F x - ∫ y, F y ∂Measure.pi (fun i : Empty => nomatch i)|} = 0 := by
  let : ∀ i : Empty, IsProbabilityMeasure (nomatch i : Measure Empty) := fun i => nomatch i
  have hconst : F = fun _ => F (fun i => nomatch i) := by
    funext x
    congr 1
    funext i
    exact i.elim
  rw [hconst]
  simp [not_le.mpr ht]

def bernoulliValue (b : Bool) : ℝ := if b then 1 else 0
lemma bernoulliValue_bounded (a b : Bool) : |bernoulliValue a - bernoulliValue b| ≤ 1 := by
  cases a <;> cases b <;> norm_num [bernoulliValue]

/-- A sum of two Bernoulli indicators has coordinate bounds one. -/
lemma bernoulli_sum_boundedDiff : McdiarmidLean.BoundedDiff
    (fun x : Fin 2 → Bool => bernoulliValue (x 0) + bernoulliValue (x 1)) (fun _ => 1) := by
  intro x y i hxy
  fin_cases i
  · have heq := hxy 1 (by decide)
    simpa only [heq, add_sub_add_right_eq_sub] using bernoulliValue_bounded (x 0) (y 0)
  · have heq := hxy 0 (by decide)
    simpa only [heq, add_sub_add_left_eq_sub] using bernoulliValue_bounded (x 1) (y 1)

-- A two-coordinate application with arbitrary, potentially different, marginal laws.
theorem two_bernoulli (μ : Fin 2 → Measure Bool) [∀ i, IsProbabilityMeasure (μ i)]
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | (∫ y, bernoulliValue (y 0) + bernoulliValue (y 1) ∂Measure.pi μ) + t
      ≤ bernoulliValue (x 0) + bernoulliValue (x 1)} ≤ ENNReal.ofReal (Real.exp (-t ^ 2)) := by
  have hm : Measurable (fun x : Fin 2 → Bool => bernoulliValue (x 0) + bernoulliValue (x 1)) := by
    fun_prop
  have hb := bernoulli_sum_boundedDiff
  have hs : -(2 * t ^ 2) / (∑ _i : Fin 2, (1 : ℝ) ^ 2) = -t ^ 2 := by
    norm_num [Fin.sum_univ_two]
    ring
  simpa only [hs] using McdiarmidLean.mcdiarmid_upper_tail_pi μ
    (fun x => bernoulliValue (x 0) + bernoulliValue (x 1)) (fun _ => 1) hm hb t ht


/-- The random-variable API applies to two independent Bernoulli variables with arbitrary laws. -/
theorem two_bernoulli_rv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Xv : Fin 2 → Ω → Bool)
    (hXm : ∀ i, Measurable (Xv i)) (hind : iIndepFun Xv P) (t : ℝ) (ht : 0 < t) :
    P {ω | (∫ ω', bernoulliValue (Xv 0 ω') + bernoulliValue (Xv 1 ω') ∂P) + t
      ≤ bernoulliValue (Xv 0 ω) + bernoulliValue (Xv 1 ω)}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2)) := by
  have hm : Measurable (fun x : Fin 2 → Bool => bernoulliValue (x 0) + bernoulliValue (x 1)) := by
    fun_prop
  have hs : -(2 * t ^ 2) / (∑ _i : Fin 2, (1 : ℝ) ^ 2) = -t ^ 2 := by
    norm_num [Fin.sum_univ_two]
    ring
  simpa only [hs] using McdiarmidLean.mcdiarmid_upper_tail P Xv hXm hind
    (fun x => bernoulliValue (x 0) + bernoulliValue (x 1)) (fun _ => 1)
    hm bernoulli_sum_boundedDiff t ht

/-- The centered MGF bound applies with a zero variance proxy. -/
example {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (F : (ι → X) → ℝ)
    (hFm : Measurable F) (hF : McdiarmidLean.BoundedDiff F (fun _ => 0)) :
    HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂Measure.pi μ) 0 (Measure.pi μ) := by
  have h := hasSubgaussianMGF_boundedDiff_pi μ F (fun _ => 0) hFm hF
  have hz : (⟨(∑ _i : ι, (0 : ℝ) ^ 2) / 4,
      div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg (0 : ℝ)) (by norm_num)⟩ : NNReal) = 0 := by
    ext
    simp
  rw [hz] at h
  exact h

end McdiarmidLean.Examples
