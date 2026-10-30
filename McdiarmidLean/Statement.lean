/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import McdiarmidLean.Induction
public import McdiarmidLean.JointLaw

/-!
# McDiarmid's bounded-differences inequality: public statements

Reference: S. Boucheron, G. Lugosi and P. Massart (2013), *Concentration Inequalities: A
Nonasymptotic Theory of Independence*, Oxford University Press, Theorem 6.2.

Let `ι` be a finite index type and `X` be a measurable space. The coordinate
laws `μ i` are probability measures on `X` and may differ across `i`. The statistic
`F : (ι → X) → ℝ` is measurable and has bounded differences with constants `c i`: whenever two
points `x` and `y` agree off coordinate `i`, `|F x - F y| ≤ c i`.

For each `t > 0`, writing `S = Σᵢ cᵢ²`, the library proves the following bounds:

* upper tail: `P{F ≥ E F + t} ≤ exp(-2t²/S)` (`mcdiarmid_upper_tail_pi`);
* lower tail: `P{F ≤ E F - t} ≤ exp(-2t²/S)` (`mcdiarmid_lower_tail_pi`);
* two-sided: `P{|F - E F| ≥ t} ≤ 2 exp(-2t²/S)` (`mcdiarmid_two_sided_pi`);
* the same three bounds for independent random variables `Xv i : Ω → X` under a probability
  measure (`mcdiarmid_upper_tail`, `mcdiarmid_lower_tail`, `mcdiarmid_two_sided`).

If `S = 0`, Lean's convention `x / 0 = 0` makes the bound `exp 0 = 1` (or
`2` in the two-sided case), and the statements remain true because probabilities are at most
`1`. This covers an empty index type. If `ι` is nonempty, the hypotheses force `X` to be
nonempty because a probability measure has total mass one, so no `Nonempty X` assumption
appears in the statements.

The module `McdiarmidLean.Induction` establishes the moment generating function bound by
induction over coordinates using Fubini's theorem and Hoeffding's lemma from mathlib.
The resulting `HasSubgaussianMGF` statement implies the upper-tail bound through mathlib's
Chernoff inequality. Applying this bound to `-F` yields the lower-tail bound, and a union
bound yields the two-sided result. Equality of the joint law and the product of the
marginal laws establishes the corresponding results for independent random variables.
-/

public section

open MeasureTheory ProbabilityTheory

namespace McdiarmidLean

/-! ## Product-measure form -/

section Product

variable {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]

/-- **McDiarmid's inequality, upper tail, product-measure form.** For independent coordinates
with laws `μ i` (possibly different), a measurable `F` with bounded differences `c`, and
`t > 0`: `P{F ≥ E F + t} ≤ exp(-2t²/Σᵢ cᵢ²)`. If `Σᵢ cᵢ² = 0` the right side is `1`. -/
theorem mcdiarmid_upper_tail_pi (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : BoundedDiff F c)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | (∫ y, F y ∂(Measure.pi μ)) + t ≤ F x}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) :=
  Induction.upper_tail_pi μ F c hFm hF t ht

/-- **McDiarmid's inequality, lower tail, product-measure form.** For independent coordinates
with laws `μ i` (possibly different), a measurable `F` with bounded differences `c`, and
`t > 0`: `P{F ≤ E F - t} ≤ exp(-2t²/Σᵢ cᵢ²)`. If `Σᵢ cᵢ² = 0` the right side is `1`. -/
theorem mcdiarmid_lower_tail_pi (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : BoundedDiff F c)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | F x ≤ (∫ y, F y ∂(Measure.pi μ)) - t}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) :=
  Induction.lower_tail_pi μ F c hFm hF t ht

/-- **McDiarmid's inequality, two-sided, product-measure form.**
`P{|F - E F| ≥ t} ≤ 2 exp(-2t²/Σᵢ cᵢ²)`. If `Σᵢ cᵢ² = 0` the right side is `2`. -/
theorem mcdiarmid_two_sided_pi (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : BoundedDiff F c)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ |F x - ∫ y, F y ∂(Measure.pi μ)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) := by
  set E := ∫ y, F y ∂(Measure.pi μ)
  set b := Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)
  have hsub : {x | t ≤ |F x - E|} ⊆ {x | E + t ≤ F x} ∪ {x | F x ≤ E - t} := by
    intro x hx
    rcases le_abs'.1 (show t ≤ |F x - E| from hx) with h | h
    · exact Or.inr (by change F x ≤ E - t; linarith)
    · exact Or.inl (by change E + t ≤ F x; linarith)
  calc Measure.pi μ {x | t ≤ |F x - E|}
      ≤ Measure.pi μ ({x | E + t ≤ F x} ∪ {x | F x ≤ E - t}) := measure_mono hsub
    _ ≤ Measure.pi μ {x | E + t ≤ F x} + Measure.pi μ {x | F x ≤ E - t} := measure_union_le _ _
    _ ≤ ENNReal.ofReal b + ENNReal.ofReal b :=
        add_le_add (mcdiarmid_upper_tail_pi μ F c hFm hF t ht)
          (mcdiarmid_lower_tail_pi μ F c hFm hF t ht)
    _ = ENNReal.ofReal (2 * b) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
        congr 1
        ring

end Product

/-! ## Random-variable form -/

section RandomVariables

variable {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
  {Ω : Type*} [MeasurableSpace Ω]

/-- A statistic of independent random variables has centered sub-Gaussian MGF
with variance proxy `Σᵢ cᵢ² / 4`. The coordinate laws may differ. -/
theorem hasSubgaussianMGF_boundedDiff (P : Measure Ω) [IsProbabilityMeasure P]
    (Xv : ι → Ω → X) (hXm : ∀ i, Measurable (Xv i)) (hind : iIndepFun Xv P)
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F) (hF : BoundedDiff F c) :
    HasSubgaussianMGF (fun ω => F (fun i => Xv i ω) - ∫ ω', F (fun i => Xv i ω') ∂P)
      ⟨(∑ i, c i ^ 2) / 4,
        div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (c i)) (by norm_num)⟩ P := by
  rw [JointLaw.integral_vec hXm hind hFm]
  apply HasSubgaussianMGF.of_map (μ := P)
    (X := fun x => F x - ∫ y, F y ∂Measure.pi (fun i => P.map (Xv i)))
    (JointLaw.measurable_vec hXm).aemeasurable
  rw [JointLaw.map_vec_eq_pi hXm hind]
  exact hasSubgaussianMGF_boundedDiff_pi _ F c hFm hF

/-- **McDiarmid's inequality, upper tail, random-variable form.** For independent random
variables `Xv i : Ω → X` (possibly not identically distributed) under a probability measure
`P`, a measurable `F` with bounded differences `c`, and `t > 0`:
`P{F(Xv) ≥ E F(Xv) + t} ≤ exp(-2t²/Σᵢ cᵢ²)`. -/
theorem mcdiarmid_upper_tail (P : Measure Ω) [IsProbabilityMeasure P] (Xv : ι → Ω → X)
    (hXm : ∀ i, Measurable (Xv i)) (hind : iIndepFun Xv P)
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : BoundedDiff F c)
    (t : ℝ) (ht : 0 < t) :
    P {ω | (∫ ω', F (fun i => Xv i ω') ∂P) + t ≤ F (fun i => Xv i ω)}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) := by
  rw [JointLaw.integral_vec hXm hind hFm]
  exact (JointLaw.prob_vec hXm hind (measurableSet_le measurable_const hFm)).trans_le
    (mcdiarmid_upper_tail_pi _ F c hFm hF t ht)

/-- **McDiarmid's inequality, lower tail, random-variable form.**
`P{F(Xv) ≤ E F(Xv) - t} ≤ exp(-2t²/Σᵢ cᵢ²)`. -/
theorem mcdiarmid_lower_tail (P : Measure Ω) [IsProbabilityMeasure P] (Xv : ι → Ω → X)
    (hXm : ∀ i, Measurable (Xv i)) (hind : iIndepFun Xv P)
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : BoundedDiff F c)
    (t : ℝ) (ht : 0 < t) :
    P {ω | F (fun i => Xv i ω) ≤ (∫ ω', F (fun i => Xv i ω') ∂P) - t}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) := by
  rw [JointLaw.integral_vec hXm hind hFm]
  exact (JointLaw.prob_vec hXm hind (measurableSet_le hFm measurable_const)).trans_le
    (mcdiarmid_lower_tail_pi _ F c hFm hF t ht)

/-- **McDiarmid's inequality, two-sided, random-variable form.**
`P{|F(Xv) - E F(Xv)| ≥ t} ≤ 2 exp(-2t²/Σᵢ cᵢ²)`. -/
theorem mcdiarmid_two_sided (P : Measure Ω) [IsProbabilityMeasure P] (Xv : ι → Ω → X)
    (hXm : ∀ i, Measurable (Xv i)) (hind : iIndepFun Xv P)
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : BoundedDiff F c)
    (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ |F (fun i => Xv i ω) - ∫ ω', F (fun i => Xv i ω') ∂P|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) := by
  rw [JointLaw.integral_vec hXm hind hFm]
  exact (JointLaw.prob_vec hXm hind
      (measurableSet_le measurable_const
        (continuous_abs.measurable.comp (hFm.sub_const _)))).trans_le
    (mcdiarmid_two_sided_pi _ F c hFm hF t ht)

end RandomVariables

end McdiarmidLean
