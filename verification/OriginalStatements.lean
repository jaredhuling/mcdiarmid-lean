/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import Lean
import McdiarmidLean

/-! # Regression checks for the original six tail-inequality theorem types

The expected elaborated types were frozen before the release refactor on 2026-10-30.
The check requires definitional equality, not merely an implication between statements.
-/

open Lean Meta Elab Command MeasureTheory ProbabilityTheory Real
universe u_1 u_2 u_3

elab "assert_original_type " name:ident " : " expected:term : command => do
  liftTermElabM do
    let expectedType ← Term.elabType expected
    let actualType ← inferType (← mkConstWithFreshMVarLevels name.getId)
    unless ← isDefEq actualType expectedType do
      throwError "Public theorem type changed: {name.getId}"

assert_original_type McdiarmidLean.mcdiarmid_upper_tail_pi :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {X : Type u_2} [_inst_1 : MeasurableSpace X] (μ : ι → Measure X)
  [∀ (i : ι), IsProbabilityMeasure (μ i)] (F : (ι → X) → ℝ) (c : ι → ℝ),
  Measurable F →
    (∀ (x y : ι → X) (i : ι), (∀ (j : ι), j ≠ i → x j = y j) → |F x - F y| ≤ c i) →
      ∀ (t : ℝ),
        0 < t →
          (Measure.pi μ) {x | ∫ (y : ι → X), F y ∂Measure.pi μ + t ≤ F x} ≤
            ENNReal.ofReal (rexp (-(2 * t ^ 2) / ∑ i, c i ^ 2)))

assert_original_type McdiarmidLean.mcdiarmid_lower_tail_pi :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {X : Type u_2} [_inst_1 : MeasurableSpace X] (μ : ι → Measure X)
  [∀ (i : ι), IsProbabilityMeasure (μ i)] (F : (ι → X) → ℝ) (c : ι → ℝ),
  Measurable F →
    (∀ (x y : ι → X) (i : ι), (∀ (j : ι), j ≠ i → x j = y j) → |F x - F y| ≤ c i) →
      ∀ (t : ℝ),
        0 < t →
          (Measure.pi μ) {x | F x ≤ ∫ (y : ι → X), F y ∂Measure.pi μ - t} ≤
            ENNReal.ofReal (rexp (-(2 * t ^ 2) / ∑ i, c i ^ 2)))

assert_original_type McdiarmidLean.mcdiarmid_two_sided_pi :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {X : Type u_2} [_inst_1 : MeasurableSpace X] (μ : ι → Measure X)
  [∀ (i : ι), IsProbabilityMeasure (μ i)] (F : (ι → X) → ℝ) (c : ι → ℝ),
  Measurable F →
    (∀ (x y : ι → X) (i : ι), (∀ (j : ι), j ≠ i → x j = y j) → |F x - F y| ≤ c i) →
      ∀ (t : ℝ),
        0 < t →
          (Measure.pi μ) {x | t ≤ |F x - ∫ (y : ι → X), F y ∂Measure.pi μ|} ≤
            ENNReal.ofReal (2 * rexp (-(2 * t ^ 2) / ∑ i, c i ^ 2)))

assert_original_type McdiarmidLean.mcdiarmid_upper_tail :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {X : Type u_2} [_inst_1 : MeasurableSpace X] {Ω : Type u_3}
  [_inst_2 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Xv : ι → Ω → X),
  (∀ (i : ι), Measurable (Xv i)) →
    iIndepFun Xv P →
      ∀ (F : (ι → X) → ℝ) (c : ι → ℝ),
        Measurable F →
          (∀ (x y : ι → X) (i : ι), (∀ (j : ι), j ≠ i → x j = y j) → |F x - F y| ≤ c i) →
            ∀ (t : ℝ),
              0 < t →
                P {ω | ∫ (ω' : Ω), F fun i => Xv i ω' ∂P + t ≤ F fun i => Xv i ω} ≤
                  ENNReal.ofReal (rexp (-(2 * t ^ 2) / ∑ i, c i ^ 2)))

assert_original_type McdiarmidLean.mcdiarmid_lower_tail :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {X : Type u_2} [_inst_1 : MeasurableSpace X] {Ω : Type u_3}
  [_inst_2 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Xv : ι → Ω → X),
  (∀ (i : ι), Measurable (Xv i)) →
    iIndepFun Xv P →
      ∀ (F : (ι → X) → ℝ) (c : ι → ℝ),
        Measurable F →
          (∀ (x y : ι → X) (i : ι), (∀ (j : ι), j ≠ i → x j = y j) → |F x - F y| ≤ c i) →
            ∀ (t : ℝ),
              0 < t →
                P {ω | (F fun i => Xv i ω) ≤ ∫ (ω' : Ω), F fun i => Xv i ω' ∂P - t} ≤
                  ENNReal.ofReal (rexp (-(2 * t ^ 2) / ∑ i, c i ^ 2)))

assert_original_type McdiarmidLean.mcdiarmid_two_sided :
  (∀ {ι : Type u_1} [_inst : Fintype ι] {X : Type u_2} [_inst_1 : MeasurableSpace X] {Ω : Type u_3}
  [_inst_2 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Xv : ι → Ω → X),
  (∀ (i : ι), Measurable (Xv i)) →
    iIndepFun Xv P →
      ∀ (F : (ι → X) → ℝ) (c : ι → ℝ),
        Measurable F →
          (∀ (x y : ι → X) (i : ι), (∀ (j : ι), j ≠ i → x j = y j) → |F x - F y| ≤ c i) →
            ∀ (t : ℝ),
              0 < t →
                P {ω | t ≤ |(F fun i => Xv i ω) - ∫ (ω' : Ω), F fun i => Xv i ω' ∂P|} ≤
                  ENNReal.ofReal (2 * rexp (-(2 * t ^ 2) / ∑ i, c i ^ 2)))
