/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Joint law of independent random variables

For independent random variables `Xv i : Ω → X` under a probability measure `P`, the law of the
random vector `ω ↦ (Xv i ω)ᵢ` is the product `Measure.pi (fun i => P.map (Xv i))` of the
marginal laws (mathlib `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`). The lemmas here
transport integrals and event probabilities along this identity, so that the random-variable
form of McDiarmid's inequality follows from the product-measure form. Each marginal law
`P.map (Xv i)` is a probability measure by a mathlib instance.
-/

public section

open MeasureTheory ProbabilityTheory

namespace McdiarmidLean
namespace JointLaw

variable {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Xv : ι → Ω → X}

omit [Fintype ι] [IsProbabilityMeasure P] in
/-- The random vector `ω ↦ (Xv i ω)ᵢ` is measurable. -/
lemma measurable_vec (hXm : ∀ i, Measurable (Xv i)) :
    Measurable (fun ω i => Xv i ω) :=
  Measurable.of_eval hXm

/-- The joint law of independent random variables is the product of the marginal laws. -/
lemma map_vec_eq_pi (hXm : ∀ i, Measurable (Xv i)) (hind : iIndepFun Xv P) :
    P.map (fun ω i => Xv i ω) = Measure.pi (fun i => P.map (Xv i)) :=
  (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hXm i).aemeasurable)).1 hind

/-- Integrals of a measurable statistic of the random vector agree with integrals against
the product of its marginal laws. If the statistic is integrable, these are expectations. -/
lemma integral_vec (hXm : ∀ i, Measurable (Xv i)) (hind : iIndepFun Xv P)
    {F : (ι → X) → ℝ} (hFm : Measurable F) :
    ∫ ω, F (fun i => Xv i ω) ∂P = ∫ x, F x ∂(Measure.pi (fun i => P.map (Xv i))) := by
  rw [← map_vec_eq_pi hXm hind,
    integral_map (measurable_vec hXm).aemeasurable hFm.aestronglyMeasurable]

/-- Probabilities of measurable events of the random vector are product-measure
probabilities. -/
lemma prob_vec (hXm : ∀ i, Measurable (Xv i)) (hind : iIndepFun Xv P)
    {s : Set (ι → X)} (hs : MeasurableSet s) :
    P {ω | (fun i => Xv i ω) ∈ s} = Measure.pi (fun i => P.map (Xv i)) s := by
  rw [← map_vec_eq_pi hXm hind, Measure.map_apply (measurable_vec hXm) hs]
  rfl

end JointLaw
end McdiarmidLean
