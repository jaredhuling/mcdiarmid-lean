/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import McdiarmidLean.Statement

/-!
# Compatibility with the cooverlap paper

This optional adapter preserves the paper's named lower-tail proposition and proves it from
McDiarmid's inequality. Import it explicitly; the generic library does not import this module.
The declaration names and proposition body are unchanged.
-/

public section

open MeasureTheory ProbabilityTheory

namespace McdiarmidLean

/-! ## The cooverlap named hypothesis, proved -/

/-- **McDiarmid's bounded-differences inequality, lower tail** (Boucheron, Lugosi and Massart
2013, Theorem 6.2), for coordinates indexed by `ι` with values in `X`: for any product of
probability measures, any measurable `F` such that changing coordinate `i` alone changes `F` by
at most `cᵢ`, and any `t > 0`, `P{F ≤ E F − t} ≤ exp(−2t²/Σᵢ cᵢ²)`.

This definition is copied verbatim from `Cooverlap.CellIntervalSampled.McDiarmidLowerTail`
(cooverlap, `Cooverlap/CellIntervalSampled.lean`), where it is a named hypothesis.
`mcDiarmidLowerTail_holds` proves it. -/
@[expose] def McDiarmidLowerTail (X : Type*) [MeasurableSpace X] (ι : Type*) [Fintype ι] : Prop :=
  ∀ (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (F : (ι → X) → ℝ) (c : ι → ℝ),
    Measurable F → (∀ x y : ι → X, ∀ i, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c i) →
    ∀ t : ℝ, 0 < t →
      Measure.pi μ {x | F x ≤ (∫ y, F y ∂(Measure.pi μ)) - t}
        ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2))

/-- `McDiarmidLowerTail X ι` holds for every measurable space `X` and finite index type `ι`. -/
theorem mcDiarmidLowerTail_holds (X : Type*) [MeasurableSpace X] (ι : Type*) [Fintype ι] :
    McDiarmidLowerTail X ι :=
  fun μ _ F c hFm hF t ht => mcdiarmid_lower_tail_pi μ F c hFm hF t ht

end McdiarmidLean
