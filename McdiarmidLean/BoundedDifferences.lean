/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Bounded differences

A real statistic on a product space has bounded differences if changing only coordinate `i`
changes its value by at most `c i`. This condition is pointwise on the whole product space.
-/

public section

namespace McdiarmidLean

/-- Changing coordinate `i` alone changes `F` by at most `c i`. -/
@[expose] def BoundedDiff {ι X : Type*} (F : (ι → X) → ℝ) (c : ι → ℝ) : Prop :=
  ∀ x y : ι → X, ∀ i, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c i

end McdiarmidLean
