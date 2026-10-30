/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

import McdiarmidLean.Compat.Cooverlap
import McdiarmidLean.Examples

/-! # Explicit build target for examples and paper compatibility -/

example : McdiarmidLean.McDiarmidLowerTail ℝ (Fin 3) :=
  McdiarmidLean.mcDiarmidLowerTail_holds ℝ (Fin 3)
