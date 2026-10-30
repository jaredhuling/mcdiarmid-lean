/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.SubGaussian
public import McdiarmidLean.BoundedDifferences

/-!
# McDiarmid's inequality by induction over coordinates

This module proves the centered sub-Gaussian MGF bound and both tails of McDiarmid's inequality in
product-measure form,

* `McdiarmidLean.hasSubgaussianMGF_boundedDiff_pi`,
* `McdiarmidLean.Induction.upper_tail_pi`,
* `McdiarmidLean.Induction.lower_tail_pi`,

Its only external dependency is mathlib.

Proof outline.

1. A function with bounded differences is bounded: `|F x - F x₀| ≤ Σᵢ cᵢ`
   (`abs_sub_le_sum`), so it and `exp (l * (F - E))` are integrable under any finite measure.
2. Moment generating function bound for `ι = Fin n`, by induction on `n` (`mgf_le_fin`):
   `∫ exp (l (F - ∫ F)) ≤ exp (l² Σᵢ cᵢ² / 8)` for every real `l`. In the step, the product
   measure on `Fin (n + 1) → X` is identified with `μ 0 ⊗ (product of the other coordinates)`
   (`MeasureTheory.measurePreserving_piFinSuccAbove`). Write `H (a, y)` for `F` evaluated at
   first coordinate `a` and remaining coordinates `y`, and `g a = ∫ H (a, y) dy`. By Fubini,
   `E = ∫ F = ∫ g`, and
   `∫ exp (l (F - E)) = ∫ exp (l (g a - E)) · (∫ exp (l (H (a, y) - g a)) dy) da`.
   The inner integral is at most `exp (l² Σ_{i ≥ 1} cᵢ² / 8)` by the induction hypothesis applied
   to `y ↦ H (a, y)`. The function `g` takes values in an interval of length `c₀`, so Hoeffding's
   lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) bounds the outer integral by
   `exp (l² c₀² / 8)`.
3. Transfer to a general finite index type through `Fintype.equivFin` and
   `MeasureTheory.measurePreserving_piCongrLeft` (`mgf_le`).
4. Package the MGF bound and exponential integrability as `HasSubgaussianMGF` with parameter
   `Σᵢ cᵢ² / 4`. Its mathlib Chernoff theorem gives the upper tail, including the zero-parameter
   convention. The lower tail is the upper tail of `-F`.
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace McdiarmidLean
namespace Induction

section Aux

variable {X : Type*} [MeasurableSpace X]

/-- Compatibility abbreviation for `McdiarmidLean.BoundedDiff`. -/
abbrev BoundedDiff {ι : Type*} (F : (ι → X) → ℝ) (c : ι → ℝ) : Prop :=
  McdiarmidLean.BoundedDiff F c

/-! ## Boundedness and integrability -/

omit [MeasurableSpace X] in
/-- The values of a function with bounded differences differ by at most `Σᵢ cᵢ`. -/
lemma abs_sub_le_sum {ι : Type*} [Fintype ι] {F : (ι → X) → ℝ} {c : ι → ℝ}
    (hF : BoundedDiff F c) (x₀ : ι → X) (x : ι → X) : |F x - F x₀| ≤ ∑ i, c i := by
  classical
  have key : ∀ s : Finset ι, ∀ x : ι → X, (∀ j, j ∉ s → x j = x₀ j) →
      |F x - F x₀| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      have : x = x₀ := funext fun j => hx j (Finset.notMem_empty j)
      simp [this]
    | insert i s hi ih =>
      intro x hx
      set x' := Function.update x i (x₀ i) with hx'
      have h1 : |F x - F x'| ≤ c i :=
        hF x x' i (fun j hj => by rw [hx', Function.update_of_ne hj])
      have h2 : |F x' - F x₀| ≤ ∑ i ∈ s, c i := by
        refine ih x' (fun j hj => ?_)
        by_cases hji : j = i
        · subst hji
          simp [hx']
        · rw [hx', Function.update_of_ne hji]
          exact hx j (by simp [hji, hj])
      rw [Finset.sum_insert hi]
      calc |F x - F x₀| = |(F x - F x') + (F x' - F x₀)| := by ring_nf
        _ ≤ |F x - F x'| + |F x' - F x₀| := abs_add_le _ _
        _ ≤ c i + ∑ i ∈ s, c i := add_le_add h1 h2
  exact key Finset.univ x (fun j hj => absurd (Finset.mem_univ j) hj)

omit [MeasurableSpace X] in
/-- A function with bounded differences on a nonempty space is bounded. -/
lemma exists_abs_le {ι : Type*} [Finite ι] [Nonempty (ι → X)] {F : (ι → X) → ℝ}
    {c : ι → ℝ} (hF : BoundedDiff F c) : ∃ C, ∀ x, |F x| ≤ C := by
  let := Fintype.ofFinite ι
  obtain ⟨x₀⟩ := ‹Nonempty (ι → X)›
  refine ⟨|F x₀| + ∑ i, c i, fun x => ?_⟩
  calc |F x| = |(F x - F x₀) + F x₀| := by ring_nf
    _ ≤ |F x - F x₀| + |F x₀| := abs_add_le _ _
    _ ≤ ∑ i, c i + |F x₀| := by gcongr; exact abs_sub_le_sum hF x₀ x
    _ = |F x₀| + ∑ i, c i := add_comm _ _

/-- A bounded measurable real function is integrable under a finite measure. -/
lemma integrable_of_abs_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    {f : α → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ x, |f x| ≤ C) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using h x)

/-- `exp (l * (f - E))` is integrable when `f` is bounded and measurable. -/
lemma integrable_exp_mul_sub {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (h : ∀ x, |f x| ≤ C) (l E : ℝ) :
    Integrable (fun x => exp (l * (f x - E))) ν := by
  refine integrable_of_abs_le ν ((hf.sub_const E).const_mul l).exp (exp (|l| * (C + |E|)))
    (fun x => ?_)
  rw [abs_of_pos (exp_pos _)]
  refine exp_le_exp.2 ?_
  calc l * (f x - E) ≤ |l * (f x - E)| := le_abs_self _
    _ = |l| * |f x - E| := abs_mul _ _
    _ ≤ |l| * (C + |E|) := by
        gcongr
        calc |f x - E| ≤ |f x| + |E| := abs_sub _ _
          _ ≤ C + |E| := by gcongr; exact h x

/-- Under a probability measure, a measurable function with bounded differences is integrable. -/
lemma integrable_of_boundedDiff {ι : Type*} [Finite ι] (ν : Measure (ι → X))
    [IsProbabilityMeasure ν] {F : (ι → X) → ℝ} {c : ι → ℝ} (hFm : Measurable F)
    (hF : BoundedDiff F c) : Integrable F ν := by
  have : Nonempty (ι → X) := nonempty_of_isProbabilityMeasure ν
  obtain ⟨C, hC⟩ := exists_abs_le hF
  exact integrable_of_abs_le ν hFm C hC

/-- A real function with oscillation at most `C` lies in an interval of length `C`.
The left endpoint is an infimum; attainment is not required. -/
lemma exists_mem_Icc_of_abs_sub_le {α : Type*} [Nonempty α] (g : α → ℝ) (C : ℝ)
    (hg : ∀ a a', |g a - g a'| ≤ C) : ∃ m, ∀ a, g a ∈ Set.Icc m (m + C) := by
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hbdd : BddBelow (Set.range g) :=
    ⟨g a₀ - C, by
      rintro _ ⟨a, rfl⟩
      linarith [(abs_le.1 (hg a₀ a)).1, (abs_le.1 (hg a₀ a)).2]⟩
  refine ⟨⨅ a, g a, fun a => ⟨ciInf_le hbdd a, ?_⟩⟩
  have : g a - C ≤ ⨅ a', g a' := le_ciInf fun a' => by linarith [(abs_le.1 (hg a a')).2]
  linarith

/-! ## The moment generating function bound -/

/-- **MGF bound for `Fin n` coordinates.** For a measurable `F` with bounded differences `c`
under a product of probability measures, `∫ exp (l (F - ∫ F)) ≤ exp (l² Σᵢ cᵢ² / 8)`. -/
theorem mgf_le_fin (n : ℕ) :
    ∀ (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (F : (Fin n → X) → ℝ)
      (c : Fin n → ℝ), Measurable F → BoundedDiff F c → ∀ l : ℝ,
      ∫ x, exp (l * (F x - ∫ y, F y ∂(Measure.pi μ))) ∂(Measure.pi μ)
        ≤ exp (l ^ 2 * (∑ i, c i ^ 2) / 8) := by
  induction n with
  | zero =>
    intro μ _ F c _ _ l
    have hconst : F = fun _ => F default := funext fun x => by rw [Subsingleton.elim x default]
    rw [hconst]
    simp
  | succ n ih =>
    intro μ _ F c hFm hF l
    classical
    -- Split off coordinate `0`.
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0 with he
    have hmp := measurePreserving_piFinSuccAbove μ 0
    set ν : Measure (Fin n → X) := Measure.pi fun j => μ (Fin.succAbove 0 j) with hν
    set H : X × (Fin n → X) → ℝ := fun p => F (e.symm p) with hH
    have hHm : Measurable H := hFm.comp e.symm.measurable
    have htr : ∀ φ : (Fin (n + 1) → X) → ℝ,
        ∫ x, φ x ∂(Measure.pi μ) = ∫ p, φ (e.symm p) ∂((μ 0).prod ν) := by
      intro φ
      rw [← hmp.integral_comp' (fun p => φ (e.symm p))]
      congr 1
      funext x
      rw [he, MeasurableEquiv.symm_apply_apply]
    have he0 : ∀ a y, e.symm (a, y) 0 = a := by
      intro a y
      simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have heS : ∀ a y (j : Fin n), e.symm (a, y) j.succ = y j := by
      intro a y j
      simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    -- Bounded differences of the slices.
    set c' : Fin n → ℝ := fun j => c (Fin.succAbove 0 j) with hc'
    have hHa : ∀ a, BoundedDiff (fun y => H (a, y)) c' := by
      intro a y y' j hyy
      refine hF _ _ (Fin.succAbove 0 j) (fun k hk => ?_)
      induction k using Fin.cases with
      | zero => rw [he0, he0]
      | succ m =>
        rw [heS, heS]
        refine hyy m (fun hmj => hk ?_)
        rw [hmj, Fin.succAbove_zero]
    have hHy : ∀ y a a', |H (a, y) - H (a', y)| ≤ c 0 := by
      intro y a a'
      refine hF _ _ 0 (fun k hk => ?_)
      induction k using Fin.cases with
      | zero => exact absurd rfl hk
      | succ m => rw [heS, heS]
    have hHam : ∀ a, Measurable (fun y => H (a, y)) := fun a => hHm.comp measurable_prodMk_left
    have hHai : ∀ a, Integrable (fun y => H (a, y)) ν :=
      fun a => integrable_of_boundedDiff ν (hHam a) (hHa a)
    -- Boundedness of `F` and `H`.
    have : Nonempty (Fin (n + 1) → X) := nonempty_of_isProbabilityMeasure (Measure.pi μ)
    obtain ⟨C, hC⟩ := exists_abs_le hF
    have hHC : ∀ p, |H p| ≤ C := fun p => hC _
    -- The partial mean `g`.
    set g : X → ℝ := fun a => ∫ y, H (a, y) ∂ν with hg
    have hgm : Measurable g := hHm.stronglyMeasurable.integral_prod_right'.measurable
    have hgd : ∀ a a', |g a - g a'| ≤ c 0 := by
      intro a a'
      rw [hg, ← integral_sub (hHai a) (hHai a')]
      have := norm_integral_le_of_norm_le_const (μ := ν)
        (f := fun y => H (a, y) - H (a', y)) (C := c 0)
        (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hHy y a a')
      simpa [Real.norm_eq_abs] using this
    have : Nonempty X := nonempty_of_isProbabilityMeasure (μ 0)
    obtain ⟨a₀⟩ := ‹Nonempty X›
    obtain ⟨m, hIcc⟩ := exists_mem_Icc_of_abs_sub_le g (c 0) hgd
    -- Fubini: the mean of `F` is the mean of `g`.
    have hHint : Integrable H ((μ 0).prod ν) := integrable_of_abs_le _ hHm C hHC
    have hE : ∫ y, F y ∂(Measure.pi μ) = ∫ a, g a ∂(μ 0) := by
      rw [htr F, integral_prod H hHint]
    set E := ∫ y, F y ∂(Measure.pi μ) with hEdef
    -- Hoeffding's lemma for `g`.
    have hsg := hasSubgaussianMGF_of_mem_Icc (μ := μ 0) hgm.aemeasurable (ae_of_all _ hIcc)
    have hHoeff : ∫ a, exp (l * (g a - E)) ∂(μ 0) ≤ exp (l ^ 2 * c 0 ^ 2 / 8) := by
      have h1 := hsg.mgf_le l
      rw [mgf] at h1
      rw [hE]
      refine h1.trans (le_of_eq ?_)
      congr 1
      have : ((‖m + c 0 - m‖₊ / 2) ^ 2 : NNReal) = ((|c 0| / 2) ^ 2 : ℝ) := by
        push_cast
        simp
      rw [this, div_pow, sq_abs]
      ring
    -- The inner bound from the induction hypothesis.
    set B' := exp (l ^ 2 * (∑ j, c' j ^ 2) / 8) with hB'
    have hinner : ∀ a, ∫ y, exp (l * (H (a, y) - E)) ∂ν ≤ exp (l * (g a - E)) * B' := by
      intro a
      have hsplit : (fun y => exp (l * (H (a, y) - E))) =
          fun y => exp (l * (g a - E)) * exp (l * (H (a, y) - g a)) := by
        funext y
        rw [← exp_add]
        ring_nf
      rw [hsplit, integral_const_mul]
      gcongr
      exact ih (fun j => μ (Fin.succAbove 0 j)) (fun y => H (a, y)) c' (hHam a) (hHa a) l
    -- Assemble.
    have hexpint : Integrable (fun p => exp (l * (H p - E))) ((μ 0).prod ν) :=
      integrable_exp_mul_sub _ hHm hHC l E
    have hgC : ∀ a, |g a| ≤ |g a₀| + c 0 := by
      intro a
      calc |g a| = |(g a - g a₀) + g a₀| := by ring_nf
        _ ≤ |g a - g a₀| + |g a₀| := abs_add_le _ _
        _ ≤ c 0 + |g a₀| := by gcongr; exact hgd a a₀
        _ = |g a₀| + c 0 := add_comm _ _
    have hgint : Integrable (fun a => exp (l * (g a - E)) * B') (μ 0) :=
      (integrable_exp_mul_sub _ hgm hgC l E).mul_const B'
    have hsum : ∑ i, c i ^ 2 = c 0 ^ 2 + ∑ j, c' j ^ 2 :=
      Fin.sum_univ_succAbove (fun i => c i ^ 2) 0
    calc ∫ x, exp (l * (F x - E)) ∂(Measure.pi μ)
        = ∫ p, exp (l * (H p - E)) ∂((μ 0).prod ν) := htr (fun x => exp (l * (F x - E)))
      _ = ∫ a, ∫ y, exp (l * (H (a, y) - E)) ∂ν ∂(μ 0) := integral_prod _ hexpint
      _ ≤ ∫ a, exp (l * (g a - E)) * B' ∂(μ 0) :=
          integral_mono_of_nonneg (ae_of_all _ fun a => integral_nonneg fun y => (exp_pos _).le)
            hgint (ae_of_all _ hinner)
      _ = (∫ a, exp (l * (g a - E)) ∂(μ 0)) * B' := integral_mul_const _ _
      _ ≤ exp (l ^ 2 * c 0 ^ 2 / 8) * B' := by gcongr
      _ = exp (l ^ 2 * (∑ i, c i ^ 2) / 8) := by
          rw [hB', ← exp_add, hsum]
          ring_nf

/-- **MGF bound for a general finite index type.** -/
theorem mgf_le {ι : Type*} [Fintype ι] (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F) (hF : BoundedDiff F c) (l : ℝ) :
    ∫ x, exp (l * (F x - ∫ y, F y ∂(Measure.pi μ))) ∂(Measure.pi μ)
      ≤ exp (l ^ 2 * (∑ i, c i ^ 2) / 8) := by
  set f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  set φ := MeasurableEquiv.piCongrLeft (fun _ : ι => X) f
  have hmp := measurePreserving_piCongrLeft μ f
  have htr : ∀ G : (ι → X) → ℝ, ∫ x, G x ∂(Measure.pi μ)
      = ∫ y, G (φ y) ∂(Measure.pi fun a => μ (f a)) := fun G => (hmp.integral_comp' G).symm
  have hφ : ∀ y a, φ y (f a) = y a := fun y a =>
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => X) f y a
  have hF' : BoundedDiff (fun y => F (φ y)) (fun a => c (f a)) := by
    intro y y' a hyy
    refine hF _ _ (f a) (fun k hk => ?_)
    obtain ⟨b, rfl⟩ := f.surjective k
    rw [hφ, hφ]
    exact hyy b (fun hba => hk (by rw [hba]))
  have := mgf_le_fin (Fintype.card ι) (fun a => μ (f a)) (fun y => F (φ y)) (fun a => c (f a))
    (hFm.comp φ.measurable) hF' l
  rw [htr, htr F]
  rw [Equiv.sum_comp f (fun i => c i ^ 2)] at this
  exact this

end Aux

end Induction

/-- A measurable statistic with bounded differences has centered sub-Gaussian MGF
with variance proxy `Σᵢ cᵢ² / 4` under a product of probability measures. -/
theorem hasSubgaussianMGF_boundedDiff_pi {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : McdiarmidLean.BoundedDiff F c) :
    HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂Measure.pi μ)
      ⟨(∑ i, c i ^ 2) / 4, div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (c i)) (by norm_num)⟩
      (Measure.pi μ) := by
  have : Nonempty (ι → X) := nonempty_of_isProbabilityMeasure (Measure.pi μ)
  obtain ⟨C, hC⟩ := McdiarmidLean.Induction.exists_abs_le hF
  refine ⟨?_, ?_⟩
  · intro t
    exact McdiarmidLean.Induction.integrable_exp_mul_sub (Measure.pi μ) hFm hC t _
  · intro t
    have h := McdiarmidLean.Induction.mgf_le μ F c hFm hF t
    change (∫ x, exp (t * (F x - ∫ y, F y ∂Measure.pi μ)) ∂Measure.pi μ)
      ≤ exp (((∑ i, c i ^ 2) / 4) * t ^ 2 / 2)
    convert h using 1
    congr 1
    ring


namespace Induction

/-! ## Tail bounds -/

section Tails

variable {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]

/-- If `Σᵢ cᵢ² = 0`, the McDiarmid bound equals `1`. -/
lemma bound_eq_one_of_sum_eq_zero {c : ι → ℝ} (h : ∑ i, c i ^ 2 = 0)
    (t : ℝ) : ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) = 1 := by
  rw [h, div_zero, Real.exp_zero, ENNReal.ofReal_one]

/-- **Upper tail, product-measure form.** -/
theorem upper_tail_pi (μ : ι → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : ∀ x y : ι → X, ∀ i, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c i)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | (∫ y, F y ∂(Measure.pi μ)) + t ≤ F x}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) := by
  have hreal := (hasSubgaussianMGF_boundedDiff_pi μ F c hFm hF).measure_ge_le ht.le
  have hexp : -t ^ 2 / (2 * ((∑ i, c i ^ 2) / 4)) = -(2 * t ^ 2) / ∑ i, c i ^ 2 := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  change (Measure.pi μ).real {x | t ≤ F x - ∫ y, F y ∂Measure.pi μ}
    ≤ exp (-t ^ 2 / (2 * ((∑ i, c i ^ 2) / 4))) at hreal
  rw [hexp] at hreal
  have hset : {x | (∫ y, F y ∂Measure.pi μ) + t ≤ F x}
      = {x | t ≤ F x - ∫ y, F y ∂Measure.pi μ} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  rw [hset]
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (exp_pos _).le).2 hreal

/-- **Lower tail, product-measure form.** -/
theorem lower_tail_pi (μ : ι → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : ∀ x y : ι → X, ∀ i, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c i)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | F x ≤ (∫ y, F y ∂(Measure.pi μ)) - t}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2)) := by
  have hF' : ∀ x y : ι → X, ∀ i, (∀ j, j ≠ i → x j = y j) → |(-F x) - (-F y)| ≤ c i := by
    intro x y i h
    rw [show (-F x) - (-F y) = -(F x - F y) by ring, abs_neg]
    exact hF x y i h
  have h := upper_tail_pi μ (fun x => -F x) c hFm.neg hF' t ht
  have hset : {x | (∫ y, -F y ∂(Measure.pi μ)) + t ≤ -F x}
      = {x | F x ≤ (∫ y, F y ∂(Measure.pi μ)) - t} := by
    ext x
    simp only [Set.mem_ofPred_eq, integral_neg]
    constructor <;> intro hx <;> linarith
  rw [hset] at h
  exact h

end Tails

end Induction
end McdiarmidLean
