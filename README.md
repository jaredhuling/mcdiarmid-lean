# mcdiarmid-lean

A Lean 4 / mathlib formalization of McDiarmid's bounded-differences inequality in
product-measure form and in random-variable form, with laws that may differ across
coordinates.

Reference statement: S. Boucheron, G. Lugosi and P. Massart (2013), *Concentration
Inequalities: A Nonasymptotic Theory of Independence*, Oxford University Press, Theorem 6.2.

For the prior Lean formalization by Sonoda et al. (2026), see
[Prior work and acknowledgement](#prior-work-and-acknowledgement).

## What is proved

Setting: `ι` is a finite index type (`[Fintype ι]`), `X` is any measurable space, and the
coordinate laws `μ i` are probability measures on `X` (they need not be equal). The statistic
`F : (ι → X) → ℝ` is measurable and has bounded differences with constants `c i`: whenever
`x` and `y` agree off coordinate `i`, `|F x - F y| ≤ c i`. For every `t > 0`, with
`S = Σᵢ cᵢ²`,

* upper tail: `P{F ≥ E F + t} ≤ exp(-2t²/S)`;
* lower tail: `P{F ≤ E F - t} ≤ exp(-2t²/S)`;
* two-sided: `P{|F - E F| ≥ t} ≤ 2 exp(-2t²/S)`;

both for the product measure `Measure.pi μ` and for independent random variables
`Xv i : Ω → X` under a probability measure `P`.

The namespace is `McdiarmidLean`. `import McdiarmidLean` provides the generic API,
including `BoundedDiff`, the sub-Gaussian results, and all six tail inequalities.
Examples and paper compatibility are separate imports.

### Sub-Gaussian interface

`hasSubgaussianMGF_boundedDiff_pi` proves that `F - E F` has
`HasSubgaussianMGF` with variance proxy `S/4` under the product law.
`hasSubgaussianMGF_boundedDiff` gives the same result for independent random variables.
These results include exponential integrability for every real tilt. The upper-tail
proof applies the product sub-Gaussian theorem and mathlib's Chernoff bound.

The reusable condition `BoundedDiff F c` lives in `McdiarmidLean/BoundedDifferences.lean`.
It means exactly the coordinatewise condition above and applies on the whole product
space. `Induction.BoundedDiff` remains a compatibility abbreviation.

### Product-measure form

```lean
theorem mcdiarmid_upper_tail_pi (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : BoundedDiff F c)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | (∫ y, F y ∂(Measure.pi μ)) + t ≤ F x}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2))

theorem mcdiarmid_lower_tail_pi (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : BoundedDiff F c)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | F x ≤ (∫ y, F y ∂(Measure.pi μ)) - t}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2))

theorem mcdiarmid_two_sided_pi (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ) (c : ι → ℝ) (hFm : Measurable F)
    (hF : BoundedDiff F c)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ |F x - ∫ y, F y ∂(Measure.pi μ)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2))
```

### Optional paper compatibility

Import `McdiarmidLean.Compat.Cooverlap` to obtain the following two declarations.
Their names and mathematical statements are unchanged; they are no longer imported
by the generic root module. The paper's consumer uses this explicit import.

```lean
def McDiarmidLowerTail (X : Type*) [MeasurableSpace X] (ι : Type*) [Fintype ι] : Prop :=
  ∀ (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (F : (ι → X) → ℝ) (c : ι → ℝ),
    Measurable F → (∀ x y : ι → X, ∀ i, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c i) →
    ∀ t : ℝ, 0 < t →
      Measure.pi μ {x | F x ≤ (∫ y, F y ∂(Measure.pi μ)) - t}
        ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2))

theorem mcDiarmidLowerTail_holds (X : Type*) [MeasurableSpace X] (ι : Type*) [Fintype ι] :
    McDiarmidLowerTail X ι
```

### Random-variable form

For `P : Measure Ω` with `[IsProbabilityMeasure P]`, `Xv : ι → Ω → X`,
`hXm : ∀ i, Measurable (Xv i)` and `hind : iIndepFun Xv P`, with the same `F`, `c`, `hFm`,
`hF`, `t`, `ht` as above:

```lean
theorem mcdiarmid_upper_tail ... :
    P {ω | (∫ ω', F (fun i => Xv i ω') ∂P) + t ≤ F (fun i => Xv i ω)}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2))

theorem mcdiarmid_lower_tail ... :
    P {ω | F (fun i => Xv i ω) ≤ (∫ ω', F (fun i => Xv i ω') ∂P) - t}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2))

theorem mcdiarmid_two_sided ... :
    P {ω | t ≤ |F (fun i => Xv i ω) - ∫ ω', F (fun i => Xv i ω') ∂P|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 * t ^ 2) / ∑ i, c i ^ 2))
```

### Relation to Boucheron, Lugosi and Massart (2013), Theorem 6.2

* The book writes the bound as `exp(-t²/(2v))` with `v = Σᵢ cᵢ²/4`; this equals
  `exp(-2t²/Σᵢ cᵢ²)`.
* The book states the upper tail with a strict inequality, `P{Z - EZ > t}`, and the lower tail
  as `P{Z - EZ < -t}`. The Lean events use non-strict inequalities, so they contain the book's
  events and the Lean statements are slightly stronger.
* The book assumes nonnegative constants `cᵢ`. The Lean statements do not assume this; when
  `X` is nonempty the bounded-differences hypothesis with `x = y` already forces `cᵢ ≥ 0`.
* The two-sided bound is the union of the two one-sided bounds; the book does not state it as
  part of Theorem 6.2.
* Measurability of `F` is implicit in the book and explicit in Lean.

### Degenerate cases

* If `Σᵢ cᵢ² = 0` (including an empty index type), Lean's convention `x / 0 = 0` makes the
  bound `exp 0 = 1` (or `2` in the two-sided case). The statements remain true because a
  probability is at most `1`. The sub-Gaussian bound covers this convention as well.
  The examples also prove the actual positive-threshold tail is zero when all `c i = 0`.
* No `Nonempty X` assumption appears. If `ι` is nonempty, a coordinate law is a probability
  measure on `X`, so `X` is nonempty; the proof derives this where it needs it.
* Bounded differences make `F` bounded, so `∫ F` is the genuine expectation rather than
  the default zero value of a nonintegrable Bochner integral.

## How it is proved

The proof uses mathlib only.

* `McdiarmidLean/Induction.lean` proves the two one-sided product-measure bounds,
  `Induction.upper_tail_pi` and `Induction.lower_tail_pi`:
  1. A function with bounded differences is bounded (`|F x - F x₀| ≤ Σᵢ cᵢ`), so `F` and
     `exp(l (F - E F))` are integrable.
  2. Moment generating function bound, by induction on the number of coordinates for
     `ι = Fin n` (`mgf_le_fin`), then for any finite `ι` through `Fintype.equivFin` and
     `measurePreserving_piCongrLeft` (`mgf_le`): for every real `l`,
     `E exp(l (F - E F)) ≤ exp(l² Σᵢ cᵢ² / 8)`. In the induction step the product measure is
     split as (first coordinate) × (remaining coordinates) with `measurePreserving_piFinSuccAbove`.
     With `g(a)` the mean of `F` over the remaining coordinates when the first equals `a`,
     Fubini gives `E F = E g`; the induction hypothesis bounds the inner integral of
     `exp(l (F - g(a)))`; and `g` takes values in an interval of length `c₀`, so Hoeffding's
     lemma (mathlib's `hasSubgaussianMGF_of_mem_Icc`) bounds `E exp(l (g - E g))` by
     `exp(l² c₀² / 8)`.
  3. The integral bound and exponential integrability give `HasSubgaussianMGF` with
     parameter `S/4`. Its `measure_ge_le` theorem gives the upper tail, including `S = 0`;
     the lower tail is the upper tail of `-F`. The two-sided result uses a union bound.
* `McdiarmidLean/JointLaw.lean` shows that the joint law of independent random variables is
  the product of the marginal laws (mathlib's `iIndepFun_iff_map_fun_eq_pi_map`) and
  transports integrals and event probabilities along it.
* `McdiarmidLean/Statement.lean` states the public tails and the random-variable
  sub-Gaussian result, using the proved product bounds and joint-law transport.
* `McdiarmidLean/Compat/Cooverlap.lean` contains the optional paper adapter.
* `McdiarmidLean/Examples.lean` checks strict textbook events, zero variation, empty
  products (even with an empty value space), two Bernoulli coordinates with possibly
  different laws, random-variable transport, and the zero-parameter MGF.
  `McdiarmidLeanTest` builds these examples and checks paper compatibility.

Every public theorem, and the lemmas `Induction.upper_tail_pi`,
`Induction.lower_tail_pi`, `Induction.mgf_le` and `Induction.mgf_le_fin`, depends only on the
standard axioms `propext`, `Classical.choice`, and `Quot.sound` (checked with
`#print axioms`). The library contains no `sorry` and no new `axiom`.

## Prior work and acknowledgement

McDiarmid's inequality was previously formalized in Lean by Sonoda et al.:

> Sonoda, S., Kasaura, K., Mizuno, Y., Tsukamoto, K., and Onda, N. (2026).
> *Lean Formalization of Generalization Error Bound by Rademacher Complexity and
> Dudley's Entropy Integral*. [arXiv:2503.19605v5](https://arxiv.org/abs/2503.19605v5),
> revised May 24, 2026 (first submitted March 25, 2025).

Their [lean-rademacher implementation of McDiarmid's inequality](https://github.com/auto-res/lean-rademacher/blob/f34ab4f0a9029682f1af3179a3fe9b5e114e511f/FoML/McDiarmid.lean)
provides the prior formalization. An earlier version of this repository derived
its statements from that implementation (MIT License, Copyright (c) 2025 AutoRes).
The current coordinate-induction proof is a separate implementation using only
mathlib. This library's contribution is its proof organization, reusable
interfaces, and verification tooling.

## Building

Requirements: [elan](https://github.com/leanprover/elan), Git, and Python 3.11+ for the audit. The toolchain is pinned in
`lean-toolchain` (`leanprover/lean4:v4.35.0`) and mathlib is pinned to `v4.35.0` in
`lakefile.toml` and `lake-manifest.json`.

```bash
lake exe cache get   # download prebuilt mathlib artifacts; do not build mathlib from source
lake build --wfail
lake test --wfail
python3 scripts/verify.py
```

The audit command builds and tests the checkout, checks the original seven public
theorem types by definitional equality, inventories every named declaration, checks
axioms both from compiled imports and freshly elaborated source, records proof
dependencies, and checks the generic import boundary. It also tests rejection of
a custom axiom and of missing or changed evidence. Warnings fail the build.

Results, source hashes, dependency revisions, and logs are written to
`.lake/verification/`. The workflow in `.github/workflows/verify.yml` runs the same
command on GitHub. A local passing run does not establish a remote CI run.
[VERIFICATION.md](VERIFICATION.md) explains the checks and their limits.

To use the library from another Lake project on the same mathlib version, add

```toml
[[require]]
name = "mcdiarmid"
git = "<repository URL>"
rev = "<commit>"
```

and `import McdiarmidLean`.

## License

MIT, Copyright (c) 2026 Jared Huling (see `LICENSE`).

## Acknowledgment

The Lean proof was developed by Opus 5.5 and double-checked by Astra and Jared Huling.
