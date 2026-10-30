# mcdiarmid-lean

McDiarmid's bounded-differences inequality bounds the deviation of a function of independent random variables from its expectation when the effect of changing each coordinate is controlled. This library formalizes the inequality in Lean 4 with mathlib, including upper-tail, lower-tail, and two-sided bounds for a finite family of coordinates whose probability laws may differ.

The mathematical reference is S. Boucheron, G. Lugosi and P. Massart (2013), *Concentration Inequalities: A Nonasymptotic Theory of Independence*, Oxford University Press, Theorem 6.2. An earlier Lean formalization is due to Sonoda et al. (2026), whose work is described under [Prior work](#prior-work).

## Mathematical results

Let `ι` be a finite index type, let `X` be a measurable space, and let `μ i` be a probability measure on `X` for each `i`. Suppose that `F : (ι → X) → ℝ` is measurable and has bounded differences: whenever `x` and `y` agree outside coordinate `i`, `|F x - F y| ≤ c i`. Write `S = Σᵢ cᵢ²`. For each `t > 0`, the library proves

* the upper-tail bound `P{F ≥ E F + t} ≤ exp(-2t²/S)`;
* the lower-tail bound `P{F ≤ E F - t} ≤ exp(-2t²/S)`;
* the two-sided bound `P{|F - E F| ≥ t} ≤ 2 exp(-2t²/S)`.

Under the product measure `Measure.pi μ`, the probabilities and expectations are taken over the coordinate vector. The same bounds hold for `F` evaluated at independent measurable random variables `Xv i : Ω → X` under a probability measure `P`. When `S > 0`, the sum of squared coordinate bounds determines the concentration rate. The case `S = 0` is described under [Integrability and degenerate cases](#integrability-and-degenerate-cases).

The import `McdiarmidLean` provides the bounded-differences predicate, the sub-Gaussian results, and the six tail inequalities in the namespace `McdiarmidLean`. The predicate `BoundedDiff F c`, defined in `McdiarmidLean/BoundedDifferences.lean`, requires the coordinatewise bound throughout the product space. `Induction.BoundedDiff` is an abbreviation for the same predicate.

### Sub-Gaussian bounds

The centered moment generating function (MGF) satisfies `E exp(l (F - E F)) ≤ exp(l² S/8)` for each real `l`. The theorem `hasSubgaussianMGF_boundedDiff_pi` expresses this result through mathlib's `HasSubgaussianMGF` with variance proxy `S/4`; `hasSubgaussianMGF_boundedDiff` establishes the corresponding result for independent random variables. Both results include exponential integrability for each real `l`, so they can also be used in arguments that require an MGF bound. The upper-tail proof applies the product-measure result and mathlib's Chernoff bound.

### Product-measure form

The three product-measure statements have the following signatures.

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

### Random-variable form

Let `P : Measure Ω` be a probability measure, and suppose that `Xv : ι → Ω → X` is a family of measurable independent random variables. These assumptions are expressed by `[IsProbabilityMeasure P]`, `hXm : ∀ i, Measurable (Xv i)`, and `hind : iIndepFun Xv P`. With the same assumptions on `F`, `c`, and `t` as above, the corresponding conclusions are as follows; the argument lists are abbreviated here.

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

The reference theorem expresses the bound as `exp(-t²/(2v))`, where `v = Σᵢ cᵢ²/4`, which equals `exp(-2t²/Σᵢ cᵢ²)`. Its upper- and lower-tail events use strict inequalities, `P{Z - EZ > t}` and `P{Z - EZ < -t}`. The Lean statements use non-strict inequalities, so the reference theorem follows by inclusion of events. The two-sided bound follows from a union bound and is additional to the statement of Theorem 6.2.

Measurability of `F` is explicit in the Lean statements. Although the reference theorem also assumes nonnegative constants `cᵢ`, this follows from the bounded-differences condition by taking `x = y` when `X` is nonempty. The formalization therefore derives this property within the proof.

### Integrability and degenerate cases

Bounded differences imply boundedness of `F` because there are finitely many coordinates. Together with measurability, this establishes integrability under the product probability measure and justifies the expectation in each bound.

When `S = 0`, including the case of an empty index type, Lean's convention `x / 0 = 0` gives a displayed upper bound of `exp 0 = 1`, or `2` for the two-sided result. The inequalities remain valid under this convention. The examples additionally prove that the tail probability at a positive threshold is zero when all `c i = 0`, as well as for an empty product. The sub-Gaussian theorem also applies when its variance proxy is zero.

The theorem statements do not require a separate `Nonempty X` assumption. If `ι` is nonempty, the existence of a coordinate probability measure implies that `X` is nonempty. An empty index type is also permitted when `X` is empty.

## Proof structure

The proof proceeds by induction on the number of coordinates. First, the bounded-differences condition implies `|F x - F x₀| ≤ Σᵢ cᵢ` by changing one coordinate at a time. This establishes boundedness and hence integrability of `F` and `exp(l (F - E F))` under the product probability measure.

For `ι = Fin n`, the theorem `Induction.mgf_le_fin` establishes the MGF bound by separating the first coordinate from the remaining coordinates. Let `g(a)` be the expectation of `F` over the remaining coordinates when the first coordinate equals `a`. Fubini's theorem implies `E F = E g`, and the induction hypothesis bounds the inner integral of `exp(l (F - g(a)))`. The bounded-differences condition implies that `g` takes values in an interval of length `c₀`. Hoeffding's lemma, provided by mathlib's `hasSubgaussianMGF_of_mem_Icc`, then bounds `E exp(l (g - E g))` by `exp(l² c₀² / 8)`. Combining these bounds completes the induction.

The theorem `Induction.mgf_le` extends the result to any finite index type through `Fintype.equivFin` and `measurePreserving_piCongrLeft`. The MGF bound and exponential integrability establish `HasSubgaussianMGF` with parameter `S/4`. Its theorem `measure_ge_le` yields the upper-tail inequality, including the convention for `S = 0`. Applying the upper-tail inequality to `-F` yields the lower-tail inequality, and a union bound yields the two-sided result.

For independent random variables, `JointLaw.map_vec_eq_pi` identifies their joint law with the product of their marginal laws using mathlib's `iIndepFun_iff_map_fun_eq_pi_map`. Equality of the joint and product laws then establishes the corresponding expectations, tail probabilities, and sub-Gaussian bound.

### Source organization

| Module | Contents |
| --- | --- |
| `McdiarmidLean/BoundedDifferences.lean` | The coordinatewise bounded-differences condition. |
| `McdiarmidLean/Induction.lean` | Boundedness, integrability, the MGF bound, and the one-sided product-measure inequalities. |
| `McdiarmidLean/JointLaw.lean` | Equality of the joint law and the product of the marginal laws, with the corresponding integral and event identities. |
| `McdiarmidLean/Statement.lean` | Product-measure and random-variable tail bounds, and the random-variable sub-Gaussian result. |
| `McdiarmidLean/Examples.lean` | Applications to Bernoulli coordinates with possibly different laws, strict tail events, zero variation, empty products, and a zero variance proxy. |

The test target `McdiarmidLeanTest` builds the examples.

## Prior work

Sonoda et al. previously formalized McDiarmid's inequality in Lean:

> Sonoda, S., Kasaura, K., Mizuno, Y., Tsukamoto, K., and Onda, N. (2026).
> *Lean Formalization of Generalization Error Bound by Rademacher Complexity and
> Dudley's Entropy Integral*. [arXiv:2503.19605v5](https://arxiv.org/abs/2503.19605v5),
> revised May 24, 2026 (first submitted March 25, 2025).

An earlier version of this library derived its statements from their [lean-rademacher implementation](https://github.com/auto-res/lean-rademacher/blob/f34ab4f0a9029682f1af3179a3fe9b5e114e511f/FoML/McDiarmid.lean) (MIT License, Copyright (c) 2025 AutoRes). The present implementation proves the result by coordinate induction using mathlib and provides both product-measure and random-variable statements.

## Build and verification

The build requires [elan](https://github.com/leanprover/elan), Git, and Python 3.11+ for the verification script. The Lean version is specified in `lean-toolchain` as `leanprover/lean4:v4.35.0`. The mathlib version is fixed at `v4.35.0` in `lakefile.toml` and `lake-manifest.json`.

```bash
lake exe cache get   # download prebuilt mathlib artifacts; do not build mathlib from source
lake build --wfail
lake test --wfail
python3 scripts/verify.py
```

The verification script builds and tests the library with warnings treated as errors. It checks theorem signatures against the recorded statements, records hypotheses and direct proof dependencies, and checks axioms using both compiled imports and freshly elaborated source. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`; the checks reject `sorry` and additional axioms. The script also checks the modules imported by `McdiarmidLean` and tests rejection of incomplete or altered verification records.

Results, source hashes, dependency revisions, and logs are written to `.lake/verification/`. The GitHub Actions workflow in `.github/workflows/verify.yml` runs the same verification command. [VERIFICATION.md](VERIFICATION.md) describes the checks, their scope, and the comparison with the reference theorem.

## Use in another Lean project

A project using the same mathlib version can declare the dependency as follows, replacing the repository URL and commit with those of the desired revision:

```toml
[[require]]
name = "mcdiarmid"
git = "<repository URL>"
rev = "<commit>"
```

The library is then available through `import McdiarmidLean`.

## License

Released under the MIT License, Copyright (c) 2026 Jared Huling. See `LICENSE`.

## Acknowledgment

The Lean proof was developed by Opus 5.5 and double-checked by Astra and Jared Huling.
