# Verification of the McDiarmid library

The command `python3 scripts/verify.py` builds the library and checks its declarations, hypotheses, and proof dependencies. It should be run from the project root after obtaining the mathlib cache for the version specified in `lake-manifest.json`. The results and logs are written to `.lake/verification/`.

A successful release check reports `status: pass` and `build_performed: true` in `result.json`. The development options report `development-pass` or `inventory-only`, which distinguish those runs from a complete release check. At the start of each run, the script replaces the previous result, so an earlier success is not reported after a failed check.

## Verification scope

| Check | Scope |
| --- | --- |
| Compilation and axioms | The library and test target are built with warnings treated as errors. The 33 named source declarations are checked through compiled imports and freshly elaborated source. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. |
| Parameters and hypotheses | The inventory records the full elaborated type, its 303 binders and their kinds, the 95 proposition binders, and the conclusion. It also retains parameters such as measurable-space structures and `Fintype`. |
| Sources of hypotheses | `verification/reviewed_statements.json` classifies each proposition binder and records its mathematical source or the proof in which it is applied. Changes to a signature or the reviewed definitions and versions require review of the affected entries. |
| Proof dependencies | The source check records the declarations used directly in each proof and checks the required dependencies between library results. These include the boundedness and integrability lemmas, coordinate induction, Hoeffding's lemma, Chernoff's bound, equality of the joint and product laws, and the two-sided union bound. |
| Statement preservation | `verification/OriginalStatements.lean` checks definitional equality with the six original tail-inequality theorem types. The comparison below describes their relation to the reference theorem. |

The 33 declarations consist of 25 library declarations and 8 named examples. Anonymous examples are checked when the test target is built. The declaration index recognizes the explicit syntax used in these source files; changes to the module set require a corresponding review of the index and verification scope. Imported mathlib results are checked through Lean's kernel and their transitive axiom dependencies. Their source files are not separately re-elaborated by this script.

The automated checks establish consistency with the reviewed statements and hypothesis classifications. The comparison with the reference theorem also requires mathematical judgment about the meaning of the definitions and assumptions. The recorded comparison was conducted with Codex. The proof was also reviewed by Astra and Jared Huling, as acknowledged in the README. Referee review and acceptance into mathlib are separate processes.

## Relation to the reference theorem

The reference is Boucheron, Lugosi and Massart (2013), *Concentration Inequalities*, Theorem 6.2, printed page 171. The formalization concerns finitely many independent coordinates whose probability laws may differ. The coordinates take values in a common measurable space `X`; a family of different coordinate value types is outside the present statement. The statistic `F` is measurable and satisfies a pointwise coordinate oscillation bound `c i` throughout the product space, so the hypothesis applies beyond the support of the coordinate laws as well.

The centered moment generating function (MGF) satisfies `E exp(l(F-EF)) ≤ exp(l² S/8)` for each real `l`, where `S = Σᵢ cᵢ²`. The proof establishes integrability of `F` and exponential integrability, which justify these expectations. The parameter of `HasSubgaussianMGF` is `S/4` because mathlib expresses its MGF bound as `exp(parameter * l² / 2)`. Its tail inequality therefore yields `exp(-2t²/S)`.

The tail statements assume `t > 0` and use non-strict inequalities. They imply the strict inequalities in the reference theorem by inclusion of events, as checked in an example. The two-sided extension follows by adding the two one-sided bounds. Measurability is explicit in Lean, while the needed nonnegativity of `c i` and nonemptiness of `X` follow from the bounded-differences condition and coordinate probability laws. Empty products are permitted, including when the value space is empty.

When `S = 0`, Lean's division convention gives a displayed upper bound of `1`, or `2` for the two-sided inequality. The statements remain valid in this case. Separate examples prove that the tail probability at a positive threshold is zero when each `c i = 0`, and for an empty product. Thus the public statements apply without an assumption that `S > 0`.

The definition `BoundedDiff` is exposed under Lean's module system and is included in the reviewed definition context. The theorem-type checks unfold this predicate, so the comparison includes the coordinatewise inequality it defines.

## Proof dependencies

The theorem `Induction.abs_sub_le_sum` bounds the difference between two values of `F` by changing one coordinate at a time. The lemma `exists_abs_le` then establishes boundedness relative to a fixed point. The integrability lemmas justify the expectations and applications of Fubini's theorem. Where nonemptiness is needed, it follows from the probability-law assumptions.

The induction in `Induction.mgf_le_fin` separates the first coordinate from the remaining coordinates and applies the induction hypothesis to the latter. The partial expectation `g` satisfies the coordinate oscillation bound, so `exists_mem_Icc_of_abs_sub_le` places its values in an interval of the required length. The left endpoint is an infimum and need not be attained. Mathlib's `hasSubgaussianMGF_of_mem_Icc` supplies Hoeffding's lemma, and `Induction.mgf_le` extends the result from `Fin n` to an arbitrary finite index type.

The theorem `hasSubgaussianMGF_boundedDiff_pi` combines the MGF bound with exponential integrability. The proof of `Induction.upper_tail_pi` applies this result and `HasSubgaussianMGF.measure_ge_le`. Applying the upper-tail result to `-F` establishes the lower-tail result, and a union bound establishes the two-sided result.

For independent random variables, `JointLaw.map_vec_eq_pi` identifies the joint law with the product of the marginal laws. The lemmas `integral_vec` and `prob_vec` establish the corresponding identities for expectations and event probabilities. The theorem `hasSubgaussianMGF_boundedDiff` uses `HasSubgaussianMGF.of_map` to establish the sub-Gaussian property under the original probability measure.

## Verification records

| File | Contents |
| --- | --- |
| `commands.json` and command logs | Commands, exit codes, and elapsed times. |
| `declarations.json` | Full types, hypotheses, axioms, and direct proof dependencies. Signatures obtained from fresh source and compiled imports must agree. |
| `source_hashes.json` | Hashes of the source files, documentation, and verification code. |
| `dependency_revisions.json` | Dependency revisions, checked against the manifest together with the absence of modifications to tracked dependency sources. |
| `original_statements.log` | Definitional-equality checks for the recorded theorem types. |
| `root_imports.log` | A check that the main import excludes example modules and external proof implementations. |
| `reject_axiom.log` | The result of a deliberate custom-axiom rejection check. |

The custom-axiom check must fail with the specified rejection message; an unrelated syntax error also fails verification. The Python tests check rejection of missing or duplicate records, `sorryAx`, additional axioms, errors following a declaration record, changed theorem types, and unreviewed hypotheses.

The option `--inventory-only` generates elaborated statements and dependency records for review after an intended interface change. Updating the reviewed inventory requires comparison of the statements, definitions, and proof dependencies; regenerating hashes alone does not establish that the change is correct.

The GitHub Actions workflow runs the same verification command and retains the resulting records. Local and GitHub runs have separate logs and outcomes. A proposed mathlib contribution additionally requires review of the proof, agreement with maintainers about namespaces and file placement, and compatibility with the mathlib revision used for submission.
