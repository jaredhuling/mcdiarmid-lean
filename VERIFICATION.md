# Verification of the McDiarmid library

Run `python3 scripts/verify.py` from the project root after obtaining the pinned
mathlib cache. A release check succeeds only when `result.json` reports `pass`
and `build_performed` is `true`. The evidence is in `.lake/verification/`.
Development options produce `development-pass` or `inventory-only`, never a
release pass. A failed run invalidates any earlier success marker.

## Certificates and their scope

| Certificate | Check and scope |
| --- | --- |
| Kernel | Build both library and test target with warnings treated as errors. Audit all 35 named source declarations, once through compiled imports and once through freshly elaborated source. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. |
| Premises | Record the entire elaborated type, all 311 binders and their kinds, all 95 proposition binders, and the conclusion. Parameters such as measurable-space structures and `Fintype` are retained even though they are not propositions. |
| Premise provenance | `verification/reviewed_statements.json` classifies each proposition binder and explains its source or consuming proof. Changes to signatures or the reviewed definition/version context require a new review. |
| Proof regions | The source audit records actual direct proof dependencies and checks the essential library-to-library proof edges. The chain below accounts for boundedness, integrability, the coordinate induction, Hoeffding's lemma, Chernoff's bound, joint-law transport, and the two-sided union bound. |
| Statement and composition | `OriginalStatements.lean` checks definitional equality with the seven original public theorem types and the original compatibility predicate. The mathematical comparison below states the scope of agreement with the textbook. |

The 35 declarations consist of 27 library declarations and 8 named example
declarations. Anonymous examples are checked by the test build. The declaration
index is tailored to the explicit declaration syntax used in these files; it is
not a general Lean parser. A changed module set fails the audit and must be
reviewed. Imported mathlib dependencies are trusted through Lean's kernel checks
and transitive axiom audit; their full source trees are not independently
re-elaborated by this command.

The recorded provenance and textbook comparison are mathematical review evidence,
not machine-proved equivalence to English prose. The review was performed with
Codex; it is not human referee approval or mathlib acceptance. The automated
checks enforce consistency with the reviewed inventory, not the correctness of
arbitrarily edited review metadata.

## Mathematical statement comparison

The reference is Boucheron, Lugosi and Massart (2013), *Concentration Inequalities*,
Theorem 6.2, printed page 171.

* There are finitely many independent coordinates. Their probability laws can
  differ. The API uses a common measurable value space `X`; it does not yet
  provide a dependent family of different value types.
* `F` is measurable and has a global, pointwise coordinate oscillation bound
  `c i`. This is not merely an almost-everywhere or on-support bound.
* The centered MGF satisfies `E exp(l(F-EF)) ≤ exp(l² S/8)` for every real
  `l`, where `S = Σᵢ cᵢ²`. Exponential integrability is proved, as is
  integrability of `F`. Thus `EF` is an expectation, not the default value of a
  nonintegrable Bochner integral.
* The `HasSubgaussianMGF` parameter is `S/4`: mathlib writes the MGF bound as
  `exp(parameter * l² / 2)`. Its tail bound therefore gives `exp(-2t²/S)`.
* The public tails take `t > 0` and use closed events. These imply the book's
  strict events; an example checks the inclusion explicitly. The two-sided
  extension adds the two one-sided bounds.
* Measurability is explicit in Lean. Nonnegative `c i` and nonempty `X` need
  not be supplied separately: the probability-law and bounded-difference
  assumptions imply the needed facts when coordinates exist. Empty products
  are valid, including an empty value space.
* When `S = 0`, Lean's division convention gives a displayed bound of `1`
  (or `2` for two sides). This is valid but weak. Examples separately prove
  that positive-threshold tails are actually zero when every `c i = 0`, and
  for an empty product. There is no assumption `S > 0` hidden in the API.

`BoundedDiff` and `McDiarmidLowerTail` are explicitly exposed definitions under
Lean's module system. Their bodies are part of the review context. The latter
packages the entire lower-tail statement as a proposition; its apparent absence
of proposition binders in the declaration inventory does not remove the
conditions quantified *inside* its definition. The frozen definition-equality
check checks that complete body.

## Proof composition

`Induction.abs_sub_le_sum` changes one coordinate at a time.
`exists_abs_le` then bounds `F` relative to a fixed point, and the integrability
helpers justify each integral and use of Fubini. Nonempty spaces needed for
these helpers are obtained from the probability laws.

`Induction.mgf_le_fin` splits off one coordinate. It applies its induction
hypothesis to the remaining coordinates. It proves an oscillation bound for the
partial expectation `g`, then applies `exists_mem_Icc_of_abs_sub_le` to put `g`
in an interval of the required length. The endpoint is an infimum and need not
be attained. Mathlib's `hasSubgaussianMGF_of_mem_Icc` supplies Hoeffding's lemma.
`Induction.mgf_le` transports the result from `Fin n` to any finite index type.

`hasSubgaussianMGF_boundedDiff_pi` packages the MGF bound and exponential
integrability. `Induction.upper_tail_pi` actually applies this theorem and
`HasSubgaussianMGF.measure_ge_le`; the sub-Gaussian API is part of the main
proof. The lower tail applies the upper tail to `-F`. The public product
statements wrap these results, and the two-sided statement applies a union bound.

`JointLaw.map_vec_eq_pi` uses independence to identify the joint law with the
product of the marginals. `integral_vec` and `prob_vec` transport the expectation
and tail events. `hasSubgaussianMGF_boundedDiff` transports the sub-Gaussian
property with `HasSubgaussianMGF.of_map`.

The optional `Compat.Cooverlap` module applies the public product lower tail to
prove the existing paper adapter. It is excluded from the generic root import,
as are examples. Downstream users of that adapter must change their import to
`McdiarmidLean.Compat.Cooverlap`; its name and mathematical type are preserved.
This project verifies the concentration input, not every result in the paper.

## Evidence and failure checks

* `commands.json` and the logs record commands, exit codes, and durations.
* `declarations.json` contains full types, premises, allowed axioms, and direct
  proof dependencies. Fresh and compiled signatures must agree.
* `source_hashes.json` identifies the source, documentation, and audit tooling.
  `dependency_revisions.json` must match the pinned manifest, and tracked
  dependency sources must be clean.
* `original_statements.log` checks the original theorem interfaces by Lean
  definitional equality, including the unfolded bounded-difference predicate.
* `root_imports.log` excludes the optional compatibility and example modules,
  FoML, and the former bridge from the generic root import.
* `reject_axiom.log` is an **expected failing** Lean check. The runner requires
  the specific custom-axiom rejection, so a syntax error cannot count as a pass.
  Python tests also check rejection of missing or duplicate records, `sorryAx`,
  custom axioms, late errors, changed types, and unreviewed premises.

To inspect a deliberate interface change, use `--inventory-only` and read the
new elaborated statements, definition context, and proof edges before manually
updating the reviewed inventory. This mode does not approve the change.
Do not refresh hashes merely to make the check pass.

The GitHub workflow runs this same audit and retains its evidence. Local
validation establishes no remote CI result. Before an upstream submission,
a human contributor should review the proof, settle upstream namespaces and
file placement with maintainers, and adapt the contribution to the then-current
mathlib revision and contribution requirements.
