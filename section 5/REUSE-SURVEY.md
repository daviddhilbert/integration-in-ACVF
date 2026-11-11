# Section 5 reuse survey

Started November 10, 2026 (America/Los_Angeles).

| Source | Revision | License |
| --- | --- | --- |
| Special transformations | `9cc9760892092dd34cfad4a6dee655843c52f30c` | MIT |
| ACVF-QE | `939346b0a99899e22a873479364e3cc5d142731c` | MIT |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` | Apache-2.0 |
| Sequel starting checkpoint | `c8f4270` | Existing repository terms |
| Lean | `leanprover/lean4:v4.35.0` | Existing toolchain |

Read the predecessor's `LANGUAGE-ERRATA.md`, `Section4/STATUS.md` and
`Section5/STATUS.md`. Preserve named RV inversion and the single absorbing
point. The original old `CategoryLift` exports are conditional; prefer the
proved producers and repaired `Paper` exports rather than treating those
conditions as standing authorizations in this sequel.

## Selected reuse

- `Section5/Geometry.lean`: use actual `Point`, `key`, `SameRV`, hull and
  `IsRVPullback`; these compare RV classes, not only valuations.
- `Section5/Core.lean`: use actual definable `Map`, alternating
  `SpecialBijection`, its inverse, `Contractible`, `keyImage`,
  `contractionFun`, `contractionMap` and the unique definable contraction.
  No duplicate language, RV quotient or special-bijection definition.
- `Section5/GeneralExistence.lean`: `map_preparation_at_boundary` constructs
  actual special bijections in every finite mixed arity. It explicitly
  takes uniform vertical obstacles; discharge that premise with
  `Section5/VerticalObstacles.uniformVerticalObstacles` using genuine
  saturation and smallness. `Values.presentationValuation` and its proved
  compatibility remove a separately postulated valuation.
- `Section5/GammaExistence.lean`: `gamma_map_preparation_at_boundary` keeps
  full invariant locus/focus graphs over the original Gamma base, even when
  the working real code set is larger. Supply its logic and support inputs
  from `gammaLogicInput` and `gammaPolynomialSupportInput_of_fieldBase` in
  `GammaInvariantLogic` and `GammaPolynomialSupport`; never assume them.
- `GammaRestriction`: reuse chain graph and inverse graph theorems.
  `GammaBaseInputs.gammaPresentationInput` and
  `GammaGraphDefinable.real_specialize` offer the next common-presentation
  bridge. Their finite code sets must be combined without changing the
  final original-base graphs.
- Sequel `IntegrationSection3ACVF.CoordinatePartitions`: reuse the actual
  uniform coordinate-fibre partition for 5.2. Do not restate it as an
  assumed property of saturation.
- Pinned Mathlib: use `Function.Bijective`, `Equiv`, subtypes and ordinary
  function composition for the new quotient and relatively unary calculus.

The new 5.1 draft applies map preparation first to the target identity and
then to the transformed map. This avoids rebuilding polynomial preparation.
The new 5.2 quotient criterion proves exactly which remaining geometric
condition is necessary: inverse contractibility. It does not construct that
condition or complete 5.2.

No external proof source, HK theorem, referee claim or new citation is used
as an input. This batch imports existing declarations directly, with their
source attribution retained in the dependency. No source was ported from a
new external Lean project. Further reuse surveys are required before the
substantial 2-cell/relative-special construction, beyond these existing APIs.

## Build evidence

Fresh local dependency and proof compilation is pending. Toolchain version
was checked as Lean 4.35.0. Mathlib cache download was denied by the environment
proxy for `cache.mathlib.org`; an allowlist update was requested. A from-source
build of the actual prerequisite modules is running instead. The earlier
broad builds were deliberately interrupted (exit 130), retaining completed
artifacts. The target still inherits the foundation's whole-Mathlib import. Do not treat this
running build or source inspection as a passed proof certificate.

`GammaMapPresentation` now drafts the common-presentation bridge: take the
union of the three finite-code parameter sets, apply existing parameter
monotonicity, and retain the exact same source, target and function. The
set-level 5.1 wrapper has no presentation or code-set smallness premise.

## Checked first batch

All required pinned dependencies were built from source. The 72-head Section 5
build and complete type/axiom audit passed locally. The verifier prints proof
arguments and deeply nested types without omissions and records the full
types. Only the three permitted axioms occur. See VERIFICATION.json for exact
source and audit identities. Wider root integration remains a separate run.

The source focus is now constructed by composing the definable target-focus
section with the given inverse, selecting exactly those source RV cells
containing that point, and taking the VF coordinate as centre. Existing
first-order relation, graph and parameter-base operations prove the entire
locus and centre graphs over the original real base. The compatible-focus
induction and invariant Gamma certificate remain distinct obligations.
