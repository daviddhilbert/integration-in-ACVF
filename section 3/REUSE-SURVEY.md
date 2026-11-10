# Reuse survey for the first Section 3 implementation

Checked 2026-11-09 (America/Los_Angeles).

## Fixed inputs

- Paper: arXiv:0809.0473v2, 29 December 2010, Definition 3.1 and the proof of
  Lemma 3.2; Section 2 supplies the review boundary.
- Special transformations: `9cc9760892092dd34cfad4a6dee655843c52f30c`.
- ACVF-QE: `939346b0a99899e22a873479364e3cc5d142731c`, inherited.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Lean: `leanprover/lean4:v4.35.0`.

No OpenMathOS sources, plans, proof artifacts or claims were imported.

## Sources inspected and decisions

1. `Mathlib/ModelTheory/Definability.lean`: use `Set.Definable`, `DefinableMap`,
   parameter monotonicity and projection/preimage closure directly. The new
   atomicity definitions describe the paper's semantic condition over these
   genuine first-order predicates. The graph/projection argument for images
   follows this file's `Set.Definable.preimage_map` construction. Mathlib code
   is Apache-2.0; its original source and notices remain in the dependency.
2. `Mathlib/Order/BooleanSubalgebra.lean`: reuse `closure` and
   `closure_bot_sup_induction` instead of introducing another inductive syntax
   for finite Boolean combinations. `HasFiniteBallSupport` is a finite support
   witness, not a replacement ACVF language.
3. The predecessor's `Section3/Parameters.lean`, `ModelContext.lean`,
   `BallGeometry.lean`, `BooleanCombinations.lean`, `CMinimal.lean`,
   `QuotientFamilies.lean`, `FibreDescent.lean` and relevant status/errata.
   Their parameter, ball, saturation and powerset-family interfaces are the
   intended ACVF reuse boundary. They do not already define the sequel's
   atomic subsets. The finite-exception lemma is first proved independently
   in a generic laminar family; adapting it to `Enc.IsBoolComb` and actual
   imaginary ball codes is still required.
4. Repository-wide source searches for `atomic`, `Atomic`, `CompleteType`,
   `IsBoolComb`, `BallGeometry`, `DefinableMap` and Boolean closures found
   syntax-level uses of atomic formulas and the above reusable APIs. Those
   are different from the sequel's atomic definable subsets. Legacy
   scaffolds with duplicate RV encodings were excluded.

This initial task adds generic logical and finite-set arguments, rather than
rebuilding a substantial external mathematical prerequisite. No new external
dependency or toolchain upgrade was selected. Broader external searches are
still required if the ACVF imaginary-code bridge needs a new major interface.
Source inspection and upstream verification reports are distinct from the
fresh local compiler/axiom evidence recorded by `verify.py`.

## First-order family argument and ACVF bridge

The unary parameter-promotion proof adapts
`SpecialTransformations.ModelTheory.promote_definable_tuple_fibre` from
`Section3/GammaBaseTools.lean`, retaining its formula-relabeling construction.
The definable exceptional-family proof uses Mathlib projection and Boolean
closure; it adds no index or support-ball representative to the original base.
These two new core modules have passed compilation and full type/axiom audits.

The pending ACVF bridge adapts the valuation conversion in the predecessor's
`GammaThresholdGeometry.encodedBall_good`, retaining the stronger single-ball
property. It uses `ValOneEC.isKBall_subset_or_subset`,
`EncodedBallGeometry.isBall_subset_vf`,
`SortedBoolean.definableAt_iff_normalized_raw`, and the proved
`CMinimal.theorem_2_8_c_minimal`. The full raw definability is interpreted in
canonical normalization, because arbitrary unsorted totalizations must not
be mistaken for the sorted language. The predecessor's source and notices
remain in the pinned dependency. Compilation of this bridge is pending CI.

For the remaining imaginary interpretation, inspect `ClosedBallCodes`,
`ClosedBallQuotient`, `OpenBallCodes`, `GeneralBallCenters` and
`GeneralCosetChoice`. They supply actual quotients by equality of underlying
balls and define family definability by full real preimages in both charts.
`GammaParameters` uses the corresponding invariant-preimage convention for
genuine value-group parameters. These are preferable to naming chosen real
representatives or introducing an unrelated ACVF language.

`ImaginaryFamilies` now supplies the language-generic full-preimage argument.
Its presentation consists of real code data, a surjective decoding map, and
separate first-order definability of the domain and interpreted equality.
Equality can be proved from an injective definable point-membership relation.
This is an interpretation interface, not an assumed atomicity or algebraicity
result. Its closure, projection, composition, algebraicity-transfer and
finite-exception theorems passed the same local compiler/type/axiom checks.
The bridge to the actual predecessor ball presentation remains in progress.
