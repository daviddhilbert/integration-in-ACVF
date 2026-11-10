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

The checked ACVF bridge adapts the valuation conversion in the predecessor's
`GammaThresholdGeometry.encodedBall_good`, retaining the stronger single-ball
property. It uses `ValOneEC.isKBall_subset_or_subset`,
`EncodedBallGeometry.isBall_subset_vf`,
`SortedBoolean.definableAt_iff_normalized_raw`, and the proved
`CMinimal.theorem_2_8_c_minimal`. The full raw definability is interpreted in
canonical normalization, because arbitrary unsorted totalizations must not
be mistaken for the sorted language. The predecessor's source and notices
remain in the pinned dependency. This bridge passed the full project build
and its full type/axiom audits in CI run 42789563292. The sorted C-minimality
wrapper is reused directly from `RVUnaryLift.DefinableAt.isBoolComb_balls`.

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
The actual predecessor ball presentation is now checked over real bases.
The additional imaginary names in a full C• base remain open.

## Lemma 3.3: search beyond the predecessor's Section 3

The pinned predecessor's `Section4/GammaDefinablePoint.lean` already proves
`SpecialTransformations.Section4.gamma_definable_point` and its finite-tuple
version. The scalar theorem assumes ACVF(0,0), an actual Gamma value `δ`
whose singleton is definable over the original real base, and `1 < δ`.
Every nonempty Gamma-definable set then contains a point with its singleton
definable over that same base. These are proved from intrinsic finite
controllers and ordered-group samples; no o-minimality or choice conclusion
is assumed as a model field.

Reuse this result for the nonempty exceptional Gamma set in Lemma 3.3.
Related checked interfaces are `Section4/GammaPredicates.lean`,
`GammaControllerDefinability.lean`, `GammaFiniteDefinablePoints.lean`,
`GammaDefinableClosure.lean` and `FiniteOrderSamples.lean`.
For real outputs, the Section 3 `GammaParameters.Relation` API supplies
complement, intersection, real-coordinate projection and definable-parameter
elimination. `GammaAtomicity.lean` now proves the real-base case for arbitrary
finite mixed output arity and every finite Gamma tuple; its five type/axiom
audits passed in CI run 42789563292. The full C• base containing ball names
still needs an explicit sequel bridge. Do not rebuild
the original-base Gamma definable-point theorem or silently drop its named
nontrivial-value hypothesis.

## Lemma 3.4: additive cosets and interpreted ranges

`DefinableCosets.relation_definable` already proves original-base
definability of the actual VF difference/coset relation. Its
`mem_relation` identifies membership with equality in the actual additive
quotient. Reuse these results and `QuotientAddGroup` rather than introducing
a new equivalence relation or assuming same-radius ball families definable.

`InterpretedRanges.rangeFamily_definable` derives definability of the family
of interpreted objects whose underlying sets equal fibres of a definable
real relation. Equality is a universal real quantifier and range membership
is an existential real quantifier, both over the original base. This is the
missing family-construction step for `atomic_below_complete_type`.

`BallCosetAtomicity` applies it to all ball imaginaries that are cosets of an
actual definable additive subgroup of VF. Disjointness is proved in the
quotient, and no centre is named. This new instance is awaiting compilation
and type/axiom checks. To specialize to a ball with a named radius, inspect
Mathlib's `Valuation.leAddSubgroup` and `Valuation.ltAddSubgroup`, together
with the predecessor's `RVUnaryLift`, `rv_le_normalize` and RV definability
APIs. These supply actual zero-centred valuation-ball subgroups; their
original-base definability and the ball/coset equality still need proof.
# Named-radius specialization

`NamedRadiusAtomicity.lean` uses the same pinned predecessor revision and
Mathlib revision listed above. `GammaParameters.raw_le_definable`,
`rv_le_normalize`, and `DefinableAt.rv_preimage` give the zero-centred
subgroup's definability over the original base. Mathlib's
`Valuation.leAddSubgroup` and `Valuation.ltAddSubgroup` supply the actual
additive subgroups. `CanonicalRV.encodedRv_surjective` supplies a VF lift only
inside the proof; no chosen VF representative appears in the parameter base.
The resulting real-base statement covers a nonzero RV radius already in
the base and both the open and closed inequalities. Full imaginary bases
and the singleton/whole-field cases are separate follow-up obligations.

The preceding coset module passed the complete root build and 84 Section 3
headline audits in run 42805178064 at source 19265875181911103ae0c8fabfd03891b3d42d4c.
The named-radius specialization awaits its own complete build and audit.

`GammaRadiusAtomicity.lean` further reuses the predecessor's
`Section4/RVValueFibres.lean`: `RVValueDefinable`, `rvValuePullback` and
`gamma_value_definable`. Quantifying the full value fibre extends the argument
to every original-base definable Gamma radius. `Values.vrv_le_iff` proves the
comparison invariant under a change of RV representative. Singleton balls
use the checked subsingleton argument, and VF uses the full additive
subgroup. These extensions await compilation and full audits.

## Additional imaginary parameters

The new generic `ImaginaryParameters.lean` follows the finite-support/full-code
design of the pinned predecessor's `GammaParameters.lean` and
`GammaSpecialization.lean`. The latter's `GammaBaseCMinimal.lean` provides the
same proof pattern: choose real codes inside a specialization proof, then
use C-minimality over that explicitly enlarged real base. No representative
is inserted into the original definability definition.

The pinned Mathlib `ModelTheory/Quotients.lean` defines quotients of
structures with a prestructure; it does not supply definability over an
arbitrary collection of names from an interpreted sort. Searches of the
predecessor's ball-imaginary sources found no such ball-parameter base.
GitHub repository searches for “Lean model theory imaginaries” and “Lean
model theory interpretation” on November 10 returned no candidate project.
The chosen extension reuses the existing presentations and Mathlib's
definability operations, rather than adding a second ACVF signature.

`OverBase` explicitly uses a finite subset of the named imaginary elements,
with a full invariant first-order relation in all their codes. The module
proves real-code specialization, parameter monotonicity, Boolean closure,
and the transfer of finite ball support. Connecting it to combined actual
Gamma/ball names and to the complete-type family arguments remains work
in progress. The generic parameter-base and family extensions have compiled locally and passed all 86 current core full-type/axiom checks. The family proofs preserve the original interpreted base in the exceptional sets; real-code specialization is confined to obtaining finite ball support.
