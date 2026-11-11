# Section 2 reuse and new proofs

The finite-immediate batch adds actual algebraic-envelope and valuation-ring
transport. `AlgebraicEnvelopeBases` derives algebraicity and Galoisness of
the comap bases from the actual algebraic closure. `ValuedSubfieldRestriction`
constructs exact base field/ring equivalences. Mathlib's checked
`AlgHom.liftNormal`, normal-embedding bijectivity and trace as a sum of all
embeddings extend the earlier argument to non-Galois finite extensions.
`FiniteImmediateSubfield` constructs the envelope internally, with degree
transport from `rank_eq_of_equiv_equiv`. Primitive subextension degree is
proved using actual independent powers and the minimal polynomial bound.
The residue-image surjectivity and immediate-approximation arguments are
proved directly on the actual field/residue maps. No new external result
or accepted finite-extension reference is assumed in these ingredients.

The henselian-support batch reuses the actual proved
`Section6.HenselianInvariance.henselian_automorphism_invariance` (in namespace
`SpecialTransformations.Section6`), the checked algebraically closed valued
field Hensel bridge in `Section7/ValuationHenselian.lean`, and Mathlib's
`InfiniteGalois.mem_range_algebraMap_iff_fixed`, trace as a sum of Galois
automorphisms, basis/finite-dimension calculus and primitive element theorem.
Complete source types and assumptions were inspected. These are already
formalized results, not new external reference inputs. The residue-normalization
calculation generalizes the pinned `ValuedPowerBasis.lean` proof. Primitive
root lifting adapts `UnramifiedGenerator.lean` while replacing its use of the
desired degree equality by the independently proved residue finiteness.
The source notices and exact predecessor pin are retained in the new files.

Source version: arXiv:0809.0473v2. Dependency revisions are fixed by
`lake-manifest.json`; Special transformations is pinned at
`9cc9760892092dd34cfad4a6dee655843c52f30c`.

Corollary 2.15 is not merely a restatement imported by name. The stronger
`SpecialTransformations.Section3.GammaParameters.GammaRVFamily.finite_projection`
in `Section3/GammaRVSeparation.lean` proves finite projection for a uniform
actual-Gamma-to-RV relation with finite rows. Its hypotheses are genuine
saturation, a countable lower bound on the saturation cardinal, a small real
base, and ACVF(0,0). Its full invariant graph is interpreted in canonical
normalization. The new proof applies this theorem to a partial function's
graph: every row is subsingleton, and the projection is exactly its range.

For a base also containing genuine Gamma names, use
`GammaParameters.DefinableOverBase.specialize` and `small_union_range`.
The chosen finite representative tuple is used only inside the proof of
finiteness. The stated hypothesis remains full graph definability over the
original base. No bound on the total set of Gamma names is added.

The new wrappers passed the full project build and both full type/axiom
audits in CI run 42789563292. The stronger predecessor theorem is proved rather than supplied
as an unproved field of a model interface. Its original sources and notices
remain in the pinned dependency.

For Corollary 2.34, inspect the concrete Jacobian bridge and the Section 10
status before choosing a target. `Sec10RVVol.lean` includes explicit volume,
dimension and Jacobian inputs. A generic theorem under those inputs must not
be counted as the full concrete ACVF assertion without providing them.

## Concrete volume descent

The new bridge uses the pinned active `Section9/PaperLiftComparison.lean`,
`GammaPolydiscDescent.lean`, `MixedJacobian.lean`, `RVJacobian.lean`,
`GammaJacobian.lean`, `RVFiniteEssential.lean` and `GaussGraphConstruction.lean`.
Their actual sources, theorem types and Section 9 status, handoff, category
audit and language errata were inspected. The RV comparison and constant-value
Gamma descent retain `HenselizedGaussGraphInput`. Its construction retains
`FiniteHenselianExtensionReference`. The predecessor records the underlying
Engler–Prestel facts as authorized inputs; no new reference is introduced.
Neither input is treated as an unconditional checked theorem.

`LiftFibreAvoidance` uses the actual full-polydisc VF-dimension theorem.
`FixedLabelLift` constructs the restriction and proves bijectivity and
preservation of actual derivative charts. `LiftFibreGeometry` checks the
exact released RV quotient/polydisc relation. `GenericVolumeDescent` uses
actual Jacobian uniqueness. `GammaVolumeDescent` separately proves the value
equation at every essential label via checked polydisc descent.
`VolumeBadLabels` pulls the RV exception back along the finite volume map.
`ConcreteVolumeMorphisms` spells out both volume conditions with actual
Jacobians. No volume law, comparison or Gamma compatibility is assumed as
a model-interface field.

All 11 modules compiled individually and passed complete type/axiom checks
before integration. The full root and both section audits then passed.
The Section 2 verifier prints forms, morphism conditions and precise
reference inputs with a larger pretty-printer limit for long category types.
Reprinting all previous 1,244 Section 3 types at that larger limit gave
exactly the same types; their omissions were proof arguments rather than
omitted type structure. Pins and dependency sources are unchanged.
