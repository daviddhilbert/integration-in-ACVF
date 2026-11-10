# Section 2 reuse and new proofs

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
