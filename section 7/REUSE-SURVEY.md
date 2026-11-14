# Section 7 reconstruction and reuse

The target paper is Yin, arXiv:0809.0473v2, Section 7. Lemma 7.5 has the
user-approved restriction to a nonempty selected coordinate set; see
`TARGETS.md`. Recovery and subsequent reconstruction are separate activities.

The original 1,201-module working copy is unavailable. Sixty complete module
texts were reconstructed from visible conversation commands and remain
preserved in `.scratch/recovery/transcript/Integration7/`. Their manifests
record current hashes, provenance limitations, and verification status.
Newly written prerequisites are not counted as recovered original sources.

## Pinned inputs

- Lean 4.35.0, `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Special transformations `9cc9760892092dd34cfad4a6dee655843c52f30c`.
- ACVF-QE `939346b0a99899e22a873479364e3cc5d142731c`.

All eleven dependency checkouts passed `scripts/prepare_ci.py`. The
predecessor's language errata and the relevant Section 4 and Section 9
status documents were read before reusing their interfaces. Historical
verification paragraphs under older pins are not new build evidence.

## Algebra

`SemiringGroupification.lean` uses Mathlib's `FreeRing`, `ringConGen`, and
`RingCon.Quotient`/`lift`. Mathlib's sources are Apache-2.0; their authors
and attribution remain in the imported modules. The construction imposes
the semiring generator relations for zero, one, addition, and multiplication.
It works for a possibly noncommutative semiring without cancellation.

The recovered `SemiringGroupificationDifferences.lean` compiles unchanged
against this reconstructed interface. Its difference normal form,
surjectivity result, and induced ring equivalence passed a targeted full
type/axiom audit along with the reconstructed provider. This is algebraic
support for 7.13; it does not establish the missing geometric isomorphism.

`CentralAwayLocalization` and `GradedUnitNormalization` were recovered,
compiled, and audited separately. Their existing receipts remain valid;
they have not been subjected to another full-section audit.

## Definable geometry

Use the predecessor's actual `Space`, `DefSet`, `Map`, `RVFiniteObject`,
`rvFiniteEssential`, RV operations, RV dimension, and partial RV/Gamma
Jacobians. Do not introduce a replacement language, a second absorbing RV
element, or theorem-shaped saturation assumptions.

`VolumeForms.lean` reconstructs nonzero definable RV-valued densities and
their pullback, parameter extension, and restriction. `RVVolumeObjects`
uses these on the existing finite-volume objects and retains ordinary
RV[0] in degree zero. `RVVolumeMorphisms` states the actual generic RV
and pointwise Gamma compatibility equations on essential parts, matching
the checked Section 2 concrete-volume interfaces and the recovered source
uses. `UniformVolumeData` forgets its auxiliary density only at degree zero.

The recovered `RVCoordinateSelection` needs no Section 7 geometry provider.
The recovered `VFRVFibres` only uses the form interface, so its promoted
copy replaces the unavailable `UnaryVFVolumeFibres` import with
`VolumeForms`. Its proof text is otherwise preserved. The quarantined
recovered copy remains unchanged.

Definitions or still-uncompiled reconstructed sources are not proofs of
7.1–7.15. Source compilation, full types, axiom checks, and affected import
checks are recorded per completed batch. No new Section 5.8 hypothesis is
introduced by this reconstruction.

## Elementary-blowup comparison reconstruction

At the same pinned predecessor revision, `exists_definable_generic_RVJacobian`
supplies actual head and full Jacobians. `isRVJacobianAt_zero_arity` handles
the empty head without changing RV[0]. Section 6's
`Admissible.finite_label_fibres` and the source finite-volume fibres prove
that the unchanged head is finite-to-one. No finiteness conclusion is taken
as an extra saturation premise.

The new tangent calculation uses Mathlib's polynomial renaming, partial
derivatives, polynomial roots, `Polynomial.derivative'`, and determinant
expansion. The punctured vertical line consists of actual corrected chart
points. Its polynomial identity forces the last tangent column; coordinate
projection supplies the head block. Algebraic closedness of the residue
field is obtained from the released `VFAlgClosed.isAlgClosed_vfType` and
`ValOneEC.Johnson.isAlgClosed_residueField` declarations. Imported Mathlib
sources retain their Apache-2.0 attribution.

`elementaryBlowupIso` now compiles with full type and allowed-axiom inspection.
The affected 62-module Library build passed. The complete fourth targeted
batch has 26 exports; its receipt is
`.scratch/recovery/recovered-fourth-geometry-receipt.json`. The theorem uses
only the actual model/BaseContext hypotheses, source isomorphism and two
concrete admissible elementary blowups; no graph-field or new Section 5.8
input was added. Common refinement remains separate work.

## Actual common refinement

The reconstructed volume overlap uses actual source images, complementary
restrictions and density-preserving coproduct maps. The source geometry in
`IntegrationSection6.OverlapRefinement` and `Confluence` was consulted for
its architecture; an ordinary RV diamond was not used as a volume diamond.
`volumeBlowup_diamond` proves the volume statement from the four pieces and
the checked elementary-blowup comparison. The only imported combinatorial
result is `IntegrationInACVF.Section6.Iteration.grid`, whose geometric
hypothesis is supplied by the newly proved volume class diamond.

The exact-length iterated common refinement and transitivity of actual
common-blowup equivalence compiled, passed full type/allowed-axiom review,
and passed the affected 88-module Library build. The 19-source sixth batch
has 70 exports; no new Section 5.8 premise or theorem-shaped model input is
present. The recovered `VolumeBlowupEquivalence`, `VolumeDegreeTransport`
and `OrdinaryZeroVolumeRows` compile against these reconstructed providers.
Ordinary degree-zero rows are support for the retained RV[0] convention,
not an attempt to reopen the excluded empty-selected-set case of 7.5.

## Concrete VF volume category and prescribed lifts

`Section2VolumeBridge` identifies the density and volume-morphism definitions
with Section2.ConcreteVolumeForms and ConcreteVolumeMorphisms. The positive
lift existence theorem reuses the pinned predecessor's actual
`theorem_9_16_finite_volume_of_reference_input`, supplying its graph input
from the checked sequel `ConstructedGaussGraph.acvf_graph_input`. Generation
of the original VF/Gamma base is retained. The reverse descent uses the
checked `corollary_2_34_nonzero`, with actual label compatibility.

The VF category uses native fixed-label partial derivatives, the checked
generic mixed chain rule, actual same-base dimensions, and genuine
subdomain images/preimages. The local determinant-one argument for maps
preserving VF coordinates follows the checked private argument in
Section9.SpecialJacobianGeneric; attribution is recorded in the source.
It does not assert that a Jacobian is defined at every boundary point.
The thirteen-module batch passed 56 full type/axiom inspections and its
affected Library build (9,849 jobs counting cached dependencies).

## Selected density graphs and positive ordered contractions

The paper's v2 HTML/PDF became accessible through the web connector and
Section7 was read directly. Definition7.1 and Lemma7.2 match the concrete
elementary chart and corrected isomorphism. The numbered wrapper is now
checked. Lemma7.5 retains the author-approved nonempty selected E scope.

Density graphs and their actual volume bijections are rebuilt directly.
NativeVolumeDomains converts the same raw points to the pinned Section5
presentations using canonical normalization, without adding parameters.
The construction of ordered augmented objects reuses
`ordered_selected_fibres_finite` and the actual certified preparation
program theorem. All contracted VF labels and selected original labels
remain in their explicit recursive numerical order. Density transport
follows original-label preservation. No comparison theorem is an object
field. The standing VFFieldBase premise remains explicit for existence.
The target fibrewise common-blowup comparison remains open.

The ten-module batch passed65 full type/axiom checks, including named
instances, and its affected Library build passed10,161 jobs with caches.

## Positive products and signed coordinates

Mathlib's actual `Matrix.det_permute`, `det_submatrix_equiv_self` and
`det_fromBlocks_zero₂₁` are used with explicit coordinate maps. Polynomial
tangent projection gives both complementary blocks; generic existence is
kept separate from determinant comparison. The finite-volume maps bound
RV dimensions by volume degrees, so auxiliary label arities do not enlarge
the almost-everywhere threshold. The resulting positive product map has
both genuine volume equations. Degree-zero factors and multiplicative
common-blowup compatibility remain separate work.

The original VolumeCoordinatePermutation and GammaRVVolumeSchemata texts
were promoted unchanged after rebuilding their missing providers. The
function-row validity theorem reuses checked original-base Gamma logical
operations. No arbitrary Gamma representative is silently added to the
generation hypothesis. All56 new exported types/axioms were inspected,
and the affected Library build passed10,173 jobs including cached imports.

## Tenth reconstruction batch: volume graph realization

Reused the checked Section 6 GammaFiniteGraphPresentation, finite-extra code
extension and full Gamma relation specialization. Added a genuine functional
density map using unique row outputs and exact support. Canonical raw RV
adapters use normalize_eq_of_isCanonical on definability proofs while keeping
points and functions unchanged. Presentation independence uses the checked
coordinate/density-preserving volume isomorphism, hence the existing generic
Jacobian proof rather than a new comparison premise. No new references or
dependency changes were introduced.

## Eleventh reconstruction batch: positive products and blowups

Reused native RV cartesian associators, coproduct maps and elementary
right-product coordinate algebra. The new explicit distributivity chart
retains pointwise coordinates and densities. The recovered signed product
swap was promoted with narrowed imports; its original text remains in
quarantine. Named determinant signs belong to the native residue parameter
field. Left multiplication of elementary blowups is proved by an actual
product chart and algebraicity monotonicity. Right multiplication of common
blowups follows from the signed swap and a proved common rescaling operation.
Only the new batch and affected library were audited; no full repeat was run.
