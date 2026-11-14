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
