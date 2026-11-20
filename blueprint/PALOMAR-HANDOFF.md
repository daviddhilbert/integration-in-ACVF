# Palomar handoff

Project: **Integration in algebraically closed valued fields**.
Author of the source paper: **Yimu Yin**.
Paper: <https://arxiv.org/abs/0809.0473v2>.
Repository: <https://github.com/daviddhilbert/integration-in-ACVF>.
Release: **v1.0.0**, accepted Sections 2–7 scopes.

The release contains the mathematical blueprint PDF, a portable web blueprint
with clickable dependency graph, its complete editable source, a whole-project
integrity receipt and SHA256 checksums. GitHub also supplies a source archive of
the exact release commit. The blueprint links to proof commit
`862aa448b4314df673bccd928d1353af6650d7f1`; the release adds documentation,
packaging and corrected root comments without changing any section proof.

Validation: Lean 4.35.0; exact pinned Mathlib, ACVF-QE and special-transformations
revisions in `lake-manifest.json`; root build and foundation plus all six section
verifiers passed. The registered section boundary has **12,597 audited exports**.
There are **71 blueprint nodes / 87 distinct linked declarations**. *(v1.0.0 submission counts. As of November 20, 2026 the blueprint has
84 nodes / 132 linked declarations and the section verifiers audit 12,877
exports; see `verification/project-integrity-2026-11-20.json`.)* The source
manifest covers all section Lean files, including retained audit programs, not
only the selected blueprint declarations. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted by the exported audits.

The paper is formalized in the accepted scopes recorded in the blueprint and
section status files. Preserve the scope and correction paragraphs in any
submission description: the measured-zero convention, nonempty selection in
7.5, positive VF function dimension, explicit 5.5 presentation charts, 3.17's
whole-field boundary, and the original model/base hypotheses all matter.
The graph is a selected mathematical dependency graph. Historical conditional
interfaces and superseded status entries are not additional closed results.

This package is ready for the author's submission preparation. It records no
claim that Palomar has received, validated or accepted the project. Any
Palomar-specific form fields can be filled from this handoff and the linked
exact statements.
