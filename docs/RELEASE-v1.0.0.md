# v1.0.0 — Integration in ACVF

This release collects the checked Sections 2–7 development in the accepted
scopes, including the HK correction to measured degree zero and the completed
Section 7 raw and normalized integration results.

The corrected measured categories retain arbitrary nonzero definable RV forms
in degree zero, with exact weight preservation and multiplication of both forms.
The final interfaces prove all-degree class integration, the actual
single-generator raw volume kernel, full-coefficient raw supported Fubini and
unpadded change of variables over the coefficient semiring and its Grothendieck
ring, and normalized supported Fubini and change of variables. The closed
Section 6 interfaces derive their needed Section 5 input by checked proofs.

Scope remains explicit: RV[k] has finite-to-one volume maps and arbitrary
auxiliary RV arity; 5.5 uses explicit presentation charts; 7.5 has nonempty
selected coordinates; the function interfaces have positive VF dimension and
nonempty retained-coordinate projections, with separate total integration.
The standing model/base hypotheses and approved earlier corrections remain.
Ordinary degree-zero categories are unchanged. This release does not claim
additional pure Gamma/RES integration results or unrestricted versions of
statements beyond the documented scope.

Validation: Lean 4.35.0 and exact pinned dependencies; a passing whole root
build and foundation plus Sections 2–7 verification; **12,597 registered section
exports**; only `propext`, `Classical.choice` and `Quot.sound` in allowed-axiom
audits. The proof revision is `862aa448b4314df673bccd928d1353af6650d7f1`, with
[passing CI](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43851204054).
Every published file at that revision was compared against the cloud workspace.
The release workflow additionally checks that every protected proof input on
`main` equals that CI-passed revision. The root aggregate has only comment
changes and identical imports; no section proof is changed by the packaging.

Assets include a **71-node / 87-declaration mathematical blueprint**, its PDF,
portable HTML and clickable graph, editable source, Palomar handoff,
whole-project integrity receipt and SHA256 checksums. The blueprint source links
are pinned to the checked proof revision. Palomar submission remains the
author's next step; no submission or acceptance is implied.

Read `blueprint/README.md`, `PROJECT-AUDIT.md`, `PAPER-CORRECTIONS.md` and
`section 7/COMPLETION.md` for the exact boundary and build instructions.
