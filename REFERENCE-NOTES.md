# Annotated referee reference

The user supplied `blowup_accepted_version_annotated.tex` on November10,2026
(America/Los_Angeles), as reference material only, explicitly asking that
the formalization be developed independently. It contains an annotated
manuscript and51 inserted referee remarks. The referee's classifications,
proof suggestions and citations are claims to inspect, not checked inputs.
The target version remains arXiv:0809.0473v2; no statement correction or
new citation is authorized by this attachment alone.

SHA256:`fab0f527a81af3503adcfb0da3bc2f623958e294ccc959a860520b41867bf8d5`.
A local reference copy is in
`.scratch/reference/blowup_accepted_version_annotated.tex`.
The annotated source itself has not been added to the published repository.

Section3 comparisons:

- R010 discusses the unnamed-radius issue in3.4, independently already
  recorded in this project. Its proposed repair invokes quantifier
  elimination with named balls; that full parameter bridge is not thereby
  verified. The new finite-hitting/profile approach was developed before
  reading the attachment and continues independently. The route now proves full-base open-ball3.4 and3.15 in the969-head local
  checkpoint; the983-head local extension also includes unnamed closed radii.
  Its earlier plan `.scratch/full-base-315-plan.md` is historical;
  no proof input is taken from the report.
- R013 discusses a last step in3.16. The existing checked formalization
  already supplies its own Gamma-slope rigidity proof. No new premise or
  proof claim is taken from this remark.
- R014 discusses least-radius existence in3.17. Current checked scope
  explicitly quantifies over a given least-radius function. Existence is
  not added to that scope by the referee's suggested justification.
- R017 concerns the endpoint description in the proof of3.24, not a
  counterexample to its proposition. Independently from the definitions,
  after translating a point of the open hole to zero, a closed parent of
  radiusrho and open hole of radiusr give rho<=val(x)<=r; an open parent
  gives rho<val(x)<=r. Thus the respective value intervals are closed
  and half-open (the first can be a point). This is an elementary endpoint
  check, not a completed Lean proof of3.24. The induced quotient map and
  the required definable-bijection obstruction still need checked proofs.

No assertion is made that all51 remarks have been independently verified.
The existing no-HK-citation and outside-citation approval rules remain in force.
