# Section 2 handoff

The corrected weighted-zero Corollary 2.34 is checked in
`WeightedZeroVolumeDescent.lean`, directly in upstream `MeasuredRVZero`.
Its determinant-one argument preserves the exact RV form and the given
label map. The four new exports passed full type/axiom review, and the
Section 2 verifier passed all **72** reports under predecessor
`25852c85a31c67069b148bd31348128318303510`. See
`verification/hk-zero/receipt.json`. Positive descent and 2.15 are unchanged.
The old PUnit zero interface remains its neutral-form specialization.

*November 19, 2026:* the all-degree entry point is
`VolumeDescentAllDegrees.corollary_2_34_all_degrees_weighted`. Its degree-zero
branch is `corollary_2_34_zero_weighted`; its positive branches are those of
the legacy theorem. The legacy `corollary_2_34_all_degrees` concludes `True`
in degree zero. See [TARGETS.md](TARGETS.md) for the Section 2 inventory.

## Historical ordinary-zero checkpoint


The final all-degree Corollary 2.34 has no graph or finite-extension
reference hypothesis. Entry points:

- `VolumeDescentAllDegrees.corollary_2_34_all_degrees` for every degree
  (historical; its degree-zero branch is `True`. Use
  `VolumeDescentAllDegrees.corollary_2_34_all_degrees_weighted`.)
- `IntegrationInACVF.Section2.corollary_2_34` for positive essential objects.
- `IntegrationInACVF.Section2.corollary_2_34_nonzero` for nondegenerate objects.
- `ConstructedGaussGraph.acvf_graph_input` supplies the actual predecessor
  graph input from ACVF alone.

All standing canonical-model, BaseContext, actual full-base graph, lift,
bijection and measure assumptions remain explicit. Degree zero has no
volume data or equation. Positive degree uses actual forms and essential
restrictions, a generic RV equation and a Gamma equation on every label.
No unproved volume/Jacobian interface or universal reference is counted as
its own proof. The universal finite-extension reference is not needed.

The full root, inherited QE,68 Section2 and1244 Section3 type/axiom audits
pass. All54 previous Section2 and1244 Section3 complete types are unchanged;
all14 new complete types match individually reviewed audits. Source counts
are41 and368; only the three permitted standard axioms occur. Evidence:
`.scratch/local-closed-volume-68/`, with its own Section2 andSection3 archives.
[CI 43010073720](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43010073720) passed.
All complete types and source/audit hashes match the reviewed local batch
and publication checkout.

All 68 Section 2 and 1,244 Section 3 complete CI types, all 41 and 368 source
hashes, and both audit hashes match these archives and the publication
checkout. The type
parser must allow optional leading `@`: Lean prints the fully explicit
`ConstructedGaussGraph.graph_input` without that character. Use `set -e` in
publication shell sequences. Do not compare with later live artifacts.

The degree proof builds henselian ascent through a constructed Galois
fixed field, then a primitive residue lift. Its generated subextension has
the residue degree and the full residue field. Equal values plus residue
surjectivity make the remainder immediate, and all-embedding trace proves
its degree one. The actual embedding and scalar transports are constructed.
Pins and common language are unchanged. No new outside citation, HK result
or referee assertion is a proof input.

Section 2.15 remains checked. Section 3's exact scopes and the ordinary-ball
least-radius existence boundary in 3.17 are recorded separately. The final
whole-paper writeup remains deferred; its ledger has the completed 2.34 route.
