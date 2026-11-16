# Section 7 completion

The active Section 7 mathematical targets are complete in the accepted scope.
The public corrected entrypoint is
`Integration7.HKCorrectedSection7Results`; corrected declarations use
`IntegrationInACVF.Section7.HK`.

The corrected convention retains arbitrary nonzero definable RV forms in
measured degree zero, with exact weight-preserving zero isomorphisms and
multiplication of both forms in every product. Ordinary RV[0]/VF[0] remain
ordinary. The checked predecessor is
`25852c85a31c67069b148bd31348128318303510`.

| Result | Checked interface |
| --- | --- |
| 7.5 | `lemma_7_5`, `lemma_7_5_ordinary`: actual specified contractions, with the accepted nonempty selected set |
| 7.6–7.9 | The existing positive-dimensional contraction, order-exchange and lift/integration results, together with exact weighted-zero lift/integration adapters |
| 7.10 | `HK.theorem_7_10`: corrected all-degree class integration and lift equivalence |
| 7.11 | `HK.proposition_7_11`, `HK.proposition_7_11_ring`: actual supported coordinate integration over the full corrected coefficient semiring and its Grothendieck ring |
| 7.12 | `HK.proposition_7_12`, `HK.proposition_7_12_ring`: the unpadded actual supported Jacobian transform in every function degree |
| 7.13 | `HK.raw_volume_kernel_principal`, `HK.theorem_7_13`: the actual single-generator raw kernel and ring quotient |
| 7.14–7.15 | `HK.theorem_7_14`, `HK.theorem_7_15`: normalized supported Fubini and change of variables |

Raw head, prefix and arbitrary-coordinate integrals and global/supported
Jacobian transforms are linear over the full corrected graded coefficient
semiring. The support module is the faithful image of actual supported
presentations. Balanced scalar extension gives the unnormalized ring-valued
functions, their geometric operators and their integral identities on all
formal differences. The corrected normalized coefficient ring is commutative.
No raw point padding is cancelled.

The accepted restrictions and standing hypotheses are retained: Lemma 7.5
has nonempty selected E; function-space interfaces have positive VF dimension
(index n represents n+1 VF coordinates), with nonempty retained-coordinate
projections and a separate total integral. Actual finite-volume conditions,
the original parameter base, canonical structure, characteristic, saturation,
smallness, VF/Gamma generation and named Gamma assumptions remain explicit
where required. Completion does not assert stronger statements obtained by
dropping those hypotheses, or equality of legacy and corrected measured-zero
categories.

There is no remaining Section 7 proof obligation in this accepted target.
Earlier open-boundary paragraphs in incremental ledgers are historical.

The sealed registry contains 2,041 source modules plus Library and 6,711
audited exports. The final two batches add 40 modules / 140 exports; every
new actual source compiled, every complete new exported type and allowed-axiom
report was reviewed once (1,791 + 1,356 lines), and both affected Library
builds passed. Only `propext`, `Classical.choice` and `Quot.sound` occur.
The final root build passed 13,548 jobs including valid cached dependencies.
Final automated verification and publication evidence are recorded separately
in `../verification/hk-upgrade/` and `HK-CORRECTION-STATUS.md`.
