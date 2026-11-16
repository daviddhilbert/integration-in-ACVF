# Weighted measured-zero correction

**The accepted correction and active Section 7 mathematical targets are complete.**
See [COMPLETION.md](COMPLETION.md) for the result map and precise scope. The public
corrected entrypoint is `Integration7.HKCorrectedSection7Results`.

The predecessor is `25852c85a31c67069b148bd31348128318303510`, including weighted-zero
proof commit `d7d7419`. Lean, Mathlib and QE pins are unchanged. Corrected interfaces
use `IntegrationInACVF.Section7.HK`; legacy interfaces retain their original scope.

## Checked boundary

The sealed registry contains **2,041 source modules plus Library / 6,711 exports**.
The final two batches add 40 modules / 140 exports, each with actual source
compilation, one complete exported-type/axiom review (1,791 and 1,356 lines), and
Library integration. The final Library build passed 13,336 jobs and the final
root build passed 13,548 jobs including valid cached dependencies. Only propext,
Classical.choice and Quot.sound occur. Earlier exports were not manually audited again.

Exact weighted RV/VF zero adapters, geometric coproducts/products, genuine
weighted degree-one blowup factors, and the actual point-minus-cone principal
kernel prove corrected class 7.10 and 7.13. Actual head/prefix/coordinate and
supported Jacobian operators are linear over the full corrected graded coefficient
semiring, including zero coefficients and zero-valued inputs. Balanced scalar
extension proves raw supported 7.11/7.12 over the corrected Grothendieck ring on
every function and formal difference. Corrected normalized supported 7.14/7.15
and commutativity of the normalized coefficient ring are proved. No raw point
padding is cancelled. The accepted nonempty-selected scope of 7.5 and standing
hypotheses remain explicit; the function interfaces have positive VF dimension.

Section 2 exact weighted-zero descent and the nine open-radius consumers in
Sections 3–5 were adapted and reviewed once. No new pure Gamma/RES campaign or
general coarsening functor is part of the accepted target.

There is no remaining Section 7 mathematical proof obligation in this scope.

## Automation and publication

The final full-project automated verification passed for the foundation and Sections 2–7 at the sealed 2,041-module / 6,711-export boundary. The Section 7 audit took 46.7 seconds. No fresh remote CI pass is claimed yet.

The completed source is the 2,041-module / 6,711-export completion revision on
`section-7/reconstructed-foundation`. The previous checkpoint is
`f032c6ae97948837191867cf94a749637708d5a4` (2,001 modules / 6,571 exports).
The final 40-module increment is task-completion publication; routine intermediate
backup cadence remains about 100 modules. The final workflow preserves an
in-progress cache-warming run instead of cancelling it on every new push.

Versioned incremental receipts are under `verification/reconstruction/`;
`../verification/hk-upgrade/` records integration evidence. Historical receipts
retain their original types and revisions.
