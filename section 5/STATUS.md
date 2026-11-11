# Section 5 status

**Lemmas 5.1 and 5.2 are locally checked** in the recorded original
real/Gamma base scope. The full Section5 is still in progress. The current
197-declaration full type/axiom audit passes with only propext,
Classical.choice and Quot.sound. All161 prior complete types are unchanged.
The root build and full project audits pass for foundation and Sections2,3,5;
Sections4,6,7 have no local verifiers and are skipped.

Lemma5.1 prepares arbitrary mixed finite maps. Lemma5.2 now constructs both
special bijections for an arbitrary unary definable bijection and produces
the unique commuting definable RV-key bijection. Its final theorem does
not assume contractibility, inverse contractibility, an open-to-open
partition or the desired geometric equivalence.

The original-base5.2 scope is ACVF(0,0), genuine saturation with aleph0≤κ,
small P.real, VFFieldBase P.real and a named Gamma value δ with1<δ.
The complete original map graph and domain definability are explicit.
Internal real presentations may be enlarged, but every constructed focus
and special chain has a full invariant certificate over the original P.
No smallness bound on the internal code set or ball names is introduced.

The proof imports checked Proposition3.21, proves the Gamma/no-ball-full-base
bridge and its mixed tuple translation, then prepares all finite partition
membership flags. Actual inverse-special geometry yields the required
open-to-open property. Compatible chain induction matches every target
focus, keeping both directions contractible. Boundary alternation and the
existing last canonical step are tracked explicitly. Inverse preparation
comes from genuine saturation and the checked predecessor producer.

Entry points: `UnaryBijection.lemma_5_2` is the set-level result;
`UnaryBijectionPreparation.lemma_5_2_gamma_presented` starts from an actual
working real presentation. `UnaryBijectionFromPartition` and
`GammaOpenPreparation` record the assembly. `GammaFullBaseBridge`,
`GammaPointRawBridge`, `GammaGraphRawBridge` and `UnaryCoordinatePartition`
retain original-base semantics. `GammaMembershipPreparation` prepares
finite map families at an explicit chain boundary. The earlier geometry,
quotient and relatively-unary modules remain checked support.

Next: Lemma5.3 must construct actual RV[1,·] morphisms in both directions,
including weight and finite-volume-image conditions. Full fibrewise
relative specialness(5.4), standard contractions(5.5), general5.6 and
2-cell results5.7–5.8 remain open. An arbitrary RV-valued map is not a
standard contraction; an RV-key bijection alone does not prove5.3.

Local evidence: `.scratch/section5-197-verified/`, full types and exact
source/pin/audit hashes in VERIFICATION.json, plus the lemma52 root and
project verification logs. The prior161-head checkpoint2428bd0 passed
CI43075798136. Artifact13882848565 exactly matches its preserved local
receipt and that verified checkpoint was promoted to main. Remote CI
confirmation of this197-head batch is a separate publication step.

No Section5 result is assumed as a prerequisite of itself. No HK result,
referee assertion or new external citation is a proof input. This work
follows the paper's partition-and-matching argument; ordinary parameter
and Lean API bridges are not counted as substantially different proofs.
