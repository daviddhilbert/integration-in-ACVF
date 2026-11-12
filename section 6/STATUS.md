# Section 6 status

Updated November 12, 2026 (UTC). All numbered Section 6 targets are
implemented in the finite-category scope below. The complete Section 6
audit, root build and project-wide verification pass.
No numbered Section 6 obligation remains in the scope below.

## Scope and explicit inputs

All public numbered statements concern **RV[k]**, whose volume maps have
finite fibres, and the graded category **RV[*]**. The underlying domains
may be infinite. RV[k,·] is abandoned as a target. Ambient-object modules
are implementation support for these actual finite full subcategories.

The common language, RV morphisms, absorbing zero and reversed valuation
order are inherited from the pinned dependencies. No dependency revision
was changed. Equal valuation is never substituted for equal RV class.

The model is ACVF(0,0), with the recorded cardinal saturation and small
original real/Gamma parameter bases. Native lifting retains the genuine
`VFGammaGeneratedBase` hypothesis. The earlier canonical-presentation
restriction has been removed. Internal real code sets may be Set.univ;
there is no smallness assumption on these presentation sets.

The only unfinished Section 5 input used by the final integration results
is the explicit `Section5TwoOrderInputAll`, precisely the authorized
Section 5.8 refinement over frozen parameter bases. The actual standing
hypotheses and this input are packaged in `FiniteRV.IntegrationContext`.
No Section 6 conclusion occurs as an assumed input.

## Verification boundary

The complete selected audit covers **733 modules**, **2,268 full exported
types and allowed-axiom reports**, with 2 fresh modules and 731
certified-reused modules. Only `propext`, `Classical.choice` and `Quot.sound`
occur. The root build passed **11,202 jobs**. Evidence:

* `.scratch/section6-final-audit.log`
* `.scratch/section6-final-root.log`
* `.scratch/section6-final-733/`

The project-wide command
`lake env python3 scripts/verify_ci.py --reuse-certified` passed on the final
integrated state, including the inherited QE audit and all available
verifiers for Sections2–6. Section 7 has no verifier and was skipped.
Section 6 rechecked all 2,268 full types and reports, with 0 fresh modules and
733 exact certified artifacts. Earlier passes compiled every added module.
Evidence is in `.scratch/section6-final-project-audit.log`,
`.scratch/ci-verified/summary.json` and `.scratch/section6-final-733/`.

The first default project run passed QE and Sections2–5 before its redundant
fresh Section 6 rebuild was stopped. The final successful run explicitly
selected certified reuse. The runner forwards that option to Section 6 and
retains fresh compilation as its default.

The verifier recompiles every selected source by default. Its optional
`--reuse-certified` mode accepts an artifact only when its passed-receipt
seal, source hash, direct import artifact hashes, output artifact hash,
toolchain and manifest match. Changed modules/imports are recompiled.
Every full type and allowed-axiom report is checked afresh in either mode.
Receipts distinguish fresh and certified-reused modules. Historical
receipts are retained in `.scratch/`; they certify their own snapshots.

## Completed mathematical coverage

* **6.1–6.8:** actual elementary and locus blowups, finite-volume
  preservation, arbitrary isomorphism transport, exact-length confluence,
  common-blowup equivalence, additive congruences and graded product
  compatibility. Original-Gamma domain, volume and morphism graphs remain
  certified throughout. Least elementary/basic generators are proved.
* **6.9–6.13:** the full canonical key-image elementary diagram, alternating
  special chains with all intermediate objects finite, the RV[1] comparison
  allowing different internal presentations, and original-Gamma lifting of
  elementary, general and finite blowups. The 6.12 diagram has length one,
  a full focus, bijective arrows and the specified quotient coordinate.
* **6.14–6.16:** arbitrary-arity fibrewise comparison and relative unary
  invariance, exact selected old RV volumes, genuine finite-witness
  compactness over the original base, and first-two-coordinate exchange
  using the authorized Section 5.8 input. Arbitrary contraction orders and
  preparations are compared. Canonical contractions of pullbacks give
  actual RV isomorphisms, avoiding an additional global-specialness premise.
* **6.17:** full lift-isomorphism/common-blowup equivalence in every degree,
  with actual finite partition gluing and the original-base graphs.
* **6.18:** the actual additive integration equivalence on finite Gamma
  VF[k] scissors and RV[k]/Isp, including empty/scissor relations,
  representative independence, both inverse laws and the lift formula.
* **6.19:** the actual global finite VF scissor semiring, with its original
  addition, Cartesian product and singleton unit, is equivalent to the
  nonzero graded RV quotient. Nonzero compression, finite weight assembly,
  coherent padding, injective transitions, exhaustion and identification
  of finite-stage Isp with its semiring-congruence union are proved.
* **6.20:** coefficient semirings over dcl(B,x), their field/size/generation
  conditions, literal total family lifts, representative independence
  across different finite degrees, the actual quotient of definable
  functions, its semimodule, and linear integration. Constant families use
  the canonical coefficient-base homomorphisms. Zero padding and native
  coproducts/products give actual representatives for all operations.
  Coordinate pushforward is defined on the function quotient and its
  pointwise value is the integral of the literal projected total-lift
  fibre. Relative contractions preserve every retained VF parameter.
* **6.21:** iterated integration agrees for any two nonempty coordinate
  subsets. Each pushforward integrates to the original total integral.
* **6.22:** the actual nonzero basic relation, principal ideal (j−1),
  groupified quotient equivalence, additive graded-colimit universal
  property, injective integration ring homomorphism into localization at
  j, and homogeneous normalization by j^{-k} are proved.

## Main entry points

All names below are in `IntegrationInACVF.Section6`, unless qualified.
The full import is `IntegrationSection6.Library`.

* `FiniteRV.lemma_6_17`
* `FiniteRV.proposition_6_18`
* `FiniteRV.theorem_6_19`, `FiniteRV.theorem_6_19_characterization`
* `FiniteRV.IntegrationContext.functionModule`
* `FiniteRV.IntegrationContext.integralLinearMap`
* `FiniteRV.remark_6_20_linearity`
* `coordinatePushforward`, `coordinatePushforward_value`
* `coordinatePushforward_integral`, `proposition_6_21`
* `FiniteRV.theorem_6_22`, `FiniteRV.theorem_6_22_injective`
* `FiniteRV.theorem_6_22_lift`, `FiniteRV.theorem_6_22_graded_colimit`

See TARGETS.md for the numbered coverage map and REUSE-SURVEY.md for
source provenance, mathematical bridges and earlier verification records.
PROOF-WRITEUP.md retains the substantive replacement-proof ledger.

## Workspace

The verified proof work is based on `00558511e4f4467cb5507f48ead8e25bae8796fc`. The upstream Section 5
interfaces were inspected, not merged. Preserve the backup stash
`section 6 active formalization before upstream sync`. Native pinned
prerequisites were built from source after the binary-cache access failure.
No subagents or dependency changes were used. After completion, the user
authorized committing and pushing this verified state to origin/main.
