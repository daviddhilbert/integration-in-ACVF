# Continue Sections 1–3

Read AGENTS.md, WORKFLOW.md, STATUS.md, TARGETS.md, REUSE-SURVEY.md and pinned
predecessor LANGUAGE-ERRATA.md. Use arXiv:0809.0473v2 through 3.24. Continuous
work and pushes are authorized; no subagents. HK is background for proof
ideas only: no citation or unproved input. Keep R.Nonempty in 3.11.

Fresh full local root, inherited QE, Section2 and824 Section3 checks pass:
308generic,516actual heads;213source hashes. All805 prior complete types
unchanged;19 new complete types exactly match individually reviewed audits.
Only standard three axioms. .scratch/local-acf-conservation-824/ and
VERIFICATION.json hold evidence. Source e13d791 passed CI42952242946; every824 complete
type,213source hashes and both audit hashes match. This receipt promotes it
to main. Preceding sourcefc136c5 passed CI42949057513; all
805types/205hashes matched; receipt6fee1a5 promoted to main. Its main CI42950124650 is green.

Fifteen numbered Section 3 results are checked in exact scope: 3.2,3.3,
3.4 at named radii plus singleton/VF,3.6,3.7,3.8,3.9,3.10,corrected3.11,
3.12 both,3.13,3.14,3.16,3.17 and3.18. Six remain:3.15,3.19,3.21–3.24
(two lemmas,four propositions);3.20 is a definition. The remaining3.4/3.15 issue concerns old ball parameters; the unnamed
open-radius case over real/Gamma bases now works with undefinable complete types. Section2 has2.15 checked and2.34 open. Keep precise restrictions
from STATUS:3.14 has only old Gamma names and the source ball imaginary;
3.16/3.18 genuineSat/infiniteCardinal/smallReal/ACVF00/namedNontrivialDelta;
3.17 no original named centre/radius/delta or imaginary-cardinality bound.

Lemma3.18 is fully assembled in RVLinearity.lemma_3_18, with the actual
nonzero RV coefficient and original full-base partial-domain graph.
All source pairs, including diagonal, satisfy the actual RV equation.
No desired GammaLinear or error-map injectivity hypothesis is assumed.
GammaLinearity.ordinary supplies the original scale. If coefficients at
gamma<eta differ, RVSlopeRigidity chooses a newly atomic RV fibre at gamma
after finite real-code specialization. The translated error has every
output above gamma+scale and a pair at eta realizing exactly that scale.

VFExchangeAnyBase removes the pinned exchange theorem's field-base premise.
FiniteFibresFromExchange/AtomicFunctionFibres give constant or finite
fibres for a real-definable larger-domain map on an atomic open restriction.
FullFibreEnumerations/FullFibreMeans/AtomicFibreMeanGraph define actual means
over the unchanged full base; image completeness supplies the bound.
FiniteFibreInjectivity uses the checked characteristic-zero mean-centred
RV nonconstancy and3.9, giving AtomicFunctionInjectivity.
The eta-pair excludes constant. RealAtomicValueBoundRigidity then applies
AtomicValueBoundRigidity and checked3.16 to force an open image containing
zero, contradicting atomicity. RealGraphOperations,VFErrorSyntax,
TranslationSyntax,TranslatedErrorGeometry,RVLeadingDifference,
RVLinearitySlopeValues,RVSlopePairFormula supply actual syntax/geometry.
Do not assume the enlarged original whole source remains atomic.

The old printed endpoint inference still does not follow from piecewise
affinity and zeta(t)>t alone. It is documented in PROOF-OBLIGATIONS.md and
is not used in the replacement. The author's requested writeup after the
whole paper is complete is tracked durably in ../PROOF-WRITEUP.md and AGENTS.
Keep that ledger current; no unproved idea counts as a replacement.

New proof batch: CompleteTypeRVProfiles,SelfCentredBallProfiles,
OpenCompleteTypeAtomicity,CompleteTypeOpenImages. Every relevant type has
hOnly excluding old ball parameters. Gamma specialization preserves the
original VF coefficient field. Finite definable polynomial obstacles are
excluded by an infinite complete-type ambient, without ambient definability.
The tested point itself is a valid centre code of its containing ball;
the radius remains an RV variable. This yields actual atomicity over the
original base plus the ball name without naming its radius. Applying3.13
gives3.15 over real/Gamma bases, no saturation; named nontrivial delta stays
explicit in3.15. Whole-VF case excluded by parameter-free zero. Do not
count unrestricted3.15 or silently permit old ball parameters here.

Next: extension with old ball parameters, then3.19,3.21–3.24 and Section2's2.34.
Do not extend3.3 to arbitrary undefinable complete-type sets without proof:
its cut-parameter definability uses ambient definability. Self-centred RV
profiles avoid that error in the now checked real/Gamma-base scope.
Paper PDF https://arxiv.org/pdf/0809.0473v2 via web tool,
ref turn101834view0:3.15 lines567–569,3.18 lines609–660,3.19 lines662–674,
3.21 lines687–701,3.22 lines704–722,3.23–3.24 lines725–751. Direct shell
download was blocked; do not try alternate hosts to evade it.

Draft checker .scratch/check_actual_draft.py freezes all snapshots and
registered proof inputs; run sequentially and never change them mid-check.
All pinned dependencies and needed predecessor artifacts are available;
never restart cold builds. Fresh root first, then scripts/verify_ci.py.
Compile/full-type/axiom audit locally before push; CI confirms integration.
Primary /workspace/integration-in-ACVF branch section-1-3/ordinary-separation;
publication /workspace/integration-in-ACVF-publish. No PR created.

New pure-field batch for3.22: FiniteFieldDefinableMaps,
LocallyFiniteDefinableInjection,LocallyFiniteRelations,
DefinableInjectionSentence,ACFDefinableInjection,FiniteDefinablePatching,
CofiniteDefinableInjection,CofiniteDefinableBijection. General definable
injective self-maps on finite tuples over any algebraically closed field
are proved surjective, not assumed from the polynomial Ax theorem. The
proof uses native finite-field Frobenius, a finite restriction containing
the finite formula parameters and target tuple, then a fully checked
first-order relation sentence and ACF completeness/characteristic transfer.
Finite patching gives finite deficit inequalities, finite image complement
and exact finite-complement counts for cofinite definable bijections.
All19 new full types and all5 sentence definitions reviewed; no new axiom.

Next3.22 bridge: pinned Section4.ResidueNormalization.normalizedResidueSet_definable
is already proved, as is Section7.ResidueConstructibility.remark_7_5.
Read their exact types/source and Section4/7 status (read this turn) before
reuse. normalizedResidueSet_definable has explicit hcan:IsCanonical and
an LRV substructure/residue parameter field. For intrinsic counts, B=top
and E=top give pure-field definability with all residue parameters, harmless
inside the proof. Section4.ResidueNormalization.olean is already available.
Ignored .scratch/ResidueFieldConservation.lean drafts three actual-model
bridges: residue pullback, actual RV graph to pure graph, finite complement
conservation. It has NOT been compiled yet; wait for full root/audit before
running another draft checker. Its hcan premise is explicit helper scope;
normalize/transport it before claiming a final all-model ball theorem.
Native ball-quotient interpretation and positive-component comparison are
also still needed for full3.22. Full3.15 with old ball parameters remains
open independently; real/Gamma case is proved. Counts remain six.
