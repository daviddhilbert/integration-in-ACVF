# Section 5 handoff

The active numbered Section 5 targets are complete in the author's RV[k] scope.
Use STATUS.md for the entry points and exact assumptions. RV[k,*] is abandoned
as a target; ambient machinery is internal proof support. Arbitrary auxiliary
RV arities remain allowed, with finite RV fibres on the applicable sources.

1852 complete type/axiom audits and full project verification pass. All 1686 prior
records are exact; 166 new full types/constructors were reviewed in 1997 lines.
Root 10708 passed. Evidence: .scratch/section5-final-1852-verified/ and the versioned
compact index plus lossless full receipt. Pins and toolchain are unchanged.

Definition 5.5 uses explicit VF-fixed RV presentation charts under the paper's
Notation 2.5. StandardSpecialPresentation and NormalizedStandardSpecialPresentation
carry actual global special chains, full Gamma certificates and exact squares
to the actual natural lifts. The padded chain target is not asserted to be an
RV-pullback; the chart target is the actual pinned lift. Preserve this precision
when using the result downstream.

Primary finite declarations: lemma_5_1_finite, lemma_5_2_finite,
lemma_5_3_finite, lemma_5_5, lemma_5_6_finite, lemma_5_7_finite,
lemma_5_8_finite. The Definition 5.4 factorization and coordinate-injectivity
observation after 5.5 remain checked. FiniteStandardContractionData methods
provide actual RV[n] objects, Gamma normalization and the normalized special
presentation. Finite comparisons expose actual GammaRVFiniteIso values.

The replacement proofs are recorded in PROOF-WRITEUP.md for the future writeup
after the whole paper is formalized. Do not substitute external unproved
citations or introduce smallness of the internal coding presentation.

Keep all source inventories and verifiers frozen during future audits. Never
edit a source while it or a downstream importer is being compiled. Compile,
review full types and constructors, run allowed-axiom and root/project checks,
and confirm CI/artifact identity before publishing another proof checkpoint.
No main promotion beyond 30071af is authorized in this session.
