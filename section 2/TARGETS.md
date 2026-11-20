# Section 2 targets

Paper: arXiv:0809.0473v2, Section 2 ("Preliminaries and review", pp. 3–7).
Section 2 mostly reviews conventions and results from the predecessor
paper (Special transformations) and the HK framework. Following the
standing rule in [AGENTS.md](../AGENTS.md), only selected results are
formalization targets.

This inventory lists only the Section 2 numbered items that the repository
records. The repository does not contain a transcription of the paper's
full Section 2 numbering, so every other numbered Section 2 item is
**untracked**: it is neither claimed as formalized nor recorded as false.
Do not read the absence of an item below as a statement about it.

| Item | Status | Where |
| --- | --- | --- |
| Definition 2.2 | Convention, not a theorem target. Its open-polydisc convention and the convention that VF is clopen are used as stated by the sequel's predicates. | [PAPER-CORRECTIONS.md](../PAPER-CORRECTIONS.md) (3.24 and the observation after 4.7); [section 3/TARGETS.md](../section%203/TARGETS.md) |
| Corollary 2.15 | **Formalized** over real and genuine Gamma-named bases: `IntegrationInACVF.Section2.corollary_2_15_real_base`, `IntegrationInACVF.Section2.corollary_2_15`. | `IntegrationSection2/GammaFiniteImage.lean`; [STATUS.md](STATUS.md) |
| Lemma 2.33 | **False as stated; not a target.** Its unrestricted Gamma clause repeats the Gamma assertion of Special transformations Lemma 9.15, which an arity-two counterexample refutes. The formalization does not use it. | [PAPER-CORRECTIONS.md](../PAPER-CORRECTIONS.md), "Lemma 2.33" |
| Corollary 2.34 | **Formalized** without graph or finite-extension reference hypotheses. Positive degree: `IntegrationInACVF.Section2.corollary_2_34` (essential objects) and `corollary_2_34_nonzero`. Corrected weighted degree zero: `WeightedZeroVolumeDescent.corollary_2_34_zero_weighted`. All degrees: `VolumeDescentAllDegrees.corollary_2_34_all_degrees_weighted`. | `IntegrationSection2/VolumeDescentTheorem.lean`, `WeightedZeroVolumeDescent.lean`, `VolumeDescentAllDegreesWeighted.lean`; [STATUS.md](STATUS.md) |

The legacy `VolumeDescentAllDegrees.corollary_2_34_all_degrees` remains
with an unchanged type. Its degree-zero branch concludes `True`, so it is
not the all-degree entry point; use
`corollary_2_34_all_degrees_weighted` instead.

The legacy conditional `VolumeLiftDescent.corollary_2_34_of_finite_extension_reference`
also remains with an unchanged type. It assumes a finite-extension
reference premise that the final theorems above do not need.

The audited Section 2 declarations are listed in [verify.py](verify.py);
their full statements are pinned in
[`verification/headline-types/section2.txt`](../verification/headline-types/section2.txt).
