# Section 5 continuation

User explicitly requested uninterrupted work until the whole section is done.
Do not stop at this verified checkpoint. No subagents are authorized.

Lemmas5.1 and5.2 are now locally checked in the scope in STATUS/TARGETS.
`UnaryBijection.lemma_5_2` is the set-level5.2 entry point; the presented
wrapper is in UnaryBijectionPreparation. The197-head full type/axiom audit
passed;161 previous types are unchanged. Root build and full project audits
passed(foundation,2,3,5;4/6/7 skipped). VERIFICATION.json has complete types,
source/pin/audit hashes and scope review. Preserved receipt:
`.scratch/section5-197-verified/`. Publish only this verified source identity.

Checkpoint2428bd0(161 heads) passed CI43075798136. Downloaded artifact
13882848565 matches every retained type/source/pin/audit hash; it has been
promoted to main. Current feature branch is section-5/contracting-to-rv.

Next:5.3 actual RV[1,·] isomorphism. Weight equality follows because an
actual mutually contractible bijection between unary RV-pullbacks maps a
singleton zero cell to a singleton zero cell; a nonzero RV cell is infinite.
Use checked Sec3Fibre.fibre_infinite. Finite volume images follow by fixing
a common VF representative of the input RV value (pullback property) and
using the checked finite RV-to-VF image theorem for the old RV labels.
A scratch proof `.scratch/UnaryVFFibreFinite.lean` is in progress; it needs
an explicit normalized instance in ImaginaryParameters.OverBase.specialize.
Use original-Gamma graph→full raw graph→finite real support, adjoin fixedx,
then finite_rv_to_vf_relation_image in the canonical normalization. No
smallness assumption on the potentially large internal code set is needed.

Then finish5.4 fibrewise relatively-special definition/witnesses,5.5 actual
standard contractions with permutation and lifting square, general5.6,
and5.7–5.8(actual2-cell geometry/uniform4.8). Section4 is active separately;
do not assume its open results or send messages without authorization.
The existing UnaryChain gives actual relatively-unary factors of specials
and the arity-one5.6 case only. No full5.6 claim yet.


Current continuation: Remark5.3 now complete locally in the227-head batch,
with all197 earlier full types unchanged. Entry `UnaryRVCategory.lemma_5_3`
constructs the actual RV[1,·] isomorphism, square and original-Gamma graphs
in both directions. `UnaryRVIsomorphism.unaryRVHom` proves both category
fields; the inverse laws are checked. The finite-image and cell-zero proofs
have moved from scratch to checked source. Preserved227 receipt:
.scratch/section5-227-verified/. Root and full project audits pass.
The prior197-head9426f7e checkpoint passed CI43079850718; artifact13885675375
matches the preserved receipt exactly and that checkpoint is promoted to main.
Do not repeat5.3 work. Next: actual fibrewise relative-special witnesses5.4,
coordinate-canonical factorization, then standard contractions5.5.
