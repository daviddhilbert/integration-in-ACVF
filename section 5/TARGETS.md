# Section 5 targets

Source: [arXiv:0809.0473v2, Section 5](https://arxiv.org/html/0809.0473v2#S5),
“Contracting to RV”, through Corollary 5.8. This folder is for the sequel,
not Section 5 of the pinned predecessor.

## Standing scope

Use the predecessor's LRV, its single absorbing RV element, actual mixed
`Point n m` tuples, `SameRV`, `IsRVPullback`, `Map` and `SpecialBijection`.
Definability in the paper is over its fixed small VF/Gamma-generated base S.
Keep ACVF(0,0), genuine saturation, smallness and nontrivial named Gamma
visible wherever required. The Gamma preparation producer currently uses
the explicit `VFFieldBase` hypothesis. Internal real codes do not become
new names in the original Gamma base.

Section 3 allowed ball imaginaries in its base. Do not carry that broader
scope into Section 5's standing assumptions without a proof. Conversely,
real-base results alone do not settle the Gamma-named target.

| Item | Intended Lean content | Initial proof boundary |
| --- | --- | --- |
| 5.1 | For an actual definable map between arbitrary mixed finite arities, produce two special bijections to RV-pullbacks with contractible conjugate. | Draft real-base proof, Gamma proof for a common real presentation, and the set-level wrapper that constructs that presentation internally. All three versions compile; the complete 19-declaration type/axiom audit passed. Root integration and full project audits passed. |
| 5.2 | For a definable bijection in VF arity one, produce two special bijections whose conjugate induces an actual bijection of RV keys. | Complete in the recorded ACVF00/saturation/small-real-base/VFFieldBase/nontrivial named Gamma scope. Proposition3.21 partition, finite membership preparation, original-Gamma graphs and matching chains are constructed; the final theorem produces a unique commuting RV-key bijection without any contractibility or geometric conclusion as a premise. All197 complete types/axioms and root/project integration pass locally. |
| 5.3 | The induced bijection is an RV[1,·] morphism in both directions, using the actual RV-algebraicity criterion. | Complete: actual pinned RV[1,·] isomorphism with weight and finite-volume-image fields, inverse laws, induced-key square and full original-Gamma graphs in both directions. All227 full types/axioms and root/project integration pass locally. The finite-image/singleton-cell replacement proof is recorded in PROOF-WRITEUP.md. |
| 5.4 | Relatively unary means every other VF coordinate is fixed; RV labels may change. Relative specialness additionally requires the actual fibrewise special bijections. | Definition and exact factorization proved: actual fibre maps, restricted foci, one-coordinate canonical factors and finite relatively-special chains. All683 full types/axioms pass locally; all601 earlier types are unchanged. Uniform relative preparation belongs to the remaining construction leading to5.5. |
| 5.5 | Standard contraction for each VF coordinate permutation, from successive relatively special fibre preparations, with the specified RV ordering and lifting square. | Actual relative preparations for arbitrary original-Gamma sources and contraction sequences in every coordinate order are constructed, with a natural bijection to the pinned RV lift and coordinate-injectivity observation. First-n volume normalization, the actual RV-category isomorphism and the original-Gamma normalized natural lift are proved. The full global-special bridge remains open. All683 full types/axioms and root/project integration pass. |
| 5.6 | Finite definable partition of a definable bijection into compositions of relatively unary definable bijections, including uniformity over parameters. | Complete for positive VF arity p+1: finite disjoint covering original-Gamma pieces, constructed actual unary factors, and one common internal real presentation with full original-Gamma certificates for every factor. ACVF00, genuine saturation, aleph0≤κ, small G.real and named δ>1; no VFFieldBase or code-set smallness. All683 full types/axioms and root/project integration pass. The scalar-refinement/active-coordinate replacement proof is recorded in PROOF-WRITEUP.md. |
| 5.7 | Actual RV[2,·] isomorphism between standard contractions of each 2-cell in the two orders. | Complete for every actual definable2-cell: both actual standard contractions and an actual pinned RV[2] isomorphism with full original-Gamma graphs in both directions. Actual cell geometry supplies the exhaustive balanced, injective graph and rectangle cases. All912 complete types/axioms and root/project checks pass. |
| 5.8 | A VF-coordinate-preserving RV-label injection, then standard contractions in both orders with an actual RV[2,·] isomorphism. | Open; requires the uniform family form of 4.8 and 5.7. |

## Initial dependencies

Checked source declarations in the pinned predecessor provide map preparation,
uniform vertical obstacles, invariant Gamma graph operations and polynomial
support from the VF coefficient field. Their required import closure has now been built locally from source; the
first sequel 5.1 batch passed its fresh complete type/axiom audit.

The sequel's `CoordinatePartitions.proposition_3_21` is available on main.
Its exact saturation, smallness, characteristic and nontrivial-value scope
must be matched when used in 5.2. Section 3.24 and the least-radius existence
followup in 3.17 remain open separately. They are not inputs to the first
5.1 batch. Section 2.34 is now proved on the rebased main checkpoint `3c3e478`. The checked Section4 cell/family library at802eb9c is merged; its source identities are included in the601-head receipt.
