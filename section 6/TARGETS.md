# Section 6 targets

Source: Yimu Yin, *Integration in algebraically closed valued fields*,
[arXiv:0809.0473v2, Section 6](https://arxiv.org/html/0809.0473v2#S6),
pp. 17–24. The version is fixed: these numbers do not refer to Section 6
of the predecessor. Statements below are paraphrases, not replacements
for the source.

## Standing scope

User clarification, November12,2026: **only RV[k] is in scope**. Every
numbered result is to be restated for the full category of objects whose
volume map has finite fibres, and the graded category RV[*]. The larger
RV[k,·] categories are abandoned as targets. Existing ambient-object lemmas
serve only as implementation support for the inherited finite full subcategory.


The intended ambient model is ACVF(0,0), sufficiently saturated over a
small original parameter base S, with nontrivial Gamma(S). An added tuple
must appear in the base of every definability and algebraicity statement.
When needed the base is VF/Gamma-generated, using the predecessor's actual
`GammaParameters.Base` and `VFGammaGeneratedBase`. No definition of saturation
may include a desired geometric conclusion. Elementary algebraic arguments
can be proved under weaker assumptions, provided their scope is recorded.

Use the inherited `CanonicalRV.RVSort`, `rawRVSpace`, `DefSet`, `Map`,
`RVFiniteObject`, its inherited morphisms, finite coproduct/product operations,
and positive Grothendieck quotients. There is one absorbing RV zero,
corresponding to the paper's infinity. `RV^{>1}` includes that point; it is
an absolute-value condition `< 1` in Mathlib's reversed valuation order.
Equality of absolute values is never substituted for equality of RV classes.

## Full coverage map

| Item | Intended content and Lean boundary | Current state |
| --- | --- | --- |
| Definition 6.1 | Choose a coordinate of an `RVFiniteObject`; require its label nonzero and algebraic over S and the other labels. Form U × RV^{>1}, multiplying that label. A general blowup replaces a definable locus via an RV isomorphism; retain the locus, presentation and finite length. | Actual elementary construction, admissibility, general locus replacement and finite forward iteration freshly compiled and audited over a small real parameter base. Original-Gamma additive/graded congruence, product compatibility and the least elementary/basic generator descriptions are audited. |
| Remark 6.2 | Projection to U is an `RVHom`; a finite-to-one original volume remains finite-to-one. | Elementary, general and iterated finite-volume preservation freshly compiled and audited over a small real base. |
| Lemma 6.3 | Arbitrary RV isomorphisms induce isomorphisms of elementary blowups, allowing different chosen coordinates. | Freshly compiled and audited for arbitrary RV isomorphisms and different chosen coordinates over a small real base. |
| Corollary 6.4 | Transport a blowup through an isomorphism identifying the two loci. | Freshly compiled and audited using actual definable restrictions, complements and coproduct gluing over a small real base. |
| Lemma 6.5 | Starting at isomorphic objects, length m and n blowups admit isomorphic further blowups of lengths n and m. | Actual local diamond and exact-length grid specialization freshly compiled and audited over a small real base. |
| Corollary 6.6 | Existence of isomorphic iterated blowups is invariant under changing original objects by isomorphism. | Freshly compiled and audited on actual objects over a small real base. |
| Definition 6.7 | Isp is existence of isomorphic finite forward blowups, on RV[k], degree by degree, with additional-parameter versions. | Actual finite forward common-blowup relation is freshly compiled and audited. Real-parameter extension is checked; finite-volume support has compiled. Original-Gamma finite wrappers and parameter extension are freshly audited. |
| Lemma 6.8 | Isp is an additive congruence at fixed degree and a semiring congruence after grading. | Actual common-blowup equivalence, additive/product compatibility, graded semiring congruence and finite-volume restrictions freshly compiled and audited over a small real base. Original-Gamma additive/graded congruence, product compatibility and the least elementary/basic generator descriptions are audited. |
| Lemma 6.9 | A full-locus centripetal step followed by canonical RV labeling yields an elementary blowup up to RV isomorphism. | Actual full canonical key-image object and elementary isomorphism freshly compiled and audited under a literal lift-carrier interface, a full focus and nonzero active labels. The native original-Gamma lift-presentation bridge and finite wrappers are audited. |
| Corollary 6.10 | A special bijection of a lift yields an iterated blowup up to isomorphism. | The RV[k] alternating-chain theorem is freshly audited over a small real base, with exactly the special length. Its original-Gamma RV[k] wrapper is freshly audited, including finite volume of every intermediate object and smallness only on B.real. |
| Corollary 6.11 | Definably isomorphic one-VF-dimensional lifts have Isp-equivalent RV sources. | Full RV[1] theorem, including different real code presentations, is freshly compiled and audited: actual common finite blowups with all original-Gamma charts, using checked Section 5.2/5.3, with only B.real small. |
| Lemma 6.12 | Over a VF/Gamma-generated base an elementary blowup is realized by a full-locus special bijection of length one, with the specified unary re-labeling diagram. | Freshly compiled and audited over the original Gamma base: full focus, length-one special bijection, both bijective diagram arrows, complete Gamma graphs, commuting square, identity VF coordinates and the explicit quotient coordinate. Only B.real is small; no bound on internal codes. General finite blowups remain in6.13. |
| Corollary 6.13 | Finite blowups have definably isomorphic lifts. | Original-Gamma elementary, general and finite-chain lift isomorphisms are audited without a canonical-structure hypothesis. The genuine VF/Gamma-generation hypothesis remains explicit. |
| Lemma 6.14 | Fibrewise Isp over each VF parameter passes to same-order standard contractions, with E enlarged by all contracted VF coordinates. | Audited for arbitrary VF arity and any common order in actual RV[n+k], with exact selected-label finiteness, full original-Gamma witness uniformity and no Section 6 assumption. The arbitrary-small-base form uses aleph0<κ; the coefficient-field form derives this from ACVF00 and smallness. |
| Corollary 6.15 | Relatively unary bijections preserve Isp classes of contractions starting in the active coordinate. | General selected-label form audited for arbitrary VF arity and common remaining order. The ordinary RV[n] specialization and real-presentation extension are audited. |
| Lemma 6.16 | Exchanging the first two contraction coordinates preserves the Isp class. | Full arbitrary-arity result audited, using only the explicit authorized Section 5.8 refinement at frozen VF bases and proved6.14/6.15. Actual prefix restrictions, unary special witnesses, partial programs and native volume presentations are constructed. |
| Proposition 6.17 | Lift isomorphism is equivalent to Isp in RV[k]. | Full equivalence audited in every degree, with original-base graphs, genuine VF/Gamma generation and only the explicitly authorized unfinished5.8 input. Arbitrary contraction independence and finite partition gluing are proved. |
| Proposition 6.18 | Canonical additive integration is inverse to lifting from the fixed-degree quotient by Isp. | Actual additive equivalence `proposition_6_18` audited on finite Gamma VF[k] scissor classes and the actual RV[k]/Isp quotient. Binary partitions, empty and scissor relations, both inverse laws and the lift-class formula are proved. |
| Theorem 6.19 | Assemble the nonzero-label graded pieces into the canonical semiring integration isomorphism. | Full actual semiring equivalence `theorem_6_19` and class characterization audited. The source has original VF scissors, actual Cartesian product and singleton unit. Finite-stage Isp is exactly its semiring-congruence union; dimension-bound independence and both inverse laws are proved. |
| Remark 6.20 | Define integration of RV-valued definable families and pushforward along coordinate projections. | Implemented: actual varying coefficient semirings over dcl(B,x), literal family lifts, representative independence in different degrees, the function quotient and its semimodule, linear integration, and coordinate pushforward with the literal fibre-integral formula. The complete Section 6 and project-wide type/axiom audits pass. |
| Proposition 6.21 | The two iterated integrations over any nonempty coordinate projections agree. | Implemented as `proposition_6_21` for any two nonempty coordinate subsets and the actual quotient of definable functions. Every coordinate pushforward integrates to the original integral. The complete Section 6 and project-wide type/axiom audits pass. |
| Theorem 6.22 | Identify the groupified ideal generated by the basic blowup relation; put j = [1]_1 − [(RV^×)^{>1}]_1 and embed integration into K(RV)[j⁻¹]. | Proved and audited: the actual nonzero basic generating pair, principal ideal (j−1), groupified quotient equivalence, additive graded-colimit universal property, injective integration ring homomorphism and homogeneous normalization by j^{-k}. |

All numbered statements now target the finite-volume categories themselves.
The additional-parameter versions are still needed by later fibre arguments.

## Section 5 authorization and interface boundary

The user explicitly authorizes treating the unformalized results of this
paper's Section 5 as given while that section is being formalized elsewhere.
Relevant inputs include 5.1, 5.2/Remark 5.3, 5.5 (the definition of standard
contraction), 5.6, 5.7 and 5.8. These are **this paper's** results, not the
similarly numbered results in the predecessor dependency.

No new Section 5 axioms, `sorry`s or speculative duplicate contraction
language have been added. The published Section 5 interfaces are now present from upstream main. Import
the actual declarations and use explicit, named hypotheses for its remaining
unfinished numbered results where needed.
A conditional theorem must retain that hypothesis in its exported full type.
This authorization does not cover any assertion numbered 6.x or a stronger
uniformity statement absent from Section 5.

## Completion checks

All numbered targets are implemented in the recorded RV[k] scope.
The final 733-module / 2,268-declaration audit and 11,202-job root build pass.
Project-wide verification passes: inherited QE and every available verifier
for Sections2–6. Section 7 has no verifier. No numbered Section 6 obligation
remains under the recorded standing hypotheses and authorized 5.8 input.
