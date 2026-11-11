# Section3: parametric balls and atomic subsets

Target: arXiv:0809.0473v2,through Proposition3.24.

The full local root build, inherited QE audit, Section2 audit and1004
Section3 type/axiom audits pass:348 generic and656 actual heads.
All287 source hashes match; all983 previous complete types are unchanged,
and all21 new complete types exactly match individually reviewed audits.
Only propext, Classical.choice and Quot.sound occur. Evidence is in
.scratch/local-coordinate-setup-1004/ and VERIFICATION.json. [CI42971655123](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42971655123) passed;
all1004 full CI types and287 source hashes match the reviewed local archive. The full3.4 source bc7ad74 passed
[CI42968768615](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42968768615)
and was promoted to main at receipt bbcaa66 after exact type/hash matching.
The receipt itself passed CI42970350599.

## Numbered results and exact scope

Nineteen numbered results have checked implementations in the scopes below.
Green checks certify these exported types,not broader unstated claims.

| Result | Checked conclusion and boundary |
| --- | --- |
| 3.1 | Complete-type generation and atomicity calculus for actual definable finite tuples and interpreted bases. |
| 3.2 | Parametric ball atomicity over the full real/Gamma/ball base. Actual nonalgebraicity is of the output ball name; only the input name is adjoined. |
| 3.3 | Atomicity survives every finite Gamma tuple,including mixed VF/RV tuples. ACVF00 and an original-base definable nontrivial Gamma value are explicit. The ambient is definable atomic. |
| 3.4 | CompleteTypeBallAtomicity.lemma_3_4 covers every actual open/closed ball,including arbitrary unnamed radii,singletons andVF,over the full original real/Gamma/ball base. Ambient complete type need not be definable. Genuine saturation,infinite cardinal,small original real base,ACVF00 and a genuine nontrivial value explicit. Only the actual ball name is adjoined. |
| 3.6 | Actual finite nonempty disjoint primitive decomposition of an atomic VF set,with common radius,valuative centre and primitive kind. No individual component is assumed definable. |
| 3.7 | Whole-ball coverage at the radius of an inner ball,including singleton/VF cases. Initially unnamed radius is adjoined using checked3.3. |
| 3.8 | Full partial-domain VF images preserve atomicity and the one-component condition. |
| 3.9,3.10 | Actual RV-powerset constancy in every finite RV arity on an atomic open ball,and on an arbitrary-radius open subball of a definable atomic set. |
| 3.11 | Separation.lemma_3_11 with the approved R.Nonempty correction. Both radii may be originally unnamed. |
| 3.12 | Both function obstructions,including the singleton closed-source case of the finite-to-one direction. |
| 3.13 | An actual definable VF image of an atomic open ball is constant or an atomic open ball. |
| 3.14 | Infinite one-component atomic target cannot be closed when its only ball imaginary is the source open-ball name. Original Gamma names are permitted; source radius need not be named. |
| 3.15 | FullCompleteTypeOpenImages.lemma_3_15 for the full original real/Gamma/ball base,arbitrary open-ball radii,and possibly undefinable complete-type ambients. The map may be defined on a larger definable domain. Genuine saturation,infinite cardinal,small original real base,ACVF00 and original-base definable nontrivial value are explicit. |
| 3.16 | Actual Gamma-linearity with coefficient target/source radius ratio,using actual HasRadius properties. Genuine saturation,infinite cardinal,small real base,ACVF00 and original-base definable nontrivial value are explicit. No linearity premise. |
| 3.17 | Actual linear subballs and the stated exclusion for every given least-radius function. Centre/radius codes are internal; no old-imaginary cardinal bound. Existence of the least-radius function is not included in the checked export. |
| 3.18 | Complete actual RV-linearity,with the same standing saturation/smallness/characteristic/nontrivial-value scope as3.16. The affine-error replacement avoids the printed endpoint inference. |
| 3.19 | FullOpenToOpenPartition.proposition_3_19 constructs an actual finite disjoint partition into nonempty original-base definable pieces with actual OpenToOpen. Full original base; same standing scope as3.15. No finiteness or cardinal bound on old imaginary names. |
| 3.20 | Actual coordinate slicing, scalar fibre maps, full uniform graph and restriction stability are checked. |
| 3.21 | Pointwise coordinate partitions and globally invariant original-base promotion of finite real labels are checked. The uniform finite global partition remains open. |
| 3.22 | Complete component and actual-hole conservation for finite disjoint thin families under an original-base definable open-to-open VF bijection. Full original base; onlyACVF and a genuine nontrivial value. No canonical-model,saturation orACVF00 premise. |
| 3.23 | No definable bijection between any distinct actual atomic primitive shapes:open,closed,thin annulus. Full original base,ACVF00 and originally definable nontrivial value. No saturation or3.15 premise. |
| 3.24 | Open. Induced RV/Gamma maps and the definable interval obstruction still need proof. Correct value intervals are closed and half-open; see REFERENCE-NOTES.md for the independent endpoint check. |

Except where a row states otherwise,the atomic unary geometry in3.6--3.13
retains its full-base ACVF00/originally definable nontrivial-value scope.
See exported full types and VERIFICATION.json for the exact hypotheses.

The two remaining numbered Section3 main targets are3.21 and3.24;
3.20 is a definition. Lemma3.4 now includes all unnamed open/closed radii.
Existence of the least-radius function supplied as input in3.17 remains
a scope followup. Section2.34 remains open separately; Section2.15 is checked.

## Full-base ball atomicity and3.15

For any putative same-base cut after naming a ball,form the full-base
definable family of balls split by that relation. Specialize finite
imaginary code support only inside a compactness argument. Checked
real/Gamma open/closed ball atomicity excludes splitting balls in a complete-type
core over that real code base. Two genuine saturation steps produce a
finite real-definable cover containing no splitting-family member.
C-minimal finite ball support supplies arbitrary finite hitting points.
No original complete type is assumed complete over the auxiliary codes.

FiniteBallProfiles derives intrinsic terminal membership classes from a
laminar family with a finite hitting set. Every family ball meets a terminal
class; there are finitely many classes. Their definitions name no hitting
points. BallProfileDefinability proves their full original-base syntax.
If a family ball lies in one original complete type,the entire ball lies
in the terminal locus. TerminalBallCover and finite proper-subball
non-covering make that ball one whole terminal class. The ball-coded
terminal classes are disjoint and same-base definable. The existing
atomic_below_complete_type theorem proves atomicity over the ball name.
This contradicts the putative cut. SplittingBallHitting constructs the
hitting set; no such premise remains in the final3.4/3.15 types.

Checked3.13 and injectivity now give3.15. This proof replaces the printed
fixed-radius step for unnamed radii and old ball parameters. The finite-hitting
strategy was developed independently before the referee attachment was read. The attachment's
proposed QE bridge is not used. PROOF-WRITEUP.md records the future writeup.

## Full-base finite partitions in3.19

FiniteBaseRealPresentation supplies common finite real codes for all
definitions over a finite interpreted base. FiniteBaseTypeNeighborhoods
keeps its type core over the original interpreted base,uses full3.15 to
exclude bad ball configurations,and applies genuine saturation only over
the internal common real code set. The neighborhood remains definable over
the original base. FiniteBaseOpenImageCovers supplies the second compactness
step. The actual definable inverse gives a second finite cover; actual
preimages and checked finite Boolean refinement yield OpenToOpen pieces.

The final theorem restricts temporarily to finite imaginary support of the
domain,full map graph and original nontrivial-value definition. Every
resulting piece is already definable over this subbase,so monotonicity
returns the actual partition to the full original base. No size assumption
on the set of all old imaginary names is introduced. The argument follows
the paper's compactness proof with its parameter handling made explicit.

## Other replacement proofs

3.18 uses actual finite-fibre means and genuine saturation to make an affine
error constant or injective on a new atomic RV fibre. A pair excludes
constancy; checked3.16 forces a radius incompatible with the strict error
value bound. See PROOF-OBLIGATIONS.md; no HK citation or unproved input.

3.22 constructs exact native residue coordinates and full induced quotient
graphs for actual finite thin families. Arbitrary definable ACF conservation
is proved by finite-field Frobenius,first-order transfer and finite patches.
Tagged lines conserve actual component and hole counts. Native normalization
transports these counts back to the original model. This replaces the
printed regular-curve conservation argument; no outside citation is added.

## Unnamed closed radii in full3.4

ClosedCompleteTypeRVProfiles applies the pinned checked closed-disc
root-free theorem to finite original-base polynomial obstacles.
ClosedSelfCentredBallProfiles uses the actual closed chart with the tested
point as centre and all VF lifts of an RV radius variable. Non-strict
valuation bounds prove recentering and full quotient equality.
ClosedCompleteTypeAtomicity supplies real/Gamma atomicity for ordinary
closed balls,with singleton/VF cases supplied by earlier checked exports.
RealBallAtomicity covers every actual ball imaginary. The same intrinsic
finite-hitting argument now applies to any splitting-ball family,so
CompleteTypeBallAtomicity.lemma_3_4 has no open/closed or radius restriction.

## Coordinate partition setup

CoordinateSlices and CoordinateFibres define the actual deleted source and
output contexts. Whole-map injectivity gives scalar fibre injectivity.
CoordinateFibreSyntax proves the full uniform scalar graph from the entire
partial tuple graph. PointwiseCoordinatePartitions applies full3.19 after
adjoining precisely the finite real contexts, preserving every old imaginary.
RealParameterPromotion promotes these label names to free variables using
the pinned proved raw formula-promotion theorem. CodeSupportHull universally
quantifies valid quotient representatives, making the promoted relation
invariant for every new label tuple. No representative becomes a final name.

Uniform compactness, definable gluing and refinement across all VF coordinate
pairs are still required for3.21. Pointwise partitions do not discharge it.
