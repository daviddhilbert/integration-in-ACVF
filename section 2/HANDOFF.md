# Section 2 handoff

Latest batch: `.scratch/local-finite-immediate-54/`. Full root,inherited QE,
54 Section2 and1244 unchanged Section3 type/axiom audits pass. All41 prior
Section2 types are unchanged; all13 new complete types match individual
reviewed audits. Source counts are30 and368; only standard axioms occur.
CI confirmation for this batch is pending. Use this batch's own Section2
andSection3 archives for promotion.

The actual ambient algebraic-extension henselianity theorem is now proved
in `AlgebraicSubfieldHenselian`, with the envelope and Galois hypotheses
constructed internally. `FiniteImmediateSubfield` similarly constructs the
envelope and proves degree one for any finite immediate subfield extension;
it adds no Galois hypothesis on that finite extension or on the original
ambient over the base. `PrimitiveResidueDegree` proves that the primitive
lift generates a subextension whose degree equals the full residue degree.
`ResidueGeneratedSurjectivity` proves surjectivity of its residue inclusion.
`ImmediateApproximationFromResidues` derives the needed actual approximation
from equality of values and residue surjectivity. These statements assume
neither the finite-extension reference nor the desired full degree equality.

Next: finish field-image/degree transport to combine the primitive
subextension with finite-immediate triviality, and supply the resulting
degree equality to the Gauss graph construction. The full reference and
unconditional2.34 remain open; these ingredients alone are not the assembled
degree theorem.

Newest batch: `.scratch/local-henselian-support-41/`. Its full root,inherited
QE,41 Section2 and1244 Section3 type/axiom audits pass locally. All27 previous
Section2 complete types and all1244 Section3 complete types are unchanged;
all14 new full types match individual reviewed audits. Source counts are22
and368. [CI43004909322](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43004909322) passed; complete types and source/audit hashes match the local batch archive and publication checkout. This archive has its own Section2 and
Section3 evidence; use it for this batch's eventual promotion.

`HenselianImmediateGalois` proves trace-kernel triviality and degree one for
an actual finite Galois immediate extension over a henselian base in residue
characteristic zero. `HenselianFixedField` proves henselianity by lifting a
simple root in the algebraically closed envelope and descending it through
the actual Galois fixed field. `HenselianAlgebraicTower` supplies comparison
invariance from the checked predecessor theorem and ascends henselianity to
intermediate fields within that envelope. `ResidueIndependentLifts` proves
finiteness and the field-degree upper bound on the residue degree for any
finite valued-field extension. `PrimitiveResidueLift` lifts a primitive
residue generator without assuming the desired degree equality.

These are proved supporting results, not a proof of the complete reference.
Next: connect an arbitrary actual algebraic intermediate field to its
algebraically closed Galois envelope, then prove the same-value finite
extension's residue-degree equality using the primitive lift and trace.
Do not infer that a non-Galois extension is Galois or assume the degree
equality in constructing its primitive residue lift.

The concrete volume-descent batch passed the full root build, inherited QE,
all 27 Section 2 complete type/axiom audits and all 1,244 unchanged Section 3
audits. [CI43002045059](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43002045059) passed; complete types and source/audit hashes match the local batch archive and publication checkout. Local evidence is archived in
`.scratch/local-volume-descent-27/`, with its own `Section2/` and `Section3/`.
All27 Section2 and1244 Section3 complete CI types,17 and368 source hashes
and both audit hashes match these archives and the publication checkout. Use `set -e`
in publication shell sequences.

`VolumeLiftDescent.corollary_2_34_positive` proves the two concrete volume
conditions on nondegenerate finite-volume RV objects. The essential wrapper
`corollary_2_34_essential` restricts the original forms to actual essential
parts, so no nonzero-coordinate hypothesis is added to the original objects.
Degree zero uses the category convention `mRV[0] = RV[0]`.

This is a conditional concrete bridge, not an unconditional proof of 2.34.
The released predecessor's `HenselizedGaussGraphInput` remains explicit.
`corollary_2_34_of_finite_extension_reference` supplies it from the exact
`FiniteHenselianExtensionReference` named in the pinned predecessor. That
reference asserts preservation of henselianity in finite extensions and the
residue-degree equality in residue characteristic zero when values agree.
Its source, complete type and prior authorization were inspected; this batch
does not prove that reference. Do not hide this input or count a theorem
assuming it as its proof. No new outside citation or HK result was introduced.
The referee manuscript supplied no proof input.

The generic RV equation and pointwise Gamma equation have independent proofs.
The former escapes the VF-small exception in each nonzero lifted fibre,
identifies actual VF Jacobians by uniqueness, and pulls back the RV-small
volume exception along the finite volume map. The latter restricts the
actual lifted bijection to each label fibre, names only its finitely many
label coordinates, preserves its actual Jacobian, and applies the checked
constant-value Gamma polydisc descent theorem. It retains every essential
label, including those excluded from the generic RV comparison.

Next: investigate the explicit henselian finite-extension input against
existing checked sources. Preserve dependency pins and the common language.
A new outside mathematical reference needs author approval unless the needed
result is already formalized. Avoid the false unrestricted Gamma clause of
predecessor 9.15.
