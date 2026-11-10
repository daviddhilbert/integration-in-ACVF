import IntegrationSection3ACVF.CanonicalRegions
import IntegrationSection3.HoleFormulas

/-! The maximal-hole relation of the canonical support over its original
combined base. Both the hole and parent are actual ball imaginaries, and
the definability statement uses the full preimage of their pair of codes. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.CanonicalHoles

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem holes_definable (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A) :
    FullBaseAtomicity.OverBase B
      ((ImaginaryParameters.tuplePresentation (@BallPresentation.presentation M sM hM)
        (Fin 2)).pullback {a | BallImaginaries.underlying (a 0) ∈
          holes F (BallImaginaries.underlying (a 1))}) := by
  let U := BallImaginaries.underlying (M := M)
  have hc : ∀ b ∈ F, ∃ k, U k = b := fun b hb =>
    BallCodeGeometry.encodedBall_coded b (minimal_support_encoded hF b hb)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have he := HoleFormulas.holeCodes_eq_pullback (q := q) hc
  have hT := CanonicalSupportFamily.support_family_definable B δ hδ hA hF
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hd : FullBaseAtomicity.OverBase B
      (HoleFormulas.HoleCodes q (U ⁻¹' (F : Set (Set M))) U) := by
    letI := CanonicalStructure.normalize (M := M)
    exact HoleFormulas.holeCodes_definable hp hq
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hT
  simpa only [he] using hd

end IntegrationInACVF.Section3ACVF.CanonicalHoles
