import IntegrationSection3ACVF.SaturatedInterpretedFamilies
import IntegrationSection3ACVF.FullBaseDefinability
import Section3.NormalizationSaturation

/-! Nonalgebraic actual ball names in an infinite disjoint family over
a small real base. Normalized saturation is proved by the pinned reduct
transfer; no saturation axiom on the imaginary ball sort is introduced. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3ACVF.SaturatedBallFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_nonalgebraic {κ : Cardinal} (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary = ∅)
    (hsmall : Cardinal.mk B.real < κ) (T : Set (BallImaginaries.Ball M))
    (hT : FullBaseAtomicity.Family B T) (hInf : T.Infinite)
    (hne : ∀ j ∈ T, (BallImaginaries.underlying j).Nonempty)
    (hdis : T.Pairwise fun i j => Disjoint (BallImaginaries.underlying i) (BallImaginaries.underlying j)) :
    ∃ i ∈ T, ¬ FullBaseAtomicity.Algebraic B i := by
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  let U := @BallImaginaries.underlying M sM
  have hsN : @Saturated M (@CanonicalStructure.normalize M sM) κ := @Saturated.normalize M sM κ hs
  have hm := @BallPresentation.membership_definable M sM hM B.real
  have hne' : ∀ j ∈ T, (U j).Nonempty := hne
  have hdis' : T.Pairwise fun i j => Disjoint (U i) (U j) := hdis
  let N := @CanonicalStructure.normalize M sM
  have ht : @Set.Definable M B.real LRV N (Fin 4) (q.pullback T) := by
    letI := N
    exact (ImaginaryParameters.OverBase.empty_iff_real (p := p) hB).mp hT
  letI := N
  obtain ⟨i,hi,hna⟩ := SaturatedInterpretedFamilies.exists_nonalgebraic hsN B.real hsmall q U hm T ht hInf hne' hdis'
  refine ⟨i,hi,?_⟩
  rintro ⟨F,hF,hFin,hiF⟩
  exact hna ⟨F,(ImaginaryParameters.OverBase.empty_iff_real (p := p) hB).mp hF,hFin,hiF⟩

end IntegrationInACVF.Section3ACVF.SaturatedBallFamilies
