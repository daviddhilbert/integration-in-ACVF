module

public import Integration7.PositiveVolumeLiftKernel
public import Integration7.PositiveBlowupLiftClasses

@[expose] public section

/-! Injectivity of the actual volume lift on the common-blowup quotient,
as a consequence of the proved original-base Proposition 7.8. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem positive_volume_lift_on_blowup_classes_injective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    Function.Injective (positiveVolumeLiftOnBlowupClasses hc C k Ξ hGenerated) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h U =>
    induction b using Quotient.inductionOn with
    | h V =>
      intro h
      obtain ⟨f⟩ := (positiveVFVolumeIsoClass_eq_iff hc C).mp h
      exact Quotient.sound (s := muIspSetoid hc C (k+1))
        (common_volume_blowup_of_lift_iso hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U V f)

end IntegrationInACVF.Section7
