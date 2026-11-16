module

public import Integration7.HKZeroLiftCoproducts
public import Integration7.HKZeroAdditiveIntegration

@[expose] public section

/-! The transported additive structure on weighted zero VF classes is
the actual tagged coproduct with the two original RV forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem zero_vf_coprod_class (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A B : ZeroVFVolumeObject (M := M) (C.base : Set M)) :
    letI := zeroVFAddCommMonoid hc C
    Quotient.mk (zeroVFVolumeSetoid (C.base : Set M)) (zeroVFCoprod hc C A B) =
      Quotient.mk (zeroVFVolumeSetoid (C.base : Set M)) A +
        Quotient.mk (zeroVFVolumeSetoid (C.base : Set M)) B := by
  letI := zeroVFAddCommMonoid hc C
  letI : AddCommMonoid (ZeroRVVolumeClasses (M := M) (C.base : Set M)) :=
    rvVolumeBlowupClassesAddCommMonoid hc C 0
  let E := zeroAdditiveIntegrationEquiv hc C
  obtain ⟨U,⟨eA⟩⟩ := zero_volume_lift_presentation_exists hc C A
  obtain ⟨V,⟨eB⟩⟩ := zero_volume_lift_presentation_exists hc C B
  have hA : E (Quotient.mk _ A) = Quotient.mk _ U :=
    (congrArg E (Quotient.sound ⟨eA⟩)).trans (zero_integration_lift hc C U)
  have hB : E (Quotient.mk _ B) = Quotient.mk _ V :=
    (congrArg E (Quotient.sound ⟨eB⟩)).trans (zero_integration_lift hc C V)
  have hSum : E (Quotient.mk _ (zeroVFCoprod hc C A B)) =
      Quotient.mk _ (coprod (C.base : Set M) 0 U V) :=
    (congrArg E (Quotient.sound ⟨(zeroVFCoprodIso hc C eA eB).trans
      (zeroLiftCoprodIso hc C U V)⟩)).trans (zero_integration_lift hc C _)
  apply E.injective
  rw [E.map_add,hA,hB]
  exact hSum

end IntegrationInACVF.Section7.HK
