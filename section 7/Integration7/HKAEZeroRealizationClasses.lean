module

public import Integration7.HKZeroFamilyUniformBijections
public import Integration7.HKZeroFamilyRestrictions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The full weighted VF realization of a measured-zero-valued
function descends to its actual almost-everywhere quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem zero_volume_full_class_eq_of_ae
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {F G : ZeroVolumeFunctionPresentation C (n+1)}
    (h : AEZeroVolumeFunctionEquivalent hc C F G) :
    positiveVFVolumeIsoClass hc C F.2.fullVFObject =
      positiveVFVolumeIsoClass hc C G.2.fullVFObject := by
  obtain ⟨E,hE,h⟩ := h
  exact (zero_family_full_class_outside_base hc F.2 E hE).trans
    ((zero_volume_full_class_eq_of_pointwise hc (F.2.outsideBase E) (G.2.outsideBase E)
      (zero_outside_rows_eq_of_ae hc F.2 G.2 E h)).trans
        (zero_family_full_class_outside_base hc G.2 E hE).symm)

def aeZeroVolumeFunctionRealizationClass
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    AEZeroVolumeFunction hc C n → PositiveVFVolumeIsoClasses hc C n :=
  Quotient.lift (fun F => positiveVFVolumeIsoClass hc C F.2.fullVFObject)
    (fun _ _ h => zero_volume_full_class_eq_of_ae hc C h)

@[simp] theorem aeZeroVolumeFunctionRealizationClass_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : ZeroVolumeFunctionPresentation C (n+1)) :
    aeZeroVolumeFunctionRealizationClass hc C n (Quotient.mk _ F) =
      positiveVFVolumeIsoClass hc C F.2.fullVFObject := rfl

end IntegrationInACVF.Section7.HK
