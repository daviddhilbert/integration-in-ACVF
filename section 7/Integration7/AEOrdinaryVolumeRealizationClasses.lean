import Integration7.OrdinaryVolumeFamilyUniformBijections
import Integration7.OrdinaryVolumeFamilyOutsideRows

/-! The full unit-density VF realization of an ordinary RV[0]-valued
function descends to its actual almost-everywhere quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ordinary_volume_full_class_eq_of_ae
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {F G : OrdinaryVolumeFunctionPresentation C (n+1)}
    (h : AEOrdinaryRVVolumeFunctionEquivalent hc C F G) :
    positiveVFVolumeIsoClass hc C F.2.fullVFObject =
      positiveVFVolumeIsoClass hc C G.2.fullVFObject := by
  obtain ⟨E,hE,h⟩ := h
  exact (ordinary_volume_full_class_outside_base hc F.2 E hE).trans
    ((ordinary_volume_full_class_eq_of_pointwise hc (F.2.outsideBase E) (G.2.outsideBase E)
      (ordinary_outside_rows_eq_of_ae hc F.2 G.2 E h)).trans
        (ordinary_volume_full_class_outside_base hc G.2 E hE).symm)

def aeOrdinaryRVVolumeFunctionRealizationClass
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    AEOrdinaryRVVolumeFunction hc C n → PositiveVFVolumeIsoClasses hc C n :=
  Quotient.lift (fun F => positiveVFVolumeIsoClass hc C F.2.fullVFObject)
    (fun _ _ h => ordinary_volume_full_class_eq_of_ae hc C h)

@[simp] theorem aeOrdinaryRVVolumeFunctionRealizationClass_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : OrdinaryVolumeFunctionPresentation C (n+1)) :
    aeOrdinaryRVVolumeFunctionRealizationClass hc C n (Quotient.mk _ F) =
      positiveVFVolumeIsoClass hc C F.2.fullVFObject := rfl

end IntegrationInACVF.Section7
