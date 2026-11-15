import Integration7.SelectedVolumeFamilyPositiveProducts
import Integration7.AERVVolumeFunctions
import Integration7.VolumeBlowupRightProducts
import Integration7.BlowupParameterExtension

/-! Actual multiplication by positive common-blowup coefficient classes
descends to the existing AE function quotient. Both coefficient and row
common-blowup witnesses are retained under the genuine product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k p : ℕ}

theorem ae_volume_positive_coefficient_product_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hUV : VolumeBlowupEquivalent U V)
    (hFG : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    AERVVolumeFunctionEquivalent hc C ⟨_,selectedVolumeFamilyLeftProduct U F⟩
      ⟨_,selectedVolumeFamilyLeftProduct V G⟩ := by
  obtain ⟨E,hE,hRows⟩ := hFG
  refine ⟨E,hE,?_⟩
  intro x hx
  let D := vfParameterVolumeContext C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)
  have hF := VolumeBlowupEquivalent.of_iso D (selectedVolumeFamilyLeftProductRowIso hc U F x)
  have hG := VolumeBlowupEquivalent.of_iso D (selectedVolumeFamilyLeftProductRowIso hc V G x)
  have hMiddle := (hUV.extend hCD).prod hc D ((positiveVolumeBlowupClass_eq_iff hc D).mp (hRows x hx))
  exact (positiveVolumeBlowupClass_eq_iff hc D).mpr
    ((hF.trans hc D hMiddle).trans hc D (hG.symm hc D))

def aeRVVolumeFunctionPositiveCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p k : ℕ) :
    PositiveVolumeBlowupClasses hc C p → AERVVolumeFunction hc C n k → AERVVolumeFunction hc C n ((p+1)+k) :=
  Quotient.map₂ (fun U F => ⟨_,selectedVolumeFamilyLeftProduct U F.2⟩) (by
    intro U V hUV F G hFG
    exact ae_volume_positive_coefficient_product_congr hc C U V F.2 G.2 hUV hFG)

theorem ae_rv_volume_function_positive_coefficient_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVolumeFunctionPresentation C (n+1) k) :
    aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k (positiveVolumeBlowupClass hc C U) (Quotient.mk _ F) =
      Quotient.mk _ ⟨_,selectedVolumeFamilyLeftProduct U F.2⟩ := rfl

end IntegrationInACVF.Section7
