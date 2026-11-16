import Integration7.HKSelectedFamilyWeightedZeroProducts
import Integration7.AERVVolumeFunctionAdditiveStructure

/-! Actual weighted-zero finite-factor multiplication descends to the
positive-valued AE quotient, on the same exceptional base set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem ae_weighted_zero_product_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (Z T : ZeroRVVolumeObject (M := M) (C.base : Set M)) (g : ZeroRVVolumeIso Z T)
    (hFG : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    AERVVolumeFunctionEquivalent hc C ⟨_,selectedFamilyWeightedZeroProduct F Z⟩
      ⟨_,selectedFamilyWeightedZeroProduct G T⟩ := by
  obtain ⟨E,hE,hRows⟩ := hFG
  refine ⟨E,hE,?_⟩
  intro x hx
  rw [selected_family_weighted_zero_row_scalar,selected_family_weighted_zero_row_scalar]
  exact congrArg₂ (fun z v => z • v)
    (congrArg (zeroVolumeCoefficientExtend hc C (vfParameterVolumeContext C x)
      (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)))
      (show rvVolumeBlowupClass hc C (n := 0) Z = rvVolumeBlowupClass hc C (n := 0) T
        from Quotient.sound ⟨g⟩))
    (hRows x hx)

def aeRVVolumeFunctionWeightedZeroProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    AERVVolumeFunction hc C n k → RVBlowupClasses hc C 0 → AERVVolumeFunction hc C n k :=
  Quotient.map₂ (fun F Z => ⟨_,selectedFamilyWeightedZeroProduct F.2 Z⟩) (by
    rintro F G hFG Z T ⟨g⟩
    exact ae_weighted_zero_product_congr hc C F.2 G.2 Z T g hFG)

theorem ae_rv_volume_function_weighted_zero_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVolumeFunctionPresentation C (n+1) k)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    aeRVVolumeFunctionWeightedZeroProduct hc C n k (Quotient.mk _ F) (rvVolumeBlowupClass hc C Z) =
      Quotient.mk _ ⟨_,selectedFamilyWeightedZeroProduct F.2 Z⟩ := rfl

end IntegrationInACVF.Section7.HK
