module

public import Integration7.VolumeFamilyZeroProductRows
public import Integration7.AERVVolumeFunctionAdditiveStructure
public import Integration7.ZeroFactorBlowupProducts
public import Integration7.VolumeIsoParameterExtension
public import Integration7.AllDegreeVolumeClasses

@[expose] public section

/-! Ordinary RV[0] isomorphism classes act by genuine finite-factor
products on the AE volume-function quotient. The original exceptional
set suffices, and coefficient isomorphisms extend to each named fibre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem ae_volume_zero_coefficient_product_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (Z T : RVFiniteObject (M := M) (C.base : Set M) 0) (g : Z ≅ T)
    (hFG : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    AERVVolumeFunctionEquivalent hc C ⟨_,F.prodZero Z⟩ ⟨_,G.prodZero T⟩ := by
  obtain ⟨E,hE,hRows⟩ := hFG
  refine ⟨E,hE,?_⟩
  intro x hx
  let D := vfParameterVolumeContext C x
  let hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)
  have hF := VolumeBlowupEquivalent.of_iso D (volumeFamilyZeroProductRowIso hc F Z x)
  have hG := VolumeBlowupEquivalent.of_iso D (volumeFamilyZeroProductRowIso hc G T x)
  have hMiddle := ((positiveVolumeBlowupClass_eq_iff hc D).mp (hRows x hx)).prod_zero hc D
    (finiteVolumeIsoExtend hCD g)
  exact (positiveVolumeBlowupClass_eq_iff hc D).mpr
    ((hF.trans hc D hMiddle).trans hc D (hG.symm hc D))

def aeRVVolumeFunctionZeroCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    AERVVolumeFunction hc C n k → RVVolumeBlowupClasses hc C 0 → AERVVolumeFunction hc C n k :=
  Quotient.map₂ (fun F Z => ⟨_,F.2.prodZero Z⟩) (by
    rintro F G hFG Z T ⟨g⟩
    exact ae_volume_zero_coefficient_product_congr hc C F.2 G.2 Z T g hFG)

theorem ae_rv_volume_function_zero_coefficient_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVolumeFunctionPresentation C (n+1) k)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    aeRVVolumeFunctionZeroCoefficientProduct hc C n k (Quotient.mk _ F) (rvVolumeBlowupClass hc C Z) =
      Quotient.mk _ ⟨_,F.2.prodZero Z⟩ := rfl

end IntegrationInACVF.Section7
