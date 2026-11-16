module

public import Integration7.HKZeroFamilyScalarProducts
public import Integration7.HKAEZeroFunctionAddition

@[expose] public section

/-! Weighted zero coefficients act on the actual weighted-zero-valued AE quotient
through their genuine finite-factor family representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ae_zero_volume_scalar_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z T : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (F G : ZeroVolumeFunctionPresentation C (n+1))
    (hZT : MuIsp (C.base : Set M) 0 Z T)
    (hFG : AEZeroVolumeFunctionEquivalent hc C F G) :
    AEZeroVolumeFunctionEquivalent hc C ⟨_,F.2.prodZero Z⟩ ⟨_,G.2.prodZero T⟩ := by
  obtain ⟨E,hE,hFG⟩ := hFG
  have hZ : rvVolumeBlowupClass hc C (n := 0) Z=rvVolumeBlowupClass hc C (n := 0) T := Quotient.sound hZT
  refine ⟨E,hE,?_⟩
  intro x hx
  rw [zero_volume_family_scalar_row_class,zero_volume_family_scalar_row_class,hZ,hFG x hx]

instance aeZeroVolumeFunctionSMul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    SMul (RVBlowupClasses hc C 0) (AEZeroVolumeFunction hc C n) :=
  ⟨Quotient.map₂ (fun Z F => ⟨_,F.2.prodZero Z⟩)
    (fun Z T hZT F G hFG => ae_zero_volume_scalar_congr hc C Z T F G hZT hFG)⟩

end IntegrationInACVF.Section7.HK
