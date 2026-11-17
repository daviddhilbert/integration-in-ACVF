module

public import Integration7.OrdinaryVolumeFamilyScalarProducts
public import Integration7.AEOrdinaryVolumeFunctionAddition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Ordinary coefficients act on the actual ordinary-valued AE quotient
through their genuine finite-factor family representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ae_ordinary_volume_scalar_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z T : RVFiniteObject (M := M) (C.base : Set M) 0)
    (F G : OrdinaryVolumeFunctionPresentation C (n+1))
    (hZT : MuIsp (C.base : Set M) 0 Z T)
    (hFG : AEOrdinaryRVVolumeFunctionEquivalent hc C F G) :
    AEOrdinaryRVVolumeFunctionEquivalent hc C ⟨_,F.2.prodZero Z⟩ ⟨_,G.2.prodZero T⟩ := by
  obtain ⟨E,hE,hFG⟩ := hFG
  have hZ : rvVolumeBlowupClass hc C (n := 0) Z=rvVolumeBlowupClass hc C (n := 0) T := Quotient.sound hZT
  refine ⟨E,hE,?_⟩
  intro x hx
  rw [ordinary_volume_family_scalar_row_class,ordinary_volume_family_scalar_row_class,hZ,hFG x hx]

instance aeOrdinaryRVVolumeFunctionSMul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    SMul (RVVolumeBlowupClasses hc C 0) (AEOrdinaryRVVolumeFunction hc C n) :=
  ⟨Quotient.map₂ (fun Z F => ⟨_,F.2.prodZero Z⟩)
    (fun Z T hZT F G hFG => ae_ordinary_volume_scalar_congr hc C Z T F G hZT hFG)⟩

end IntegrationInACVF.Section7
