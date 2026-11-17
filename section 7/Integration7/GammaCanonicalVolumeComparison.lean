module

public import Integration7.GammaElementaryVolumeGraphs
public import Integration7.GammaElementaryBlowupIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Canonical elementary comparison retains the original Gamma base
for arbitrary actual Gamma volume objects and ordinary admissible centers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem VolumeObjectGamma.elementary_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B)
    (hAdU : BlowupAdmissible U) (hAdV : BlowupAdmissible V)
    (f : RVVolumeIso U V) (hf : f.GammaDefinable B) :
    ∃ e : RVVolumeIso (elementaryVolumeObject C U hAdU) (elementaryVolumeObject C V hAdV),
      e.GammaDefinable B := by
  apply exists_gamma_elementaryBlowupIso hc C B f
    (elementaryVolumeBlowup C U hAdU) (elementaryVolumeBlowup C V hAdV)
    hU.coordinates hV.coordinates hU.density hV.density hf
  · exact gamma_canonical_packed_elementary_chart hc C B U hAdU
      (gamma_elementary_volume_coordinates hc C U hAdU hU.coordinates)
  · exact gamma_canonical_packed_elementary_chart hc C B V hAdV
      (gamma_elementary_volume_coordinates hc C V hAdV hV.coordinates)

end IntegrationInACVF.Section7
