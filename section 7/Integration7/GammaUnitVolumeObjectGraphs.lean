module

public import Integration7.GammaUnitVolumeIsoRealization
public import Integration7.GammaRVScalarMapGraphs
public import Integration7.GammaVolumeObjectGraphs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Literal unit-density objects retain their full original-Gamma
coordinate and density graphs in any containing real context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem gamma_unit_volume_object_graphs
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B (k+1)) (hUC : U.codes ⊆ (C.base : Set M)) :
    VolumeObjectGamma (gammaUnitVolumeObject hc C U hUC) B :=
  VolumeObjectGamma.canonical hc (FiniteRV.gammaObjectAtExtend U hUC) (VolumeForm.one _)
    (RVMapGamma.scalarOne hc _ (canonical_gamma_object_domain_graph hc (FiniteRV.gammaObjectAtExtend U hUC)))

end IntegrationInACVF.Section7
