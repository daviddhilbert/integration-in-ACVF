module

public import Integration7.GammaActualRVProducts
public import Integration7.GammaVolumeObjectGraphs
public import IntegrationSection6.GammaElementaryStructure

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Any actual canonical elementary blowup of a Gamma volume object
retains the full original-Gamma graphs. Only ordinary admissibility is
needed for this graph statement; no new Gamma-algebraicity is inferred. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point gammaLogicInput PresentedSet pointSpace carrier setDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_elementary_volume_coordinates
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hAd : BlowupAdmissible U)
    (hU : RVMapGamma U.underlying.obj.volume B) :
    RVMapGamma (elementaryVolumeObject C U hAd).underlying.obj.volume B := by
  have hDom := gamma_actual_rv_product_domain U.underlying.obj.domain
    (blowupConeSet (C.base : Set M)) hU.domain (gamma_actual_blowup_cone hc)
  have hπ : RVMapGamma (Section6.elementaryProjection U.underlying.obj (Fin.last k)) B :=
    gamma_real_rv_map_graph hc B _
      (rvCoordinateSelectMap B.real (Fin.castAdd 1 : Fin U.underlying.obj.arity → Fin (U.underlying.obj.arity+1)))
      hDom (Section6.elementaryProjection_labels U.underlying.obj (Fin.last k))
  have hσ : RVMapGamma (Section6.elementaryParameter U.underlying.obj (Fin.last k)).toUniv B :=
    gamma_real_rv_map_graph hc B _
      (rvCoordinateSelectMap B.real (Fin.natAdd U.underlying.obj.arity : Fin 1 → Fin (U.underlying.obj.arity+1)))
      hDom (Section6.elementaryParameter_labels U.underlying.obj (Fin.last k))
  have hPair := (hπ.comp hU).append hσ
  let G := Section6.oldVolumeParameterBlowupMap (C.base : Set M) (Fin.last k)
  let P := PresentedSet.univ (pointSpace (M := M) 0 ((k+1)+1)) B.real
  have hG : RVMapGamma G B := gamma_real_rv_map_graph hc B G
    (Section6.oldVolumeParameterBlowupMap B.real (Fin.last k))
    ((gammaLogicInput B).real_set (carrier P) (setDefinable P)) (fun _ => rfl)
  apply (hPair.comp hG).congr
  intro w
  exact (Section6.elementaryVolume_oldProgram U.underlying.obj (Fin.last k) w).symm

theorem VolumeObjectGamma.elementary_canonical
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : VolumeObjectGamma U B) (hAd : BlowupAdmissible U) :
    VolumeObjectGamma (elementaryVolumeObject C U hAd) B :=
  hU.elementary hc C U hAd (gamma_elementary_volume_coordinates hc C U hAd hU.coordinates)

end IntegrationInACVF.Section7
