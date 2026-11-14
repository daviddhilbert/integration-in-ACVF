import Integration7.GammaVolumeCoordinatePermutations
import Integration7.GammaRVScalarMapGraphs

/-! Simultaneous coordinate permutations of actual volume objects keep
the density and original-Gamma common forward-blowup geometry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

def PositiveRVVolumeObject.permuteVolume (U : PositiveRVVolumeObject (M := M) S k)
    (e : Equiv.Perm (Fin (k+1))) : PositiveRVVolumeObject (M := M) S k where
  underlying := ⟨U.underlying.obj.reindexVolume e,
    (Map.finiteFibres_of_injective (rvReindexMap_bijective S e).injective).comp U.underlying.property⟩
  form := U.form

theorem VolumeObjectGamma.permuteVolume
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U B)
    (e : Equiv.Perm (Fin (k+1))) : VolumeObjectGamma (U.permuteVolume e) B :=
  ⟨(hU.coordinates.select hc e).congr (fun _ => rfl),hU.density⟩

theorem GammaVolumeBlowupEquivalent.permuteVolume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V)
    (e : Equiv.Perm (Fin (k+1))) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k
      ⟨U.val.permuteVolume e,U.property.permuteVolume hc e⟩
      ⟨V.val.permuteVolume e,V.property.permuteVolume hc e⟩ := by
  let fU : U.val.underlying ≅ (U.val.permuteVolume e).underlying :=
    rvFiniteIsoOfAmbient (rvReindexVolumeIso U.val.underlying.obj e)
  let fV : V.val.underlying ≅ (V.val.permuteVolume e).underlying :=
    rvFiniteIsoOfAmbient (rvReindexVolumeIso V.val.underlying.obj e)
  have hFU : RVMapGamma (finiteIsoMap fU) B :=
    gamma_real_rv_map_graph hc B _ (rvCoordinateSelectMap B.real id)
      U.property.coordinates.domain (fun _ => rfl)
  have hFV : RVMapGamma (finiteIsoMap fV) B :=
    gamma_real_rv_map_graph hc B _ (rvCoordinateSelectMap B.real id)
      V.property.coordinates.domain (fun _ => rfl)
  exact h.of_permuted_coordinate_charts hc C e fU fV hFU hFV
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

end IntegrationInACVF.Section7
