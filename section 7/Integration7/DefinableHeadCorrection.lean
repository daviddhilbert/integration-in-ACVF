import Integration7.HeadCorrection
import Integration7.RVUnitNormalization

/-! A definable correction on all essential labels. At the labels where
the head Jacobian is defined it is the required algebraic correction.
Elsewhere the unit fallback keeps the corrected cone map bijective. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {U V : PositiveRVVolumeObject (M := M) S k}

def rawHeadCorrectionMap (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let F := finiteIsoMap f.iso
  let r := (rvCoordinateSelectMap S (fun _ : Fin 1 => Fin.last k)).comp U.essential.obj.volume
  let s := (rvCoordinateSelectMap S (fun _ : Fin 1 => Fin.last k)).comp (V.essential.obj.volume.comp F)
  let ratio := rvScalarMul U.essentialForm.map ((rvInverse S).comp (V.essentialForm.map.comp F))
  let denominator := rvScalarMul J (rvScalarMul s ((rvInverse S).comp r))
  exact rvScalarMul ratio ((rvInverse S).comp denominator)

theorem rawHeadCorrectionMap_value (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (u : U.essential.obj.domain) :
    (rawHeadCorrectionMap f J u).val 0 = headCorrection f u ((J u).val 0) := by
  simp only [rawHeadCorrectionMap, rvScalarMul_value, rvInverse_value, Map.comp_apply,
    headCorrection, blowupCorrection, div_eq_mul_inv]
  rfl

def headCorrectionMap (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  (rvUnitNormalize S).comp (rawHeadCorrectionMap f J)

theorem headCorrectionMap_absolute (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (u : U.essential.obj.domain) :
    RVOperations.absoluteHom ((headCorrectionMap f J u).val 0) = 1 :=
  rvUnitNormalize_absolute S (rawHeadCorrectionMap f J u)

theorem headCorrectionMap_of_absolute_one (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (u : U.essential.obj.domain)
    (h : RVOperations.absoluteHom (headCorrection f u ((J u).val 0)) = 1) :
    (headCorrectionMap f J u).val 0 = headCorrection f u ((J u).val 0) := by
  have hr : RVOperations.absoluteHom ((rawHeadCorrectionMap f J u).val 0) = 1 := by
    rwa [rawHeadCorrectionMap_value]
  exact (rvUnitNormalize_of_absolute_one S _ hr).trans (rawHeadCorrectionMap_value f J u)

theorem headCorrectionMap_of_jacobian (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U V) (hU : BlowupAdmissible U) (hV : BlowupAdmissible V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)))
    (u : U.essential.obj.domain)
    (hJ : IsRVJacobianAt (volumeCorrespondence (finiteIsoMap (blowupHeadIso C f hU hV))).carrier
      (U.essential.obj.value u ∘ Fin.castSucc)
      (V.essential.obj.value (finiteIsoMap f.iso u) ∘ Fin.castSucc) ((J u).val 0)) :
    (headCorrectionMap f J u).val 0 = headCorrection f u ((J u).val 0) :=
  headCorrectionMap_of_absolute_one f J u (headCorrection_absolute_one C f hU hV u _ hJ)

end IntegrationInACVF.Section7
