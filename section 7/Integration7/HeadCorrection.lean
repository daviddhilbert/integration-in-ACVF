import Integration7.BlowupHeadIsomorphism
import Integration7.BlowupCorrection
import Integration7.GammaAbsoluteValues
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "RV" => CanonicalRV.RVSort M

def headCorrection {S : Set M} {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) S k} (f : RVVolumeIso U V)
    (u : U.essential.obj.domain) (J : RV) : RV :=
  blowupCorrection J (U.essentialForm.value u) (V.essentialForm.value (finiteIsoMap f.iso u))
    (U.essential.obj.value u (Fin.last k)) (V.essential.obj.value (finiteIsoMap f.iso u) (Fin.last k))

theorem headCorrection_absolute_one {k : ℕ} (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U V) (hU : BlowupAdmissible U) (hV : BlowupAdmissible V)
    (u : U.essential.obj.domain) (J : RV)
    (hJ : IsRVJacobianAt (volumeCorrespondence (finiteIsoMap (blowupHeadIso C f hU hV))).carrier
      (U.essential.obj.value u ∘ Fin.castSucc)
      (V.essential.obj.value (finiteIsoMap f.iso u) ∘ Fin.castSucc) J) :
    RVOperations.absoluteHom (headCorrection f u J) = 1 := by
  have hr : U.essential.obj.value u (Fin.last k) ≠ 0 := by
    intro hz
    exact U.essential_nonzero u (Fin.last k) ((congrArg Subtype.val hz).trans RVOperations.zero_val)
  have hs : V.essential.obj.value (finiteIsoMap f.iso u) (Fin.last k) ≠ 0 := by
    intro hz
    exact V.essential_nonzero _ (Fin.last k) ((congrArg Subtype.val hz).trans RVOperations.zero_val)
  apply blowupCorrection_absolute _ _ _ _ _ (rvJacobian_ne_zero hJ) hr hs
  change RVOperations.absoluteHom (volumeRatio U V f.iso u) = _
  rw [f.absolute_volumeRatio u, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, ← div_mul_div_comm]
  rw [hJ.absolute_eq_weight_ratio]
  rfl
end IntegrationInACVF.Section7
