import IntegrationSection5.UnaryCellZeros
import Section4.RVCategories
/-! The actual unary RV weight, with normalization of the single absorbing RV element made explicit. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] Classical.propDecidable
theorem rvWeight_unary (x : VF (M := M)) :
    @SpecialTransformations.Section4.rvWeight M (@CanonicalStructure.normalize M sM) 1
      (fun _ => @rv M sM hM x) = if x = 0 then 0 else 1 := by
  classical
  simp only [SpecialTransformations.Section4.rvWeight,Fin.sum_univ_one]
  have hZero : @iRVZero M (@CanonicalStructure.normalize M sM) = @iRVZero M sM :=
    @CanonicalStructure.sortZero_normalize M sM .rv
  rw [hZero]
  have hz : (rv x).val = iRVZero ↔ x = 0 := CanonicalRV.encodedRv_zero_iff x
  by_cases hx : x = 0
  · rw [if_pos hx,if_neg (not_not_intro (hz.mpr hx))]
  · rw [if_neg hx,if_pos (fun h => hx (hz.mp h))]
theorem rvWeight_unary_tuple (x : Fin 1 → VF (M := M)) :
    @SpecialTransformations.Section4.rvWeight M (@CanonicalStructure.normalize M sM) 1
      (fun i => @rv M sM hM (x i)) = if x 0 = 0 then 0 else 1 := by
  have he : (fun i : Fin 1 => @rv M sM hM (x i)) = (fun _ : Fin 1 => @rv M sM hM (x 0)) := by
    funext i
    exact congrArg (fun j => @rv M sM hM (x j)) (Subsingleton.elim _ _)
  rw [he,rvWeight_unary]
end IntegrationInACVF.Section5
