import Integration7.LowerDimensionRVVolumeIsomorphisms
import Integration7.VolumeDensityRescaling
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open scoped BigOperators
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
local notation "RV" => CanonicalRV.RVSort M

def densityUnitLowerDimensionIso (U : PositiveRVVolumeObject (M := M) S k)
    (hd : rvDim U.essential.obj.domain < k+1)
    (c : RV) (hc : c.val ∈ S) (h0 : c ≠ 0) (habs : RVOperations.absoluteHom c = 1) :
    RVVolumeIso U (U.rescale c hc h0) := by
  let e : U.essential ≅ (U.rescale c hc h0).essential := Iso.refl U.essential
  apply RVVolumeIso.of_absoluteRatio_of_lower_rvDim e hd
  intro u
  have hf : RVOperations.absoluteHom (U.essentialForm.value u) ≠ 0 :=
    (RVOperations.absolute_eq_zero _).not.mpr (U.essentialForm_nonzero u)
  have hp : (∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (RVOperations.absolute_eq_zero _).not.mpr
      ((rv_nonzero_iff_raw _).mpr (U.essential_nonzero u i)))
  change RVOperations.absoluteHom (U.essentialForm.value u / (c * U.essentialForm.value u)) =
    (∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)) /
      ∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)
  rw [map_div₀,map_mul,habs,one_mul,div_self hf,div_self hp]
end IntegrationInACVF.Section7
