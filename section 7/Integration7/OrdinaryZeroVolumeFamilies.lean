import Integration7.OrdinaryVolumeFamilyCoproducts
import Section4.EmptyMaps
import Integration7.VFVolumeClasses

/-! The literal empty family represents the zero ordinary RV-valued
function and the empty positive VF volume object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ordinaryZeroVolumeFamily (C : BaseContext M) (n : ℕ) : OrdinaryVFVolumeFamily C n 0 where
  domain := DefSet.empty _ (C.base : Set M)
  finite_labels _ := Set.finite_empty

theorem ordinary_zero_volume_family_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ)
    (x : Fin n → VFType (M := M)) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0)
      ((ordinaryZeroVolumeFamily C n).rowInContext x) = 0 := by
  let U := (ordinaryZeroVolumeFamily C n).rowInContext x
  let V := rvVolumeEmpty ((vfParameterVolumeContext C x).base : Set M) 0
  let f : Map U.obj.domain V.obj.domain := Map.fromEmpty rfl V.obj.domain
  exact Quotient.sound ⟨finiteIsoOfNondegenerateBijection f (Map.bijective_of_empty f rfl rfl)
    (fun _ i => i.elim0) (fun _ i => i.elim0)⟩

@[simp] theorem ordinary_zero_volume_family_full_object (C : BaseContext M) (n : ℕ) :
    (ordinaryZeroVolumeFamily C (n+1)).fullVFObject = PositiveVFVolumeObject.empty (C.base : Set M) n := rfl

end IntegrationInACVF.Section7
