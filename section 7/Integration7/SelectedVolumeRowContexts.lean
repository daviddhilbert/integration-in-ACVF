import Integration7.FiniteVolumeParameterContexts
import Integration7.PositiveVolumeParameterExtension
import Integration7.SelectedVolumeFamilies

/-! Actual positive fibre objects in their genuine finite-VF-parameter
contexts. The selected coordinates and density are unchanged. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.rowInContext (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) :
    PositiveRVVolumeObject (M := M) ((vfParameterVolumeContext C x).base : Set M) k :=
  (F.rowObject x).extend (vfParameterVolumeContext_contains C x)

@[simp] theorem SelectedVFVolumeFamily.rowInContext_density
    (F : SelectedVFVolumeFamily C n a k) (x : Fin n → VFType (M := M))
    (r : (F.rowInContext x).underlying.obj.domain) :
    (F.rowInContext x).form.value r = F.form.value ⟨(x,r.val),r.property⟩ := rfl

@[simp] theorem SelectedVFVolumeFamily.rowInContext_coordinates
    (F : SelectedVFVolumeFamily C n a k) (x : Fin n → VFType (M := M))
    (r : (F.rowInContext x).underlying.obj.domain) :
    (F.rowInContext x).underlying.obj.value r = r.val ∘ F.selected := rfl

end IntegrationInACVF.Section7
