import Integration7.UniformVolumeData
import IntegrationSection6.FiniteRVParameterExtension

/-! Extending the real parameter set retains the actual finite-volume
object, its density and its points. It asserts no generation of the new base. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S T : Set M} {n : ℕ}

def RVVolumeData.extend (D : RVVolumeData (M := M) S n) (h : S ⊆ T) :
    RVVolumeData (M := M) T n where
  underlying := Section6.FiniteRV.extendObject h D.underlying
  form := D.form.extend h

@[simp] theorem RVVolumeData.extend_domain (D : RVVolumeData (M := M) S n) (h : S ⊆ T) :
    (D.extend h).underlying.obj.domain.carrier = D.underlying.obj.domain.carrier := rfl

@[simp] theorem RVVolumeData.extend_coordinates (D : RVVolumeData (M := M) S n)
    (h : S ⊆ T) (x : (D.extend h).underlying.obj.domain) :
    (D.extend h).underlying.obj.value x = D.underlying.obj.value ⟨x.val,x.property⟩ := rfl

@[simp] theorem RVVolumeData.extend_density (D : RVVolumeData (M := M) S n)
    (h : S ⊆ T) (x : (D.extend h).underlying.obj.domain) :
    (D.extend h).form.value x = D.form.value ⟨x.val,x.property⟩ := rfl

end IntegrationInACVF.Section7
