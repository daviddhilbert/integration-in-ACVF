import Integration7.VolumeParameterExtension

/-! Real parameter extension retains the actual positive volume object
and its essential labels, without adding a generation hypothesis. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M} {k : ℕ}

def PositiveRVVolumeObject.extend (U : PositiveRVVolumeObject (M := M) S k) (h : S ⊆ T) :
    PositiveRVVolumeObject (M := M) T k where
  underlying := Section6.FiniteRV.extendObject h U.underlying
  form := U.form.extend h

@[simp] theorem PositiveRVVolumeObject.extend_density (U : PositiveRVVolumeObject (M := M) S k)
    (h : S ⊆ T) (x : (U.extend h).underlying.obj.domain) :
    (U.extend h).form.value x = U.form.value ⟨x.val,x.property⟩ := rfl

@[simp] theorem PositiveRVVolumeObject.extend_coordinates (U : PositiveRVVolumeObject (M := M) S k)
    (h : S ⊆ T) (x : (U.extend h).underlying.obj.domain) :
    (U.extend h).underlying.obj.value x = U.underlying.obj.value ⟨x.val,x.property⟩ := rfl

@[simp] theorem PositiveRVVolumeObject.extend_essential_domain
    (U : PositiveRVVolumeObject (M := M) S k) (h : S ⊆ T) :
    (U.extend h).essential.obj.domain.carrier = U.essential.obj.domain.carrier := rfl

end IntegrationInACVF.Section7
