import Integration7.ScalarRVAlgebra
import Section4.MapProduct

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.VolumeForm

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {P Q : Space LRV M} {A : DefSet P S} {B : DefSet Q S}

def prod (ω : VolumeForm A) (η : VolumeForm B) : VolumeForm (A.prod B) where
  map := rvScalarMul (ω.map.comp (Map.prodFst A B)) (η.map.comp (Map.prodSnd A B))
  nonzero a := mul_ne_zero (ω.nonzero (Map.prodFst A B a)) (η.nonzero (Map.prodSnd A B a))

@[simp] theorem prod_value (ω : VolumeForm A) (η : VolumeForm B) (a : A.prod B) :
    (ω.prod η).value a = ω.value (Map.prodFst A B a) * η.value (Map.prodSnd A B a) := rfl

end IntegrationInACVF.Section7.VolumeForm
