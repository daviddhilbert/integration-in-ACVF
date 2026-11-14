import Integration7.VolumeForms
import Section4.UnionMapLaws

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.VolumeForm

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Space LRV M} {S : Set M} {A B : DefSet P S}

def union (ω : VolumeForm A) (η : VolumeForm B) : VolumeForm (A.union B) where
  map := ω.map.union η.map
  nonzero a := by
    classical
    by_cases h : a.val ∈ A.carrier
    · simpa only [Map.union, dif_pos h] using ω.nonzero ⟨a.val, h⟩
    · simpa only [Map.union, dif_neg h] using η.nonzero ⟨a.val, a.property.resolve_left h⟩

@[simp] theorem union_value_left (ω : VolumeForm A) (η : VolumeForm B) (a : A) :
    (ω.union η).value ⟨a.val, Or.inl a.property⟩ = ω.value a :=
  congrArg (fun z : DefSet.univ (rawRVSpace (M := M) 1) S => z.val 0)
    (Map.union_on_left ω.map η.map a)

theorem union_value_right (ω : VolumeForm A) (η : VolumeForm B)
    (h : Disjoint A.carrier B.carrier) (b : B) :
    (ω.union η).value ⟨b.val, Or.inr b.property⟩ = η.value b :=
  congrArg (fun z : DefSet.univ (rawRVSpace (M := M) 1) S => z.val 0)
    (Map.union_on_right ω.map η.map h b)

end IntegrationInACVF.Section7.VolumeForm
