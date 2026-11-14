import Section4.MapParameters
import Section4.Products
import Section4.RealPresentations
import Section3.RVOperations

/-! Definable nonzero RV-valued densities, with their actual parameter base.
This is a reconstruction of the form interface used by the recovered
Section 7 modules. It introduces no Jacobian or integration assumptions. -/

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P Q : Space LRV M} {S T : Set M}

structure VolumeForm (A : DefSet P S) where
  map : Map A (DefSet.univ (rawRVSpace (M := M) 1) S)
  nonzero : ∀ a, (map a).val 0 ≠ 0

namespace VolumeForm

def value {A : DefSet P S} (ω : VolumeForm A) (a : A) : CanonicalRV.RVSort M :=
  (ω.map a).val 0

theorem value_ne_zero {A : DefSet P S} (ω : VolumeForm A) (a : A) : ω.value a ≠ 0 :=
  ω.nonzero a

def pullback {A : DefSet P S} {B : DefSet Q S} (ω : VolumeForm B) (f : Map A B) :
    VolumeForm A where
  map := ω.map.comp f
  nonzero a := ω.nonzero (f a)

@[simp] theorem pullback_value {A : DefSet P S} {B : DefSet Q S}
    (ω : VolumeForm B) (f : Map A B) (a : A) :
    (ω.pullback f).value a = ω.value (f a) := rfl

def restrict {A B : DefSet P S} (ω : VolumeForm A) (h : B.carrier ⊆ A.carrier) :
    VolumeForm B := ω.pullback (Map.inclusion h)

@[simp] theorem restrict_value {A B : DefSet P S} (ω : VolumeForm A)
    (h : B.carrier ⊆ A.carrier) (b : B) :
    (ω.restrict h).value b = ω.value ⟨b.val, h b.property⟩ := rfl

def extend {A : DefSet P S} (ω : VolumeForm A) (h : S ⊆ T) :
    VolumeForm (A.extend h) where
  map := ω.map.extend h
  nonzero a := ω.nonzero ⟨a.val, a.property⟩

@[simp] theorem extend_value {A : DefSet P S} (ω : VolumeForm A) (h : S ⊆ T)
    (a : A.extend h) : (ω.extend h).value a = ω.value ⟨a.val, a.property⟩ := rfl

end VolumeForm

end IntegrationInACVF.Section7
