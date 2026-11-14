import Section4.Products

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}

def definableMapPreimage (F : Map A B) (D : DefSet Q S) : DefSet P S :=
  ⟨{x | ∃ a : A, a.val = x ∧ (F a).val ∈ D.carrier}, F.definable_preimage D.definable⟩

theorem definableMapPreimage_subset (F : Map A B) (D : DefSet Q S) :
    (definableMapPreimage F D).carrier ⊆ A.carrier := by
  rintro x ⟨a, rfl, _⟩
  exact a.property

theorem mem_definableMapPreimage (F : Map A B) (D : DefSet Q S) (a : A) :
    a.val ∈ (definableMapPreimage F D).carrier ↔ (F a).val ∈ D.carrier := by
  constructor
  · rintro ⟨b, hb, h⟩
    have he : b = a := Subtype.ext hb
    rwa [he] at h
  · intro h
    exact ⟨a, rfl, h⟩

end IntegrationInACVF.Section7
