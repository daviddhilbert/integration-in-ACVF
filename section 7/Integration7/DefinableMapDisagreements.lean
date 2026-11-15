import Section4.RVRestrictions
import Section4.MapParameters

/-! The literal locus where two definable maps disagree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}

def mapAgreementLocus (f g : Map A B) : DefSet P S :=
  ⟨{x | ∃ y, f.graph x y ∧ g.graph x y},
    (f.graph_definable.inter P Q g.graph_definable).exists_right P Q⟩

theorem mem_mapAgreementLocus (f g : Map A B) (u : A) :
    u.val ∈ (mapAgreementLocus f g).carrier ↔ (f u).val = (g u).val := by
  constructor
  · rintro ⟨y,⟨v,hv,hfy⟩,w,hw,hgy⟩
    have hvu : v = u := Subtype.ext hv
    have hwu : w = u := Subtype.ext hw
    subst v
    subst w
    exact hfy.trans hgy.symm
  · intro h
    exact ⟨(f u).val,⟨u,rfl,rfl⟩,u,rfl,h.symm⟩

def mapDisagreementLocus (f g : Map A B) : DefSet P S := A.sdiff (mapAgreementLocus f g)

theorem mem_mapDisagreementLocus (f g : Map A B) (u : A) :
    u.val ∈ (mapDisagreementLocus f g).carrier ↔ (f u).val ≠ (g u).val := by
  change (u.val ∈ A.carrier ∧ u.val ∉ (mapAgreementLocus f g).carrier) ↔ _
  rw [mem_mapAgreementLocus]
  simp only [u.property,true_and]

end IntegrationInACVF.Section7
