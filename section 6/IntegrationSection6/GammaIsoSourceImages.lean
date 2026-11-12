import IntegrationSection6.GammaIsoRestrictions

/-! Restrict a Gamma isomorphism to a definable source and its actual
image, with no extra definability assumption on that image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m k l : ℕ}

def gammaIsoSourceImage {A : Set (Point (M := M) n m)} {D : Set (Point (M := M) k l)}
    (e : GammaIso B A D) (E : Set (Point (M := M) n m)) (hEA : E ⊆ A)
    (hE : GammaSetDefinable B E) :
    GammaIso B E {q | ∃ p : E, (e.equiv ⟨p.val,hEA p.property⟩).val = q} := by
  have hD : {q | ∃ p : E, (e.equiv ⟨p.val,hEA p.property⟩).val = q} ⊆ D := by
    rintro q ⟨p,rfl⟩
    exact (e.equiv ⟨p.val,hEA p.property⟩).property
  apply gammaIsoRestrict e hEA hD ?_ hE
  intro a
  constructor
  · intro ha
    exact ⟨⟨a.val,ha⟩,rfl⟩
  · rintro ⟨p,hp⟩
    have he : e.equiv ⟨p.val,hEA p.property⟩ = e.equiv a := Subtype.ext hp
    have he' : p.val = a.val := congrArg (fun u : A => u.val) (e.equiv.injective he)
    exact he' ▸ p.property

end IntegrationInACVF.Section6
