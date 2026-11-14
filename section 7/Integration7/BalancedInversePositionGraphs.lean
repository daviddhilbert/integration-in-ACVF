import Integration7.BalancedCellTranslationEquivalences
import Integration7.GammaPositionCodeCentres

/-! The inverse balanced positioning function has its graph over the
same original parameter base; its totalization outside the image is unused. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.BalancedFibres
open IntegrationInACVF.Section4.Cells IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {D E : Set (VF (M := M))}
variable {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

def balancedInversePosition (h : HasBalancedFibres D E R f r t) (b : VF (M := M)) : VF (M := M) :=
  if hb : b ∈ E then ((balancedPositionEquiv h).symm ⟨b,hb⟩).val else 0

theorem balanced_inverse_position_value (h : HasBalancedFibres D E R f r t)
    (b : VF (M := M)) (hb : b ∈ E) :
    balancedInversePosition h b = ((balancedPositionEquiv h).symm ⟨b,hb⟩).val := by
  exact dif_pos hb

theorem balanced_inverse_position_graph (h : HasBalancedFibres D E R f r t)
    (hPosition : DefinableOverBase B (fun _ : Fin 2 => .vf) (positionCodes D f)) :
    DefinableOverBase B (fun _ : Fin 2 => .vf) (positionCodes E (balancedInversePosition h)) := by
  have hp := hPosition.preimage_real (fun _ : Fin 2 => .vf) (![1,0] : Fin 2 → Fin 2)
  convert hp using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨b,hb,rfl⟩
    let a := (balancedPositionEquiv h).symm ⟨b,hb⟩
    refine ⟨⟨a.val,a.property,?_⟩,?_⟩
    · funext k
      fin_cases k
      · exact congrArg Subtype.val (balanced_inverse_position_value h b hb)
      · exact congrArg Subtype.val (balanced_position_inverse_value h ⟨b,hb⟩).symm
    · intro k
      fin_cases k <;> exact (show iVF _ from (by first | exact b.property | exact (balancedInversePosition h b).property))
  · rintro ⟨⟨a,ha,he⟩,_⟩
    have h0 : z 0 = (f a).val := congrFun he 1
    have h1 : z 1 = a.val := congrFun he 0
    have hb : f a ∈ E := h.bijective.mapsTo ha
    have hi : balancedInversePosition h (f a) = a := by
      rw [balanced_inverse_position_value h (f a) hb]
      exact congrArg Subtype.val ((balancedPositionEquiv h).symm_apply_apply ⟨a,ha⟩)
    refine ⟨f a,hb,?_⟩
    funext k
    fin_cases k
    · exact h0
    · exact h1.trans (congrArg Subtype.val hi.symm)

end IntegrationInACVF.Section7
