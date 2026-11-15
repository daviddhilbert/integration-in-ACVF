import Integration7.AppendedFamilyLiftCoordinates

/-! Coordinate bookkeeping for the product of a positive coefficient
lift and a coefficient-first family lift. The blocks are coefficient,
old family volume, and original family base, in that order. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem appended_positive_coefficient_degree_eq (n p k : ℕ) :
    appendVolumeDegree n ((p+1)+k)=(p+1)+appendVolumeDegree n k := by
  rw [append_volume_degree_eq,append_volume_degree_eq]
  omega

def appendedPositiveCoefficientHead (n p k : ℕ)
    (x : Fin (appendVolumeDegree n ((p+1)+k)+1) → VFType (M := M)) : Fin (p+1) → VFType (M := M) :=
  x ∘ (finCongr (congrArg Nat.succ (appended_positive_coefficient_degree_eq n p k))).symm ∘
    Fin.castAdd (appendVolumeDegree n k+1)

def appendedPositiveCoefficientTail (n p k : ℕ)
    (x : Fin (appendVolumeDegree n ((p+1)+k)+1) → VFType (M := M)) :
    Fin (appendVolumeDegree n k+1) → VFType (M := M) :=
  x ∘ (finCongr (congrArg Nat.succ (appended_positive_coefficient_degree_eq n p k))).symm ∘ Fin.natAdd (p+1)

theorem appended_positive_coefficient_head_coordinates (n p k : ℕ)
    (x : Fin (appendVolumeDegree n ((p+1)+k)+1) → VFType (M := M)) :
    appendedFamilyCoefficientCoordinates n ((p+1)+k) x ∘ Fin.castAdd (k+1) =
      appendedPositiveCoefficientHead n p k x := by
  funext i
  apply congrArg x
  exact Fin.ext rfl

theorem appended_positive_coefficient_tail_coordinates (n p k : ℕ)
    (x : Fin (appendVolumeDegree n ((p+1)+k)+1) → VFType (M := M)) :
    appendedFamilyCoefficientCoordinates n ((p+1)+k) x ∘ Fin.natAdd (p+1) =
      appendedFamilyCoefficientCoordinates n k (appendedPositiveCoefficientTail n p k x) := by
  funext i
  apply congrArg x
  exact Fin.ext rfl

theorem appended_positive_coefficient_base_coordinates (n p k : ℕ)
    (x : Fin (appendVolumeDegree n ((p+1)+k)+1) → VFType (M := M)) :
    appendedFamilyBaseCoordinates n ((p+1)+k) x =
      appendedFamilyBaseCoordinates n k (appendedPositiveCoefficientTail n p k x) := by
  funext i
  apply congrArg x
  apply Fin.ext
  change ((p+1)+k)+1+i.val=(p+1)+((k+1)+i.val)
  omega

end IntegrationInACVF.Section7
