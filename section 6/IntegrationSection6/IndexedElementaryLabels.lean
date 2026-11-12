import IntegrationSection6.GammaIndexedFiniteObjects

/-! The actual coordinate reassociation between an indexed elementary
row and the elementary blowup of the indexed object. -/
noncomputable section
open Classical
namespace IntegrationInACVF.Section6

def indexedElementaryCoordinates (p a : ℕ) : Fin ((p+a)+1) → Fin (p+(a+1)) :=
  Fin.cast (Nat.add_assoc p a 1)

def indexedElementaryLabels {Y : Type*} {p a : ℕ} (w : Fin (p+(a+1)) → Y) : Fin ((p+a)+1) → Y :=
  w ∘ indexedElementaryCoordinates p a

def indexedElementaryTupleEquiv (Y : Type*) (p a : ℕ) :
    (Fin (p+(a+1)) → Y) ≃ (Fin ((p+a)+1) → Y) where
  toFun := indexedElementaryLabels
  invFun := fun w => w ∘ Fin.cast (Nat.add_assoc p a 1).symm
  left_inv w := by
    funext j
    simp only [indexedElementaryLabels,indexedElementaryCoordinates,Function.comp_apply,Fin.cast_cast,Fin.cast_eq_self]
  right_inv w := by
    funext j
    simp only [indexedElementaryLabels,indexedElementaryCoordinates,Function.comp_apply,Fin.cast_cast,Fin.cast_eq_self]

theorem indexedElementaryLabels_head {Y : Type*} {p a : ℕ} (w : Fin (p+(a+1)) → Y) :
    indexedElementaryLabels w ∘ Fin.castAdd 1 = Fin.append (indexedLeft w) (indexedRight w ∘ Fin.castAdd 1) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [indexedElementaryLabels,indexedElementaryCoordinates,Function.comp_apply,Fin.append_left,indexedLeft]
    exact congrArg w (Fin.ext rfl)
  · simp only [indexedElementaryLabels,indexedElementaryCoordinates,Function.comp_apply,Fin.append_right,indexedRight]
    exact congrArg w (Fin.ext rfl)

theorem indexedElementaryLabels_parameter {Y : Type*} {p a : ℕ} (w : Fin (p+(a+1)) → Y) :
    indexedElementaryLabels w ∘ Fin.natAdd (p+a) = indexedRight w ∘ Fin.natAdd a := by
  funext j
  simp only [indexedElementaryLabels,indexedElementaryCoordinates,Function.comp_apply,indexedRight]
  apply congrArg w
  apply Fin.ext
  simp only [Fin.val_cast,Fin.val_natAdd]
  omega

end IntegrationInACVF.Section6
