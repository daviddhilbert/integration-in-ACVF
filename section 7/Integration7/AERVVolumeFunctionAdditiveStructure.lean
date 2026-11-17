module

public import Integration7.AERVVolumeFunctionAddition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual pointwise addition of positive homogeneous definable
volume functions gives an additive commutative monoid on the paper's
almost-everywhere function quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

instance aeRVVolumeFunctionAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    AddCommMonoid (AERVVolumeFunction hc C n k) where
  add_assoc f g h := Quotient.inductionOn₃ f g h (fun F G H => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_volume_family_sum_row_class]
      exact add_assoc _ _ _)))
  add_comm f g := Quotient.inductionOn₂ f g (fun F G => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      simp only [selected_volume_family_sum_row_class]
      exact add_comm _ _)))
  zero_add f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      rw [selected_volume_family_sum_row_class,selected_zero_volume_family_row_class]
      exact zero_add _)))
  add_zero f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => by
      rw [selected_volume_family_sum_row_class,selected_zero_volume_family_row_class]
      exact add_zero _)))
  nsmul := nsmulRec

end IntegrationInACVF.Section7
