import Integration7.HKZeroFamilyCoproducts

/-! Actual weighted zero-valued function addition descends to the AE
quotient and gives its additive commutative monoid structure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ae_zero_family_coprod_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F F' G G' : ZeroVolumeFunctionPresentation C (n+1))
    (hF : AEZeroVolumeFunctionEquivalent hc C F F')
    (hG : AEZeroVolumeFunctionEquivalent hc C G G') :
    AEZeroVolumeFunctionEquivalent hc C ⟨_,F.2.coprod G.2⟩ ⟨_,F'.2.coprod G'.2⟩ := by
  obtain ⟨E,hE,hF⟩ := hF
  obtain ⟨D,hD,hG⟩ := hG
  refine ⟨E.union D,by rw [pure_vf_dim_union hc C]; exact max_lt hE hD,?_⟩
  intro x hx
  exact (zero_family_coprod_row_class hc F.2 G.2 x).trans
    ((congrArg₂ (fun u v => u+v) (hF x (fun he => hx (Or.inl he)))
      (hG x (fun hd => hx (Or.inr hd)))).trans
        (zero_family_coprod_row_class hc F'.2 G'.2 x).symm)

instance aeZeroVolumeFunctionAdd
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Add (AEZeroVolumeFunction hc C n) :=
  ⟨Quotient.map₂ (fun F G => ⟨_,F.2.coprod G.2⟩)
    (fun F F' hF G G' hG => ae_zero_family_coprod_congr hc C F F' G G' hF hG)⟩

instance aeZeroVolumeFunctionZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Zero (AEZeroVolumeFunction hc C n) := ⟨Quotient.mk _ ⟨0,zeroFamily C (n+1)⟩⟩

instance aeZeroVolumeFunctionAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    AddCommMonoid (AEZeroVolumeFunction hc C n) where
  add_assoc f g h := Quotient.inductionOn₃ f g h (fun F G H => Quotient.sound
    (ae_zero_volume_equivalent_of_pointwise hc C (fun x => by
      simp only [zero_family_coprod_row_class]
      exact add_assoc _ _ _)))
  add_comm f g := Quotient.inductionOn₂ f g (fun F G => Quotient.sound
    (ae_zero_volume_equivalent_of_pointwise hc C (fun x => by
      simp only [zero_family_coprod_row_class]
      exact add_comm _ _)))
  zero_add f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_zero_volume_equivalent_of_pointwise hc C (fun x => by
      rw [zero_family_coprod_row_class,zero_family_row_class]
      exact zero_add _)))
  add_zero f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_zero_volume_equivalent_of_pointwise hc C (fun x => by
      rw [zero_family_coprod_row_class,zero_family_row_class]
      exact add_zero _)))
  nsmul := nsmulRec

end IntegrationInACVF.Section7.HK
