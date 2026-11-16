module

public import Integration7.AEOrdinaryRVVolumeFunctions
public import Integration7.OrdinaryZeroVolumeFamilies

@[expose] public section

/-! Actual pointwise addition of ordinary RV[0]-valued functions
descends through the union of the two VF-small exceptional sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem ae_ordinary_volume_family_coprod_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F F' G G' : OrdinaryVolumeFunctionPresentation C (n+1))
    (hF : AEOrdinaryRVVolumeFunctionEquivalent hc C F F')
    (hG : AEOrdinaryRVVolumeFunctionEquivalent hc C G G') :
    AEOrdinaryRVVolumeFunctionEquivalent hc C ⟨_,F.2.coprod G.2⟩ ⟨_,F'.2.coprod G'.2⟩ := by
  obtain ⟨E,hE,hF⟩ := hF
  obtain ⟨D,hD,hG⟩ := hG
  refine ⟨E.union D,by rw [pure_vf_dim_union hc C]; exact max_lt hE hD,?_⟩
  intro x hx
  exact (ordinary_volume_family_coprod_row_class hc F.2 G.2 x).trans
    ((congrArg₂ (fun u v => u+v) (hF x (fun he => hx (Or.inl he)))
      (hG x (fun hd => hx (Or.inr hd)))).trans
        (ordinary_volume_family_coprod_row_class hc F'.2 G'.2 x).symm)

instance aeOrdinaryRVVolumeFunctionAdd
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Add (AEOrdinaryRVVolumeFunction hc C n) :=
  ⟨Quotient.map₂ (fun F G => ⟨_,F.2.coprod G.2⟩)
    (fun F F' hF G G' hG => ae_ordinary_volume_family_coprod_congr hc C F F' G G' hF hG)⟩

instance aeOrdinaryRVVolumeFunctionZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Zero (AEOrdinaryRVVolumeFunction hc C n) := ⟨Quotient.mk _ ⟨0,ordinaryZeroVolumeFamily C (n+1)⟩⟩

instance aeOrdinaryRVVolumeFunctionAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    AddCommMonoid (AEOrdinaryRVVolumeFunction hc C n) where
  add_assoc f g h := Quotient.inductionOn₃ f g h (fun F G H => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      simp only [ordinary_volume_family_coprod_row_class]
      exact add_assoc _ _ _)))
  add_comm f g := Quotient.inductionOn₂ f g (fun F G => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      simp only [ordinary_volume_family_coprod_row_class]
      exact add_comm _ _)))
  zero_add f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      rw [ordinary_volume_family_coprod_row_class,ordinary_zero_volume_family_row_class]
      exact zero_add _)))
  add_zero f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_ordinary_rv_volume_equivalent_of_pointwise hc C (fun x => by
      rw [ordinary_volume_family_coprod_row_class,ordinary_zero_volume_family_row_class]
      exact add_zero _)))
  nsmul := nsmulRec

end IntegrationInACVF.Section7
