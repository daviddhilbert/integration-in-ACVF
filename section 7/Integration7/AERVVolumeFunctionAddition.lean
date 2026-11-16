module

public import Integration7.SelectedVolumeFamilyAddition
public import Integration7.AERVVolumeFunctions

@[expose] public section

/-! Addition and zero on positive homogeneous almost-everywhere
functions are represented by the actual tagged family coproduct and the
empty family. The exceptional set for a sum is the union of the two
original definable VF-small exceptional sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b c d k : ℕ}

theorem ae_selected_volume_family_sum_congr
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k) (F' : SelectedVFVolumeFamily C (n+1) b k)
    (G : SelectedVFVolumeFamily C (n+1) c k) (G' : SelectedVFVolumeFamily C (n+1) d k)
    (hF : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,F'⟩)
    (hG : AERVVolumeFunctionEquivalent hc C ⟨c,G⟩ ⟨d,G'⟩) :
    AERVVolumeFunctionEquivalent hc C ⟨_,selectedVolumeFamilySum F G⟩ ⟨_,selectedVolumeFamilySum F' G'⟩ := by
  obtain ⟨E,hE,hRowsF⟩ := hF
  obtain ⟨D,hD,hRowsG⟩ := hG
  refine ⟨E.union D,by rw [pure_vf_dim_union hc C]; exact max_lt hE hD,?_⟩
  intro x hx
  exact (selected_volume_family_sum_row_class hc F G x).trans
    ((congrArg₂ (fun y z => y+z) (hRowsF x (fun h => hx (Or.inl h)))
      (hRowsG x (fun h => hx (Or.inr h)))).trans (selected_volume_family_sum_row_class hc F' G' x).symm)

instance aeRVVolumeFunctionAdd (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    Add (AERVVolumeFunction hc C n k) :=
  ⟨Quotient.map₂ (fun F G => ⟨_,selectedVolumeFamilySum F.2 G.2⟩)
    (fun F F' hF G G' hG => ae_selected_volume_family_sum_congr hc C F.2 F'.2 G.2 G'.2 hF hG)⟩

instance aeRVVolumeFunctionZero (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    Zero (AERVVolumeFunction hc C n k) := ⟨Quotient.mk _ ⟨k+1,selectedZeroVolumeFamily C (n+1) k⟩⟩

theorem ae_rv_volume_function_add_representatives
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVolumeFunctionPresentation C (n+1) k) (G : SelectedVolumeFunctionPresentation C (n+1) k) :
    (Quotient.mk (aeRVVolumeFunctionSetoid hc C n k) F) + Quotient.mk _ G =
      Quotient.mk _ ⟨_,selectedVolumeFamilySum F.2 G.2⟩ := rfl

end IntegrationInACVF.Section7
