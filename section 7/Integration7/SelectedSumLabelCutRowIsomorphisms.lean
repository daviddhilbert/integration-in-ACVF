module

public import Integration7.SelectedSumTagPredicates
public import Integration7.SelectedSumRowCoverage

@[expose] public section

/-! The two old-tag cuts of the actual selected sum recover its
original summands by genuine coordinate- and density-preserving row bijections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

def selectedSumLeftCutFamily (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k) :=
  (selectedVolumeFamilySum F G).onRVLabels hc Ξ (selectedSumTagIndex a b k)
    (selectedSumLeftTagPredicate hc C) (selected_sum_left_tag_gamma hc C Ξ) hNames

def selectedSumRightCutFamily (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k) :=
  (selectedVolumeFamilySum F G).onRVLabels hc Ξ (selectedSumTagIndex a b k)
    (Set.univ \ selectedSumLeftTagPredicate hc C) (selected_sum_right_tag_gamma hc C Ξ) hNames

theorem selected_sum_left_row_tag (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (F.rowInContext x).underlying.obj.domain) :
    (Fin.elim0,(selectedSumLeftRowMap F G x r).val ∘ selectedSumTagIndex a b k) ∈ selectedSumLeftTagPredicate hc C := by
  apply (selected_sum_left_tag_mem hc C _).mpr
  change ((selectedSumLeftRowMap F G x r).val (selectedSumTagIndex a b k 0)).val=iRVZero
  rw [selected_sum_left_row_value]
  simp only [selectedSumTagIndex,Fin.append_left,rvLeftTag]
  rfl

theorem selected_sum_right_row_not_left_tag (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (G.rowInContext x).underlying.obj.domain) :
    (Fin.elim0,(selectedSumRightRowMap F G x r).val ∘ selectedSumTagIndex a b k) ∉ selectedSumLeftTagPredicate hc C := by
  intro h
  have hz := (selected_sum_left_tag_mem hc C _).mp h
  change ((selectedSumRightRowMap F G x r).val (selectedSumTagIndex a b k 0)).val=iRVZero at hz
  rw [selected_sum_right_row_value] at hz
  simp only [selectedSumTagIndex,Fin.append_left,rvRightTag] at hz
  exact RVCalc.rv_one_ne_zero (M := M) inferInstance hz

def selectedSumLeftCutRowIso (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso (F.rowInContext x) ((selectedSumLeftCutFamily hc Ξ hNames F G).rowInContext x) := by
  let H := selectedVolumeFamilySum F G
  let L := (selectedSumLeftCutFamily hc Ξ hNames F G).rowInContext x
  let f : Map (F.rowInContext x).underlying.obj.domain L.underlying.obj.domain :=
    (selectedSumLeftRowMap F G x).corestrict (fun r =>
      ⟨(selectedSumLeftRowMap F G x r).property,selected_sum_left_row_tag hc F G x r⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro r s h
      exact selected_sum_left_row_injective F G x (Subtype.ext (congrArg (fun q : L.underlying.obj.domain => q.val) h))
    · intro q
      let qH : (H.rowInContext x).underlying.obj.domain := ⟨q.val,q.property.1⟩
      rcases selected_sum_row_cover F G x qH with ⟨r,hr⟩ | ⟨r,hr⟩
      · exact ⟨r,Subtype.ext (congrArg (fun z : (H.rowInContext x).underlying.obj.domain => z.val) hr)⟩
      · have hNot := selected_sum_right_row_not_left_tag hc F G x r
        rw [hr] at hNot
        exact (hNot q.property.2).elim
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf (selected_sum_left_row_coordinates F G x)))
    (selected_sum_left_row_coordinates F G x) (selected_sum_left_row_density F G x)

def selectedSumRightCutRowIso (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso (G.rowInContext x) ((selectedSumRightCutFamily hc Ξ hNames F G).rowInContext x) := by
  let H := selectedVolumeFamilySum F G
  let L := (selectedSumRightCutFamily hc Ξ hNames F G).rowInContext x
  let f : Map (G.rowInContext x).underlying.obj.domain L.underlying.obj.domain :=
    (selectedSumRightRowMap F G x).corestrict (fun r =>
      ⟨(selectedSumRightRowMap F G x r).property,Set.mem_univ _,selected_sum_right_row_not_left_tag hc F G x r⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro r s h
      exact selected_sum_right_row_injective F G x (Subtype.ext (congrArg (fun q : L.underlying.obj.domain => q.val) h))
    · intro q
      let qH : (H.rowInContext x).underlying.obj.domain := ⟨q.val,q.property.1⟩
      rcases selected_sum_row_cover F G x qH with ⟨r,hr⟩ | ⟨r,hr⟩
      · have hTag := selected_sum_left_row_tag hc F G x r
        rw [hr] at hTag
        exact (q.property.2.2 hTag).elim
      · exact ⟨r,Subtype.ext (congrArg (fun z : (H.rowInContext x).underlying.obj.domain => z.val) hr)⟩
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf (selected_sum_right_row_coordinates F G x)))
    (selected_sum_right_row_coordinates F G x) (selected_sum_right_row_density F G x)
end IntegrationInACVF.Section7
