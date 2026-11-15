import Integration7.AERVVolumeFunctionAdditiveStructure

/-! Arithmetic reindexing of the homogeneous coefficient degree changes
no family or AE relation. A heterogeneous fibre equality gives equality
of the corresponding reindexed AE function classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

def aeRVVolumeFunctionReindexDegree
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) (h : a=b) :
    AERVVolumeFunction hc C n a ≃+ AERVVolumeFunction hc C n b := by
  cases h
  exact AddEquiv.refl _

theorem ae_rv_volume_function_reindex_degree_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (h : a=b)
    (f : AERVVolumeFunction hc C n a) : HEq (aeRVVolumeFunctionReindexDegree hc C n h f) f := by
  cases h
  rfl

theorem ae_rv_volume_function_class_heq_of_rows
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (h : a=b)
    (F : SelectedVolumeFunctionPresentation C (n+1) a) (G : SelectedVolumeFunctionPresentation C (n+1) b)
    (hRows : ∀ x, HEq (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.2.rowInContext x))
      (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (G.2.rowInContext x))) :
    HEq (Quotient.mk (aeRVVolumeFunctionSetoid hc C n a) F) (Quotient.mk (aeRVVolumeFunctionSetoid hc C n b) G) := by
  cases h
  exact heq_of_eq (Quotient.sound (ae_rv_volume_function_equivalent_of_pointwise hc C (fun x => eq_of_heq (hRows x))))

end IntegrationInACVF.Section7
