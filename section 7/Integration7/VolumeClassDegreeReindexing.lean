import Integration7.VolumeBlowupClasses
import Integration7.VolumeBlowupRightProducts

/-! Arithmetic degree reindexing on the actual common-blowup classes.
It changes no mathematical object: its value is heterogeneously equal
to the original class and its inverse is the opposite arithmetic cast. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b : ℕ}

def positiveVolumeClassReindexDegree
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (h : a=b) :
    PositiveVolumeBlowupClasses hc C b → PositiveVolumeBlowupClasses hc C a :=
  Quotient.map (fun U => U.reindexDegree h) (fun _ _ g => g.reindexDegree hc C h)

theorem positive_volume_class_reindex_degree_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (h : a=b)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) b) :
    positiveVolumeClassReindexDegree hc C h (positiveVolumeBlowupClass hc C U) =
      positiveVolumeBlowupClass hc C (U.reindexDegree h) := rfl

theorem positive_volume_class_reindex_degree_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (h : a=b)
    (x : PositiveVolumeBlowupClasses hc C b) : HEq (positiveVolumeClassReindexDegree hc C h x) x := by
  cases h
  induction x using Quotient.inductionOn with
  | h U => exact heq_of_eq (positiveVolumeBlowupClass_iso hc C (volumeCastReindexIso hc C U rfl))

def positiveVolumeClassDegreeReindexEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (h : a=b) :
    PositiveVolumeBlowupClasses hc C b ≃ PositiveVolumeBlowupClasses hc C a where
  toFun := positiveVolumeClassReindexDegree hc C h
  invFun := positiveVolumeClassReindexDegree hc C h.symm
  left_inv x := eq_of_heq ((positive_volume_class_reindex_degree_heq hc C h.symm _).trans
    (positive_volume_class_reindex_degree_heq hc C h x))
  right_inv x := eq_of_heq ((positive_volume_class_reindex_degree_heq hc C h _).trans
    (positive_volume_class_reindex_degree_heq hc C h.symm x))

end IntegrationInACVF.Section7
