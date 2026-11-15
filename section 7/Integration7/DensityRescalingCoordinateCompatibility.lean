import Integration7.DefinableVolumeClassRescaling
import Integration7.VolumeFunctionIntegralCoordinateNormalization

/-! Raw density rescaling commutes with the genuine coordinate and
degree identifications between appended and canonical integral values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (c : CanonicalRV.RVSort M) (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (hc0 : c ≠ 0)

theorem positive_density_rescale_degree_reindex {i j : ℕ} (h : i=j)
    (x : PositiveVolumeBlowupClasses hc C j) :
    positiveVolumeClassReindexDegree hc C h (positiveVolumeClassRescaleDefinable hc C c hDef hc0 x)=
      positiveVolumeClassRescaleDefinable hc C c hDef hc0 (positiveVolumeClassReindexDegree hc C h x) := by
  cases h
  exact (eq_of_heq (positive_volume_class_reindex_degree_heq hc C rfl _)).trans
    (congrArg (positiveVolumeClassRescaleDefinable hc C c hDef hc0)
      (eq_of_heq (positive_volume_class_reindex_degree_heq hc C rfl x)).symm)

theorem positive_density_rescale_coordinate_permutation {k : ℕ} (σ : Equiv.Perm (Fin (k+1)))
    (x : PositiveVolumeBlowupClasses hc C k) :
    positiveVolumeClassPermute hc C σ (positiveVolumeClassRescaleDefinable hc C c hDef hc0 x)=
      positiveVolumeClassRescaleDefinable hc C c hDef hc0 (positiveVolumeClassPermute hc C σ x) :=
  Quotient.inductionOn x (fun _ => rfl)

theorem canonical_from_appended_density_rescale (n k : ℕ)
    (x : PositiveVolumeBlowupClasses hc C (appendVolumeDegree (n+1) k)) :
    canonicalFromAppendedVolumeClass hc C n k (positiveVolumeClassRescaleDefinable hc C c hDef hc0 x)=
      positiveVolumeClassRescaleDefinable hc C c hDef hc0 (canonicalFromAppendedVolumeClass hc C n k x) := by
  unfold canonicalFromAppendedVolumeClass
  rw [positive_density_rescale_coordinate_permutation,positive_density_rescale_degree_reindex]

theorem canonical_from_appended_injective (n k : ℕ) :
    Function.Injective (canonicalFromAppendedVolumeClass hc C n k) :=
  (positiveVolumeClassDegreeReindexEquiv hc C (selected_append_degree_eq n k).symm).injective.comp
    (positiveVolumeClassPermutationEquiv hc C (appendedToOriginalVolumePermutation (n+1) k)).injective
end IntegrationInACVF.Section7
