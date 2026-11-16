import Integration7.VolumeCoordinateAdditiveEquivalences
import Integration7.HKZeroCoefficientScalarRows

/-! Explicit volume-coordinate and arithmetic identifications are
linear over ordinary RV[0] coefficients, which change no volume order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k a b : ℕ}

def volumePermutedZeroProductIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) (e : Equiv.Perm (Fin (k+1))) :
    RVVolumeIso ((positiveZeroProduct U Z).permuteVolume e) (positiveZeroProduct (U.permuteVolume e) Z) := by
  let P := (positiveZeroProduct U Z).permuteVolume e
  let Q := positiveZeroProduct (U.permuteVolume e) Z
  let f : Map P.underlying.obj.domain Q.underlying.obj.domain := Map.id _
  have hCoord : ∀ q, Q.underlying.obj.value (f q)=P.underlying.obj.value q := by
    intro q
    change (positiveZeroProduct (U.permuteVolume e) Z).underlying.obj.value q=(positiveZeroProduct U Z).underlying.obj.value q ∘ e
    rw [positiveZeroProduct_coordinates,positiveZeroProduct_coordinates]
    rfl
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f Function.bijective_id hCoord)) hCoord (fun _ => rfl)

def positiveVolumeClassPermutationWeightedZeroLinearEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (e : Equiv.Perm (Fin (k+1))) :
    PositiveVolumeBlowupClasses hc C k ≃ₗ[RVBlowupClasses hc C 0] PositiveVolumeBlowupClasses hc C k where
  toAddEquiv := positiveVolumeClassPermutationAddEquiv hc C e
  map_smul' z v := by
    induction z using Quotient.inductionOn with
    | h Z =>
      induction v using Quotient.inductionOn with
      | h U =>
        let z := rvVolumeBlowupClass hc C (n := 0) Z
        have hU := (zero_volume_coefficient_smul_eq_right_product hc C z (positiveVolumeBlowupClass hc C U)).trans
          (positiveVolumeBlowupClass_iso hc C (productPositiveZeroIso hc C U Z))
        have hV := (zero_volume_coefficient_smul_eq_right_product hc C z (positiveVolumeBlowupClass hc C (U.permuteVolume e))).trans
          (positiveVolumeBlowupClass_iso hc C (productPositiveZeroIso hc C (U.permuteVolume e) Z))
        have hChart := positiveVolumeBlowupClass_iso hc C (volumePermutedZeroProductIso hc C U Z e)
        exact (congrArg (positiveVolumeClassPermute hc C e) hU).trans (hChart.trans hV.symm)

def positiveVolumeClassDegreeReindexWeightedZeroLinearEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (h : a=b) :
    PositiveVolumeBlowupClasses hc C b ≃ₗ[RVBlowupClasses hc C 0] PositiveVolumeBlowupClasses hc C a where
  toAddEquiv := positiveVolumeClassDegreeReindexAddEquiv hc C h
  map_smul' z v := by
    cases h
    have hSum := eq_of_heq (positive_volume_class_reindex_degree_heq hc C rfl (z • v))
    have hv := eq_of_heq (positive_volume_class_reindex_degree_heq hc C rfl v)
    exact hSum.trans (congrArg (fun v => z • v) hv.symm)

end IntegrationInACVF.Section7.HK
