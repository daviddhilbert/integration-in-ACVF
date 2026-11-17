module

public import Integration7.TwoOrderRectangleFiniteProducts
public import Integration7.NormalizedContractionUnitComparisons

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The two actual normalized rectangle contractions have a full
original-Gamma volume isomorphism at every retained constant density.
The common finite RV product is constructed from the unary chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.TwoOrderRectanglePreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {d : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hPC : P.real ⊆ (C.base : Set M))
variable {D E : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0}
variable {z : Fin d → SpecialTransformations.Section5.RV (M := M)} {hz : ∀ j, (z j).val ∈ (C.base : Set M)}
variable (F : TwoOrderRectanglePreparations D E z hz P)

def headRawFiniteVolume := (finite_volume_iso (F.headRawRVIso hc C hPC)).mpr (F.commonProduct hc C hPC).property
def tailRawFiniteVolume := (finite_volume_iso (F.tailRawRVIso hc C hPC)).mpr (F.commonProduct hc C hPC).property

def headNormalizedVolumeObject (η : CanonicalRV.RVSort M) (hη : η.val ∈ C.base) (hη0 : η ≠ 0) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) 1 :=
  (normalizedUnitVolumeContraction hc F.headContraction (F.headRawFiniteVolume hc C hPC)).rescale η hη hη0

def tailNormalizedVolumeObject (η : CanonicalRV.RVSort M) (hη : η.val ∈ C.base) (hη0 : η ≠ 0) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) 1 :=
  (normalizedUnitVolumeContraction hc F.tailContraction (F.tailRawFiniteVolume hc C hPC)).rescale η hη hη0

theorem normalized_volume_comparison (η : CanonicalRV.RVSort M) (hη : η.val ∈ C.base) (hη0 : η ≠ 0) :
    ∃ i : RVVolumeIso (F.headNormalizedVolumeObject hc C hPC η hη hη0)
      (F.tailNormalizedVolumeObject hc C hPC η hη hη0), i.GammaDefinable P := by
  obtain ⟨eH,heH⟩ := normalized_contraction_finite_unit_volume_comparison hc C F.headContraction
    (gamma_program_final_set _ F.head_contraction_gamma) (F.commonProduct hc C hPC)
    (F.headRawRVIso hc C hPC) (F.head_raw_coordinates hc C hPC) (F.head_raw_iso_gamma hc C hPC) η hη hη0
  obtain ⟨eT,heT⟩ := normalized_contraction_finite_unit_volume_comparison hc C F.tailContraction
    (gamma_program_final_set _ F.tail_contraction_gamma) (F.commonProduct hc C hPC)
    (F.tailRawRVIso hc C hPC) (F.tail_raw_coordinates hc C hPC) (F.tail_raw_iso_gamma hc C hPC) η hη hη0
  exact ⟨eH.trans hc C (eT.symm hc C),heH.trans hc C P (heT.symm hc C P)⟩

end IntegrationInACVF.Section7.TwoOrderRectanglePreparations
