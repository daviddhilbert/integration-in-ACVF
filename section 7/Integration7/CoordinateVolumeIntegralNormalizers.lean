import Integration7.AERVVolumeCoordinatePushforwards
import Integration7.VolumeFunctionIntegralCoordinateNormalization
import Integration7.VolumeFunctionIntegralPermutationCovariance

/-! Return the iterated integral of a coordinate projection to the
original global coordinate order. The map consists solely of arithmetic
degree casts, the fixed appended-to-canonical permutation, and the
inverse VF block permutation of the actual coordinate split. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p k : ℕ}

theorem append_volume_degree_split (p d k : ℕ) :
    appendVolumeDegree ((p+d)+1) k = appendVolumeDegree (p+1) (appendVolumeDegree d k) := by
  simp only [append_volume_degree_eq]
  omega

def coordinateVolumeIntegralNormalizer
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (E : VFCoordinateProjection (n+1) (p+1)) (k : ℕ) :
    PositiveVolumeBlowupClasses hc C (appendVolumeDegree (p+1) (appendVolumeDegree E.discarded k)) →
      PositiveVolumeBlowupClasses hc C ((k+1)+n) :=
  fun x => positiveVolumeClassReindexDegree hc C
    (congrArg (fun j => (k+1)+j) (volume_projection_index_eq E).symm)
      (positiveVolumeClassPermute (k := (k+1)+(p+E.discarded)) hc C
        (selectedVFTailPermutation (n := (p+E.discarded)+1) (k+1) (volumeProjectionFibreOrder E)).symm
          (canonicalFromAppendedVolumeClass hc C (p+E.discarded) k
            (positiveVolumeClassReindexDegree hc C (append_volume_degree_split p E.discarded k) x)))

theorem ae_rv_volume_integral_reindex_base_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {a b k : ℕ} (h : a=b) (f : AERVVolumeFunction hc C b k) :
    HEq (aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (aeRVVolumeFunctionReindexBase hc C h f))
      (aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  cases h
  rfl

end IntegrationInACVF.Section7
