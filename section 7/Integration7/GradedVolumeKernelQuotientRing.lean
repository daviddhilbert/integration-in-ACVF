import Integration7.VolumeDegreeKernelQuotients
import Integration7.BlowupVolumeHomogeneousProducts
import Integration7.AdditiveEquivalenceRingTransport
import Integration7.RawVolumeKernelIdeal

/-! The actual degree-k kernel quotients form a graded ring. The
multiplication is transported through the independently proved additive
decomposition, and products of homogeneous elements are proved to have
the sum degree. This closes the ring decomposition of Theorem 7.13
without assuming the preceding single-generator assertion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

abbrev VolumeGradedKernelQuotient := DirectSum ℕ
  (fun n => Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n) ⧸ volumeDegreeKernelAddSubgroup hc C n)

def volumeGradedKernelQuotientCompositionEquiv : VolumeGradedKernelQuotient hc C ≃+ RVVolumeBlowupRing hc C :=
  (volumeGradedKernelQuotientAddEquiv hc C).trans (blowupVolumeGradedAddEquiv hc C).symm

instance volumeGradedKernelQuotientRing : Ring (VolumeGradedKernelQuotient hc C) :=
  ringOfAdditiveEquivalence (volumeGradedKernelQuotientCompositionEquiv hc C)

def volumeGradedKernelQuotientRingEquiv : VolumeGradedKernelQuotient hc C ≃+* RVVolumeBlowupRing hc C :=
  ringEquivOfAdditiveEquivalence (volumeGradedKernelQuotientCompositionEquiv hc C)

theorem volume_graded_kernel_composition_of (n : ℕ)
    (x : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n) ⧸ volumeDegreeKernelAddSubgroup hc C n) :
    volumeGradedKernelQuotientRingEquiv hc C (DirectSum.of _ n x)=
      blowupVolumeHomogeneousAdditiveMap hc C n (volumeDegreeKernelQuotientEquiv hc C n x) := by
  change blowupVolumeComposition hc C ((volumeGradedKernelQuotientAddEquiv hc C) (DirectSum.of _ n x)) = _
  change blowupVolumeComposition hc C
    (DirectSum.map (fun j => (volumeDegreeKernelQuotientEquiv hc C j).toAddMonoidHom) (DirectSum.of _ n x)) = _
  rw [DirectSum.map_of,blowup_volume_composition_of]
  rfl

theorem volume_graded_kernel_homogeneous_product (n m : ℕ)
    (x : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n) ⧸ volumeDegreeKernelAddSubgroup hc C n)
    (y : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C m) ⧸ volumeDegreeKernelAddSubgroup hc C m) :
    ∃ z : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C (n+m)) ⧸ volumeDegreeKernelAddSubgroup hc C (n+m),
      (DirectSum.of _ n x : VolumeGradedKernelQuotient hc C)*DirectSum.of _ m y=DirectSum.of _ (n+m) z := by
  obtain ⟨z,hz⟩ := blowup_volume_homogeneous_product_closed hc C n m
    (volumeDegreeKernelQuotientEquiv hc C n x) (volumeDegreeKernelQuotientEquiv hc C m y)
  refine ⟨(volumeDegreeKernelQuotientEquiv hc C (n+m)).symm z,?_⟩
  apply (volumeGradedKernelQuotientRingEquiv hc C).injective
  rw [map_mul,volume_graded_kernel_composition_of,volume_graded_kernel_composition_of,
    volume_graded_kernel_composition_of,AddEquiv.apply_symm_apply]
  exact hz

theorem volume_graded_kernel_unit_degree_zero :
    (1 : VolumeGradedKernelQuotient hc C)=DirectSum.of _ 0
      ((volumeDegreeKernelQuotientEquiv hc C 0).symm
        (Algebra.GrothendieckAddGroup.of (1 : RVVolumeBlowupClasses hc C 0))) := by
  apply (volumeGradedKernelQuotientRingEquiv hc C).injective
  rw [map_one,volume_graded_kernel_composition_of,AddEquiv.apply_symm_apply,blowup_volume_homogeneous_unit]

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def theorem_7_13 :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFVolumeRing hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+* VolumeGradedKernelQuotient hc C := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact (volumeIntegrationRingEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).trans
    (volumeGradedKernelQuotientRingEquiv hc C).symm

def theorem_7_13_kernel_quotient :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFVolumeRing hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+* (RawRVVolumeRing hc C ⧸ rawVolumeKernelIdeal hc C) :=
  volumeIntegrationKernelIdealQuotientEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
end IntegrationInACVF.Section7
