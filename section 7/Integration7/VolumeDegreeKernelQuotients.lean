import Integration7.GradedVolumeKernelComponents
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Each completed degree is quotiented by its actual kernel component.
Their direct sum is the complete blowup ring as an additive group. The
kernel component equals the intersection with the full raw kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def volumeDegreeKernelAddSubgroup (n : ℕ) :
    AddSubgroup (Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n)) :=
  (volumeDegreeGroupProjection hc C n).ker

theorem volume_degree_group_projection_surjective (n : ℕ) :
    Function.Surjective (volumeDegreeGroupProjection hc C n) := by
  intro z
  obtain ⟨a,b,rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of z
  obtain ⟨x,rfl⟩ := rvVolumeBlowupProjection_surjective hc C n a
  obtain ⟨y,rfl⟩ := rvVolumeBlowupProjection_surjective hc C n b
  refine ⟨Algebra.GrothendieckAddGroup.of x-Algebra.GrothendieckAddGroup.of y,?_⟩
  rw [map_sub,volume_degree_group_projection_of,volume_degree_group_projection_of]

def volumeDegreeKernelQuotientEquiv (n : ℕ) :
    (Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n) ⧸ volumeDegreeKernelAddSubgroup hc C n) ≃+
      Algebra.GrothendieckAddGroup (RVVolumeBlowupClasses hc C n) :=
  QuotientAddGroup.quotientKerEquivOfSurjective (volumeDegreeGroupProjection hc C n)
    (volume_degree_group_projection_surjective hc C n)

def volumeGradedKernelQuotientAddEquiv :
    DirectSum ℕ (fun n => Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n) ⧸
      volumeDegreeKernelAddSubgroup hc C n) ≃+ BlowupVolumeGradedAddGroup hc C :=
  DFinsupp.mapRange.addEquiv (volumeDegreeKernelQuotientEquiv hc C)

theorem raw_volume_decomposition_homogeneous (n : ℕ)
    (x : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n)) :
    rawVolumeDecomposition hc C (rawVolumeHomogeneousAdditiveMap hc C n x)=DirectSum.of _ n x := by
  have h := raw_volume_grading_right_inverse hc C (DirectSum.of _ n x)
  rw [raw_volume_composition_of] at h
  exact h

theorem volume_degree_kernel_iff_raw_homogeneous (n : ℕ)
    (x : Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n)) :
    x ∈ volumeDegreeKernelAddSubgroup hc C n ↔
      rawVolumeHomogeneousAdditiveMap hc C n x ∈ rawVolumeKernelIdeal hc C := by
  rw [raw_volume_kernel_iff_degree_components,raw_volume_decomposition_homogeneous]
  change volumeDegreeGroupProjection hc C n x=0 ↔
    ∀ i, volumeDegreeGroupProjection hc C i
      ((DirectSum.of (fun n => Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n)) n x) i)=0
  constructor
  · intro hx i
    by_cases h : i=n
    · subst i; rw [DirectSum.of_eq_same]; exact hx
    · rw [DirectSum.of_eq_of_ne _ _ _ h,map_zero]
  · intro h
    simpa only [DirectSum.of_eq_same] using h n

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def volumeIntegrationGradedKernelQuotientAddEquiv :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFVolumeRing hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+
      DirectSum ℕ (fun n => Algebra.GrothendieckAddGroup (RVVolumeIsoClasses hc C n) ⧸
        volumeDegreeKernelAddSubgroup hc C n) := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact (volumeIntegrationRingEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).toAddEquiv.trans
    ((blowupVolumeGradedAddEquiv hc C).trans (volumeGradedKernelQuotientAddEquiv hc C).symm)
end IntegrationInACVF.Section7
