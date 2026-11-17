module

public import Integration7.HKZeroAdditiveIntegration
public import Integration7.HKPrincipalVolumeKernel
public import Integration7.GradedAdditiveEquivalenceSemiring
public import Integration7.PositiveVFVolumeAdditiveStructure

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Additive and ring assembly of the corrected degreewise classification.
Positive-degree additive structures are the existing actual coproduct
structures. Zero uses the weighted lift. Concrete Cartesian-product
agreement is a separate geometric check, not a premise of these constructions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def vfClassesAddCommMonoid : (n : ℕ) → AddCommMonoid (VFVolumeClasses hc C n)
  | 0 => zeroVFAddCommMonoid hc C
  | k+1 => positiveVFVolumeAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := k)

def classIntegrationAddEquiv (n : ℕ) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFVolumeClasses hc C n ≃+ RVBlowupClasses hc C n := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  cases n with
  | zero => exact zeroAdditiveIntegrationEquiv hc C
  | succ k => exact positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1

abbrev VFClassSemiring : Type := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact DirectSum ℕ (VFVolumeClasses hc C)

def vfClassGradedSemiring :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    DirectSum.GSemiring (VFVolumeClasses hc C) := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact gradedAddEquivGSemiring (classIntegrationAddEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1)

def gradedClassIntegrationEquiv :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFClassSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+* RVVolumeBlowupSemiring hc C := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact gradedAddEquivSemiringEquiv (classIntegrationAddEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1)

abbrev VFClassRing : Type := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact SemiringGroupification (VFClassSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1)

def classIntegrationRingEquiv :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFClassRing hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+* RVVolumeBlowupRing hc C := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact semiringGroupificationEquiv (gradedClassIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1)

def classIntegrationPrincipalQuotientEquiv :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFClassRing hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+*
      (RawRVVolumeRing hc C ⧸ basicVolumeRelationIdeal hc C) := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact (classIntegrationRingEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).trans
    (principalVolumeKernelQuotientEquiv hc C).symm

end IntegrationInACVF.Section7.HK
