module

public import Integration7.AllDegreeVolumeLiftKernel

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The canonical homogeneous additive integration equivalence of
Proposition 7.9, with ordinary degree zero and all positive degrees. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def volumeIntegrationEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n : ℕ) :
    letI := vfVolumeIsoClassesAdd hc C n
    letI := rvVolumeBlowupClassesAddCommMonoid hc C n
    VFVolumeIsoClasses hc C n ≃+ RVVolumeBlowupClasses hc C n := by
  cases n with
  | zero => exact zeroVolumeIntegrationAddEquiv hc C
  | succ k => exact positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1

theorem proposition_7_9
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (n : ℕ) (A : VFVolumeObject (M := M) (C.base : Set M) n)
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    volumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (vfVolumeIsoClass hc C A) =
      rvVolumeBlowupClass hc C U ↔
      vfVolumeIsoClass hc C A = vfVolumeIsoClass hc C (rvVolumeLiftOfDegree (C.base : Set M) n U) := by
  cases n with
  | zero => exact proposition_7_9_zero hc C A U
  | succ k => exact proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 A U

end IntegrationInACVF.Section7
