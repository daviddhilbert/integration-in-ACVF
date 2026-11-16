module

public import Integration7.HKVFClassSemiringGeometry

@[expose] public section

/-! Corrected numbered class and ring statements, with geometric products
and coproducts checked and the actual principal kernel discharged. -/
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

theorem class_integration_lift (n : ℕ) (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    classIntegrationAddEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (vfClass hc C n (volumeLift (C.base : Set M) n U)) = rvVolumeBlowupClass hc C U := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  cases n with
  | zero => exact zero_integration_lift hc C U
  | succ k => exact (proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (rvVolumeLift U) U).mpr rfl

theorem volume_graded_integration_of (n : ℕ) (a : VFVolumeClasses hc C n) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    gradedClassIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (DirectSum.of (VFVolumeClasses hc C) n a) =
      DirectSum.of (RVBlowupClasses hc C) n
        (classIntegrationAddEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n a) := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  change DirectSum.map (fun i => (classIntegrationAddEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 i).toAddMonoidHom)
    (DirectSum.of (VFVolumeClasses hc C) n a) = _
  rw [DirectSum.map_of]
  rfl

theorem volume_graded_integration_lift (n : ℕ)
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    gradedClassIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (DirectSum.of (VFVolumeClasses hc C) n
          (vfClass hc C n (volumeLift (C.base : Set M) n U))) =
      DirectSum.of (RVBlowupClasses hc C) n (rvVolumeBlowupClass hc C U) := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  have h := class_integration_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n U
  exact (volume_graded_integration_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n _).trans
    (congrArg (DirectSum.of (RVBlowupClasses hc C) n) h)

theorem theorem_7_10
    (a : VFClassSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1) (n : ℕ)
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    gradedClassIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a =
        DirectSum.of (RVBlowupClasses hc C) n (rvVolumeBlowupClass hc C U) ↔
      a = DirectSum.of (VFVolumeClasses hc C) n
        (vfClass hc C n (volumeLift (C.base : Set M) n U)) := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  rw [← volume_graded_integration_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n U]
  exact (gradedClassIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).injective.eq_iff

def theorem_7_13 :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFClassRing hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+*
      (RawRVVolumeRing hc C ⧸ basicVolumeRelationIdeal hc C) :=
  classIntegrationPrincipalQuotientEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1

end IntegrationInACVF.Section7.HK
