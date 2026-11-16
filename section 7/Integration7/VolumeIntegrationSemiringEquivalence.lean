module

public import Integration7.AllDegreeVFVolumeClassProducts
public import Integration7.GradedAdditiveEquivalenceSemiring
public import Integration7.AllDegreeVolumeBlowupSemiring

@[expose] public section

/-! Proposition7.10: the graded integration semiring equivalence.
Multiplication on generators is the actual positive Cartesian product,
the ordinary degree-zero product, or the checked zero-coefficient action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def volumeIntegrationEquivWithMonoids (n : ℕ) :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFVolumeIsoClasses hc C n ≃+ RVVolumeBlowupClasses hc C n := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  cases n with
  | zero => exact zeroVolumeIntegrationAddEquiv hc C
  | succ n => exact positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1

abbrev VFVolumeSemiring : Type := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact DirectSum ℕ (VFVolumeIsoClasses hc C)

def vfVolumeGradedSemiringStructure :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    DirectSum.GSemiring (VFVolumeIsoClasses hc C) := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact gradedAddEquivGSemiring (volumeIntegrationEquivWithMonoids hc C Ξ hΞ hGenerated hNames γ hγ hγ1)

def volumeGradedIntegrationEquiv :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFVolumeSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+* RVVolumeBlowupSemiring hc C := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact gradedAddEquivSemiringEquiv (volumeIntegrationEquivWithMonoids hc C Ξ hΞ hGenerated hNames γ hγ hγ1)

theorem volume_graded_integration_of (n : ℕ) (a : VFVolumeIsoClasses hc C n) :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    volumeGradedIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (DirectSum.of (VFVolumeIsoClasses hc C) n a) =
      DirectSum.of (RVVolumeBlowupClasses hc C) n
        (volumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n a) := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  change DirectSum.map (fun i => (volumeIntegrationEquivWithMonoids hc C Ξ hΞ hGenerated hNames γ hγ hγ1 i).toAddMonoidHom)
    (DirectSum.of (VFVolumeIsoClasses hc C) n a) = _
  rw [DirectSum.map_of]
  cases n <;> rfl

theorem vf_volume_semiring_of_mul_of {n m : ℕ}
    (a : VFVolumeIsoClasses hc C n) (b : VFVolumeIsoClasses hc C m) :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    DirectSum.of (VFVolumeIsoClasses hc C) n a * DirectSum.of (VFVolumeIsoClasses hc C) m b =
      DirectSum.of (VFVolumeIsoClasses hc C) (n+m)
        (vfVolumeClassesProduct hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n m a b) := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  rw [DirectSum.of_mul_of]
  congr 1
  cases n <;> cases m <;> rfl

def proposition_7_10 :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    VFVolumeSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ≃+* RVVolumeBlowupSemiring hc C :=
  volumeGradedIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1

theorem volume_graded_integration_lift (n : ℕ)
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    volumeGradedIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (DirectSum.of (VFVolumeIsoClasses hc C) n
          (vfVolumeIsoClass hc C (rvVolumeLiftOfDegree (C.base : Set M) n U))) =
      DirectSum.of (RVVolumeBlowupClasses hc C) n (rvVolumeBlowupClass hc C U) := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  have h := (proposition_7_9 hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (rvVolumeLiftOfDegree (C.base : Set M) n U) U).mpr rfl
  exact (volume_graded_integration_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n _).trans
    (congrArg (DirectSum.of (RVVolumeBlowupClasses hc C) n) h)

theorem theorem_7_10
    (a : VFVolumeSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1) (n : ℕ)
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    volumeGradedIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a =
        DirectSum.of (RVVolumeBlowupClasses hc C) n (rvVolumeBlowupClass hc C U) ↔
      a = DirectSum.of (VFVolumeIsoClasses hc C) n
        (vfVolumeIsoClass hc C (rvVolumeLiftOfDegree (C.base : Set M) n U)) := by
  letI := vfVolumeIsoClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfVolumeGradedSemiringStructure hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  rw [← volume_graded_integration_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n U]
  exact (volumeGradedIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).injective.eq_iff

end IntegrationInACVF.Section7
