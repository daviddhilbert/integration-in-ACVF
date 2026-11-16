import Integration7.HKVFClassCartesianProducts
import Integration7.HKZeroVFCoproductClasses

/-! Geometric identification of the transported VF graded operations.
The product cases are actual Cartesian constructions, and measured zero
addition is the concrete coproduct with its two forms. -/
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

theorem class_integration_equiv_geometric (n : ℕ) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (classIntegrationAddEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).toEquiv =
      volumeIntegrationEquivAsEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  cases n <;> rfl

theorem vf_graded_product_geometric {n m : ℕ} (a : VFVolumeClasses hc C n) (b : VFVolumeClasses hc C m) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    GradedMonoid.GMul.mul a b = vfVolumeClassesProduct hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n m a b := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  change ((classIntegrationAddEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+m)).toEquiv).symm
    (rvVolumeBlowupClassesProduct hc C n m
      ((classIntegrationAddEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).toEquiv a)
      ((classIntegrationAddEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 m).toEquiv b)) = _
  simp only [class_integration_equiv_geometric]
  rfl

theorem vf_graded_product_positive {n m : ℕ}
    (a : PositiveVFVolumeIsoClasses hc C n) (b : PositiveVFVolumeIsoClasses hc C m) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    GradedMonoid.GMul.mul (A := VFVolumeClasses hc C) (i := n+1) (j := m+1) a b =
      positiveVFVolumeClassesProduct hc C a b := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact
    (vf_graded_product_geometric hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n := n+1) (m := m+1) a b).trans
    (vf_volume_classes_product_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a b)

theorem vf_graded_product_zero
    (a b : ZeroVFVolumeClasses (M := M) (C.base : Set M)) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    GradedMonoid.GMul.mul (A := VFVolumeClasses hc C) (i := 0) (j := 0) a b =
      zeroVFClassesProduct (C.base : Set M) a b := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact
    (vf_graded_product_geometric hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n := 0) (m := 0) a b).trans
    (vf_volume_classes_product_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a b)

theorem vf_graded_product_positive_zero {n : ℕ}
    (a : PositiveVFVolumeIsoClasses hc C n) (b : ZeroVFVolumeClasses (M := M) (C.base : Set M)) :
    letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    GradedMonoid.GMul.mul (A := VFVolumeClasses hc C) (i := n+1) (j := 0) a b =
      positiveVFZeroCoefficientProduct hc C a (zeroVolumeIntegrationEquiv hc C b) := by
  letI := vfClassesAddCommMonoid hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  letI := vfClassGradedSemiring hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact
    (vf_graded_product_geometric hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n := n+1) (m := 0) a b).trans
    (vf_volume_classes_product_positive_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a b)

end IntegrationInACVF.Section7.HK
