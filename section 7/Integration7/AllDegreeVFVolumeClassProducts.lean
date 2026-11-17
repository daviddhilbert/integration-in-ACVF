module

public import Integration7.PositiveVolumeIntegrationProducts
public import Integration7.ZeroFactorVFVolumeClassProducts
public import Integration7.ZeroVFVolumeClassProducts
public import Integration7.ZeroCoefficientProductSymmetry
public import Integration7.VolumeIntegrationEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Graded multiplication of actual VF volume classes. Its positive,
ordinary-zero and mixed coefficient cases agree with the actual Cartesian
constructions; the zero coefficient is presented by its ordinary full lift. -/
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

def volumeIntegrationEquivAsEquiv (n : ℕ) :
    VFVolumeIsoClasses hc C n ≃ RVVolumeBlowupClasses hc C n := by
  letI := vfVolumeIsoClassesAdd hc C n
  letI := rvVolumeBlowupClassesAddCommMonoid hc C n
  exact (volumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).toEquiv

def vfVolumeClassesProduct (n m : ℕ)
    (a : VFVolumeIsoClasses hc C n) (b : VFVolumeIsoClasses hc C m) : VFVolumeIsoClasses hc C (n+m) :=
  (volumeIntegrationEquivAsEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+m)).symm
    (rvVolumeBlowupClassesProduct hc C n m
      (volumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n a)
      (volumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 m b))

theorem vf_volume_integration_product (n m : ℕ)
    (a : VFVolumeIsoClasses hc C n) (b : VFVolumeIsoClasses hc C m) :
    volumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+m)
        (vfVolumeClassesProduct hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n m a b) =
      rvVolumeBlowupClassesProduct hc C n m
        (volumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n a)
        (volumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 m b) :=
  (volumeIntegrationEquivAsEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+m)).apply_symm_apply _

theorem vf_volume_classes_product_positive {n m : ℕ}
    (a : PositiveVFVolumeIsoClasses hc C n) (b : PositiveVFVolumeIsoClasses hc C m) :
    vfVolumeClassesProduct hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) (m+1) a b =
      positiveVFVolumeClassesProduct hc C a b := by
  apply (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).injective
  exact (vf_volume_integration_product hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) (m+1) a b).trans
    (positive_volume_integration_product hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a b).symm

theorem vf_volume_classes_product_zero
    (a b : ZeroVFVolumeIsoClasses C) :
    vfVolumeClassesProduct hc C Ξ hΞ hGenerated hNames γ hγ hγ1 0 0 a b = zeroVFVolumeClassesProduct C a b := by
  apply (zeroVolumeIntegrationEquiv hc C).injective
  exact (vf_volume_integration_product hc C Ξ hΞ hGenerated hNames γ hγ hγ1 0 0 a b).trans
    (zero_volume_integration_product hc C a b).symm

theorem vf_volume_classes_product_positive_zero {n : ℕ}
    (a : PositiveVFVolumeIsoClasses hc C n) (b : ZeroVFVolumeIsoClasses C) :
    vfVolumeClassesProduct hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) 0 a b =
      positiveVFZeroCoefficientProduct hc C a (zeroVolumeIntegrationEquiv hc C b) := by
  apply (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).injective
  exact (vf_volume_integration_product hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+1) 0 a b).trans
    (positive_volume_integration_zero_coefficient_product hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a
      (zeroVolumeIntegrationEquiv hc C b)).symm

theorem dependent_degree_map_heq {A B : ℕ → Type} (F : ∀ n, A n → B n)
    {n m : ℕ} (h : n=m) {a : A n} {b : A m} (hab : HEq a b) : HEq (F n a) (F m b) := by
  cases h
  cases hab
  rfl

theorem vf_volume_classes_product_zero_positive {n : ℕ}
    (a : ZeroVFVolumeIsoClasses C) (b : PositiveVFVolumeIsoClasses hc C n) :
    HEq (vfVolumeClassesProduct hc C Ξ hΞ hGenerated hNames γ hγ hγ1 0 (n+1) a b)
      (positiveVFZeroCoefficientProduct hc C b (zeroVolumeIntegrationEquiv hc C a)) := by
  have h := rv_volume_blowup_classes_zero_product_swap hc C
    (zeroVolumeIntegrationEquiv hc C a)
    (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 b)
  have he := dependent_degree_map_heq
    (fun k => (volumeIntegrationEquivAsEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 k).symm)
    (Nat.zero_add (n+1)) h
  exact he.trans (heq_of_eq (vf_volume_classes_product_positive_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1 b a))

end IntegrationInACVF.Section7
