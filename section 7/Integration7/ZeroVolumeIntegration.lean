module

public import Integration7.ZeroVFVolumeClasses
public import Mathlib.Algebra.Group.TransferInstance

@[expose] public section

/-! The canonical degree-zero additive coefficient structure, with the
ordinary lift as its inverse, retaining the actual VF[0] classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev zeroVFVolumeIsoClassesAdd (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Add (ZeroVFVolumeIsoClasses C) := by
  letI := rvVolumeBlowupClassesAddCommMonoid hc C 0
  exact (zeroVolumeIntegrationEquiv hc C).add

abbrev zeroVFVolumeIsoClassesZero (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Zero (ZeroVFVolumeIsoClasses C) := by
  letI := rvVolumeBlowupClassesAddCommMonoid hc C 0
  exact (zeroVolumeIntegrationEquiv hc C).zero

abbrev zeroVFVolumeAddCommMonoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    AddCommMonoid (ZeroVFVolumeIsoClasses C) := by
  letI := rvVolumeBlowupClassesAddCommMonoid hc C 0
  exact (zeroVolumeIntegrationEquiv hc C).addCommMonoid

def zeroVolumeIntegrationAddEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    letI := rvVolumeBlowupClassesAddCommMonoid hc C 0
    letI := zeroVFVolumeIsoClassesAdd hc C
    ZeroVFVolumeIsoClasses C ≃+ RVVolumeBlowupClasses hc C 0 := by
  letI := rvVolumeBlowupClassesAddCommMonoid hc C 0
  letI := zeroVFVolumeIsoClassesAdd hc C
  exact ⟨zeroVolumeIntegrationEquiv hc C,fun a b => (zeroVolumeIntegrationEquiv hc C).apply_symm_apply _⟩

theorem proposition_7_9_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : VFVolumeObject (M := M) (C.base : Set M) 0) (U : RVVolumeObject (M := M) (C.base : Set M) 0) :
    zeroVolumeIntegrationEquiv hc C (zeroVFVolumeIsoClass C A) = rvVolumeBlowupClass hc C (n := 0) U ↔
      zeroVFVolumeIsoClass C A = zeroVFVolumeIsoClass C (rvLiftFiniteObject (rawRVSpace (M := M) 1) U) :=
  (zeroVolumeIntegrationEquiv hc C).eq_symm_apply.symm

end IntegrationInACVF.Section7
