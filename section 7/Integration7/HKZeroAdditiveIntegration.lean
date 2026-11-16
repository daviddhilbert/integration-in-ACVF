module

public import Integration7.HKZeroVolumeIntegration
public import Integration7.HKVolumeClassCoherence
public import Mathlib.Algebra.Group.TransferInstance

@[expose] public section

/-! The weighted zero lift transports the actual coproduct addition on
RV classes to zero VF classes. Agreement with concrete VF coproducts is
checked separately from this algebraic transport. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev zeroVFAddCommMonoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    AddCommMonoid (ZeroVFVolumeClasses (M := M) (C.base : Set M)) := by
  letI : AddCommMonoid (ZeroRVVolumeClasses (M := M) (C.base : Set M)) :=
    rvVolumeBlowupClassesAddCommMonoid hc C 0
  exact (zeroVolumeIntegrationEquiv hc C).addCommMonoid

def zeroAdditiveIntegrationEquiv (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    letI : AddCommMonoid (ZeroRVVolumeClasses (M := M) (C.base : Set M)) :=
      rvVolumeBlowupClassesAddCommMonoid hc C 0
    letI := zeroVFAddCommMonoid hc C
    ZeroVFVolumeClasses (M := M) (C.base : Set M) ≃+ ZeroRVVolumeClasses (M := M) (C.base : Set M) := by
  letI : AddCommMonoid (ZeroRVVolumeClasses (M := M) (C.base : Set M)) :=
    rvVolumeBlowupClassesAddCommMonoid hc C 0
  letI := zeroVFAddCommMonoid hc C
  exact ⟨zeroVolumeIntegrationEquiv hc C,fun a b => (zeroVolumeIntegrationEquiv hc C).apply_symm_apply _⟩

end IntegrationInACVF.Section7.HK
