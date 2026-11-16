module

public import Integration7.HKAEZeroModules
public import Integration7.HKAERVWeightedZeroModules
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section

/-! The full finitely graded AE function space includes weighted
degree zero and every positive homogeneous coefficient degree. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def AEVolumeFunctionComponent (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) : ℕ → Type
  | 0 => AEZeroVolumeFunction hc C n
  | k+1 => AERVVolumeFunction hc C n k

instance aeVolumeFunctionComponentAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n j : ℕ) :
    AddCommMonoid (AEVolumeFunctionComponent hc C n j) := by
  cases j with
  | zero => exact aeZeroVolumeFunctionAddCommMonoid hc C n
  | succ k => exact aeRVVolumeFunctionAddCommMonoid hc C n k

instance aeVolumeFunctionComponentWeightedZeroModule
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n j : ℕ) :
    Module (RVBlowupClasses hc C 0) (AEVolumeFunctionComponent hc C n j) := by
  cases j with
  | zero => exact aeZeroVolumeFunctionModule hc C n
  | succ k => exact aeRVVolumeFunctionWeightedZeroModule hc C n k

abbrev GradedAEVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :=
  DirectSum ℕ (AEVolumeFunctionComponent hc C n)

end IntegrationInACVF.Section7.HK
