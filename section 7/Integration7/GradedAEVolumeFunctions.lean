import Integration7.AEOrdinaryVolumeModules
import Integration7.AERVVolumeOrdinaryCoefficientModules
import Mathlib.Algebra.DirectSum.Module

/-! The full finitely graded AE function space includes ordinary
degree zero and every positive homogeneous coefficient degree. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def AEVolumeFunctionComponent (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) : ℕ → Type
  | 0 => AEOrdinaryRVVolumeFunction hc C n
  | k+1 => AERVVolumeFunction hc C n k

instance aeVolumeFunctionComponentAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n j : ℕ) :
    AddCommMonoid (AEVolumeFunctionComponent hc C n j) := by
  cases j with
  | zero => exact aeOrdinaryRVVolumeFunctionAddCommMonoid hc C n
  | succ k => exact aeRVVolumeFunctionAddCommMonoid hc C n k

instance aeVolumeFunctionComponentOrdinaryModule
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n j : ℕ) :
    Module (RVVolumeBlowupClasses hc C 0) (AEVolumeFunctionComponent hc C n j) := by
  cases j with
  | zero => exact aeOrdinaryRVVolumeFunctionModule hc C n
  | succ k => exact aeRVVolumeFunctionOrdinaryModule hc C n k

abbrev GradedAEVolumeFunction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :=
  DirectSum ℕ (AEVolumeFunctionComponent hc C n)

end IntegrationInACVF.Section7
