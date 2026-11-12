import IntegrationSection6.ContractionProgramExtensions

/-! Extending an internal presentation leaves every contraction-volume
selector unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S R : Set M}

theorem extendContractionProgram_volumeIndex {n a l : ℕ}
    {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S U V) (hSR : S ⊆ R) :
    (extendContractionProgram T hSR).volumeIndex = T.volumeIndex := by
  funext i
  induction T with
  | zero U => exact Fin.elim0 i
  | step T tail ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih i

theorem extendStandardContraction_volumeIndex {n a : ℕ} {U : DefSet (M := M) S n a}
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction U σ) (hSR : S ⊆ R) :
    (extendStandardContraction C hSR).volumeIndex = C.volumeIndex := by
  funext i
  exact congrFun (extendContractionProgram_volumeIndex C.program hSR) (σ.symm i)

theorem gamma_extendStandardContraction {B : Base (M := M)} {n a : ℕ} {U : DefSet (M := M) S n a}
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction U σ) (hSR : S ⊆ R)
    (hC : GammaProgramDefinable B C.program) :
    GammaProgramDefinable B (extendStandardContraction C hSR).program :=
  gamma_extendContractionProgram C.program hSR hC

end IntegrationInACVF.Section6
