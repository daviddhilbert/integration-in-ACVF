import IntegrationSection5.StandardContraction
import IntegrationSection6.ProgramEqualityTransport
import IntegrationSection6.GammaPermutedFibrePresentations

/-! An actual ordered program on an equal permutation presentation gives
an actual standard contraction, with unchanged selected volume. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a l : ℕ}
variable {U X : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}

theorem vfPermutationImage_id_eq (U : DefSet (M := M) S n a) :
    vfPermutationImage U (Equiv.refl _) = U := by
  apply defSet_eq_of_carrier_eq
  ext q
  simpa using vfPermutationImage_row U (Equiv.refl _) q.1 q.2

def standardFromProgram (U : DefSet (M := M) S n a) (σ : Equiv.Perm (Fin n))
    (T : OrderedContractionProgram S X V) (hX : X = vfPermutationImage U σ) : StandardContraction U σ where
  arity := l
  target := V
  program := orderedCastSource T hX

theorem standardFromProgram_selectedIndex (U : DefSet (M := M) S n a) (σ : Equiv.Perm (Fin n))
    (T : OrderedContractionProgram S X V) (hX : X = vfPermutationImage U σ)
    {k : ℕ} (ρ : Fin k → Fin a) :
    orderedSelectedIndex (standardFromProgram U σ T hX).program ρ = orderedSelectedIndex T ρ :=
  orderedCastSource_selectedIndex T hX ρ

theorem gamma_standardFromProgram (U : DefSet (M := M) S n a) (σ : Equiv.Perm (Fin n))
    (T : OrderedContractionProgram S X V) (hX : X = vfPermutationImage U σ)
    (hT : GammaProgramDefinable B T) : GammaProgramDefinable B (standardFromProgram U σ T hX).program :=
  gamma_orderedCastSource T hX hT

end IntegrationInACVF.Section6
