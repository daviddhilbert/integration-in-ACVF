import IntegrationSection6.VFPrefixHeadPreparations
import IntegrationSection6.ProgramEqualityTransport
import IntegrationSection6.PartialSelectedVolume

/-! A partial contraction restricts to an actual ordered contraction after
its frozen VF tuple is named. The recursive selected-volume projection is
unchanged and all Gamma graphs retain precisely the named tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n p a l : ℕ}
variable {U : DefSet (M := M) S (n+p) a} {V : DefSet (M := M) S n l}

def restrictPartialToPrefix (T : PartialContractionProgram S n (n := p) U V)
    (x : Fin n → VF (M := M)) :
    OrderedContractionProgram (S ∪ Set.range (fun j => (x j).val))
      (vfPrefixFibre (n := n) (p := p) U x) (vfPrefixFibre (n := n) (p := 0) V x) := by
  induction T with
  | zero U => exact .zero (vfPrefixFibre (p := 0) U x)
  | @step p a l U V T tail ih =>
    exact .step (vfPrefixHeadPreparation (n := n) (p := p) T x)
      (orderedCastSource ih (vfPrefixHeadPreparation_contracted (n := n) (p := p) T x).symm)

theorem restrictPartialToPrefix_selectedIndex (T : PartialContractionProgram S n (n := p) U V)
    (x : Fin n → VF (M := M)) {k : ℕ} (ρ : Fin k → Fin a) :
    orderedSelectedIndex (restrictPartialToPrefix T x) ρ = partialSelectedIndex T ρ := by
  induction T generalizing k with
  | zero U => rfl
  | @step p a l U V T tail ih =>
    change orderedSelectedIndex (orderedCastSource (restrictPartialToPrefix tail x)
      (vfPrefixHeadPreparation_contracted (n := n) (p := p) T x).symm)
      (headVolumeIndex (vfPrefixHeadPreparation (n := n) (p := p) T x) ρ) = _
    rw [orderedCastSource_selectedIndex]
    exact ih (headVolumeIndex T ρ)

theorem gamma_restrictPartialToPrefix (T : PartialContractionProgram S n (n := p) U V)
    (hT : GammaPartialProgramDefinable B T) (x : Fin n → VF (M := M)) :
    GammaProgramDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ (restrictPartialToPrefix T x) := by
  induction T with
  | zero U => exact gamma_vfPrefixFibre (p := 0) U hT x
  | @step p a l U V T tail ih =>
    exact ⟨gamma_vfPrefixHeadPreparation_map (n := n) (p := p) T hT.1 x,
      gamma_vfPrefixHeadPreparation_target (n := n) (p := p) T hT.2.1 x,
      gamma_orderedCastSource (restrictPartialToPrefix tail x)
        (vfPrefixHeadPreparation_contracted (n := n) (p := p) T x).symm (ih hT.2.2)⟩

end IntegrationInACVF.Section6
