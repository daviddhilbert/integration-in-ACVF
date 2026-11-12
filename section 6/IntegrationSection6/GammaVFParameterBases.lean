import IntegrationSection6.GammaPreparedRowAgreements

/-! The actual VF parameter set in raw sorted coordinates keeps its
complete original Gamma certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ}

theorem gamma_raw_vf_parameter_base {A : Set (Point (M := M) p 0)} (hA : GammaSetDefinable B A) :
    DefinableOverBase B (fun _ : Fin p => .vf) (rawVFParameter '' A) := by
  change DefinableOverBase B (fun _ : Fin p => .vf) ((fun a j => (a.1 j).val) '' A)
  simpa only [GammaSetDefinable,gammaPointSort_vf_zero,gammaPointCode_vf_zero,Nat.add_zero,
    rawVFParameter] using hA

end IntegrationInACVF.Section6
