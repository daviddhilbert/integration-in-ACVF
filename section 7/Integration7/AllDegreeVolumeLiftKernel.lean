module

public import Integration7.AllDegreeVFVolumeClasses

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Proposition 7.8 including ordinary degree zero. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem proposition_7_8_all_degrees
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (n : ℕ) (U V : RVVolumeObject (M := M) (C.base : Set M) n) :
    Nonempty (VFVolumeIsoInDegree (C.base : Set M) n (rvVolumeLiftOfDegree (C.base : Set M) n U)
      (rvVolumeLiftOfDegree (C.base : Set M) n V)) ↔ MuIsp (C.base : Set M) n U V := by
  cases n with
  | zero => exact ordinary_zero_lift_iso_iff U V
  | succ k => exact proposition_7_8 hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U V

end IntegrationInACVF.Section7
