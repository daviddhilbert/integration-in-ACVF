module

public import Integration7.TwoOrderProductPreparations

@[expose] public section

/-! The constructed opposite-order standard programs retain full
original-Gamma certificates for every actual preparation stage. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.TwoOrderProductPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d : ℕ}
variable {X Y : DefSet (M := M) S 2 0} {D E : DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}

theorem head_contraction_gamma (F : TwoOrderProductPreparations X Y D E r t z hz P)
    (hX : GammaSetDefinable P (carrier X))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val}) :
    GammaProgramDefinable P F.headContraction.program :=
  gamma_standardFromProgram _ _ _ _ (gamma_rv_class_product_contraction_program
    (extendBase X F.contains) (extendBase E F.contains) F.eTarget F.eSpecial hX F.headSaturated
    r z (fun j => F.contains (hz j)) hzΓ F.headPreparation)

theorem tail_contraction_gamma (F : TwoOrderProductPreparations X Y D E r t z hz P)
    (hY : GammaSetDefinable P (carrier Y))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val}) :
    GammaProgramDefinable P F.tailContraction.program :=
  gamma_swapped_rv_class_product_standard_contraction (extendBase Y F.contains) (extendBase D F.contains)
    F.dTarget F.dSpecial F.tailSaturated t z (fun j => F.contains (hz j)) F.tailPreparation hY hzΓ

end IntegrationInACVF.Section7.TwoOrderProductPreparations
