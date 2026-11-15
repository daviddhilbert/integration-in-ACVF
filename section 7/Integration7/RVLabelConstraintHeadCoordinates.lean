import Integration7.RVLabelConstraintHeadProjections

/-! Literal coordinate identities for the head key of a shared-label
special preparation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.RVLabelConstraintSpecialPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {ρ : Fin a → Fin l} {T : SpecialBijection A B}
variable {H : DefSet (M := M) S 1 l} {Q : DefSet (M := M) S 0 l}

theorem head_projection_zero (L : RVLabelConstraintSpecialPreparation T H Q ρ P) :
    L.headProjection (0 : Fin (1+b)) = (0 : Fin (1+L.arity)) := by
  change L.headProjection (Fin.castAdd b (0 : Fin 1)) = _
  rw [headProjection,Fin.append_left]
  rfl

theorem head_parameter_value (L : RVLabelConstraintSpecialPreparation T H Q ρ P)
    (p : H) (j : Fin l) :
    (headKey (L.special.toMap p).val).2 (L.headParameters j) = p.val.2 j := by
  simpa only [headKey,headParameters,Fin.append_right,Function.comp_apply]
    using congrFun (L.parameters p) j

end IntegrationInACVF.Section7.RVLabelConstraintSpecialPreparation
