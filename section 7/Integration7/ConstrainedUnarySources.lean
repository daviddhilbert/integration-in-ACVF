import Integration7.RVLabelConstraintSpecialPreparations
import Integration7.GammaRVLabelCuts

/-! Actual unary sources with any pure-RV label constraint. This
includes coefficient products with functional density and selection
labels, over the same real parameter context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b l : ℕ}

def constrainedUnarySource (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) 1 a)
    (Q : DefSet (M := M) (C.base : Set M) 0 l) (ρ : Fin a → Fin l) :
    DefSet (M := M) (C.base : Set M) 1 l := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let D : DefSet (M := M) (C.base : Set M) 1 l := PresentedSet.mk {p : Point (M := M) 1 l | retainVFLabels ρ p ∈ carrier A}
    (retain_vf_labels_preimage_definable ρ (carrier A) (setDefinable A))
  exact rvLabelCut D ((gammaLogicInput B).real_set _ (setDefinable D)) id (carrier Q)
    ((gammaLogicInput B).real_set _ (setDefinable Q)) hNames

theorem constrained_unary_source_mem (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) 1 a)
    (Q : DefSet (M := M) (C.base : Set M) 0 l) (ρ : Fin a → Fin l) (p : Point (M := M) 1 l) :
    p ∈ carrier (constrainedUnarySource C Ξ hNames A Q ρ) ↔
      retainVFLabels ρ p ∈ carrier A ∧ (Fin.elim0,p.2) ∈ carrier Q := by
  change (_ ∧ (Fin.elim0,p.2 ∘ id) ∈ carrier Q) ↔ _
  rw [Function.comp_id]
  rfl

theorem constrained_unary_special_preparation_exists (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    {A : DefSet (M := M) (C.base : Set M) 1 a} {B : DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (hB : IsRVPullback (carrier B)) (Q : DefSet (M := M) (C.base : Set M) 0 l) (ρ : Fin a → Fin l) :
    Nonempty (RVLabelConstraintSpecialPreparation T (constrainedUnarySource C Ξ hNames A Q ρ) Q ρ
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let H := constrainedUnarySource C Ξ hNames A Q ρ
  exact gamma_rv_label_constraint_special_preparation_exists T hT hB H
    ((gammaLogicInput G).real_set _ (setDefinable H)) Q ρ (constrained_unary_source_mem C Ξ hNames A Q ρ)
end IntegrationInACVF.Section7
