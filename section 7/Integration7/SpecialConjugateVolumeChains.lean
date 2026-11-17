module

public import Integration7.SpecialPullbackVolumeObjects
public import Integration7.UnaryChainVolumeOperations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Conjugate a genuine volume factor chain by special bijections,
with any pointwise compatible source and target volume forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b c d : ℕ}

theorem special_conjugate_volume_chain_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    {D : DefSet (M := M) (C.base : Set M) (n+1) c} {E : DefSet (M := M) (C.base : Set M) (n+1) d}
    (P : SpecialBijection A D) (R : SpecialBijection B E)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (ψ : VolumeForm (rawSpecialSet hc D)) (χ : VolumeForm (rawSpecialSet hc E))
    (hP : ∀ p, ω.value p = ψ.value (rawSpecialMap hc P.toMap p))
    (hR : ∀ p, π.value p = χ.value (rawSpecialMap hc R.toMap p))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (T : UnaryChain (C.base : Set M) (n+1) A B) (hT : unaryChainVolumeData hc T ω π) :
    ∃ W : UnaryChain (C.base : Set M) (n+1) D E, unaryChainVolumeData hc W ψ χ := by
  let tP := specialUnaryChain (Nat.zero_lt_succ n) P.chain
  let tR := specialUnaryChain (Nat.zero_lt_succ n) R.chain
  have hVP := special_unary_chain_volume_data hc C P ω ψ hP
  have hVR := special_unary_chain_volume_data hc C R π χ hR
  have hInv := unary_chain_volume_data_inverse hc C tP ω ψ hVP hfinA
  have hTail := unary_chain_volume_data_append hc C T tR ω π χ hT hVR hfinA
  refine ⟨tP.inverse.append (T.append tR),?_⟩
  exact unary_chain_volume_data_append hc C tP.inverse (T.append tR) ψ ω χ hInv hTail
    (special_target_finite_labels C ∅ P hfinA)

end IntegrationInACVF.Section7
