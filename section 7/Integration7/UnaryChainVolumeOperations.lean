module

public import Integration7.UnaryChainInverses
public import Integration7.UnaryChainVolumePreservation
public import Integration7.RawVFVolumeComposition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Inversion and composition of actual unary volume factorizations.
The composite volume equation is proved before its intermediate
nonzero definable densities are constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (VF RV carrier gammaLogicInput)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b c : ℕ}

theorem unary_chain_volume_data_inverse
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : UnaryChain (C.base : Set M) (n+1) A B)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (hData : unaryChainVolumeData hc T ω π)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    unaryChainVolumeData hc T.inverse π ω := by
  apply unary_chain_volume_data_of_composite hc C (Nat.zero_lt_succ n)
  rw [UnaryChain.inverse_to_map]
  exact preservesVFVolume_inverse hc C (Nat.zero_lt_succ n) ω π (rawSpecialMap hc T.toMap) T.bijective
    (unary_chain_volume_data_preserves hc C T ω π hData hfinA)

theorem unary_chain_volume_data_append
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) c}
    (T : UnaryChain (C.base : Set M) (n+1) A B) (R : UnaryChain (C.base : Set M) (n+1) B D)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (η : VolumeForm (rawSpecialSet hc D))
    (hT : unaryChainVolumeData hc T ω π) (hR : unaryChainVolumeData hc R π η)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    unaryChainVolumeData hc (T.append R) ω η := by
  let G : Base (M := M) := ⟨(C.base : Set M),∅⟩
  have hfinB := finite_rv_fibres_of_gamma_bijection (B := G) C.uncountable.le C.saturated C.small
    T.toMap T.bijective ((gammaLogicInput G).real_map_graph T.toMap) hfinA
  apply unary_chain_volume_data_of_composite hc C (Nat.zero_lt_succ n)
  rw [UnaryChain.append_toMap]
  exact preservesVFVolume_comp hc C (Nat.zero_lt_succ n) ω π η (rawSpecialMap hc T.toMap)
    (rawSpecialMap hc R.toMap) T.bijective.injective
    (unary_chain_volume_data_preserves hc C T ω π hT hfinA)
    (unary_chain_volume_data_preserves hc C R π η hR hfinB)

end IntegrationInACVF.Section7
