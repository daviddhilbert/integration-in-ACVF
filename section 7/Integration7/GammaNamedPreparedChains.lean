import Integration7.GammaNamedFinitePullbacks
import Integration7.PreparedSubdomainVolumeChains
import Integration7.UnaryChainVolumePreservation

/-! Gamma unary chains are closed under append and inverse. Conjugating a
Gamma unary chain by Gamma special bijections gives a Gamma unary chain with
Gamma volume data, using `gamma_volume_transport_input`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M}
variable {n a b c d : ℕ}

theorem gamma_unary_chain_append {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    {D : DefSet (M := M) S n c} (t : UnaryChain S n A B) (u : UnaryChain S n B D)
    (ht : GammaUnaryChainDefinable G t) (hu : GammaUnaryChainDefinable G u) :
    GammaUnaryChainDefinable G (t.append u) := by
  induction t with
  | nil A => exact hu
  | cons i f hf hi tail ih => exact ⟨ht.1,ih u ht.2 hu⟩

theorem gamma_unary_chain_source {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (t : UnaryChain S n A B) (ht : GammaUnaryChainDefinable G t) : GammaSetDefinable G (carrier A) := by
  cases t with
  | nil A => exact ht
  | cons i f hf hi tail =>
    have h := (gammaLogicInput G).image_graph ((gammaLogicInput G).swap_graph ht.1)
    convert h using 1
    ext p
    constructor
    · intro hp
      exact ⟨_,⟨p,hp⟩,rfl,rfl⟩
    · rintro ⟨q,u,rfl,rfl⟩
      exact u.property

theorem gamma_inverse_map_graph {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable G (pointMapGraph f)) :
    GammaGraphDefinable G (pointMapGraph (Map.inverse f hf)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).swap_graph hfΓ)
  intro q p
  constructor
  · rintro ⟨u,rfl,rfl⟩
    refine ⟨f u,rfl,?_⟩
    rw [Map.inverse_apply]
  · rintro ⟨v,rfl,rfl⟩
    refine ⟨Map.inverse f hf v,rfl,?_⟩
    rw [Map.apply_inverse]

theorem gamma_unary_chain_inverse {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (t : UnaryChain S n A B) (ht : GammaUnaryChainDefinable G t) :
    GammaUnaryChainDefinable G t.inverse := by
  induction t with
  | nil A => exact ht
  | @cons a c b A W B i f hf hi tail ih =>
    apply gamma_unary_chain_append _ _ (ih ht.2)
    exact ⟨gamma_inverse_map_graph f hf ht.1,gamma_unary_chain_source (.cons i f hf hi tail) ht⟩

/-- Gamma chain volume data from ordinary chain volume data, via Gamma transport. -/
theorem gamma_unary_chain_volume_data_of_data
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : UnaryChain (C.base : Set M) (n+1) A B) (hT : GammaUnaryChainDefinable G T)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (hω : GammaSetDefinable G (volumeDensityGraph ω).carrier)
    (hData : unaryChainVolumeData hc T ω π)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    gammaUnaryChainVolumeData hc G T ω π :=
  gamma_unary_chain_volume_data_of_composite hc C (Nat.zero_lt_succ n) T hT ω π hω
    (unary_chain_volume_data_preserves hc C T ω π hData hfinA)

namespace GammaNamed

theorem special_conjugate_volume_chain_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    {D : DefSet (M := M) (C.base : Set M) (n+1) c} {E : DefSet (M := M) (C.base : Set M) (n+1) d}
    (P : SpecialBijection A D) (R : SpecialBijection B E)
    (hP : GammaChainDefinable G P.chain) (hR : GammaChainDefinable G R.chain)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (ψ : VolumeForm (rawSpecialSet hc D)) (χ : VolumeForm (rawSpecialSet hc E))
    (hψ : GammaSetDefinable G (volumeDensityGraph ψ).carrier)
    (hPω : ∀ p, ω.value p = ψ.value (rawSpecialMap hc P.toMap p))
    (hRπ : ∀ p, π.value p = χ.value (rawSpecialMap hc R.toMap p))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (T : UnaryChain (C.base : Set M) (n+1) A B) (hTΓ : GammaUnaryChainDefinable G T)
    (hT : unaryChainVolumeData hc T ω π) :
    ∃ W : UnaryChain (C.base : Set M) (n+1) D E,
      GammaUnaryChainDefinable G W ∧ gammaUnaryChainVolumeData hc G W ψ χ := by
  let tP := specialUnaryChain (Nat.zero_lt_succ n) P.chain
  let tR := specialUnaryChain (Nat.zero_lt_succ n) R.chain
  have hVP := special_unary_chain_volume_data hc C P ω ψ hPω
  have hVR := special_unary_chain_volume_data hc C R π χ hRπ
  have hInv := unary_chain_volume_data_inverse hc C tP ω ψ hVP hfinA
  have hTail := unary_chain_volume_data_append hc C T tR ω π χ hT hVR hfinA
  have hfinD := special_target_finite_labels C ∅ P hfinA
  have hW : GammaUnaryChainDefinable G (tP.inverse.append (T.append tR)) :=
    gamma_unary_chain_append _ _ (gamma_unary_chain_inverse _ (gamma_special_unary_chain _ P.chain hP))
      (gamma_unary_chain_append _ _ hTΓ (gamma_special_unary_chain _ R.chain hR))
  refine ⟨tP.inverse.append (T.append tR),hW,?_⟩
  exact gamma_unary_chain_volume_data_of_data hc C _ hW ψ χ hψ
    (unary_chain_volume_data_append hc C tP.inverse (T.append tR) ψ ω χ hInv hTail hfinD) hfinD

end GammaNamed
end IntegrationInACVF.Section7
