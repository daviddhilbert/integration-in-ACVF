import Integration7.GammaNamedUnaryChains
import Integration7.VFVolumeCancellation
import Integration7.GammaNamedJacobianTransport

/-! The Gamma volume-transport input and Gamma chain volume data.

`GammaVolumeTransportInput hc G S` says: along an actual mixed bijection in
positive VF dimension with a Gamma graph over `G`, every density with a Gamma
density graph is transported to a density with a Gamma density graph that it
preserves. `gamma_volume_transport_input` proves it over `C.base` for every
Gamma base `G`, from the provider's Gamma total mixed Jacobian
(`gamma_exists_totalMixedJacobianMap`). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (VF RV carrier gammaLogicInput GammaSetDefinable GammaGraphDefinable
  setDefinable pointMapGraph)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M}

/-- Gamma transport of densities along Gamma mixed bijections. -/
def GammaVolumeTransportInput (hc : CanonicalStructure.IsCanonical (M := M))
    (G : Base (M := M)) (S : Set M) : Prop :=
  ∀ {n a b : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S n b}
    (f : SpecialTransformations.Section5.Map A B), 0 < n → Function.Bijective f →
    GammaGraphDefinable G (pointMapGraph f) →
    ∀ ω : VolumeForm (rawSpecialSet hc A), GammaSetDefinable G (volumeDensityGraph ω).carrier →
    ∃ η : VolumeForm (rawSpecialSet hc B), GammaSetDefinable G (volumeDensityGraph η).carrier ∧
      PreservesVFVolume ω η (rawSpecialMap hc f)

/-- The Gamma transport input holds over the real base of any base context. -/
theorem gamma_volume_transport_input (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) : GammaVolumeTransportInput hc G (C.base : Set M) := by
  intro n a b A B f hn hf hfΓ ω hω
  have hF := vf_mixed_map_graph_raw_special hc f hfΓ
  obtain ⟨j,hjΓ,hj⟩ := gamma_exists_totalMixedJacobianMap hc hn (rawSpecialMap hc f) hF
  refine ⟨jacobianTransportedForm (rawSpecialMap hc f) hf j ω,?_,
    preserves_jacobian_transported_form hc C hn (rawSpecialMap hc f) hf j hj ω⟩
  exact density_graph_of_volume_form_graph _
    (gamma_jacobian_transported_form_graph hc (rawSpecialMap hc f) hf hF j hjΓ ω
      (volume_form_graph_of_density_graph ω hω))

theorem gamma_unary_chain_volume_data_of_composite
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ} (hn : 0 < n)
    {a b : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n b}
    (T : UnaryChain (C.base : Set M) n A B) (hT : GammaUnaryChainDefinable G T) :
    ∀ (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B)),
      GammaSetDefinable G (volumeDensityGraph ω).carrier →
      PreservesVFVolume ω π (rawSpecialMap hc T.toMap) → gammaUnaryChainVolumeData hc G T ω π := by
  induction T with
  | nil A => intro ω π _ h; exact h
  | cons i f hf hi tail ih =>
    intro ω π hω h
    obtain ⟨η,hη,hF⟩ := gamma_volume_transport_input hc C G f hn hf hT.1 ω hω
    refine ⟨η,hη,hF,ih hT.2 η π hη ?_⟩
    exact preservesVFVolume_cancel_left hc C hn ω η π (rawSpecialMap hc f)
      (rawSpecialMap hc tail.toMap) hf hF h

end IntegrationInACVF.Section7
