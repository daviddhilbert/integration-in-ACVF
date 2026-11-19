import Integration7.GammaNamedUnaryChains
import Integration7.VFVolumeCancellation

/-! The Gamma volume-transport input and Gamma chain volume data.

`GammaVolumeTransportInput hc G S` says: along an actual mixed bijection
with a Gamma graph over `G`, every density with a Gamma density graph is
transported to a density with a Gamma density graph that it preserves. Over
the real base it holds by transporting along the definable Jacobian; with
genuine Gamma parameters it is the consequence of a Gamma-definable a.e.
Jacobian (not yet formalized). It is recorded here as a named input so that
the Gamma-named kernel can be assembled; no headline is stated under it. -/
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
    (f : SpecialTransformations.Section5.Map A B), Function.Bijective f →
    GammaGraphDefinable G (pointMapGraph f) →
    ∀ ω : VolumeForm (rawSpecialSet hc A), GammaSetDefinable G (volumeDensityGraph ω).carrier →
    ∃ η : VolumeForm (rawSpecialSet hc B), GammaSetDefinable G (volumeDensityGraph η).carrier ∧
      PreservesVFVolume ω η (rawSpecialMap hc f)

theorem gamma_unary_chain_volume_data_of_composite
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ} (hn : 0 < n)
    (hTransport : GammaVolumeTransportInput hc G (C.base : Set M))
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
    obtain ⟨η,hη,hF⟩ := hTransport f hf hT.1 ω hω
    refine ⟨η,hη,hF,ih hT.2 η π hη ?_⟩
    exact preservesVFVolume_cancel_left hc C hn ω η π (rawSpecialMap hc f)
      (rawSpecialMap hc tail.toMap) hf hF h

end IntegrationInACVF.Section7
