module

public import Integration7.VFVolumeDensityTransport
public import Integration7.VFVolumeCancellation
public import Integration7.SpecialVolumeJacobians
public import IntegrationSection5.UnaryFactorizations

@[expose] public section

/-! A volume-preserving finite unary factorization carries actual
nonzero definable densities on every intermediate domain. No factor is
assumed to have Jacobian1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}

def unaryChainVolumeData (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S n b}
    (T : UnaryChain S n A B) :
    VolumeForm (rawSpecialSet hc A) → VolumeForm (rawSpecialSet hc B) → Prop :=
  by
    induction T with
    | nil A =>
      exact fun ω π => PreservesVFVolume ω π (rawSpecialMap hc (SpecialTransformations.Section5.Map.id A))
    | cons i f hf hi tail ih =>
      exact fun ω π => ∃ η, PreservesVFVolume ω η (rawSpecialMap hc f) ∧ ih η π

theorem unary_chain_volume_data_of_composite
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n b}
    (T : UnaryChain (C.base : Set M) n A B) :
    ∀ (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B)),
      PreservesVFVolume ω π (rawSpecialMap hc T.toMap) → unaryChainVolumeData hc T ω π := by
  induction T with
  | nil A => intro ω π h; exact h
  | cons i f hf hi tail ih =>
    intro ω π h
    let η := transportedVFVolumeForm (rawSpecialMap hc f) hf ω
    have hF := preserves_transported_vf_volume hc C hn (rawSpecialMap hc f) hf ω
    refine ⟨η,hF,ih η π ?_⟩
    exact preservesVFVolume_cancel_left hc C hn ω η π (rawSpecialMap hc f)
      (rawSpecialMap hc tail.toMap) hf hF h

end IntegrationInACVF.Section7
