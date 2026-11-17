module

public import Integration7.UnaryChainVolumeDensities
public import Integration7.NativeRVGraphVolumeRefinements
public import IntegrationSection6.GammaFiniteMixedBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual densities on every unary factor imply volume preservation
of the composite. Intermediate finite-label domains follow from the
genuine definable bijections over the same real base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (VF RV carrier gammaLogicInput)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem unary_chain_volume_data_preserves
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : UnaryChain (C.base : Set M) (n+1) A B) :
    ∀ (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B)),
      unaryChainVolumeData hc T ω π →
      (∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite) →
      PreservesVFVolume ω π (rawSpecialMap hc T.toMap) := by
  let G : Base (M := M) := ⟨(C.base : Set M),∅⟩
  induction T with
  | nil A => intro ω π hData hfinA; exact hData
  | @cons a c b A W B i f hf hi tail ih =>
    intro ω π hData hfinA
    obtain ⟨η,hfVolume,hTailVolume⟩ := hData
    have hfinW := finite_rv_fibres_of_gamma_bijection (B := G) C.uncountable.le C.saturated C.small
      f hf ((gammaLogicInput G).real_map_graph f) hfinA
    have hfinB := finite_rv_fibres_of_gamma_bijection (B := G) C.uncountable.le C.saturated C.small
      tail.toMap tail.bijective ((gammaLogicInput G).real_map_graph tail.toMap) hfinW
    let U := nativeMixedVFVolumeObject hc A hfinA ω
    let V := nativeMixedVFVolumeObject hc W hfinW η
    let Z := nativeMixedVFVolumeObject hc B hfinB π
    let F : VFVolumeBijection U V := ⟨rawSpecialMap hc f,hf,hfVolume⟩
    let H : VFVolumeBijection V Z := ⟨rawSpecialMap hc tail.toMap,tail.bijective,ih η π hTailVolume hfinW⟩
    exact (F.trans hc C H).preserves

end IntegrationInACVF.Section7
