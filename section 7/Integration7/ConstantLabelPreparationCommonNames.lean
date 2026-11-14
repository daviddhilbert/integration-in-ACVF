import Integration7.GammaSpecialCommonNames
import Integration7.ConstantRVLabelSpecialPreparations

/-! The actual fixed-label lift of a unary special preparation can be
presented over common names, retaining its geometry and projection indices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.ConstantRVLabelSpecialPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S R : Set M} {b l : ℕ}
variable {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {t : Fin l → RV (M := M)}

def present (L : ConstantRVLabelSpecialPreparation T H t P)
    (hT : GammaChainDefinable P T.chain) (hNames : commonRealNames P ⊆ R) :
    ConstantRVLabelSpecialPreparation (gammaSpecialPresentation T hT hNames)
      (gammaNativePresentation H (L.gamma.source P L.special.chain) hNames) t P where
  source_mem := L.source_mem
  source_surjective := by
    intro a
    obtain ⟨p,hp⟩ := L.source_surjective ⟨a.val,a.property⟩
    exact ⟨⟨p.val,p.property⟩,hp⟩
  source_labels p := L.source_labels ⟨p.val,p.property⟩
  arity := L.arity
  target := gammaNativePresentation L.target (L.gamma.target P L.special.chain) hNames
  projection := L.projection
  carried := L.carried
  special := gammaSpecialPresentation L.special L.gamma hNames
  gamma := gamma_chain_presentation_gamma L.special.chain L.gamma hNames
  jointly_determine := L.jointly_determine
  commutes := by
    intro p
    change retainVFLabels L.projection ((gammaChainPresentation L.special.chain L.gamma hNames).toMap p).val = _
    rw [gamma_chain_presentation_apply]
    change _ = ((gammaChainPresentation T.chain hT hNames).toMap _).val
    rw [gamma_chain_presentation_apply]
    exact L.commutes ⟨p.val,p.property⟩
  labels := by
    intro p
    change ((gammaChainPresentation L.special.chain L.gamma hNames).toMap p).val.2 ∘ L.carried = t
    rw [gamma_chain_presentation_apply]
    exact L.labels ⟨p.val,p.property⟩
  pullback := L.pullback

end IntegrationInACVF.Section7.ConstantRVLabelSpecialPreparation
