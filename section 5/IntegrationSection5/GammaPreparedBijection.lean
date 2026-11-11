import IntegrationSection5.GammaMatchedChain
import IntegrationSection5.QuotientBijection

/-! Prepared unary bijections: actual inverse preparation and matching over
an original Gamma base, followed by the unique definable RV-key bijection.
The open-to-open partition input remains an explicit geometric obligation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem gamma_prepared_bijective_contraction {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (f : Map A B) (hf : Function.Bijective f) (hc : Contractible f)
    (hg : CellwiseOpenEquivalence f)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hTag : ∃ j : Fin m, Tagged (carrier A) 0 j)
    (hADef : GammaSetDefinable P (carrier A)) (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    ∃ d e : ℕ, ∃ A' : DefSet (M := M) S 1 d, ∃ B' : DefSet (M := M) S 1 e,
      ∃ TA : SpecialBijection A A', ∃ TB : SpecialBijection B B',
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        TA.chain.Alternating (some false) ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        Contractible (unaryConjugate TA TB f) ∧
        Contractible (Map.inverse (unaryConjugate TA TB f)
          (unaryConjugate_bijective TA TB f hf)) ∧
        GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB f)) ∧
        ∃! g : Map (keyImage A') (keyImage B'), Function.Bijective g ∧
          ∀ a : A', g (toKeyImage A' a) = toKeyImage B' (unaryConjugate TA TB f a) := by
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have ho := uniformVerticalObstacles hs hsmall v hv
  let L := gammaLogicInput P
  have hp : GammaPolynomialSupportInput P := gammaPolynomialSupportInput_of_fieldBase P FBase
  obtain ⟨e,B',TB,_,hTB,hB',hFinal⟩ := gamma_map_preparation_at_boundary
    h00 v hv ho L hp hPS B hBDef (Map.inverse f hf) (gamma_inverse_map_graph f hf hfDef)
    none (by intro h; cases h)
  obtain ⟨d,A',TA,hTA,hAlt,hA',_,hForward,hReverse⟩ := gamma_matched_chain_induction
    TB.chain TB.alternating hTB f hf hc hg hADef hfDef hA hB hB' hTag hFinal
  have hBack : Contractible (Map.inverse (unaryConjugate TA TB f)
      (unaryConjugate_bijective TA TB f hf)) := by
    intro a b hab
    rw [unaryConjugate_inverse,unaryConjugate_inverse]
    exact hReverse a b hab
  exact ⟨d,e,A',B',TA,TB,hTA,hTB,hAlt,hA',hB',hForward,hBack,
    gamma_unaryConjugate_graph TA TB f hTA hTB hfDef,
    exists_unique_bijective_contraction _ (unaryConjugate_bijective TA TB f hf) hForward hBack⟩

end IntegrationInACVF.Section5
