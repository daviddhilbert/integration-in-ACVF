import IntegrationSection5.MatchedChainInduction
import IntegrationSection5.QuotientBijection

/-! The geometric matching construction yields an actual definable bijection
of RV keys. Preparation and the open-to-open partition are separate inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {F : DefSet (M := M) S 1 r}

theorem prepared_mutual_contraction (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hg : CellwiseOpenEquivalence f)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hTag : ∃ j : Fin m, Tagged (carrier A) 0 j)
    (R : SpecialBijection B F) (hF : IsRVPullback (carrier F))
    (hFinal : Contractible (Map.comp (Map.inverse f hf) R.inverseMap)) :
    ∃ d : ℕ, ∃ A' : DefSet (M := M) S 1 d, ∃ TA : SpecialBijection A A',
      TA.chain.Alternating (some false) ∧ IsRVPullback (carrier A') ∧
      (∃ j : Fin d, Tagged (carrier A') 0 j) ∧
      Contractible (unaryConjugate TA R f) ∧
      Contractible (Map.inverse (unaryConjugate TA R f)
        (unaryConjugate_bijective TA R f hf)) := by
  obtain ⟨d, A', TA, hAlt, hA', hTag', hForward, hReverse⟩ :=
    matched_chain_induction R.chain R.alternating f hf hc hg hA hB hF hTag hFinal
  refine ⟨d, A', TA, hAlt, hA', hTag', hForward, ?_⟩
  intro a b hab
  rw [unaryConjugate_inverse, unaryConjugate_inverse]
  exact hReverse a b hab

/-- A unique RV-key bijection, obtained from the matched finite chains. -/
theorem prepared_bijective_contraction (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hg : CellwiseOpenEquivalence f)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hTag : ∃ j : Fin m, Tagged (carrier A) 0 j)
    (R : SpecialBijection B F) (hF : IsRVPullback (carrier F))
    (hFinal : Contractible (Map.comp (Map.inverse f hf) R.inverseMap)) :
    ∃ d : ℕ, ∃ A' : DefSet (M := M) S 1 d, ∃ TA : SpecialBijection A A',
      TA.chain.Alternating (some false) ∧ IsRVPullback (carrier A') ∧
      (∃ j : Fin d, Tagged (carrier A') 0 j) ∧
      ∃! g : Map (keyImage A') (keyImage F), Function.Bijective g ∧
        ∀ a : A', g (toKeyImage A' a) = toKeyImage F (unaryConjugate TA R f a) := by
  obtain ⟨d, A', TA, hAlt, hA', hTag', hForward, hReverse⟩ :=
    prepared_mutual_contraction f hf hc hg hA hB hTag R hF hFinal
  exact ⟨d, A', TA, hAlt, hA', hTag', exists_unique_bijective_contraction
    (unaryConjugate TA R f) (unaryConjugate_bijective TA R f hf) hForward hReverse⟩

end IntegrationInACVF.Section5
