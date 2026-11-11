import IntegrationSection5.ChainAlgebra
import IntegrationSection5.MatchedFocusReverse

/-! One complete matched-focus step, including the remaining target chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {F : DefSet (M := M) S 1 r} {j : Fin m} {k : Fin l}

theorem focussedCanonical_alternating {k : Fin m} (D : Focus A 0 k) :
    (focussedCanonical D).chain.Alternating (some false) := by
  exact ⟨by decide, by decide, trivial⟩

theorem focussedCanonical_lastKind {k : Fin m} (D : Focus A 0 k) (previous : Option Bool) :
    (focussedCanonical D).chain.lastKind previous = some false := rfl

theorem focussedCanonical_tagged {k : Fin m} (D : Focus A 0 k) :
    ∃ j : Fin (1 + m), Tagged (carrier (canonicalImage D.etaImage)) 0 j := by
  refine ⟨Fin.castAdd m 0, ?_⟩
  rw [canonicalImage_carrier]
  exact canonical_tagged (carrier D.etaImage) 0

theorem matched_focus_step (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hg : CellwiseOpenEquivalence f) (D : Focus B 0 k)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hF : IsRVPullback (carrier F)) (hTag : Tagged (carrier A) 0 j)
    (R : SpecialBijection B F) (U : SpecialBijection D.etaImage F)
    (hR : ∀ b : B, R.toMap b = U.toMap ((SpecialBijection.centripetal D).toMap b))
    (hFinal : Contractible (Map.comp (Map.inverse f hf) R.inverseMap)) :
    let TA := focussedCanonical (pulledFocus f hf hc D hA hB hTag)
    let TB := SpecialBijection.centripetal D
    let g := unaryConjugate TA TB f
    Contractible g ∧ CellwiseOpenEquivalence g ∧
      Contractible (Map.comp (Map.inverse g (unaryConjugate_bijective TA TB f hf)) U.inverseMap) := by
  let TA := focussedCanonical (pulledFocus f hf hc D hA hB hTag)
  let TB := SpecialBijection.centripetal D
  have hMark : ∀ b : B, b.val ∈ D.locus →
      vfAt (R.toMap (focusSectionMap D hB b)).val 0 = 0 := by
    intro b hb
    rw [hR]
    exact unary_special_preserves_zero U _ (unary_focus_section_zero D hB b hb)
  refine ⟨matched_focus_contractible f hf hc (cellwiseOpenEquivalence_open f hc hg) D hA hB hTag,
    cellwiseOpenEquivalence_conjugate TA TB f hg, ?_⟩
  exact conjugate_tail_contractible TA TB R U hR f hf
    (matched_focus_reverse_contractible f hf hc hg D hA hB hF hTag R hFinal hMark)

end IntegrationInACVF.Section5
