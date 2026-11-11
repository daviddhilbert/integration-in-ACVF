import Section5.GeneralExistence
import Section5.VerticalObstacles
import Section3.GammaPresentation

/-!
Lemma 5.1 of arXiv:0809.0473v2, over a small real parameter base.
The two preparations use the predecessor's actual special bijections.
The finite vertical-obstacle input is discharged by its proved producer.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m u w : ℕ}

/-- Both sides become actual RV-pullbacks; the conjugated map descends to
their RV keys. Saturation is Mathlib's model-theoretic saturation. -/
theorem lemma_5_1_real_base {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk S < κ)
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w} (f : Map A B) :
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) S n r, ∃ B' : DefSet (M := M) S u s,
      ∃ TA : SpecialBijection A A', ∃ TB : SpecialBijection B B',
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
          Contractible (Map.comp TB.toMap (Map.comp f TA.inverseMap)) := by
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have ho := uniformVerticalObstacles hs hsmall v hv
  obtain ⟨s, B', TB, _, hB', _⟩ := map_preparation_at_boundary h00 v hv ho
    none (by intro h; cases h) (Map.id B)
  obtain ⟨r, A', TA, _, hA', hc⟩ := map_preparation_at_boundary h00 v hv ho
    none (by intro h; cases h) (Map.comp TB.toMap f)
  exact ⟨r, s, A', B', TA, TB, hA', hB', hc⟩

end IntegrationInACVF.Section5
