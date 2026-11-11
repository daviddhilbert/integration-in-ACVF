import IntegrationSection4.GammaUnarySyntax
import IntegrationSection4.FiniteRelationPreparation

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.UnaryPreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Prepare an original-base unary relation in all its free RV arguments.
The finite real presentation used internally does not enlarge the exported base. -/
theorem prepare {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) (A : Set M) (hA : DefinableAtBase G .vf A)
    {k : ℕ} (r : Point (M := M) 1 0 → Point (M := M) 0 k → Prop)
    (hr : GammaGraphDefinable G r) :
    ∃ l : ℕ, ∃ E : Set (Point (M := M) 1 l),
      ∃ T : GammaSpecialBijection G (GammaUnarySyntax.pointSet A) E,
        IsRVPullback E ∧ FiniteRelationPreparation.Uniform r T.special := by
  have hPoint := GammaUnarySyntax.pointSet_definable G A hA
  obtain ⟨d,t,_,D,hD⟩ := gammaPresentationInput G _ hPoint
  let S := G.real ∪ Set.range (rawTuple t)
  have hGS : G.real ⊆ S := Set.subset_union_left
  have hDG : GammaSetDefinable G (carrier D) := hD.symm ▸ hPoint
  obtain ⟨l,E,T,_,hTG,hE,hR⟩ := GammaRelationPreparation.prepare hs h00 G hsmall hGenerated hGS
    D hDG r hr none (by intro h; cases h)
  exact ⟨l,carrier E,⟨S,hGS,D,E,hD,rfl,T,hTG⟩,hE,hR⟩

end IntegrationInACVF.Section4.UnaryPreparation
