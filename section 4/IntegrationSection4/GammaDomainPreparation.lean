import IntegrationSection4.GammaFamilySyntax

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.GammaDomainPreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem prepare {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) {m : ℕ} (A : Set (Point (M := M) 1 m))
    (hA : GammaSetDefinable G A) :
    ∃ l : ℕ, ∃ E : Set (Point (M := M) 1 l), ∃ T : GammaSpecialBijection G A E, IsRVPullback E := by
  let hΓ := gammaLogicInput G
  let r (p : Point (M := M) 1 m) (_ : Point (M := M) 0 0) : Prop := p ∈ A
  have hr : GammaGraphDefinable G r := by
    have h := hΓ.restrict_graph hA (hΓ.real_map_graph
      (constantRVMap (PresentedSet.univ (pointSpace 1 m) G.real) 0))
    apply GammaGraphDefinable.congr h
    intro p q
    exact ⟨fun h => h.1,fun hp => ⟨hp,⟨p,Set.mem_univ _⟩,rfl,Subsingleton.elim _ _⟩⟩
  obtain ⟨l,E,T,hE,_⟩ := GammaFamilySyntax.prepare hs h00 G hsmall hGenerated A hA r hr
  exact ⟨l,E,T,hE⟩

end IntegrationInACVF.Section4.GammaDomainPreparation
