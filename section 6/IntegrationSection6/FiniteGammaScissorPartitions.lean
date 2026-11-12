import IntegrationSection6.FiniteGammaScissorClasses

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaFiniteScissorClass_partition (U : GammaObjectAt B S k)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A)}) :
    gammaFiniteScissorClass (gammaRestrictAt U A hA hΓ).toGamma +
      gammaFiniteScissorClass (gammaComplementAt U A hΓ).toGamma = gammaFiniteScissorClass U.toGamma := by
  let C := @complement M N S k U.object.obj A
  have hC := @complement_subset M N hN S k U.object.obj A
  have hΓC := (gammaLogicInput B).sdiff U.domain_graph hΓ
  let R := gammaRestrictAt U A hA hΓ
  let T := gammaRestrictAt U C hC hΓC
  let E := gammaRestrictAt U (@SpecialTransformations.DefinableGeometry.DefSet.inter LRV M N _ S A C)
    (fun _ h => hA h.1) ((gammaLogicInput B).inter hΓ hΓC)
  have hE : ∀ u : rvObjectDomain E.object.obj, False := fun u => u.property.2.2 u.property.1
  have hsc : GammaRVScissor R.toGamma.toGammaRVObject T.toGamma.toGammaRVObject
      U.toGamma.toGammaRVObject E.toGamma.toGammaRVObject := by
    apply (gammaRVScissor_iff_companions _ _ _ _).mpr
    refine ⟨rfl,rfl,rfl,?_,?_⟩
    · ext z
      constructor
      · rintro ⟨u,rfl⟩
        by_cases hu : u.val ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A)
        · exact Or.inl ⟨⟨u.val,hu⟩,rfl⟩
        · exact Or.inr ⟨⟨u.val,⟨u.property,hu⟩⟩,rfl⟩
      · rintro (⟨u,rfl⟩ | ⟨u,rfl⟩)
        · exact ⟨⟨u.val,hA u.property⟩,rfl⟩
        · exact ⟨⟨u.val,u.property.1⟩,rfl⟩
    · change gammaCompanionSet (gammaRestrictAt U _ _ _).toGamma.toGammaRVObject =
        gammaCompanionSet (gammaRestrictAt U A hA hΓ).toGamma.toGammaRVObject ∩
        gammaCompanionSet (gammaRestrictAt U C hC hΓC).toGamma.toGammaRVObject
      rw [gammaCompanionSet_restrict,gammaCompanionSet_restrict,gammaCompanionSet_restrict]
      exact Set.image_inter (gammaCompanionLabel_injective U.toGamma.toGammaRVObject)
  have he := gammaFiniteScissorClass_empty E.toGamma hE
  have hs := of_scissor (gammaRVFinitePresentation B k)
    (a := gammaFiniteScissorObject R.toGamma) (b := gammaFiniteScissorObject T.toGamma)
    (c := gammaFiniteScissorObject U.toGamma) (d := gammaFiniteScissorObject E.toGamma) hsc
  change gammaFiniteScissorClass R.toGamma + gammaFiniteScissorClass T.toGamma =
    gammaFiniteScissorClass U.toGamma + gammaFiniteScissorClass E.toGamma at hs
  simpa only [he,add_zero,R,T,C,gammaComplementAt] using hs

end IntegrationInACVF.Section6.FiniteRV
