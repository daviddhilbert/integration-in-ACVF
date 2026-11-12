import IntegrationSection6.GammaCompanionScissors

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

variable (U : GammaObjectAt B S k)
variable (A C : @SpecialTransformations.DefinableGeometry.DefSet LRV M (@CanonicalStructure.normalize M sM)
  (@SpecialTransformations.Section4.rawRVSpace M (@CanonicalStructure.normalize M sM) (rvObjectArity U.object.obj)) S)
variable (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ S A) ⊆
  (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ S (rvObjectDomain U.object.obj)))
variable (hC : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ S C) ⊆
  (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ S (rvObjectDomain U.object.obj)))
variable (hΓA : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
  p.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ S A)})
variable (hΓC : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
  p.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ S C)})

theorem gammaCompanionSet_restrict :
    gammaCompanionSet (gammaRestrictAt U A hA hΓA).toGamma.toGammaRVObject =
      gammaCompanionLabel U.toGamma.toGammaRVObject ''
        {u : rvObjectDomain U.object.obj | u.val ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A)} := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨⟨a.val,hA a.property⟩,a.property,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨⟨u.val,hu⟩,rfl⟩

theorem gammaRestrictionScissor :
    GammaRVScissor
      (gammaRestrictAt U A hA hΓA).toGamma.toGammaRVObject
      (gammaRestrictAt U C hC hΓC).toGamma.toGammaRVObject
      (gammaRestrictAt U (@SpecialTransformations.DefinableGeometry.DefSet.union LRV M N _ S A C)
        (fun _ h => h.elim (hA ·) (hC ·)) ((gammaLogicInput B).union hΓA hΓC)).toGamma.toGammaRVObject
      (gammaRestrictAt U (@SpecialTransformations.DefinableGeometry.DefSet.inter LRV M N _ S A C)
        (fun _ h => hA h.1) ((gammaLogicInput B).inter hΓA hΓC)).toGamma.toGammaRVObject := by
  apply (gammaRVScissor_iff_companions _ _ _ _).mpr
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · rw [gammaCompanionSet_restrict,gammaCompanionSet_restrict,gammaCompanionSet_restrict]
    exact Set.image_union _ _ _
  · rw [gammaCompanionSet_restrict,gammaCompanionSet_restrict,gammaCompanionSet_restrict]
    exact Set.image_inter (gammaCompanionLabel_injective U.toGamma.toGammaRVObject)

end IntegrationInACVF.Section6.FiniteRV
