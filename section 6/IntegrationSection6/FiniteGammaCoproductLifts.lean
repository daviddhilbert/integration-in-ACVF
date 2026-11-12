import IntegrationSection6.FiniteGammaCoproducts
import IntegrationSection6.GammaTaggedLifts
import IntegrationSection6.GammaDisjointIsomorphisms

/-! The lift of the actual finite RV coproduct is the disjoint union of
the corresponding tagged lifts. This is the gluing geometry for6.13. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaCoprodAt_lift (U V : GammaObjectAt B S n) :
    (gammaCoprodAt U V).toGamma.lift =
      taggedLeftSet U.toGamma.lift (rvObjectArity V.object.obj) ∪
        taggedRightSet V.toGamma.lift (rvObjectArity U.object.obj) := by
  ext p
  constructor
  · rintro ⟨a,ha,hvol⟩
    rcases a.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · have he : a = @rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u := Subtype.ext hu.symm
      have hU : @RVObject.value M N S n U.object.obj u = @tupleRV M N hN n p.1 := by
        rw [he] at hvol
        exact (@rvCoprod_value_left M N hN S n U.object.obj V.object.obj u).symm.trans hvol
      exact Or.inl ⟨⟨(p.1,u.val),u,rfl,hU⟩,Prod.ext rfl (hu.trans ha)⟩
    · have he : a = @rvCoprodRightMap M N hN S n U.object.obj V.object.obj v := Subtype.ext hv.symm
      have hV : @RVObject.value M N S n V.object.obj v = @tupleRV M N hN n p.1 := by
        rw [he] at hvol
        exact (@rvCoprod_value_right M N hN S n U.object.obj V.object.obj v).symm.trans hvol
      exact Or.inr ⟨⟨(p.1,v.val),v,rfl,hV⟩,Prod.ext rfl (hv.trans ha)⟩
  · rintro (⟨a,ha⟩ | ⟨a,ha⟩)
    · obtain ⟨u,hu,hvol⟩ := a.property
      refine ⟨@rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u,?_,?_⟩
      · exact (congrArg (@rvLeftTag M N hN (rvObjectArity U.object.obj) (rvObjectArity V.object.obj)) hu).trans
          (congrArg Prod.snd ha)
      · exact (@rvCoprod_value_left M N hN S n U.object.obj V.object.obj u).trans
          (hvol.trans (congrArg (@tupleRV M N hN n) (congrArg Prod.fst ha)))
    · obtain ⟨v,hv,hvol⟩ := a.property
      refine ⟨@rvCoprodRightMap M N hN S n U.object.obj V.object.obj v,?_,?_⟩
      · exact (congrArg (@rvRightTag M N hN (rvObjectArity V.object.obj) (rvObjectArity U.object.obj)) hv).trans
          (congrArg Prod.snd ha)
      · exact (@rvCoprod_value_right M N hN S n U.object.obj V.object.obj v).trans
          (hvol.trans (congrArg (@tupleRV M N hN n) (congrArg Prod.fst ha)))

end IntegrationInACVF.Section6.FiniteRV
