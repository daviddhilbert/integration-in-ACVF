import IntegrationSection6.GammaSchemaNativeRows
import IntegrationSection6.GammaRawCoproductSchemaBridge

/-! Coproduct formulas represent the actual native finite coproduct of
represented rows, including every domain and volume-graph equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {S : Set M} {p k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaSchemaRepresents_coprod (U V : FiniteRV.GammaObjectAt C S k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object.obj) k sp)
    (G : GammaFiniteRVSchema B p (rvObjectArity V.object.obj) k sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : gammaSchemaRepresents U.toGamma F z) (hG : gammaSchemaRepresents V.toGamma G z) :
    gammaSchemaRepresents (FiniteRV.gammaCoprodAt U V).toGamma (F.coprodFormula G) z := by
  apply gammaSchemaRepresents_of_typed _ _ z
  · intro w
    rw [F.coprod_row_domain_formula G z hz w]
    constructor
    · rintro (⟨x,hx,hw⟩ | ⟨y,hy,hw⟩)
      · exact Or.inl ⟨⟨x,(gammaSchemaRepresents_domain U.toGamma F z hF x).mp hx⟩,hw⟩
      · exact Or.inr ⟨⟨y,(gammaSchemaRepresents_domain V.toGamma G z hG y).mp hy⟩,hw⟩
    · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
      · exact Or.inl ⟨u.val,(gammaSchemaRepresents_domain U.toGamma F z hF u.val).mpr u.property,hu⟩
      · exact Or.inr ⟨v.val,(gammaSchemaRepresents_domain V.toGamma G z hG v.val).mpr v.property,hv⟩
  · intro w v
    rw [F.coprod_row_volume_formula G z hz w v]
    constructor
    · rintro (⟨x,hx,hw⟩ | ⟨y,hy,hw⟩)
      · obtain ⟨u,hu,huv⟩ := (gammaSchemaRepresents_volume U.toGamma F z hF x v).mp hx
        exact ⟨@rvCoprodLeftMap M N hN S k U.object.obj V.object.obj u,
          (congrArg (@rvLeftTag M N hN _ _) hu).trans hw,
          (@rvCoprod_value_left M N hN S k U.object.obj V.object.obj u).trans huv⟩
      · obtain ⟨u,hu,huv⟩ := (gammaSchemaRepresents_volume V.toGamma G z hG y v).mp hy
        exact ⟨@rvCoprodRightMap M N hN S k U.object.obj V.object.obj u,
          (congrArg (@rvRightTag M N hN _ _) hu).trans hw,
          (@rvCoprod_value_right M N hN S k U.object.obj V.object.obj u).trans huv⟩
    · rintro ⟨u,hu,hv⟩
      rcases u.property with ⟨x,hx⟩ | ⟨y,hy⟩
      · have he : u = @rvCoprodLeftMap M N hN S k U.object.obj V.object.obj x := Subtype.ext hx.symm
        have hxv : (rvObjectVolume U.object.obj x).val = v := by
          rw [he] at hv
          exact (@rvCoprod_value_left M N hN S k U.object.obj V.object.obj x).symm.trans hv
        exact Or.inl ⟨x.val,(gammaSchemaRepresents_volume U.toGamma F z hF _ _).mpr ⟨x,rfl,hxv⟩,hx.trans hu⟩
      · have he : u = @rvCoprodRightMap M N hN S k U.object.obj V.object.obj y := Subtype.ext hy.symm
        have hyv : (rvObjectVolume V.object.obj y).val = v := by
          rw [he] at hv
          exact (@rvCoprod_value_right M N hN S k U.object.obj V.object.obj y).symm.trans hv
        exact Or.inr ⟨y.val,(gammaSchemaRepresents_volume V.toGamma G z hG _ _).mpr ⟨y,rfl,hyv⟩,hy.trans hu⟩

end IntegrationInACVF.Section6
