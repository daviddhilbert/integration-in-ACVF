import Integration7.GammaVolumeCoproductFormulas
import Integration7.NormalizedRVTags

/-! The coproduct formula interprets the actual coproduct of volume
objects, with literal tags, coordinate maps and densities. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
variable {U V : PositiveRVVolumeObject (M := M) S k}
variable {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
variable {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp} {z : Fin p → M}

theorem RVVolumeSchemaRow.coprod (P : RVVolumeSchemaRow U F z) (Q : RVVolumeSchemaRow V G z)
    (hz : ∀ i, sortEval (sp i) (z i)) : RVVolumeSchemaRow (U.coprod V) (F.coprodFormula G) z := by
  constructor
  · intro w t
    change (F.object.coprodFormula G.object).rowVolume z w t ↔ _
    rw [F.object.coprod_row_volume_formula G.object z hz w t]
    constructor
    · rintro (⟨x,hx,htag⟩ | ⟨y,hy,htag⟩)
      · obtain ⟨u,rfl,hu⟩ := (P.volume_iff x t).mp hx
        refine ⟨rvCoprodLeftMap U.underlying.obj V.underlying.obj u,?_,?_⟩
        · exact (rvLeftTag_normalize u.val).symm.trans htag
        · exact (rvCoprod_value_left U.underlying.obj V.underlying.obj u).trans hu
      · obtain ⟨v,rfl,hv⟩ := (Q.volume_iff y t).mp hy
        refine ⟨rvCoprodRightMap U.underlying.obj V.underlying.obj v,?_,?_⟩
        · exact (rvRightTag_normalize v.val).symm.trans htag
        · exact (rvCoprod_value_right U.underlying.obj V.underlying.obj v).trans hv
    · rintro ⟨c,hw,ht⟩
      rcases c.property with ⟨u,hu⟩ | ⟨v,hv⟩
      · have he : c = rvCoprodLeftMap U.underlying.obj V.underlying.obj u := Subtype.ext hu.symm
        subst c
        refine Or.inl ⟨u.val,(P.volume_iff _ _).mpr ⟨u,rfl,?_⟩,?_⟩
        · exact (rvCoprod_value_left U.underlying.obj V.underlying.obj u).symm.trans ht
        · exact (rvLeftTag_normalize u.val).trans hw
      · have he : c = rvCoprodRightMap U.underlying.obj V.underlying.obj v := Subtype.ext hv.symm
        subst c
        refine Or.inr ⟨v.val,(Q.volume_iff _ _).mpr ⟨v,rfl,?_⟩,?_⟩
        · exact (rvCoprod_value_right U.underlying.obj V.underlying.obj v).symm.trans ht
        · exact (rvRightTag_normalize v.val).trans hw
  · intro w ω
    rw [F.coprod_rowDensity G z hz w ω]
    constructor
    · rintro (⟨x,hx,htag⟩ | ⟨y,hy,htag⟩)
      · obtain ⟨u,rfl,hω⟩ := (P.density_iff x ω).mp hx
        refine ⟨rvCoprodLeftMap U.underlying.obj V.underlying.obj u,?_,?_⟩
        · exact (rvLeftTag_normalize u.val).symm.trans htag
        · funext i
          fin_cases i
          exact (coprod_density_left U V u).trans (congrFun hω 0)
      · obtain ⟨v,rfl,hω⟩ := (Q.density_iff y ω).mp hy
        refine ⟨rvCoprodRightMap U.underlying.obj V.underlying.obj v,?_,?_⟩
        · exact (rvRightTag_normalize v.val).symm.trans htag
        · funext i
          fin_cases i
          exact (coprod_density_right U V v).trans (congrFun hω 0)
    · rintro ⟨c,hw,hω⟩
      rcases c.property with ⟨u,hu⟩ | ⟨v,hv⟩
      · have he : c = rvCoprodLeftMap U.underlying.obj V.underlying.obj u := Subtype.ext hu.symm
        subst c
        refine Or.inl ⟨u.val,(P.density_iff _ _).mpr ⟨u,rfl,?_⟩,?_⟩
        · funext i
          fin_cases i
          exact (coprod_density_left U V u).symm.trans (congrFun hω 0)
        · exact (rvLeftTag_normalize u.val).trans hw
      · have he : c = rvCoprodRightMap U.underlying.obj V.underlying.obj v := Subtype.ext hv.symm
        subst c
        refine Or.inr ⟨v.val,(Q.density_iff _ _).mpr ⟨v,rfl,?_⟩,?_⟩
        · funext i
          fin_cases i
          exact (coprod_density_right U V v).symm.trans (congrFun hω 0)
        · exact (rvRightTag_normalize v.val).trans hw

end IntegrationInACVF.Section7
