import Integration7.GammaVolumeObjectPromotion
import Integration7.CanonicalVolumeSchemaRows

/-! Promotion preserves the actual coordinate and density functions of
the original presentation, in every containing canonical base context. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem gamma_volume_object_promotion_rows {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    {D : Set (Fin a → RV (M := M))}
    {R : (Fin a → RV (M := M)) → (Fin (k+1) → RV (M := M)) → Prop}
    {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}
    (P : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1) D R W)
    (hP : P.finite.codes ⊆ (C.base : Set M)) :
    ∃ F : GammaRVVolumeSchema B p a k sp, F.valid z ∧
      RVVolumeSchemaRow (P.inContext hc C hP).toObject F z := by
  obtain ⟨F,hF,_,hV,hW⟩ := gamma_sorted_volume_object_promotion hκ hs hreal hgamma sp z hz P
  refine ⟨F,hF,⟨?_,?_⟩⟩
  · intro x t
    change Fin.append (Fin.append z (rvValues x)) (rvValues t) ∈ F.object.volume ↔
      ∃ u : P.finite.domain, u.val = x ∧ (P.finite.volume u).val = t
    rw [hV,gammaRawObjectVolume_append_iff]
    constructor
    · rintro ⟨u,hx,ht⟩
      exact ⟨u,funext (fun i => Subtype.ext (congrFun hx i)),
        funext (fun i => Subtype.ext (congrFun ht i))⟩
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨u,rfl,rfl⟩
  · intro x ω
    change Fin.append (Fin.append z (rvValues x)) (rvValues ω) ∈ F.density ↔ _
    rw [hW,gammaRawObjectVolume_append_iff]
    constructor
    · rintro ⟨u,hx,hω⟩
      exact ⟨u,funext (fun i => Subtype.ext (congrFun hx i)),
        funext (fun i => Subtype.ext (congrFun hω i))⟩
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨u,rfl,rfl⟩

end IntegrationInACVF.Section7
