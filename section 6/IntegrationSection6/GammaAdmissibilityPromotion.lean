import IntegrationSection6.GammaAdmissibleBounds
import IntegrationSection6.GammaFiniteObjectPromotion

/-! Actual Gamma admissibility over a named sorted tuple promotes to a genuine
first-order admissibility schema over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ}

theorem gammaRawObjectVolume_image_iff (U : GammaRVObject B k) (r : Fin k → M) :
    (∃ x, Fin.append x r ∈ gammaRawObjectVolume U) ↔ r ∈ gammaVolumeImage U := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨u,_,hu⟩ := (gammaRawObjectVolume_append_iff U x r).mp hx
    exact ⟨u,hu⟩
  · rintro ⟨u,hu⟩
    exact ⟨fun j => (u.val j).val,(gammaRawObjectVolume_append_iff U _ r).mpr ⟨u,rfl,hu⟩⟩

theorem gamma_sorted_finite_admissibility_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (U : GammaRVFiniteObject ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (i : Fin k) (hAd : GammaAdmissible U.toGammaRVObject i) :
    ∃ F : GammaFiniteAdmissibilitySchema B p (rvObjectArity U.object) k sp,
      F.coordinate = i ∧ F.valid z ∧
      (∀ x, Fin.append z x ∈ F.object.domain ↔ x ∈ gammaRawObjectDomain U.toGammaRVObject) ∧
      (∀ x s, Fin.append (Fin.append z x) s ∈ F.object.volume ↔ Fin.append x s ∈ gammaRawObjectVolume U.toGammaRVObject) := by
  obtain ⟨A,hA,hAD,hAV⟩ := gamma_sorted_finite_object_promotion hκ hs hreal hgamma sp z hz U
  have hCsmall : Cardinal.mk ↥(B.real ∪ Set.range z) < κ := small_union_range hκ B.real hreal z
  obtain ⟨N,hN⟩ := @GammaAdmissible.uniform_label_slices M sM hM
    ⟨B.real ∪ Set.range z,B.gamma⟩ k κ hκ hs h00 hCsmall hgamma U.toGammaRVObject i hAd
  let F : GammaFiniteAdmissibilitySchema B p (rvObjectArity U.object) k sp := ⟨A,i,N⟩
  have hImage (r : Fin k → M) : Fin.append z r ∈ tupleVolumeImage A.volume ↔ r ∈ gammaVolumeImage U.toGammaRVObject :=
    (tupleVolumeImage_append_iff A.volume z r).trans
      ((exists_congr (fun x => hAV x r)).trans (gammaRawObjectVolume_image_iff U.toGammaRVObject r))
  refine ⟨F,rfl,⟨hA,?_,?_⟩,hAD,hAV⟩
  · intro r hr
    exact hAd.image_nonzero ((hImage r).mp hr)
  · intro t ht
    have he : {r | Fin.append z r ∈ tupleVolumeImage A.volume ∧ ∀ j, j ≠ i → r j = t j} =
        {r | r ∈ gammaVolumeImage U.toGammaRVObject ∧ ∀ j, j ≠ i → r j = t j} :=
      Set.ext (fun r => and_congr (hImage r) Iff.rfl)
    change _ ∧ _
    rw [he]
    exact hN t ht

theorem gamma_finite_admissibility_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ j, sortEval SortTag.vf (z j))
    (U : GammaRVFiniteObject ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (i : Fin k) (hAd : GammaAdmissible U.toGammaRVObject i) :
    ∃ F : GammaFiniteAdmissibilitySchema B p (rvObjectArity U.object) k,
      F.coordinate = i ∧ F.valid z ∧
      (∀ x, Fin.append z x ∈ F.object.domain ↔ x ∈ gammaRawObjectDomain U.toGammaRVObject) ∧
      (∀ x s, Fin.append (Fin.append z x) s ∈ F.object.volume ↔ Fin.append x s ∈ gammaRawObjectVolume U.toGammaRVObject) :=
  gamma_sorted_finite_admissibility_promotion hκ hs h00 hreal hgamma (fun _ => .vf) z hz U i hAd

end IntegrationInACVF.Section6
