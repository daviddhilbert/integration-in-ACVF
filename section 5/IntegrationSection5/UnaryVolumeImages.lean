import IntegrationSection5.RVContractionMaps
import IntegrationSection5.UnaryVFFibreFinite

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem unary_vf_fibre_image_finite_typed {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : GammaGraphDefinable P (pointMapGraph f)) (x : VF (M := M)) :
    {y : VF (M := M) | ∃ a : A, vfAt a.val 0 = x ∧ vfAt (f a).val 0 = y}.Finite := by
  have h := unary_vf_fibre_image_finite hκ hs hsmall f hf x
  have hPre := Set.Finite.preimage (f := fun y : VF (M := M) => y.val) Subtype.val_injective.injOn h
  apply hPre.subset
  rintro y ⟨a,hx,hy⟩
  exact ⟨a,hx,congrArg Subtype.val hy⟩

theorem rvContractionMap_finite_volume_images {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hc : Contractible f) (hA : IsRVPullback (carrier A))
    (hf : GammaGraphDefinable P (pointMapGraph f)) (t : Fin 1 → RV (M := M)) :
    (@SpecialTransformations.Section4.RVObject.volumeFibreImage M (@CanonicalStructure.normalize M sM) S 1
      (pullbackObject A) (pullbackObject B) (rvContractionMap f hc) t).Finite := by
  obtain ⟨x,hx⟩ := CanonicalRV.encodedRv_surjective (t 0)
  have hx' : rv x = t 0 := hx
  have hFin := (unary_vf_fibre_image_finite_typed hκ hs hsmall f hf x).image
    (fun y : VF (M := M) => fun _ : Fin 1 => rv y)
  apply hFin.subset
  rintro s ⟨u,ht,hu⟩
  obtain ⟨a,rfl⟩ := rawKeyImage_surjective A u
  change (rvObjectVolume (pullbackObject A) (Map.toImage (rawKeyMap A) a)).val = t at ht
  rw [pullbackObject_value_key] at ht
  have hax : rv x = rv (vfAt a.val 0) := hx'.trans (congrFun ht 0).symm
  let p := unaryInsert a.val.2 x
  have hcell : SameRV p a.val := by
    apply (sameRV_iff _ _).mpr
    refine ⟨?_,rfl⟩
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hax
  let b : A := ⟨p,(isRVPullback_iff _).mp hA a.val a.property p hcell.symm⟩
  have hKey : Map.toImage (rawKeyMap A) b = Map.toImage (rawKeyMap A) a :=
    Subtype.ext ((rawKeyMap_eq_iff b a).mpr hcell)
  have hVolume := rvContractionMap_volume_spec f hc b
  rw [hKey] at hVolume
  change (rvObjectVolume (pullbackObject B)
    (rvContractionMap f hc (Map.toImage (rawKeyMap A) a))).val = s at hu
  refine ⟨vfAt (f b).val 0,⟨b,rfl,rfl⟩,?_⟩
  rw [← hu,hVolume]
  funext i
  exact congrArg (fun j => rv (vfAt (f b).val j)) (Subsingleton.elim _ _)

end IntegrationInACVF.Section5
