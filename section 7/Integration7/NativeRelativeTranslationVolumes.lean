module

public import Integration7.NativeRelativeTranslations
public import Integration7.RelativeFibreTranslationVolumes

@[expose] public section

/-! Actual native relative translations have Jacobian one almost
everywhere, including when the centre depends on the fixed RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

def relativeTranslationFibreCentre (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (u : Fin n → VF (M := M)) (r : Fin a → RV (M := M)) : VFType (M := M) :=
  if h : ∃ p : A, erase i p.val = erase i (u,r) then (c (Classical.choose h)).val 0 else 0

theorem relative_translation_fibre_centre_value (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (p : A) (u : Fin n → VF (M := M)) (r : Fin a → RV (M := M))
    (hp : erase i p.val = erase i (u,r)) : relativeTranslationFibreCentre A i c u r = (c p).val 0 := by
  have h : ∃ q : A, erase i q.val = erase i (u,r) := ⟨p,hp⟩
  unfold relativeTranslationFibreCentre
  rw [dif_pos h]
  exact hC (Classical.choose h) p ((Classical.choose_spec h).trans hp.symm)

set_option maxHeartbeats 1600000 in
theorem native_relative_translation_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    (A : DefSet (M := M) (C.base : Set M) n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0) :
    VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (relativeTranslationToImage A i c)) p 1) := by
  let F := relativeTranslationToImage A i c
  have hi : UnaryRelative F i := relative_translation_unary_relative A i c
  apply relative_fibre_translation_jacobian_one hc C hn F i hi (relativeTranslationFibreCentre A i c)
  intro u q
  let p : A := ⟨coordinateInsert i u q.val,q.property⟩
  have hErase : erase i p.val = erase i (u,q.val.2) :=
    Prod.ext (Function.update_idem _ _ _) rfl
  have hCentre := relative_translation_fibre_centre_value A i c hC p u q.val.2 hErase
  rw [coordinateFibreMap_apply]
  change (relativeTranslationMap A i c p).val.1 i =
    (show VFType (M := M) from q.val.1 0)-relativeTranslationFibreCentre A i c u q.val.2
  rw [relative_translation_map_value,hCentre]
  simp only [replace,p,coordinateInsert,vfAt,Function.update_self]

theorem native_relative_translation_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    (A : DefSet (M := M) (C.base : Set M) n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc (relativeTranslationImage A i c)))
    (hDensity : ∀ p, ω.value p = π.value (rawSpecialMap hc (relativeTranslationToImage A i c) p)) :
    PreservesVFVolume ω π (rawSpecialMap hc (relativeTranslationToImage A i c)) :=
  (native_relative_translation_jacobian_one hc C hn A i c hC).mono
    (fun p hJ => ⟨1,hJ,by rw [RVOperations.rv_one,mul_one];exact hDensity p⟩)

end IntegrationInACVF.Section7
