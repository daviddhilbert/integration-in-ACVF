module

public import Integration7.NativeBalancedCellImages
public import Integration7.BalancedInversePositionGraphs
public import Integration7.GammaNamesVolumeContexts
public import Integration7.NativeRelativeTranslationVolumes

@[expose] public section

/-! Actual definable balanced-cell translations, with original-base centre
graphs and Jacobian-one certificates. A containing small context realizes
the names; the graph certificates retain the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.BalancedFibres
open IntegrationInACVF.Section4.Cells IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {D E : Set (VF (M := M))} {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

structure BalancedTranslationCentres (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t) where
  vertical : Map A (PresentedSet.univ (vfSpace 1) S)
  horizontal : Map A (PresentedSet.univ (vfSpace 1) S)
  vertical_value : ∀ p : A, (vertical p).val 0 = f (p.val.1 0)
  horizontal_value : ∀ p : A, (horizontal p).val 0 =
    ((balancedPositionEquiv h).symm ⟨p.val.1 1,(h.subset ⟨p.val,p.property,rfl⟩).2⟩).val

def balancedTranslationCentresOfPositionGraphs
    (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t)
    (hf : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes D f))
    (hg : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes E (balancedInversePosition h))) :
    BalancedTranslationCentres A h where
  vertical := coordinatePositionCentreMap A 0 D f hf (fun p => (h.subset ⟨p.val,p.property,rfl⟩).1)
  horizontal := coordinatePositionCentreMap A 1 E (balancedInversePosition h) hg
    (fun p => (h.subset ⟨p.val,p.property,rfl⟩).2)
  vertical_value _ := rfl
  horizontal_value p := balanced_inverse_position_value h _ (h.subset ⟨p.val,p.property,rfl⟩).2

theorem balanced_translation_centres_exist
    (C : BaseContext M) (B : Base (M := M)) (hBC : B.real ⊆ (C.base : Set M))
    (hΓ : Cardinal.mk B.gamma < C.κ)
    (A : DefSet (M := M) (C.base : Set M) 2 0) (hA : GammaSetDefinable B (carrier A))
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t)
    (hf : DefinableOverBase B (fun _ : Fin 2 => .vf) (positionCodes D f)) :
    ∃ (C' : BaseContext M) (hCC' : (C.base : Set M) ⊆ (C'.base : Set M)),
      ∃ K : BalancedTranslationCentres (extendBase A hCC') h,
        GammaScalarGraphDefinable B (fun p z => ∃ q : extendBase A hCC',
          q.val = p ∧ (K.vertical q).val 0 = z) ∧
        GammaScalarGraphDefinable B (fun p z => ∃ q : extendBase A hCC',
          q.val = p ∧ (K.horizontal q).val 0 = z) := by
  let C' := gammaNamesContainingVolumeContext C B hBC hΓ
  have hNames := gamma_names_containing_volume_context_contains C B hBC hΓ
  have hCC' : (C.base : Set M) ⊆ (C'.base : Set M) := fun _ hx => hNames (Or.inl hx)
  have hNC' : commonRealNames B ⊆ (C'.base : Set M) := fun _ hx => hNames (Or.inr hx)
  let A' := extendBase A hCC'
  have hg := balanced_inverse_position_graph h hf
  have hf' := hf.common_names.mono hNC'
  have hg' := hg.common_names.mono hNC'
  let K := balancedTranslationCentresOfPositionGraphs A' h hf' hg'
  refine ⟨C',hCC',K,?_,?_⟩
  · exact coordinate_position_native_gamma_graph A' hA 0 D f hf' hf
      (fun p => (h.subset ⟨p.val,p.property,rfl⟩).1)
  · exact coordinate_position_native_gamma_graph A' hA 1 E (balancedInversePosition h) hg' hg
      (fun p => (h.subset ⟨p.val,p.property,rfl⟩).2)

theorem balanced_native_translation_images
    (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t)
    (hD : IntegrationInACVF.Section3ACVF.PaperBalls.IsOpenBall (rawSet D))
    (K : BalancedTranslationCentres A h) :
    nativeVFPairDomain (relativeTranslationImage A 1 K.vertical) = D ×ˢ {z | rv z = t} ∧
    nativeVFPairDomain (relativeTranslationImage A 0 K.horizontal) = {z | rv z = r} ×ˢ E :=
  ⟨balanced_vertical_native_image A h K.vertical K.vertical_value,
    balanced_horizontal_native_image A h hD K.horizontal K.horizontal_value⟩

theorem balanced_native_translation_bijections
    (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t)
    (K : BalancedTranslationCentres A h) :
    Function.Bijective (relativeTranslationToImage A 1 K.vertical) ∧
    Function.Bijective (relativeTranslationToImage A 0 K.horizontal) :=
  ⟨relative_translation_to_image_bijective A 1 K.vertical
      (balanced_vertical_native_centre_independent A K.vertical K.vertical_value),
    relative_translation_to_image_bijective A 0 K.horizontal
      (balanced_horizontal_native_centre_independent A h K.horizontal K.horizontal_value)⟩

theorem balanced_native_translation_jacobians
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : DefSet (M := M) (C.base : Set M) 2 0)
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t)
    (K : BalancedTranslationCentres A h) :
    VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (relativeTranslationToImage A 1 K.vertical)) p 1) ∧
    VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (relativeTranslationToImage A 0 K.horizontal)) p 1) :=
  ⟨native_relative_translation_jacobian_one hc C (by decide) A 1 K.vertical
      (balanced_vertical_native_centre_independent A K.vertical K.vertical_value),
    native_relative_translation_jacobian_one hc C (by decide) A 0 K.horizontal
      (balanced_horizontal_native_centre_independent A h K.horizontal K.horizontal_value)⟩

end IntegrationInACVF.Section7
