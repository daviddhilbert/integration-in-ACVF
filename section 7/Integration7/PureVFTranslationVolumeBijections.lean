module

public import Integration7.NativeRelativeTranslationVolumes

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Relative translations of pure VF domains are actual morphisms of
the volume category for every original definable density transported by
the inverse bijection. No fixed-density assumption is needed here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def nativePureVFVolumeObject (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S (k+1) 0) (ω : VolumeForm (rawSpecialSet hc A)) :
    PositiveVFVolumeObject (M := M) S k where
  arity := 0
  domain := rawSpecialSet hc A
  finite_labels _ := Set.toFinite _
  form := ω

def translatedPureVFVolumeObject (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S (k+1) 0) (i : Fin (k+1))
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (ω : VolumeForm (rawSpecialSet hc A)) : PositiveVFVolumeObject (M := M) S k :=
  nativePureVFVolumeObject hc (relativeTranslationImage A i c)
    (ω.pullback (rawSpecialMap hc (Map.inverse (relativeTranslationToImage A i c)
      (relative_translation_to_image_bijective A i c hC))))

def pureVFTranslationVolumeBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : DefSet (M := M) (C.base : Set M) (k+1) 0) (i : Fin (k+1))
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (ω : VolumeForm (rawSpecialSet hc A)) :
    VFVolumeBijection (nativePureVFVolumeObject hc A ω) (translatedPureVFVolumeObject hc A i c hC ω) where
  map := rawSpecialMap hc (relativeTranslationToImage A i c)
  bijective := relative_translation_to_image_bijective A i c hC
  preserves := native_relative_translation_preserves_volume hc C (Nat.zero_lt_succ k) A i c hC ω _ (by
    intro p
    change ω.value p = ω.value _
    apply congrArg ω.value
    apply Subtype.ext
    exact (congrArg Subtype.val (Map.inverse_apply (relativeTranslationToImage A i c)
      (relative_translation_to_image_bijective A i c hC) ⟨p.val,p.property⟩)).symm)

end IntegrationInACVF.Section7
