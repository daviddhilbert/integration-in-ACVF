module

public import Integration7.NormalizedBasicVolumePresentation
public import Mathlib.Algebra.RingQuot

@[expose] public section

/-! An explicit two-relation ring presentation of the actual normalized
coefficient ring. This is the point = cone = 1 presentation after
normalization, not the still-open raw single-principal-ideal claim. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

abbrev RawRVVolumeRing := SemiringGroupification (RVVolumeIsoSemiring hc C)

inductive NormalizedBasicVolumeRelation : RawRVVolumeRing hc C → RawRVVolumeRing hc C → Prop
  | point : NormalizedBasicVolumeRelation
      (semiringGroupificationOf _ (volumeIsoSemiringClass hc C (n := 1)
        (degreeOnePointVolumeObject (C.base : Set M)))) 1
  | cone : NormalizedBasicVolumeRelation
      (semiringGroupificationOf _ (volumeIsoSemiringClass hc C (n := 1)
        (degreeOneConeVolumeObject (C.base : Set M)))) 1

abbrev NormalizedBasicVolumeQuotient := RingQuot (NormalizedBasicVolumeRelation hc C)

def normalizedBasicQuotientCoefficients : RVVolumeIsoSemiring hc C →+* NormalizedBasicVolumeQuotient hc C :=
  (RingQuot.mkRingHom (NormalizedBasicVolumeRelation hc C)).comp (semiringGroupificationOf _)

theorem normalized_basic_quotient_point :
    normalizedBasicQuotientCoefficients hc C
      (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) = 1 :=
  (RingQuot.mkRingHom_rel (NormalizedBasicVolumeRelation.point (hc := hc) (C := C))).trans (map_one _)

theorem normalized_basic_quotient_cone :
    normalizedBasicQuotientCoefficients hc C
      (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))) = 1 :=
  (RingQuot.mkRingHom_rel (NormalizedBasicVolumeRelation.cone (hc := hc) (C := C))).trans (map_one _)

def normalizedVolumeToBasicQuotient : NormalizedRVVolumeRing hc C →+* NormalizedBasicVolumeQuotient hc C :=
  normalizedBasicVolumeLift hc C (normalizedBasicQuotientCoefficients hc C)
    (normalized_basic_quotient_point hc C) (normalized_basic_quotient_cone hc C)

theorem normalized_basic_relation_map {x y : RawRVVolumeRing hc C}
    (h : NormalizedBasicVolumeRelation hc C x y) :
    semiringGroupificationLift (normalizedBasicVolumeMap hc C) x =
      semiringGroupificationLift (normalizedBasicVolumeMap hc C) y := by
  cases h with
  | point => rw [semiringGroupificationLift_of,map_one]; exact normalized_basic_volume_point hc C
  | cone => rw [semiringGroupificationLift_of,map_one]; exact normalized_basic_volume_cone hc C

def normalizedBasicQuotientToVolume : NormalizedBasicVolumeQuotient hc C →+* NormalizedRVVolumeRing hc C :=
  RingQuot.lift ⟨semiringGroupificationLift (normalizedBasicVolumeMap hc C),
    fun _ _ h => normalized_basic_relation_map hc C h⟩

theorem normalized_volume_to_basic_map (a : RVVolumeIsoSemiring hc C) :
    normalizedVolumeToBasicQuotient hc C (normalizedBasicVolumeMap hc C a) =
      normalizedBasicQuotientCoefficients hc C a :=
  normalized_basic_volume_lift_map hc C _ _ _ a

theorem normalized_basic_to_volume_map (a : RVVolumeIsoSemiring hc C) :
    normalizedBasicQuotientToVolume hc C (normalizedBasicQuotientCoefficients hc C a) =
      normalizedBasicVolumeMap hc C a := by
  change RingQuot.lift _ (RingQuot.mkRingHom _ (semiringGroupificationOf _ a)) = _
  rw [RingQuot.lift_mkRingHom_apply,semiringGroupificationLift_of]

theorem normalized_basic_quotient_left_inverse :
    Function.LeftInverse (normalizedBasicQuotientToVolume hc C) (normalizedVolumeToBasicQuotient hc C) := by
  have h : (normalizedBasicQuotientToVolume hc C).comp (normalizedVolumeToBasicQuotient hc C) =
      RingHom.id (NormalizedRVVolumeRing hc C) := by
    apply normalized_basic_volume_hom_ext hc C
    intro a
    change normalizedBasicQuotientToVolume hc C
      (normalizedVolumeToBasicQuotient hc C (normalizedBasicVolumeMap hc C a)) = _
    rw [normalized_volume_to_basic_map,normalized_basic_to_volume_map]
    rfl
  exact RingHom.congr_fun h

theorem normalized_basic_quotient_right_inverse :
    Function.RightInverse (normalizedBasicQuotientToVolume hc C) (normalizedVolumeToBasicQuotient hc C) := by
  have h : (normalizedVolumeToBasicQuotient hc C).comp (normalizedBasicQuotientToVolume hc C) =
      RingHom.id (NormalizedBasicVolumeQuotient hc C) := by
    apply RingQuot.ringQuot_ext
    apply semiringGroupification_hom_ext
    intro a
    change normalizedVolumeToBasicQuotient hc C
      (normalizedBasicQuotientToVolume hc C (normalizedBasicQuotientCoefficients hc C a)) = _
    rw [normalized_basic_to_volume_map,normalized_volume_to_basic_map]
    rfl
  exact RingHom.congr_fun h

def normalizedBasicVolumeQuotientEquiv : NormalizedRVVolumeRing hc C ≃+* NormalizedBasicVolumeQuotient hc C :=
  { normalizedVolumeToBasicQuotient hc C with
    invFun := normalizedBasicQuotientToVolume hc C
    left_inv := normalized_basic_quotient_left_inverse hc C
    right_inv := normalized_basic_quotient_right_inverse hc C }

end IntegrationInACVF.Section7
