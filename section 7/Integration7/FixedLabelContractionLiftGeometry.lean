module

public import Integration7.FixedLabelContractionVolumeObjects
public import Integration7.LiteralVolumeLiftMaps
public import Integration7.VolumeLiftFullDimension
public import Integration7.EssentialEmptyVolumeIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual normalized contraction lifts of fixed-label mixed domains have
their original VF dimension. VF-small domains therefore have no essential
labels, independently of the specified contraction order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV GammaSetDefinable carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {n d : ℕ} {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk P.real < κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (hPC : P.real ⊆ (C.base : Set M))
variable (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) 0)
variable (hA : GammaSetDefinable P (carrier A))
variable (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
variable (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
variable (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
variable {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction (fixedRVLabelDomain A z hz) σ)
variable (hT : GammaProgramDefinable P T.program)

def fixedLabelContractionLiftMap :
    Map (rawSpecialSet hc (fixedRVLabelDomain A z hz))
      (rvVolumeLift (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT).val).domain :=
  (literalVolumeLiftMap hc (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT).val.underlying.obj
      (typedLift T.normalizedObject) (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents T.normalizedObject))).comp
    (rawSpecialMap hc (typedContractionNaturalMap T))

theorem fixed_label_contraction_lift_map_bijective :
    Function.Bijective (fixedLabelContractionLiftMap hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT) :=
  (literalVolumeLiftMap_bijective hc (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT).val.underlying.obj
    (typedLift T.normalizedObject) (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents T.normalizedObject))).comp
    (typedContractionNaturalMap_bijective T)

theorem fixed_label_contraction_lift_dimension :
    vfDim (rawRVSpace (M := M) 1)
      (rvVolumeLift (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT).val).domain =
    vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc (fixedRVLabelDomain A z hz)) :=
  (vfDim_eq_of_bijective (rawRVSpace (M := M) 1)
    (fixedLabelContractionLiftMap hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT)
    (fixed_label_contraction_lift_map_bijective hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT)).symm

theorem fixed_label_contraction_essential_empty_of_small_dimension
    (hsmall : vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc (fixedRVLabelDomain A z hz)) < n+1) :
    (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT).val.essential.obj.domain.carrier = ∅ := by
  apply essential_empty_of_volume_lift_small_dimension hc C
  rw [fixed_label_contraction_lift_dimension]
  exact hsmall

theorem small_dimension_fixed_label_contractions_compare
    (hsmall : vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc (fixedRVLabelDomain A z hz)) < n+1)
    {τ : Equiv.Perm (Fin (n+1))} (E : StandardContraction (fixedRVLabelDomain A z hz) τ)
    (hE : GammaProgramDefinable P E.program) :
    GammaVolumeBlowupEquivalent P (C.base : Set M) n
      (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT)
      (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 E hE) := by
  have hU := fixed_label_contraction_essential_empty_of_small_dimension hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT hsmall
  have hV := fixed_label_contraction_essential_empty_of_small_dimension hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 E hE hsmall
  let e := RVVolumeIso.of_essential_empty hc C _ _ hU hV
  exact GammaVolumeBlowupEquivalent.of_iso C P e (gamma_volume_iso_of_essential_empty e hU)

end IntegrationInACVF.Section7
