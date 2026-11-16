module

public import Integration7.CanonicalFocusLiftVolumeMaps
public import Integration7.RawVFVolumeComposition

@[expose] public section

/-! A full elementary focus gives an actual volume-preserving bijection
between the released RV lifts, with an arbitrary original RV density.
The elementary density is exactly its pullback along the old-label projection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (carrier Focus IsRVPullback canonicalImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n : ℕ}

theorem normalized_elementary_projection_labels {S : Set M}
    (U : @RVObject M (@CanonicalStructure.normalize M sM) S n) (i : Fin n)
    (u : @RVObject.domain M (@CanonicalStructure.normalize M sM) S n
      (@Section6.elementary M (@CanonicalStructure.normalize M sM)
        (@CanonicalStructure.normalized_model M sM hM) S n U i)) :
    (@Section6.elementaryProjection M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) S n U i u).val = u.val ∘ Fin.castAdd 1 := by
  have h := congrArg Subtype.val (@rvPack_unpack M (@CanonicalStructure.normalize M sM) S _ 1
    (@RVObject.domain M (@CanonicalStructure.normalize M sM) S n U)
    (@Section6.positiveRV M (@CanonicalStructure.normalize M sM) S) u)
  funext k
  exact (Fin.append_left _ _ k).symm.trans (congrFun h (Fin.castAdd 1 k))

def elementaryFocusFullLiftMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : @RVObject M (@CanonicalStructure.normalize M sM) (C.base : Set M) n}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n (@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)}
    (h : @Section6.PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U (normalizedPointSet A))
    {i : Fin n} {j : Fin (n+@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)} (D : Focus (canonicalImage A) i j)
    (hFull : carrier (canonicalImage A) ⊆ D.locus)
    (hAd : @Section6.Admissible M (@CanonicalStructure.normalize M sM) (C.base : Set M) n U i) :
    Map (rvLift (canonicalRVObject hc U))
      (rvLift (canonicalRVObject hc (@Section6.elementary M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U i))) :=
  let L := literalVolumeLiftMap hc (canonicalRVObject hc U) A (canonicalRVObject_presentsLift hc h)
  let E := @Section6.elementary M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U i
  let R := literalVolumeLiftMap hc (canonicalRVObject hc E) (typedLift E)
    (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents E))
  let hL := literalVolumeLiftMap_bijective hc (canonicalRVObject hc U) A (canonicalRVObject_presentsLift hc h)
  R.comp ((rawSpecialMap hc (canonicalFocusLiftMap h D hFull hAd)).comp (L.inverse hL))

theorem elementary_focus_full_lift_map_bijective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : @RVObject M (@CanonicalStructure.normalize M sM) (C.base : Set M) n}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n (@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)}
    (h : @Section6.PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U (normalizedPointSet A))
    {i : Fin n} {j : Fin (n+@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)} (D : Focus (canonicalImage A) i j)
    (hFull : carrier (canonicalImage A) ⊆ D.locus)
    (hAd : @Section6.Admissible M (@CanonicalStructure.normalize M sM) (C.base : Set M) n U i) (hA : IsRVPullback (carrier A)) :
    Function.Bijective (elementaryFocusFullLiftMap hc C h D hFull hAd) := by
  let L := literalVolumeLiftMap hc (canonicalRVObject hc U) A (canonicalRVObject_presentsLift hc h)
  let E := @Section6.elementary M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U i
  have hL := literalVolumeLiftMap_bijective hc (canonicalRVObject hc U) A (canonicalRVObject_presentsLift hc h)
  exact (literalVolumeLiftMap_bijective hc (canonicalRVObject hc E) (typedLift E)
    (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents E))).comp
    ((canonical_focus_lift_map_bijective h D hFull hAd hA).comp ((Equiv.ofBijective L hL).symm.bijective))

set_option maxHeartbeats 2000000 in
theorem elementary_focus_full_lift_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {U : @RVObject M (@CanonicalStructure.normalize M sM) (C.base : Set M) n}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n (@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)}
    (h : @Section6.PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U (normalizedPointSet A))
    {i : Fin n} {j : Fin (n+@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)} (D : Focus (canonicalImage A) i j)
    (hFull : carrier (canonicalImage A) ⊆ D.locus)
    (hAd : @Section6.Admissible M (@CanonicalStructure.normalize M sM) (C.base : Set M) n U i) (hA : IsRVPullback (carrier A))
    (ω : VolumeForm (canonicalRVObject hc U).domain) :
    PreservesVFVolume (ω.pullback (liftLabelMap (canonicalRVObject hc U)))
      ((ω.pullback (canonicalRawRVMap hc (@Section6.elementaryProjection M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U i))).pullback
        (liftLabelMap (canonicalRVObject hc (@Section6.elementary M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U i))))
      (elementaryFocusFullLiftMap hc C h D hFull hAd) := by
  let E := @Section6.elementary M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U i
  let L := literalVolumeLiftMap hc (canonicalRVObject hc U) A (canonicalRVObject_presentsLift hc h)
  let R := literalVolumeLiftMap hc (canonicalRVObject hc E) (typedLift E)
    (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents E))
  let F := rawSpecialMap hc (canonicalFocusLiftMap h D hFull hAd)
  have hL := literalVolumeLiftMap_bijective hc (canonicalRVObject hc U) A (canonicalRVObject_presentsLift hc h)
  let Ω := ω.pullback (liftLabelMap (canonicalRVObject hc U))
  let Ψ := (ω.pullback (canonicalRawRVMap hc (@Section6.elementaryProjection M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U i))).pullback
    (liftLabelMap (canonicalRVObject hc E))
  let ωA := Ω.pullback L
  let ωB := Ψ.pullback R
  have hmL : PreservesVFVolume ωA Ω L := literalVolumeLiftMap_preserves hc C _ A
    (canonicalRVObject_presentsLift hc h) hn ωA Ω (fun _ => rfl)
  have hmR : PreservesVFVolume ωB Ψ R := literalVolumeLiftMap_preserves hc C _ (typedLift E)
    (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents E)) hn ωB Ψ (fun _ => rfl)
  have hmF : PreservesVFVolume ωA ωB F :=
    canonical_focus_lift_preserves_volume hc C hn h D hFull hAd ωA ωB (by
      intro a b hab
      apply congrArg ω.value
      apply Subtype.ext
      have hp := normalized_elementary_projection_labels U i
        ⟨(liftLabelMap (canonicalRVObject hc E) (R b)).val,
          (liftLabelMap (canonicalRVObject hc E) (R b)).property⟩
      exact hab.symm.trans hp.symm)
  have hmI := preservesVFVolume_inverse hc C hn ωA Ω L hL hmL
  exact preservesVFVolume_comp hc C hn Ω ωB Ψ (F.comp (L.inverse hL)) R
    ((canonical_focus_lift_map_bijective h D hFull hAd hA).1.comp ((Equiv.ofBijective L hL).symm.bijective).1)
    (preservesVFVolume_comp hc C hn Ω ωA ωB (L.inverse hL) F ((Equiv.ofBijective L hL).symm.bijective).1 hmI hmF) hmR

end IntegrationInACVF.Section7
