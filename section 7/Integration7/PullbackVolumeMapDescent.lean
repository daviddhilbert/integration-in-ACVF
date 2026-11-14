import Integration7.RawPullbackVolumeLifts
import Integration7.RawVFVolumeComposition
import Integration7.FullLiftVolumeDescent

/-! A volume-preserving map of actual RV-pullbacks descends along its
compatible RV key isomorphism. The full lift map is constructed by conjugating
with canonical pullback presentations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (pullbackObject rvObjectVolume rvObjectDomain rawKeyMap IsRVPullback carrier)

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

def pullbackVolumeIsoOfCompatibleMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k a b : ℕ}
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) b)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hAF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (hBF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject B)))
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (e : pullbackObject A ≅ pullbackObject B)
    (hlabel : ∀ p : A,
      (@RVHom.map M N (C.base : Set M) (k+1) (pullbackObject A) (pullbackObject B) e.hom)
        (SpecialTransformations.Section5.Map.toImage (rawKeyMap A) p) =
          SpecialTransformations.Section5.Map.toImage (rawKeyMap B) (f p))
    (hMeasure : PreservesVFVolume (rawPullbackVolumeForm hc A hA hAF δ hδ)
      (rawPullbackVolumeForm hc B hB hBF ε hε) (rawSpecialMap hc f)) :
    RVVolumeIso (pullbackCoordinateVolumeObject hc A hAF δ hδ)
      (pullbackCoordinateVolumeObject hc B hBF ε hε) := by
  let U := pullbackCoordinateVolumeObject hc A hAF δ hδ
  let V := pullbackCoordinateVolumeObject hc B hBF ε hε
  let gA := rawPullbackVolumeLiftMap hc A hA
  let gB := rawPullbackVolumeLiftMap hc B hB
  have hgA := rawPullbackVolumeLiftMap_bijective hc A hA
  have hgB := rawPullbackVolumeLiftMap_bijective hc B hB
  let g := gB.comp ((rawSpecialMap hc f).comp (gA.inverse hgA))
  have hgAi : Function.Bijective (gA.inverse hgA) :=
    ⟨fun p q h => by
      have he := congrArg gA h
      simpa only [Map.apply_inverse] using he,
      fun p => ⟨gA p, Map.inverse_apply _ _ p⟩⟩
  have hg : Function.Bijective g := hgB.comp (hf.comp hgAi)
  let eC : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient (canonicalRVIso hc e)
  have hgl : ∀ p, liftLabelMap V.underlying.obj (g p) =
      finiteIsoMap eC (liftLabelMap U.underlying.obj p) := by
    intro p
    let q := gA.inverse hgA p
    have hq : gA q = p := Map.apply_inverse _ _ p
    rw [← hq]
    change liftLabelMap V.underlying.obj (g (gA q)) = _
    have he : (gA.inverse hgA) (gA q) = q := Map.inverse_apply _ _ q
    change liftLabelMap V.underlying.obj
      (gB ((rawSpecialMap hc f) ((gA.inverse hgA) (gA q)))) = _
    rw [he]
    apply Subtype.ext
    exact (congrArg (fun u : rvObjectDomain (pullbackObject B) => u.val)
      (hlabel (show A from q))).symm
  have hAi := preservesVFVolume_inverse hc C (Nat.zero_lt_succ k)
    (rawPullbackVolumeForm hc A hA hAF δ hδ) (rvVolumeLift U).form gA hgA
    (rawPullbackVolumeLiftMap_preserves hc C A hA hAF δ hδ)
  have hmid := preservesVFVolume_comp hc C (Nat.zero_lt_succ k) (rvVolumeLift U).form
    (rawPullbackVolumeForm hc A hA hAF δ hδ) (rawPullbackVolumeForm hc B hB hBF ε hε)
    (gA.inverse hgA) (rawSpecialMap hc f) hgAi.1 hAi hMeasure
  have hm := preservesVFVolume_comp hc C (Nat.zero_lt_succ k) (rvVolumeLift U).form
    (rawPullbackVolumeForm hc B hB hBF ε hε) (rvVolumeLift V).form
    ((rawSpecialMap hc f).comp (gA.inverse hgA)) gB (hf.1.comp hgAi.1) hmid
    (rawPullbackVolumeLiftMap_preserves hc C B hB hBF ε hε)
  exact RVVolumeIso.of_preserving_full_lift hc C eC g hg hgl hm

end IntegrationInACVF.Section7
