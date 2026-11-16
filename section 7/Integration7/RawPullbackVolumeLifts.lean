module

public import Integration7.LiteralVolumeLiftMaps
public import Integration7.PullbackCoordinateVolumeObjects

@[expose] public section

/-! An actual RV-pullback is volume-isomorphic to the VF lift of its
canonical key object. Canonicalization keeps every VF coordinate and puts
the retained density in the corresponding old RV label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (pullbackObject rvObjectVolume IsRVPullback carrier)

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n a k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def rawPullbackVolumeLiftMap
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a)
    (hA : IsRVPullback (carrier A)) :
    Map (rawSpecialSet hc A) (rvLift (canonicalRVObject hc (pullbackObject A))) :=
  (literalVolumeLiftMap hc (canonicalRVObject hc (pullbackObject A))
    (SpecialTransformations.Section5.canonicalImage A)
    (canonicalRVObject_presentsLift hc (Section6.normalizedCanonicalImage_presents A hA))).comp
      (rawSpecialMap hc (SpecialTransformations.Section5.SpecialBijection.canonical A).toMap)

theorem rawPullbackVolumeLiftMap_value
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a)
    (hA : IsRVPullback (carrier A)) (p : rawSpecialSet hc A) :
    (rawPullbackVolumeLiftMap hc A hA p).val =
      (p.val.1, Fin.append (fun i => SpecialTransformations.Section5.rv (p.val.1 i)) p.val.2) := rfl

theorem rawPullbackVolumeLiftMap_bijective
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a)
    (hA : IsRVPullback (carrier A)) :
    Function.Bijective (rawPullbackVolumeLiftMap hc A hA) :=
  (literalVolumeLiftMap_bijective hc _ _
    (canonicalRVObject_presentsLift hc (Section6.normalizedCanonicalImage_presents A hA))).comp
    (SpecialTransformations.Section5.SpecialBijection.canonical A).bijective

def rawPullbackVolumeForm
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S (k+1) a)
    (hA : IsRVPullback (carrier A))
    (hFinite : @Map.FiniteFibres LRV M N _ _ S _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    VolumeForm (rawSpecialSet hc A) :=
  (rvVolumeLift (pullbackCoordinateVolumeObject hc A hFinite δ hδ)).form.pullback
    (rawPullbackVolumeLiftMap hc A hA)

theorem rawPullbackVolumeForm_density
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S (k+1) a)
    (hA : IsRVPullback (carrier A))
    (hFinite : @Map.FiniteFibres LRV M N _ _ S _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (p : rawSpecialSet hc A) :
    (rawPullbackVolumeForm hc A hA hFinite δ hδ).value p = p.val.2 δ := by
  change (liftLabelMap (canonicalRVObject hc (pullbackObject A))
    (rawPullbackVolumeLiftMap hc A hA p)).val (Fin.natAdd (k+1) δ) = p.val.2 δ
  change (rawPullbackVolumeLiftMap hc A hA p).val.2 (Fin.natAdd (k+1) δ) = p.val.2 δ
  rw [rawPullbackVolumeLiftMap_value]
  simp only [Fin.append_right]

theorem rawPullbackVolumeLiftMap_preserves
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (hA : IsRVPullback (carrier A))
    (hFinite : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    PreservesVFVolume (rawPullbackVolumeForm hc A hA hFinite δ hδ)
      (rvVolumeLift (pullbackCoordinateVolumeObject hc A hFinite δ hδ)).form
      (rawPullbackVolumeLiftMap hc A hA) := by
  apply (vfJacobianOne_of_preservesVF hc C (Nat.zero_lt_succ k)
    (rawPullbackVolumeLiftMap hc A hA) (fun _ => rfl)).mono
  intro p hJ
  exact ⟨1, hJ, by rw [RVOperations.rv_one, mul_one]; rfl⟩

end IntegrationInACVF.Section7
