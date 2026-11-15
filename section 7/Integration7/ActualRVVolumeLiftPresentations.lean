import Integration7.CanonicalActualRVIdentifications
import Integration7.LiteralVolumeLiftMaps
import Integration7.PullbackCoordinateVolumeObjects
import IntegrationSection6.PresentationCoordinates

/-! A literal native lift of any actual RV volume object recovers that
object from its canonical pullback keys, including a retained density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (carrier rvObjectVolume pullbackObject pullbackObject_finiteVolume)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def actualRVVolumeLiftPresentation (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVObject (M := M) S n) := typedLift (normalizedActualRVObject hc U)

theorem actual_rv_volume_lift_presents (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVObject (M := M) S n) : PresentsLift U (actualRVVolumeLiftPresentation hc U) := by
  rw [← canonical_normalized_actual_rv_object hc U]
  exact canonicalRVObject_presentsLift hc (normalizedTypedLift_presents (normalizedActualRVObject hc U))

theorem actual_rv_volume_lift_finite_labels (hc : CanonicalStructure.IsCanonical (M := M))
    {k : ℕ} (U : PositiveRVVolumeObject (M := M) S k) :
    ∀ x : Fin (k+1) → SpecialTransformations.Section5.VF (M := M),
      {r : Fin U.underlying.obj.arity → SpecialTransformations.Section5.RV (M := M) |
        (x,r) ∈ carrier (actualRVVolumeLiftPresentation hc U.underlying.obj)}.Finite := by
  intro x
  change {r | (x,r) ∈ (rawSpecialSet hc (actualRVVolumeLiftPresentation hc U.underlying.obj)).carrier}.Finite
  rw [literalLift_carrier_eq hc U.underlying.obj _ (actual_rv_volume_lift_presents hc U.underlying.obj)]
  exact (rvVolumeLift U).finite_labels x

def actualRVVolumePullbackIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k : ℕ} (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (δ : Fin U.underlying.obj.arity) (hU : ∀ u, U.form.value u = u.val δ)
    (hδ : ∀ p : actualRVVolumeLiftPresentation hc U.underlying.obj, (p.val.2 δ).val ≠ iRVZero) :
    RVVolumeIso
      (pullbackCoordinateVolumeObject hc (actualRVVolumeLiftPresentation hc U.underlying.obj)
        (pullbackObject_finiteVolume _ (typedLift_pullback _) (actual_rv_volume_lift_finite_labels hc U)) δ hδ) U := by
  let A := actualRVVolumeLiftPresentation hc U.underlying.obj
  have h := normalizedTypedLift_presents (normalizedActualRVObject hc U.underlying.obj)
  let eN := pullbackPresentationIso h
  let eC := canonicalRVIso hc eN
  have heU : canonicalRVObject hc (normalizedActualRVObject hc U.underlying.obj) = U.underlying.obj :=
    canonical_normalized_actual_rv_object hc U.underlying.obj
  let eA : (canonicalFiniteRVObject hc ⟨pullbackObject A,
      pullbackObject_finiteVolume A (typedLift_pullback _) (actual_rv_volume_lift_finite_labels hc U)⟩) ≅ U.underlying := by
    apply rvFiniteIsoOfAmbient
    exact eC.trans (eqToIso heU)
  apply RVVolumeIso.of_preserving_coordinates_full hc C eA
  · intro u
    have hu := (Set.ext_iff.mp (normalizedPresentsLift_key_domains h) u.val).mp u.property
    exact @canonicalRVKeyIso_inv_volume M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) (k+1)
      (normalizedActualRVObject hc U.underlying.obj) ⟨u.val,hu⟩
  · intro u
    rw [hU]
    exact congrFun (pullbackPresentationIso_labels h ⟨u.val,u.property⟩) δ

end IntegrationInACVF.Section7
