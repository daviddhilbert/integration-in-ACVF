import Integration7.HKNormalizedVolumeSupports
import Integration7.HKNormalizedPositiveOperators
import Integration7.SupportedPositiveGradedRestrictions
import Integration7.SupportedPositiveGradedJacobians

/-! Restrict to an actual source domain, apply its genuine Jacobian
transform, then extend by zero. The positive-degree operator descends
to the complete corrected normalized function space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def restrictedPositiveGradedJacobian
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    Section7.PositiveDegreeGradedVolumeFunction hc C n →ₗ[Section7.RVVolumeBlowupSemiring hc C]
      Section7.PositiveDegreeGradedVolumeFunction hc C n :=
  (supportedPositiveGradedForgetShift hc C Y).comp
    ((supportedPositiveGradedJacobian hc C φ hφ).comp (positiveGradedVolumeRestriction hc C X))

theorem restricted_positive_graded_jacobian_of_supported
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : SupportedAERVVolumeFunction hc C X k) :
    restrictedPositiveGradedJacobian hc C φ hφ
      (DirectSum.of (fun j => Section7.AEVolumeFunctionComponent hc C n (j+1)) k
        (supportedVolumeFunctionForget hc C X f)) =
      DirectSum.of (fun j => Section7.AEVolumeFunctionComponent hc C n (j+1)) k
        (supportedVolumeFunctionForget hc C Y (supportedVolumeFunctionJacobian hc C φ hφ f)) := by
  change supportedPositiveGradedForgetShift hc C Y
    (supportedPositiveGradedJacobian hc C φ hφ (positiveGradedVolumeRestriction hc C X
      (DirectSum.of (fun j => Section7.AEVolumeFunctionComponent hc C n (j+1)) k
        (supportedVolumeFunctionForget hc C X f)))) = _
  rw [positive_graded_volume_restriction_of,ae_volume_restriction_forget_supported,
    supported_positive_graded_jacobian_of]
  exact graded_component_map_to_sum_of (fun j => supportedVolumeFunctionForgetAddHom (k := j) hc C Y) k _

def normalizedRestrictedVolumeJacobian
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  normalizedVolumeOperatorFromPositive hc C n n (restrictedPositiveGradedJacobian hc C φ hφ)

theorem normalized_restricted_volume_jacobian_positive
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : SupportedAERVVolumeFunction hc C X k) :
    normalizedRestrictedVolumeJacobian hc C φ hφ
      (normalizedPositiveVolumeFunction hc C n k (supportedVolumeFunctionForget hc C X f)) =
      normalizedPositiveVolumeFunction hc C n k
        (supportedVolumeFunctionForget hc C Y (supportedVolumeFunctionJacobian hc C φ hφ f)) := by
  let L := restrictedPositiveGradedJacobian hc C φ hφ
  let g := supportedVolumeFunctionForget hc C Y (supportedVolumeFunctionJacobian hc C φ hφ f)
  have h := normalized_volume_operator_from_positive_generator hc C n n L
    (DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) k (supportedVolumeFunctionForget hc C X f))
  have hSource := graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C n) 1 k
    (supportedVolumeFunctionForget hc C X f)
  have hImage : L (DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) k
      (supportedVolumeFunctionForget hc C X f)) =
      DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) k g :=
    restricted_positive_graded_jacobian_of_supported hc C φ hφ f
  have hTarget := graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C n) 1 k g
  exact (congrArg (fun v => normalizedVolumeOperatorFromPositive hc C n n L
    (normalizedVolumeFunctionGenerator hc C n v)) hSource).symm.trans
      (h.trans ((congrArg (fun v => normalizedVolumeFunctionGenerator hc C n
        (gradedShiftToSum (F := AEVolumeFunctionComponent hc C n) 1 v)) hImage).trans
          (congrArg (normalizedVolumeFunctionGenerator hc C n) hTarget)))

end IntegrationInACVF.Section7.HK
