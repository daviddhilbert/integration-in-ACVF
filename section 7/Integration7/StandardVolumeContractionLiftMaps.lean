module

public import Integration7.VFStandardVolumeContractionObjects
public import Integration7.LiteralVolumeLiftMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The natural map of any specified standard contraction is an actual
definable bijection from the original volume object's density graph to
the lift of its contraction object. This interface asserts bijectivity;
the Jacobian comparison remains a separate theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def standardVolumeContractionLiftMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    Map U.domain (rvVolumeLift (U.standardContractionObject hc C Ξ T)).domain :=
  (literalVolumeLiftMap hc (U.standardContractionObject hc C Ξ T).underlying.obj
      (typedLift T.normalizedObject) (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents T.normalizedObject))).comp
    ((rawSpecialMap hc (typedContractionNaturalMap T)).comp (appendDensityMap U.form).toImage)

theorem standard_volume_contraction_lift_map_bijective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    Function.Bijective (standardVolumeContractionLiftMap hc C Ξ U T) :=
  (literalVolumeLiftMap_bijective hc (U.standardContractionObject hc C Ξ T).underlying.obj
    (typedLift T.normalizedObject) (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents T.normalizedObject))).comp
    ((typedContractionNaturalMap_bijective T).comp (appendDensityMap_toImage_bijective U.form))

theorem standard_volume_contraction_lift_dimension
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    vfDim (rawRVSpace (M := M) 1) (rvVolumeLift (U.standardContractionObject hc C Ξ T)).domain =
      vfDim (rawRVSpace (M := M) 1) U.domain :=
  (vfDim_eq_of_bijective (rawRVSpace (M := M) 1) (standardVolumeContractionLiftMap hc C Ξ U T)
    (standard_volume_contraction_lift_map_bijective hc C Ξ U T)).symm

end IntegrationInACVF.Section7
