module

public import Integration7.RectangleFamilyHeadOrderCertificates
public import Integration7.IndependentRectangleFamilyContractions
public import Integration7.NativeRawRVMapTransfers
public import Integration7.RVLabelConstraintHeadCoordinates
public import Section4.RVIsoTools

@[expose] public section

/-! The actual raw RV objects of the two rectangle-family contractions
are isomorphic with both VF volume coordinates preserved literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {H : SpecialTransformations.Section5.DefSet (M := M) S 2 m}
variable {hRect : RectangularRVFibres (SpecialTransformations.Section5.carrier H)}

def rawOrderMap (F : IndependentRectangleFamilyPreparations G H hRect)
    (hc : CanonicalStructure.IsCanonical (M := M)) :
    Map (canonicalRVObject hc F.headContraction.contractionObject).domain
      (canonicalRVObject hc F.tailContraction.contractionObject).domain :=
  canonicalNativeRawRVMapTransfer hc F.headOrderMap

theorem raw_order_map_bijective (F : IndependentRectangleFamilyPreparations G H hRect)
    (hc : CanonicalStructure.IsCanonical (M := M)) : Function.Bijective (F.rawOrderMap hc) :=
  canonical_native_raw_rv_map_transfer_bijective hc F.headOrderMap F.head_order_bijective

theorem raw_order_map_gamma (F : IndependentRectangleFamilyPreparations G H hRect)
    (hc : CanonicalStructure.IsCanonical (M := M)) : RVMapGamma (F.rawOrderMap hc) G :=
  canonical_native_raw_rv_map_transfer_gamma hc F.headOrderMap F.head_order_graph_gamma

theorem raw_order_map_volume (F : IndependentRectangleFamilyPreparations G H hRect)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (u : (canonicalRVObject hc F.headContraction.contractionObject).domain) :
    (canonicalRVObject hc F.tailContraction.contractionObject).value (F.rawOrderMap hc u) =
      (canonicalRVObject hc F.headContraction.contractionObject).value u := by
  let p := rawLabelImageInverse (headImage F.headLift.target) ⟨u.val,u.property⟩
  let q := F.headOrderMap p
  have hp : p.val.2 = u.val := raw_label_image_inverse_labels _ _
  have hq : q.val.2 = (F.rawOrderMap hc u).val := rfl
  have hv := congrArg Subtype.val (F.head_order_square p)
  have hE := congrArg (fun z : SpecialTransformations.Section5.Point (M := M) 0 (1+F.tailArity) ×
    SpecialTransformations.Section5.Point (M := M) 0 (1+F.headArity) => z.1.2) hv
  have hD := congrArg (fun z : SpecialTransformations.Section5.Point (M := M) 0 (1+F.tailArity) ×
    SpecialTransformations.Section5.Point (M := M) 0 (1+F.headArity) => z.2.2) hv
  change q.val.2 ∘ F.tailLift.headParameters = p.val.2 ∘ F.headLift.headProjection at hE
  change q.val.2 ∘ F.tailLift.headProjection = p.val.2 ∘ F.headLift.headParameters at hD
  funext i
  change (F.rawOrderMap hc u).val (F.tailContraction.volumeIndex i) = u.val (F.headContraction.volumeIndex i)
  rw [← hp,← hq]
  fin_cases i
  · have h : q.val.2 0 = p.val.2 (F.headLift.headParameters 0) := by
      exact (congrArg q.val.2 F.tailLift.head_projection_zero).symm.trans (congrFun hD 0)
    exact (congrArg q.val.2 F.tail_volume_first).trans (h.trans (F.head_volume_first p).symm)
  · have h : q.val.2 (F.tailLift.headParameters 0) = p.val.2 0 := by
      exact (congrFun hE 0).trans (congrArg p.val.2 F.headLift.head_projection_zero)
    exact (F.tail_volume_second q).trans (h.trans (congrArg p.val.2 F.head_volume_second.symm))

def rawOrderRVIso (F : IndependentRectangleFamilyPreparations G H hRect)
    (hc : CanonicalStructure.IsCanonical (M := M)) :
    canonicalRVObject hc F.headContraction.contractionObject ≅
      canonicalRVObject hc F.tailContraction.contractionObject :=
  rvIsoOfVolumePreservingBijection (F.rawOrderMap hc) (F.raw_order_map_bijective hc) (F.raw_order_map_volume hc)

end IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
