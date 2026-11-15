import Integration7.OrdinaryUnitSelectedVolumeFamilies
import Integration7.AEOrdinaryPositiveCoefficientProducts
import Integration7.BasicVolumeRelationObjects

/-! The ordinary family's unit selected presentation is the actual
positive point-coefficient product on every named row. The graph carriers,
volume coordinates and densities are compared directly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}
variable (F : OrdinaryVFVolumeFamily C (n+1) a)

private theorem point_product_domain_carrier :
    (F.mulConstant (degreeOnePointVolumeObject (C.base : Set M))).domain.carrier=F.domain.carrier := by
  change (mixedRVFactorDomain F.domain (DefSet.univ (rawRVSpace (M := M) 0) (C.base : Set M))).carrier=F.domain.carrier
  ext ⟨x,r⟩
  rw [mem_mixed_rv_factor_domain]
  have hId : r ∘ Fin.castAdd 0=r := funext (fun i => congrArg r (Fin.ext rfl))
  rw [hId]
  exact and_iff_left (Set.mem_univ _)

theorem ordinary_unit_selected_point_product_carrier : F.unitSelectedFamily.domain.carrier =
    (selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F).domain.carrier := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  have hVol (q : (F.mulConstant P).domain) : ((F.mulConstant P).volume q).val=fun _ => 1 := rfl
  ext p
  constructor
  · rintro ⟨q,hq⟩
    let s : (F.mulConstant P).domain := ⟨q.val,(Set.ext_iff.mp (point_product_domain_carrier F) q.val).mpr q.property⟩
    refine ⟨s,?_⟩
    change (s.val.1,Fin.append s.val.2 ((F.mulConstant P).volume s).val)=p
    rw [hVol]
    exact hq
  · rintro ⟨s,hs⟩
    let q : F.domain := ⟨s.val,(Set.ext_iff.mp (point_product_domain_carrier F) s.val).mp s.property⟩
    refine ⟨q,?_⟩
    change (s.val.1,Fin.append s.val.2 ((F.mulConstant P).volume s).val)=p at hs
    rw [hVol] at hs
    exact hs

theorem ordinary_point_product_row_coordinates (x : Fin (n+1) → VFType (M := M))
    (r : ((selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F).rowInContext x).underlying.obj.domain) :
    ((selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F).rowInContext x).underlying.obj.value r =
      fun _ => 1 := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  let G := F.mulConstant P
  let q : G.toSelected.domain := ⟨(x,r.val),r.property⟩
  exact (mixed_rv_map_graph_retained_tuple G.volume q).symm.trans rfl

def ordinaryUnitSelectedPointRowIso (hc : CanonicalStructure.IsCanonical (M := M))
    (x : Fin (n+1) → VFType (M := M)) :
    RVVolumeIso (F.unitSelectedFamily.rowInContext x)
      ((selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F).rowInContext x) := by
  let U := F.unitSelectedFamily.rowInContext x
  let V := (selectedOrdinaryFamilyPositiveProduct (degreeOnePointVolumeObject (C.base : Set M)) F).rowInContext x
  have hUV : U.underlying.obj.domain.carrier=V.underlying.obj.domain.carrier := by
    ext r
    exact Set.ext_iff.mp (ordinary_unit_selected_point_product_carrier F) (x,r)
  have hCoord (u : U.underlying.obj.domain) : V.underlying.obj.value ⟨u.val,hUV.le u.property⟩=U.underlying.obj.value u :=
    (ordinary_point_product_row_coordinates F x _).trans (ordinary_unit_selected_row_coordinates F x u).symm
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := V.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain U.underlying.obj.volume V.underlying.obj.volume hUV hCoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x) e hCoord (fun _ => rfl)
end IntegrationInACVF.Section7
