import IntegrationSection6.GammaObjectPresentationIsomorphisms
import IntegrationSection6.GammaVFContractiblePullbackMaps
import IntegrationSection6.FiniteGammaPresentationCharts
import IntegrationSection6.GammaUnivPresentations

/-! In degree zero, an isomorphism of the lifts already induces an actual
Gamma RV[0] isomorphism. No blowup or saturation argument is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b : ℕ}

theorem vf_zero_map_contractible {U : DefSet (M := M) S 0 a} {V : DefSet (M := M) S 0 b}
    (f : Map U V) : Contractible f := by
  intro u v huv
  have he : u = v := Subtype.ext (Prod.ext (funext fun i => Fin.elim0 i) ((sameRV_iff _ _).mp huv).2)
  subst v
  rfl

def gamma_zero_lift_iso (U V : GammaRVFiniteObject B 0) (e : GammaIso B U.lift V.lift) :
    GammaRVIso U.toGammaRVObject V.toGammaRVObject := by
  let UA := gammaUniversalObject U
  let VA := gammaUniversalObject V
  let A := typedLift UA.object.obj
  let C := typedLift VA.object.obj
  have hA : GammaSetDefinable B (carrier A) := by rw [typedLift_carrier]; exact U.toGammaRVObject.lift_definable
  have hC : GammaSetDefinable B (carrier C) := by rw [typedLift_carrier]; exact V.toGammaRVObject.lift_definable
  let e' := e.congr (typedLift_carrier UA.object.obj).symm (typedLift_carrier VA.object.obj).symm
  let f : Map A C := Map.mk e'.equiv (gammaGraph_univ_definable e'.graph)
  let P := gammaPresentationAt UA (normalizedTypedLift_presents UA.object.obj) hA
  let Q := gammaPresentationAt VA (normalizedTypedLift_presents VA.object.obj) hC
  let d := gammaVFContractiblePullbackIso (Set.subset_univ _) hA hC P.object.property Q.object.property
    f e'.equiv.bijective (vf_zero_map_contractible f) (vf_zero_map_contractible (Map.inverse f e'.equiv.bijective))
    e'.graph (fun _ => funext fun i => Fin.elim0 i)
  let p := (gammaPresentationIsoAt UA (normalizedTypedLift_presents UA.object.obj) hA).toGamma
  let q := (gammaPresentationIsoAt VA (normalizedTypedLift_presents VA.object.obj) hC).toGamma
  let z := gammaIsoTrans (gammaIsoSymm p) (gammaIsoTrans d q)
  exact gammaIsoTrans (gammaObjectPresentationIso U (Set.subset_univ _))
    (gammaIsoTrans z (gammaIsoSymm (gammaObjectPresentationIso V (Set.subset_univ _))))

end IntegrationInACVF.Section6.FiniteRV
