import Section10.WeightedZero
import Section4.RVWeightRestriction

/-! Corollary 2.34 in the corrected measured degree zero. The supplied
ordinary label isomorphism is kept, and the actual determinant-one equation
implies exact preservation of its RV form at every point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section10 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section2.WeightedZeroVolumeDescent
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def labelMap {U V : MeasuredRVZero (M := M) S rvVolumeScale} (e : U.underlying ≅ V.underlying) :
    Map U.underlying.obj.domain V.underlying.obj.domain :=
  ((finiteVolumeProperty S 0).ι.mapIso e).hom.map

theorem labelMap_bijective {U V : MeasuredRVZero (M := M) S rvVolumeScale}
    (e : U.underlying ≅ V.underlying) : Function.Bijective (labelMap (U := U) (V := V) e) := by
  let E := (finiteVolumeProperty S 0).ι.mapIso e
  have h : Function.LeftInverse E.inv.map E.hom.map := SpecialTransformations.Section4.rvIso_inv_apply E
  have g : Function.RightInverse E.inv.map E.hom.map := SpecialTransformations.Section4.rvIso_inv_apply E.symm
  exact ⟨h.injective,g.surjective⟩

def corollary_2_34_zero_weighted (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVZero (M := M) S rvVolumeScale}
    (e : U.underlying ≅ V.underlying)
    (f : Map (rvLift U.underlying.obj) (rvLift V.underlying.obj))
    (hlabel : ∀ p, liftLabelMap V.underlying.obj (f p) =
      labelMap (U := U) (V := V) e (liftLabelMap U.underlying.obj p))
    (hMeasure : ∀ p, ∃ J : VFType (M := M), HasMixedVFJacobianAt f p J ∧
      (U.lift hc).weight p = (V.lift hc).weight (f p) * CanonicalRV.encodedRv J) : U ≅ V := by
  apply WeightedZero.isoOfExactMap
  refine ⟨labelMap e,labelMap_bijective e,?_⟩
  intro u
  let p := (liftLabelMap U.underlying.obj).inverse (liftLabelMap_zero_bijective U.underlying) u
  obtain ⟨J,hJ,hρ⟩ := hMeasure p
  have hJ1 : J = 1 := hJ.unique (hasMixedVFJacobianAt_zero_arity f p)
  rw [hJ1,RVOperations.rv_one,mul_one] at hρ
  change U.weight (liftLabelMap U.underlying.obj p) = V.weight (liftLabelMap V.underlying.obj (f p)) at hρ
  rw [hlabel] at hρ
  have hp : liftLabelMap U.underlying.obj p = u := Map.apply_inverse _ _ u
  rw [hp] at hρ
  exact hρ

@[simp] theorem corollary_2_34_zero_weighted_map (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVZero (M := M) S rvVolumeScale}
    (e : U.underlying ≅ V.underlying)
    (f : Map (rvLift U.underlying.obj) (rvLift V.underlying.obj))
    (hlabel : ∀ p, liftLabelMap V.underlying.obj (f p) = labelMap e (liftLabelMap U.underlying.obj p))
    (hMeasure : ∀ p, ∃ J : VFType (M := M), HasMixedVFJacobianAt f p J ∧
      (U.lift hc).weight p = (V.lift hc).weight (f p) * CanonicalRV.encodedRv J) :
    (corollary_2_34_zero_weighted hc e f hlabel hMeasure).hom.map = labelMap e := rfl

end IntegrationInACVF.Section2.WeightedZeroVolumeDescent
