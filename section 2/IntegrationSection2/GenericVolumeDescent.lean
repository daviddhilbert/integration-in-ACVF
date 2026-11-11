import IntegrationSection2.ConcreteVolumeForms
import IntegrationSection2.LiftFibreAvoidance
import IntegrationSection2.VolumeCharacteristic
import Section9.PaperLiftComparison

/-! The generic RV part of volume descent, on the actual full-base
finite-volume category. A fixed label fibre escapes the actual
VF-small measure exception; uniqueness then identifies the two
actual partial Jacobians. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section2.ConcreteVolumeForms

namespace IntegrationInACVF.Section2.GenericVolumeDescent

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}

theorem generic_equation (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hk : 0 < k)
    {U V : RVFiniteObject (M := M) (C.base : Set M) k} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (ω : RVForm U) (π : RVForm V)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) k).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2)
    (hMeasure : PreservesOff ω π f) (hgraph : HenselizedGaussGraphInput (VFType (M := M))) :
    let E := (finiteVolumeProperty (C.base : Set M) k).ι.mapIso e
    ∃ D : DefSet (rawRVSpace (M := M) k) (C.base : Set M),
      D.carrier ⊆ U.obj.volume.image.carrier ∧ rvDim D < k ∧
      ∀ u : U.obj.domain, U.obj.value u ∉ D.carrier →
        IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
          (U.obj.value u) (V.obj.value (E.hom.map u))
          (value ω u / value π (E.hom.map u)) := by
  letI := VolumeCharacteristic.charZero C.model00
  let E := (finiteVolumeProperty (C.base : Set M) k).ι.mapIso e
  obtain ⟨D,hD,hDim,hJ⟩ := lemma_9_15_finite_volume_of_reference_input hc C hk e hU hV f hf hlabel hgraph
  obtain ⟨Z,hZ,hMeasure⟩ := hMeasure
  obtain ⟨Γ,_,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI : Valued (VFType (M := M)) Γ := Valued.mk' v
  refine ⟨D,hD,hDim,fun u hu => ?_⟩
  obtain ⟨p,hpu,hpZ⟩ := LiftFibreAvoidance.exists_outside (Γ := Γ) hc C.saturated C.small hv U.obj u (hU u) Z hZ
  have hsource : liftLabelMap U.obj p = u := Subtype.ext hpu
  have htarget : liftLabelMap V.obj (f p) = E.hom.map u := by
    apply Subtype.ext
    have he := (E.hom.map.graph_apply (liftLabelMap U.obj p) (f p).val.2).mp (hlabel p)
    exact he.symm.trans (congrArg Subtype.val (congrArg E.hom.map hsource))
  obtain ⟨J,hJF,hJR⟩ := hJ p (by simpa only [hsource] using hu)
  obtain ⟨K,hKF,hK⟩ := hMeasure p hpZ
  have hEq : J = K := hJF.unique hKF
  have hvol : value ω u = value π (E.hom.map u) * CanonicalRV.encodedRv J := by
    simpa only [liftedValue_eq,hsource,htarget,hEq] using hK
  have hr : CanonicalRV.encodedRv J = value ω u / value π (E.hom.map u) := by
    apply (eq_div_iff (value_ne_zero π (E.hom.map u))).mpr
    exact (mul_comm _ _).trans hvol.symm
  simpa only [hsource,hr] using hJR

end IntegrationInACVF.Section2.GenericVolumeDescent
