import Integration7.VolumeLiftDescent
import Integration7.GammaAbsoluteValues
import Integration7.ScalarRVAlgebra
import IntegrationSection2.ConstructedGaussGraph
import IntegrationSection6.SmallVFFieldBases
import Section9.PrescribedVolumeLift

/-! The actual prescribed-Jacobian lift of a positive RV volume
isomorphism. Generation of the original VF/Gamma base is explicit;
the checked Section 2 construction supplies the graph-field input. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def volumeRatioMap {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential) :
    Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  rvScalarMul U.essentialForm.map
    ((rvInverse S).comp (V.essentialForm.map.comp (finiteIsoMap e)))

@[simp] theorem volumeRatioMap_value {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential) (u : U.essential.obj.domain) :
    (volumeRatioMap e u).val 0 = volumeRatio U V e u := by
  simp only [volumeRatioMap, rvScalarMul_value, rvInverse_value, Map.comp_apply,
    volumeRatio, VolumeForm.value, div_eq_mul_inv]

theorem RVVolumeIso.gamma_volumeRatio
    {U V : PositiveRVVolumeObject (M := M) S k} (e : RVVolumeIso U V)
    (u : U.essential.obj.domain) :
    Values.vrv (volumeRatio U V e.iso u) =
      (rvGammaJacobian (U.essential.obj.value u)
        (V.essential.obj.value (finiteIsoMap e.iso u))
        (U.essential_nonzero u) (V.essential_nonzero (finiteIsoMap e.iso u))).val := by
  apply (Values.paperValueEquiv (M := M)).injective
  change paperAbsoluteHom _ = paperAbsoluteHom _
  rw [paperAbsoluteHom_vrv, rvGammaJacobian_absolute]
  exact e.absolute_volumeRatio u

theorem RVVolumeIso.exists_preserving_lift
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    ∃ G : Map (rvLift U.essential.obj) (rvLift V.essential.obj),
      Function.Bijective G ∧
      (∀ p : rvLift U.essential.obj, (finiteIsoMap e.iso).graph p.val.2 (G p).val.2) ∧
      Section2.ConcreteVolumeForms.PreservesOff
        U.essentialForm.toSection2 V.essentialForm.toSection2 G := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  have hΓ : ∀ u : U.essential.obj.domain, Values.vrv ((volumeRatioMap e.iso u).val 0) =
      (rvGammaJacobian (U.essential.obj.value u)
        (V.essential.obj.value (finiteIsoMap e.iso u))
        (U.essential_nonzero u) (V.essential_nonzero (finiteIsoMap e.iso u))).val := by
    intro u
    rw [volumeRatioMap_value]
    exact e.gamma_volumeRatio u
  obtain ⟨D, _, hd, hD⟩ := e.rv
  have hRV : ∃ X : DefSet (rawRVSpace (M := M) U.essential.obj.arity) (C.base : Set M),
      rvDim X < k + 1 ∧ ∀ u : U.essential.obj.domain, u.val ∉ X.carrier →
        IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e.iso)).carrier
          (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e.iso u))
          ((volumeRatioMap e.iso u).val 0) :=
    ⟨D, hd, fun u hu => by rw [volumeRatioMap_value]; exact hD u hu⟩
  obtain ⟨G, hG, hlabel, Z, _, hz, hJ⟩ :=
    theorem_9_16_finite_volume_of_reference_input hc C Ξ hGenerated e.iso
      U.essential_nonzero V.essential_nonzero (volumeRatioMap e.iso) hΓ hRV
      Section2.ConstructedGaussGraph.acvf_graph_input
  refine ⟨G, hG, hlabel, Z, hz, ?_⟩
  intro p hp
  obtain ⟨J, hJ, hratio⟩ := hJ p hp
  have hlabels : liftLabelMap V.essential.obj (G p) =
      finiteIsoMap e.iso (liftLabelMap U.essential.obj p) := by
    obtain ⟨u, hu, hv⟩ := hlabel p
    have hsource : u = liftLabelMap U.essential.obj p := Subtype.ext hu
    apply Subtype.ext
    exact hv.symm.trans (congrArg (fun u => (finiteIsoMap e.iso u).val) hsource)
  refine ⟨J, hJ, ?_⟩
  change U.essentialForm.value (liftLabelMap U.essential.obj p) =
    V.essentialForm.value (liftLabelMap V.essential.obj (G p)) * CanonicalRV.encodedRv J
  rw [hlabels, hratio, volumeRatioMap_value, volumeRatio]
  exact (mul_div_cancel₀ _ (V.essentialForm_nonzero _)).symm

end IntegrationInACVF.Section7
