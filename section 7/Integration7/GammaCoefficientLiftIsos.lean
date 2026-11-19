import Integration7.GammaFunAppendedFullLifts
import Integration7.SelectedPositiveCoefficientLiftBijections

/-! **Gamma coefficient lift isomorphism.** For a Gamma positive RV coefficient `U` and a Gamma
selected family `F`, the actual volume bijection from the appended full lift of the
coefficient-first product `U • F` to the product of the lift of `U` with the appended full lift of
`F` has a Gamma graph. Each of its three factors acts on coordinates by an explicit selection of RV
labels, which is certified directly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open SpecialTransformations.Section4 (rawMixedSpace)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M}

/-- A mixed map acting by a fixed RV label selection and the identity on VF coordinates has a
Gamma graph on a Gamma source. -/
theorem vf_rv_coordinate_map_gamma {k a b : ℕ} {A : DefSet (rawMixedSpace (M := M) (k+1) a) S}
    {D : DefSet (rawMixedSpace (M := M) (k+1) b) S} (f : Map A D) (τ : Fin b → Fin a)
    (hf : ∀ x, (f x).val = (x.val.1,x.val.2 ∘ τ)) (hA : GammaSetDefinable G A.carrier) :
    GammaGraphDefinable G (vfMixedMapGraph f) := by
  have L := gammaLogicInput G
  have hg := gamma_global_map_graph (B := G) (mixedCoordinatePointMap (id : Fin (k+1) → Fin (k+1)) τ G.real)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.restrict_graph hA hg)
  intro p q
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl,hf _⟩
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨u.property,(hf u).symm⟩

theorem gamma_vf_reindex_domain {i j : ℕ} {U : PositiveVFVolumeObject (M := M) S j} (h : i = j)
    (hU : GammaSetDefinable G U.domain.carrier) : GammaSetDefinable G (U.reindexDegree h).domain.carrier := by
  cases h
  exact hU

theorem VFBijGamma.reindexDegree {i j : ℕ} {U V : PositiveVFVolumeObject (M := M) S j}
    {f : VFVolumeBijection U V} (hf : VFBijGamma f G) (h : i = j) : VFBijGamma (f.reindexDegree h) G := by
  cases h
  exact hf

/-- **Appended full lifts of Gamma families are Gamma.** -/
theorem SelectedVFVolumeFamily.Gamma.appendedFullLift (hc : CanonicalStructure.IsCanonical (M := M))
    {C : BaseContext M} {n a k : ℕ} {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) :
    VFVolumeObjectGamma F.appendedFullLift G :=
  ((hF.fullLift hc).reindexDegree (appended_family_lift_degree_eq n k)).permuteVF hc C
    (appendedToOriginalVolumePermutation n k).symm

set_option maxHeartbeats 1600000 in
/-- **The coefficient lift isomorphism is Gamma.** -/
theorem selected_positive_coefficient_appended_lift_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hGC : G.real ⊆ (C.base : Set M)) {n a k p : ℕ}
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p} (hU : VolumeObjectGamma U G)
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) :
    (VFVolumeIso.of_bijection (selectedPositiveCoefficientAppendedLiftBijection hc U F)).GammaDefinable G := by
  let h := appended_positive_coefficient_degree_eq n p k
  have hS : VFVolumeObjectGamma (selectedVolumeFamilyLeftProduct U F).appendedFullLift G :=
    (hF.leftProduct hc hU).appendedFullLift hc
  have hLU := rv_volume_lift_gamma hc C hGC hU
  have hFA := hF.appendedFullLift hc
  have hP : VFVolumeObjectGamma (((rvVolumeLift U).prod F.appendedFullLift).reindexDegree h) G :=
    (hLU.prod hc hFA).reindexDegree h
  have hB : VFBijGamma (definableVolumeFamilyAppendedSelectionBijection hc (F.toDefinable.mulConstant U)) G :=
    vf_rv_coordinate_map_gamma _ (Fin.castAdd (((p+1)+k)+1)) (fun _ => rfl) hS.domain
  have hDA : GammaSetDefinable G F.toDefinable.appendedFullLift.domain.carrier := by
    rw [← selected_to_definable_appended_lift_carrier F]
    exact hFA.domain
  have hAsrc : GammaSetDefinable G (appendedCoefficientVFProduct F.toDefinable U).domain.carrier :=
    gamma_vf_reindex_domain h (gamma_mixed_product_domain hLU.domain hDA)
  have hA : VFBijGamma (appendedCoefficientLiftProductBijection hc F.toDefinable U) G :=
    vf_rv_coordinate_map_gamma _ (finAddFlip : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a))
      (fun _ => rfl) hAsrc
  have hE0 : VFBijGamma ((VFVolumeBijection.refl hc C (rvVolumeLift U)).prod hc
      (selectedToDefinableAppendedLiftBijection hc F)) G :=
    gamma_positive_vf_volume_product_map_graph (vf_identity_map_gamma _ (fun _ => rfl) hLU.domain)
      (vf_identity_map_gamma _ (fun _ => rfl) hFA.domain) hLU.domain hFA.domain
  have hE := hE0.reindexDegree h
  refine ⟨hS.domain,hP.domain,?_⟩
  exact hB.trans hc C ((hA.symm hc C).trans hc C (hE.symm hc C))

end IntegrationInACVF.Section7
