import Integration7.GammaDefinableFamilies
import Integration7.HKZeroFamilyScalarProducts
import Integration7.HKZeroFamilyPositiveCoefficients

/-! **Rows of coefficient products of Gamma degree-zero families.** Gamma certificates for the
degree-zero scalar product `F • Z` of a degree-zero family, and Gamma row identifications for the
positive-coefficient product `U • F` and the scalar product `F • Z` of a degree-zero family `F`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open SpecialTransformations.Section4 (rawMixedSpace rawRVSpace)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {C : BaseContext M} {n a p : ℕ}

/-- **Degree-zero scalar products of Gamma degree-zero families are Gamma.** -/
theorem HK.ZeroVFVolumeFamily.Gamma.prodZero (hc : CanonicalStructure.IsCanonical (M := M))
    {F : HK.ZeroVFVolumeFamily C n a} (hF : F.Gamma G)
    {Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)} (hZ : Z.Gamma G) : (F.prodZero Z).Gamma G :=
  ⟨gamma_mixed_rv_factor_domain hF.domain hZ.domain,density_graph_of_volume_form_graph _
    (gamma_mixed_rv_factor_form_graph hc F.form Z.form hF.domain hZ.domain
      (volume_form_graph_of_density_graph F.form hF.densityGraph) hZ.density)⟩

/-- The row coefficient of a Gamma positive coefficient. -/
def positiveRowCoefficient (U : GammaVolumeObjects G (C.base : Set M) p) (x : Fin n → VFType (M := M)) :
    GammaVolumeObjects (rowGammaBase G x) ((vfParameterVolumeContext C x).base : Set M) p :=
  ⟨positiveVolumeCoefficientInContext U.val x,VolumeObjectGamma.changeBase (B := rowGammaBase G x)
    (U.property.extend _) (GammaBaseDominated.of_subset Set.subset_union_left (Set.Subset.refl _))⟩

set_option maxHeartbeats 800000 in
/-- Rows of the positive-coefficient product of a Gamma degree-zero family. -/
theorem gamma_zero_family_positive_product_row_class (hc : CanonicalStructure.IsCanonical (M := M))
    {F : HK.ZeroVFVolumeFamily C n a} (hF : F.Gamma G) (U : GammaVolumeObjects G (C.base : Set M) p)
    (x : Fin n → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ⟨(HK.selectedZeroFamilyPositiveProduct U.val F).rowInContext x,(hF.positiveProduct hc U.property).row hc x⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ⟨HK.zeroProduct (F.rowInContext x) (positiveRowCoefficient U x).val,
          VolumeObjectGamma.zeroProd hc (hF.row x) (positiveRowCoefficient U x).property⟩ := by
  let D := vfParameterVolumeContext C x
  let e1 := ((F.mulConstant U.val).selectionRowIso hc x).symm hc D
  let e2 := HK.zeroFamilyPositiveCoefficientRowIso hc F U.val x
  let e := e1.trans hc D e2
  have hv1 : ∀ w, (finiteIsoMap e1.iso w).val = w.val ∘ Fin.castAdd (p+1) := by
    intro w
    have h := congrArg Subtype.val (finiteIsoMap_apply_symm e1.iso.symm w)
    have hs := (F.mulConstant U.val).selectionRowMap_value x
      ⟨(finiteIsoMap e1.iso w).val,SpecialTransformations.Section9.rvEssentialLabels_subset _ (finiteIsoMap e1.iso w).property⟩
    funext i
    have hi := congrFun (h.symm.trans hs) (Fin.castAdd (p+1) i)
    simpa only [Fin.append_left,Function.comp_apply] using hi.symm
  have hv2 : ∀ w, (finiteIsoMap e2.iso w).val = w.val :=
    fun w => congrArg Subtype.val (finiteIsoMap_apply_symm e2.iso.symm w)
  have hv : ∀ w, (finiteIsoMap e.iso w).val = w.val ∘ Fin.castAdd (p+1) := by
    intro w
    change (finiteIsoMap (e1.iso.trans e2.iso) w).val = _
    rw [finiteIsoMap_trans]
    exact (hv2 _).trans (hv1 w)
  have hdom := gamma_essential_volume_domain _ ((hF.positiveProduct hc U.property).row hc x).coordinates
  apply (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
  exact GammaVolumeBlowupEquivalent.of_iso _ _ e (gamma_rv_coordinate_map hc _ (Fin.castAdd (p+1)) hdom hv)

/-- Rows of the degree-zero scalar product of a Gamma degree-zero family. -/
theorem gamma_zero_family_scalar_row_iso (hc : CanonicalStructure.IsCanonical (M := M))
    {F : HK.ZeroVFVolumeFamily C n a} (hF : F.Gamma G) (Z : HK.GammaZeroRVObjects G (C.base : Set M))
    (x : Fin n → VFType (M := M)) :
    (HK.zeroVolumeFamilyScalarRowIso F Z.val x).GammaDefinable (rowGammaBase G x) :=
  gamma_rv_coordinate_map hc _ id ((hF.prodZero hc Z.property).row x).domain (fun _ => rfl)

end IntegrationInACVF.Section7
