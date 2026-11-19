import Integration7.GammaFunPositiveLinearity
import Integration7.HKSelectedFamilyWeightedZeroProducts
import Integration7.GammaNamedZeroBlowupProducts

/-! **Weighted degree-zero coefficients on Gamma-named positive functions.** The weighted
degree-zero product `F • Z` of a selected family with a degree-zero RV volume object (the raw
`selectedFamilyWeightedZeroProduct`) is Gamma when both factors are. -/
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a b k : ℕ}

theorem gamma_mixed_rv_factor_domain {A : DefSet (rawMixedSpace (M := M) n a) S} {Z : DefSet (rawRVSpace (M := M) b) S}
    (hA : GammaSetDefinable G A.carrier) (hZ : GammaSetDefinable G {p : Point (M := M) 0 b | p.2 ∈ Z.carrier}) :
    GammaSetDefinable G (mixedRVFactorDomain A Z).carrier := by
  have L := gammaLogicInput G
  have h1 := gamma_mixed_coordinate_preimage hA (id : Fin n → Fin n) (Fin.castAdd b : Fin a → Fin (a+b))
  have h2 := gamma_mixed_coordinate_preimage hZ (Fin.elim0 : Fin 0 → Fin n) (Fin.natAdd a : Fin b → Fin (a+b))
  convert L.inter h1 h2 using 1
  ext q
  exact mem_mixed_rv_factor_domain A Z q.1 q.2

variable {C : BaseContext M}

theorem weighted_zero_product_density (F : SelectedVFVolumeFamily C n a k)
    (Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M))
    (q : (HK.selectedFamilyWeightedZeroProduct F Z).domain) :
    (HK.selectedFamilyWeightedZeroProduct F Z).form.value q =
      F.form.value ⟨_,((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.val.1 q.val.2).mp q.property).1⟩ *
        Z.form.value ⟨_,((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.val.1 q.val.2).mp
          q.property).2⟩ := by
  have hv := mixed_rv_factor_unpack_value F.domain Z.underlying.obj.domain q
  change (F.form.prod Z.form).value (mixedRVFactorUnpack F.domain Z.underlying.obj.domain q) = _
  have hu : mixedRVFactorUnpack F.domain Z.underlying.obj.domain q =
      ⟨((q.val.1,q.val.2 ∘ Fin.castAdd Z.underlying.obj.arity),q.val.2 ∘ Fin.natAdd a),
        ((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.val.1 q.val.2).mp q.property).1,
        ((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.val.1 q.val.2).mp q.property).2⟩ :=
    Subtype.ext hv
  rw [hu]
  rfl

set_option maxHeartbeats 1600000 in
theorem gamma_weighted_zero_product_form_graph (hc : CanonicalStructure.IsCanonical (M := M))
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G)
    {Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)} (hZ : Z.Gamma G) :
    GammaGraphDefinable G (volumeFormGraph (HK.selectedFamilyWeightedZeroProduct F Z).form) := by
  have L := gammaLogicInput G
  set b := Z.underlying.obj.arity
  have hFf := volume_form_graph_of_density_graph F.form hF.densityGraph
  have hRF := hFf.preimage_maps (mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.castAdd b : Fin a → Fin (a+b)) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hRZ := hZ.density.preimage_maps
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (Fin.natAdd a : Fin b → Fin (a+b)) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hP₀ := L.comp_graph hRF (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 0))
  have hP₁ := L.comp_graph hRZ (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 1))
  have hV := L.comp_graph (hP₀.inter hP₁) (gamma_rv_pair_multiply_graph hc G)
  have hR := L.restrict_graph (gamma_mixed_rv_factor_domain hF.domain hZ.domain) hV
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hR
  intro q y
  constructor
  · rintro ⟨hq,w,⟨⟨y₀,⟨v,hv,hy₀⟩,hw₀⟩,⟨y₁,⟨u,hu,hy₁⟩,hw₁⟩⟩,t,ht,hty⟩
    refine ⟨⟨q,hq⟩,rfl,?_⟩
    rw [← hty]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    change (HK.selectedFamilyWeightedZeroProduct F Z).form.value ⟨q,hq⟩ = (rvPairMultiply G.real t).val 0
    rw [weighted_zero_product_density]
    have hv' : v = ⟨_,((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.1 q.2).mp hq).1⟩ :=
      Subtype.ext hv
    have hu' : u = ⟨_,((mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q.1 q.2).mp hq).2⟩ :=
      Subtype.ext hu
    subst hv' hu'
    have et : t = ⟨w.2,Set.mem_univ _⟩ := Subtype.ext ht
    subst et
    have hw0 : w.2 0 = (F.form.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₀).symm.trans (congrFun hy₀ 0).symm
    have hw1 : w.2 1 = (Z.form.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₁).symm.trans (congrFun hy₁ 0).symm
    change _ = w.2 0 * w.2 1
    rw [hw0,hw1]
    rfl
  · rintro ⟨⟨q',hq⟩,rfl,hy⟩
    have h := (mem_mixed_rv_factor_domain F.domain Z.underlying.obj.domain q'.1 q'.2).mp hq
    let w : Point (M := M) 0 2 :=
      (Fin.elim0,![(F.form.map ⟨_,h.1⟩).val 0,(Z.form.map ⟨_,h.2⟩).val 0])
    refine ⟨hq,w,⟨⟨(Fin.elim0,(F.form.map _).val),⟨⟨_,h.1⟩,rfl,rfl⟩,?_⟩,
      ⟨(Fin.elim0,(Z.form.map _).val),⟨⟨_,h.2⟩,rfl,rfl⟩,?_⟩⟩,
      ⟨w.2,Set.mem_univ _⟩,rfl,?_⟩
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · rw [← hy]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      change w.2 0 * w.2 1 = (HK.selectedFamilyWeightedZeroProduct F Z).form.value ⟨q',hq⟩
      rw [weighted_zero_product_density]
      rfl

/-- **Weighted degree-zero products of Gamma families are Gamma.** -/
theorem SelectedVFVolumeFamily.Gamma.weightedZero (hc : CanonicalStructure.IsCanonical (M := M))
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G)
    {Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)} (hZ : Z.Gamma G) :
    (HK.selectedFamilyWeightedZeroProduct F Z).Gamma G :=
  ⟨gamma_mixed_rv_factor_domain hF.domain hZ.domain,
    density_graph_of_volume_form_graph _ (gamma_weighted_zero_product_form_graph hc hF hZ)⟩

theorem HK.ZeroRVVolumeObject.Gamma.changeBase {B' : Base (M := M)} {Z : HK.ZeroRVVolumeObject (M := M) S}
    (hZ : Z.Gamma B') (h : GammaBaseDominated B' G) : Z.Gamma G :=
  ⟨h.set hZ.domain,h.graph hZ.density⟩

theorem HK.ZeroRVVolumeObject.Gamma.extend {T : Set M} {Z : HK.ZeroRVVolumeObject (M := M) S}
    (hZ : Z.Gamma G) (h : S ⊆ T) : (Z.extend h).Gamma G :=
  ⟨hZ.domain,hZ.density⟩

/-- The row coefficient of a Gamma degree-zero object. -/
def zeroRowCoefficient (Z : HK.GammaZeroRVObjects G (C.base : Set M)) (x : Fin n → VFType (M := M)) :
    HK.GammaZeroRVObjects (rowGammaBase G x) ((vfParameterVolumeContext C x).base : Set M) :=
  ⟨HK.zeroVolumeCoefficientInContext Z.val x,
    (Z.property.extend _).changeBase (GammaBaseDominated.of_subset Set.subset_union_left (Set.Subset.refl _))⟩

theorem gamma_weighted_zero_row_class (hc : CanonicalStructure.IsCanonical (M := M))
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G)
    (Z : HK.GammaZeroRVObjects G (C.base : Set M)) (x : Fin n → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ⟨(HK.selectedFamilyWeightedZeroProduct F Z.val).rowInContext x,(hF.weightedZero hc Z.property).row hc x⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        (GammaVolumeObjects.posZeroProd hc ⟨F.rowInContext x,hF.row hc x⟩ (zeroRowCoefficient Z x)) := by
  let e := HK.selectedFamilyWeightedZeroRowIso hc F Z.val x
  apply (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
  exact GammaVolumeBlowupEquivalent.of_iso _ _ e
    (gamma_volume_iso_of_label_identity hc e ((hF.weightedZero hc Z.property).row hc x) rfl
      (fun u => congrArg Subtype.val (finiteIsoMap_apply_symm e.iso.symm u)))

end IntegrationInACVF.Section7
