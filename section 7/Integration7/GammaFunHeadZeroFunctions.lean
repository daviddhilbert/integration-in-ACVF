import Integration7.GammaFunHeadZeroCoefLinearity
import Integration7.GammaFunZeroHead
import Integration7.FrozenGeneratedVolumeContexts
import Integration7.HKZeroHeadFibreIntegralIsomorphisms
import Integration7.HKZeroScalarRealizations
import Integration7.GammaNamedPullbackComparisons
import Integration7.GammaFunIntegrationFormula
import Integration7.GammaVFZeroProducts
import Integration7.GammaFunGradedIntegral
import Integration7.GammaFunJacobianZeroZero
import Integration7.GammaFunGenericRows

/-! **Zero head integrals and weighted degree-zero coefficients** (degree-zero functions). At VF
points generic over the Gamma-named base, zero-head rows are identified with Gamma contraction
objects of the fibre's full VF object in the frozen generated context over the closure of the row
base (`zero_head_row_contraction`), where the Gamma weighted-zero contraction law applies; the
comparison is reduced back to the row base, and generic rows give almost-everywhere equivalence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV GammaChainDefinable headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {n a : ℕ}

/-- The head fibre of a Gamma zero family is a Gamma unary zero family over the row base. -/
theorem HK.ZeroVFVolumeFamily.Gamma.headFibre (hc : CanonicalStructure.IsCanonical (M := M))
    {C D : BaseContext M} {F : HK.ZeroVFVolumeFamily C (n+1) a} (hF : F.Gamma G)
    (x : Fin n → VFType (M := M)) (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    ((F.headFibre x).extendContext hD).Gamma (rowGammaBase G x) := by
  constructor
  · have h := gamma_head_fibre (nativeMixedVolumeDomain hc F.domain) (by rw [nativeMixedVolumeDomain_carrier]; exact hF.domain) x
    convert h using 1
    ext p
    change (Fin.cons (p.1 0) x,p.2) ∈ F.domain.carrier ↔ coordinateInsert 0 (headFrozenTuple x) p ∈ F.domain.carrier
    rw [coordinateInsert_head]
    rfl
  · have h := gamma_head_fibre (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)
      (by rw [nativeMixedVolumeDomain_carrier]; exact hF.densityGraph) x
    have h2 : GammaSetDefinable (rowGammaBase G x)
        (carrier (nativeMixedVolumeDomain hc ((F.headFibre x).extendContext hD).fullVFObject.densityGraph.domain)) := by
      rw [← HK.zero_head_fibre_density_contraction_source hc D F x hD]
      exact h
    rw [nativeMixedVolumeDomain_carrier] at h2
    exact h2

theorem gamma_zero_head_fibre_standard_contraction (hc : CanonicalStructure.IsCanonical (M := M))
    (C D : BaseContext M) (F : HK.ZeroVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (hT : GammaGraphDefinable G (SpecialTransformations.Section5.pointMapGraph T.map))
    (hTarget : GammaSetDefinable G (carrier T.target))
    (x : Fin n → VFType (M := M)) (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M)) :
    GammaProgramDefinable (rowGammaBase G x) (HK.zeroHeadFibreStandardContraction hc D F T x hD).program :=
  gamma_orderedCastSource _ _ ((headCoordinateFibreContraction T x).program.extendBase_gamma
    (head_fibre_contraction_base_subset C D x hD) (gamma_head_coordinate_fibre_contraction T hT hTarget x))

theorem zero_head_fibre_integral_volume_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    {C : BaseContext M} (D : BaseContext M) (Ξ : Set (Values.Gamma (M := M))) (F : HK.ZeroVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (x : Fin n → VFType (M := M)) (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (hRow : VolumeObjectGamma (((F.headIntegral hc Ξ T).rowInContext x).extend hD) G) :
    (HK.zeroHeadFibreIntegralVolumeIso hc D F T x hD Ξ).GammaDefinable G :=
  gamma_volume_iso_of_label_identity hc _ hRow rfl (fun _ => rfl)

theorem mem_head_fibre_prod_zero {C D : BaseContext M} (Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M))
    (F : HK.ZeroVFVolumeFamily C (n+1) a) (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (q : Point (M := M) 1 (a+Z.underlying.obj.arity)) :
    q ∈ (((F.prodZero Z).headFibre x).extendContext hD).domain.carrier ↔
      q ∈ (((F.headFibre x).extendContext hD).prodZero (Z.extend hCD)).domain.carrier := by
  change (Fin.cons (q.1 0) x,q.2) ∈ (mixedRVFactorDomain F.domain Z.underlying.obj.domain).carrier ↔ _
  rw [mem_mixed_rv_factor_domain]
  exact (mem_mixed_rv_factor_domain ((F.headFibre x).extendContext hD).domain
    (Z.extend hCD).underlying.obj.domain q.1 q.2).symm

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

variable (γ : Values.Gamma (M := M)) (hγ1 : 1 < γ)

include hγ1 in
set_option maxHeartbeats 1600000 in
/-- **Zero-head rows as contraction objects of the fibre**, in any context over a VF-generated Gamma
base dominating the row base, with genericity transfer. -/
theorem zero_head_row_contraction (F : ZeroPresentation C Ξ hΞ (n+1)) (x : Fin (n+1) → VFType (M := M))
    (D : BaseContext M) (hD : ((vfParameterVolumeContext 𝔇 x).base : Set M) ⊆ (D.base : Set M))
    (G : Base (M := M)) (hGD : G.real ⊆ (D.base : Set M)) (hΞG : Cardinal.mk G.gamma < D.κ)
    (hGen : VFGammaGeneratedBase G) (hNamesG : commonRealNames G ⊆ (D.base : Set M))
    (hGeneric : ∀ {p : ℕ} (y : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) y →
      AlgebraicIndependent (vfParameterField (D.base : Set M)) y)
    (hγG : γ ∈ G.gamma) (hBr : (rowGammaBase 𝔅 x).real ⊆ G.real) (hBg : (rowGammaBase 𝔅 x).gamma ⊆ G.gamma)
    (hX : VFVolumeObjectGamma ((F.family.headFibre x).extendContext hD).fullVFObject G)
    (E : StandardContraction (nativeMixedVolumeDomain hc
      ((F.family.headFibre x).extendContext hD).fullVFObject.densityGraph.domain) (Equiv.refl _))
    (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G D
      ⟨((F.headIntegral hc C Ξ hΞ hGenerated).family.rowInContext x).extend hD,
        ((((F.headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x).extend hD).baseMono hBr hBg)⟩
      ⟨((F.family.headFibre x).extendContext hD).fullVFObject.standardContractionObject hc D G.gamma E,
        GammaNamed.standard_contraction_object_gamma hc D G hGD _ hX E hE⟩ := by
  let T := F.headPrep hc C Ξ hΞ hGenerated
  let X := ((F.family.headFibre x).extendContext hD).fullVFObject
  let A := nativeMixedVolumeDomain hc X.densityGraph.domain
  have hA : GammaSetDefinable G (carrier A) := hX.densityGraph
  let R0 := HK.zeroHeadFibreStandardContraction hc D F.family T x hD
  have hR0 : GammaProgramDefinable G R0.program :=
    gamma_program_mono hBr hBg _ (gamma_zero_head_fibre_standard_contraction hc 𝔇 D F.family T
      (F.headPrep_map hc C Ξ hΞ hGenerated) (F.headPrep_target hc C Ξ hΞ hGenerated) x hD)
  have hRow := ((F.headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x).extend hD
  have h1 : CommonContextVolumeEquivalent G D ⟨_,hRow.baseMono hBr hBg⟩
      ⟨rawStandardVolumeObject hc D G.gamma A X.densityGraph.finite_labels (Fin.last _)
        (unary_density_graph_label_nonzero X) R0,
        GammaNamed.raw_standard_volume_object_gamma hc D G hGD A hA X.densityGraph.finite_labels (Fin.last _)
          (unary_density_graph_label_nonzero X) R0 hR0⟩ :=
    CommonContextVolumeEquivalent.of_iso (HK.zeroHeadFibreIntegralVolumeIso hc D F.family T x hD Ξ)
      ((zero_head_fibre_integral_volume_iso_gamma hc D Ξ F.family T x hD hRow).baseMono hBr hBg)
  have h3 := GammaNamed.raw_standard_volume_normalization hc D G hGD A hA X.densityGraph.finite_labels (Fin.last _)
    (unary_density_graph_label_nonzero X) R0 hR0
  let ω := mixedRetainedLabelVolumeForm (SpecialTransformations.Section9.rawSpecialSet hc A) (Fin.last X.arity)
    (fun p => unary_density_graph_label_nonzero X p.val p.property)
  let U1 := nativeMixedVFVolumeObject hc A X.densityGraph.finite_labels ω
  have hU1 : VFVolumeObjectGamma U1 G :=
    VFVolumeObjectGamma.of_density_graph (gamma_coordinate_volume_density_graph hc hA ω (Fin.last X.arity) (fun _ => rfl))
  obtain ⟨E1,hE1,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) D.saturated D.model00
    ((Cardinal.mk_le_mk_of_subset hGD).trans_lt D.small) hGen hGD (nativeMixedVolumeDomain hc U1.densityGraph.domain)
    hU1.densityGraph (Equiv.refl _)
  have h4 := GammaNamed.retained_density_graph_contraction_comparison hc D G hGD hΞG hGeneric γ hγG hγ1 A hA
    X.densityGraph.finite_labels ω (Fin.last X.arity) (fun _ => rfl) R0 hR0 hU1 E1 hE1
  let f : SpecialTransformations.DefinableGeometry.Map X.densityGraph.domain U1.domain :=
    SpecialTransformations.DefinableGeometry.Map.inclusion (fun _ h => h)
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      exact Subtype.ext (congrArg (fun z : U1.domain => z.val) he)
    · intro q
      exact ⟨⟨q.val,q.property⟩,rfl⟩
  let b : VFVolumeBijection X.densityGraph U1 :=
    VFVolumeBijection.of_preserving_vf_and_density hc D f hf (fun _ => rfl) (fun p => densityGraph_form_last X p)
  have hb : (VFVolumeIso.of_bijection b).GammaDefinable G :=
    ⟨hX.densityGraph,hU1.domain,vf_identity_map_gamma _ (fun _ => rfl) hX.densityGraph⟩
  have hXU : ((VFVolumeIso.of_bijection (volumeDensityGraphBijection hc D X)).trans hc D
      (VFVolumeIso.of_bijection b)).GammaDefinable G :=
    (gamma_volume_density_graph_iso hc D hX).trans hc D hb
  have a2 := GammaNamed.gamma_vf_iso_contraction_comparison hc D G hGD hΞG hGen hNamesG hGeneric γ hγG hγ1
    U1 X hU1 hX _ (hXU.symm hc D) E1 E hE1 hE
  exact ((h1.trans hc h3).trans hc h4).trans hc a2

include hγ1 in
set_option maxHeartbeats 1600000 in
/-- **Rows of zero heads of weighted degree-zero products of degree-zero functions** at generic points. -/
theorem head_zero_zero_common (hγ : γ ∈ Ξ) (Z : HK.GammaZeroRVObjects 𝔅 𝔖) (F : ZeroPresentation C Ξ hΞ (n+1))
    (x : Fin (n+1) → VFType (M := M)) (hx : AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) x) :
    CommonContextVolumeEquivalent (rowGammaBase 𝔅 x) (vfParameterVolumeContext 𝔇 x)
      ⟨((F.zeroCoef hc C Ξ hΞ Z).headIntegral hc C Ξ hΞ hGenerated).family.rowInContext x,
        ((F.zeroCoef hc C Ξ hΞ Z).headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x⟩
      (GammaVolumeObjects.posZeroProd hc
        ⟨(F.headIntegral hc C Ξ hΞ hGenerated).family.rowInContext x,
          (F.headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x⟩ (zeroRowCoefficient Z x)) := by
  let S := F.zeroCoef hc C Ξ hΞ Z
  let Cx := vfParameterVolumeContext 𝔇 x
  let Bx := rowGammaBase 𝔅 x
  have hBC := gamma_named_code_context_base C Ξ hΞ
  let D := frozenGeneratedVolumeContext hc 𝔇 𝔅 hBC hΞ x
  have hD : (Cx.base : Set M) ⊆ (D.base : Set M) :=
    Substructure.closure_le.mpr (frozen_generated_context_contains hc 𝔇 hBC hΞ x)
  let G := vfParameterCoefficientBase 𝔅 x
  have hNamesG : commonRealNames G ⊆ (D.base : Set M) :=
    frozen_generated_context_contains_names hc 𝔇 hBC (gamma_named_code_context_names C Ξ hΞ) hΞ x
  have hGD : G.real ⊆ (D.base : Set M) := fun y hy => hNamesG (Or.inl hy)
  have hGen : VFGammaGeneratedBase G := vfParameterCoefficientBase_generated hGenerated x
  have hGeneric : ∀ {p : ℕ} (y : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) y →
      AlgebraicIndependent (vfParameterField (D.base : Set M)) y :=
    fun y hy => frozen_generated_context_preserves_independence hc 𝔇 hBC hΞ
      (fun z hz => gamma_named_code_context_generic C Ξ hΞ hc z hz) x hx y hy
  have hΞG : Cardinal.mk G.gamma < D.κ :=
    vfParameterCoefficientBase_gamma_small C.uncountable (small_gamma_named_real C Ξ hΞ) hΞ x
  have hBG := subset_closureBase Bx
  have hγG : γ ∈ G.gamma := hBG.2 hγ
  have hCD : 𝔖 ⊆ (D.base : Set M) := fun y hy => hD (vfParameterVolumeContext_contains 𝔇 x (Or.inl hy))
  have h𝔅G : (𝔅).real ⊆ G.real := Set.subset_union_left.trans hBG.1
  -- fibres
  let F0 := (F.family.headFibre x).extendContext hD
  have hF0 : F0.Gamma G := by
    have h := F.gamma.headFibre hc x hD
    exact ⟨h.domain.mono hBG.1 hBG.2,h.densityGraph.mono hBG.1 hBG.2⟩
  let X := F0.fullVFObject
  have hX : VFVolumeObjectGamma X G := hF0.fullVFObject
  let S0 := (S.family.headFibre x).extendContext hD
  have hS0 : S0.Gamma G := by
    have h := S.gamma.headFibre hc x hD
    exact ⟨h.domain.mono hBG.1 hBG.2,h.densityGraph.mono hBG.1 hBG.2⟩
  let X' := S0.fullVFObject
  have hX' : VFVolumeObjectGamma X' G := hS0.fullVFObject
  let ZD : HK.ZeroRVVolumeObject (M := M) (D.base : Set M) := Z.val.extend hCD
  have hZD : ZD.Gamma G := (Z.property.extend hCD).changeBase (GammaBaseDominated.of_subset h𝔅G hBG.2)
  have hXZ : VFVolumeObjectGamma (HK.positiveVFZeroProduct X ZD) G := hX.weightedZero hc hZD
  let Y := (F0.prodZero ZD).fullVFObject
  have hY : VFVolumeObjectGamma Y G := (hF0.prodZero hc hZD).fullVFObject
  have hsmall : Cardinal.mk G.real < D.κ := (Cardinal.mk_le_mk_of_subset hGD).trans_lt D.small
  obtain ⟨E0,hE0,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) D.saturated D.model00 hsmall hGen hGD
    (nativeMixedVolumeDomain hc X.densityGraph.domain) hX.densityGraph (Equiv.refl _)
  obtain ⟨ES,hES,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) D.saturated D.model00 hsmall hGen hGD
    (nativeMixedVolumeDomain hc X'.densityGraph.domain) hX'.densityGraph (Equiv.refl _)
  obtain ⟨EZ,hEZ,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) D.saturated D.model00 hsmall hGen hGD
    (nativeMixedVolumeDomain hc (HK.positiveVFZeroProduct X ZD).densityGraph.domain) hXZ.densityGraph (Equiv.refl _)
  have hL := zero_head_row_contraction hc C Ξ hΞ hGenerated γ hγ1 S x D hD G hGD hΞG hGen hNamesG hGeneric hγG
    hBG.1 hBG.2 hX' ES hES
  have hR := zero_head_row_contraction hc C Ξ hΞ hGenerated γ hγ1 F x D hD G hGD hΞG hGen hNamesG hGeneric hγG
    hBG.1 hBG.2 hX E0 hE0
  -- the identity bijection from the fibre of the product to the product of the fibre
  let f : SpecialTransformations.DefinableGeometry.Map X'.domain Y.domain :=
    SpecialTransformations.DefinableGeometry.Map.inclusion
      (fun q hq => (mem_head_fibre_prod_zero Z.val F.family x hD hCD q).mp hq)
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      exact Subtype.ext (congrArg (fun z : Y.domain => z.val) he)
    · intro q
      exact ⟨⟨q.val,(mem_head_fibre_prod_zero Z.val F.family x hD hCD q.val).mpr q.property⟩,rfl⟩
  let b : VFVolumeBijection X' Y := VFVolumeBijection.of_preserving_vf_and_density hc D f hf (fun _ => rfl) (fun p => by
    have h1 := zero_prod_zero_density F0 ZD (f p)
    have h2 := zero_prod_zero_density F.family Z.val ⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩
    change (F.family.prodZero Z.val).form.value ⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩ = (F0.prodZero ZD).form.value (f p)
    rw [h1,h2]
    rfl)
  have hb : (VFVolumeIso.of_bijection b).GammaDefinable G :=
    ⟨hX'.domain,hY.domain,vf_identity_map_gamma _ (fun _ => rfl) hX'.domain⟩
  have hr : (VFVolumeIso.of_bijection (HK.zeroVolumeScalarRealizationBijection hc F0 ZD)).GammaDefinable G :=
    ⟨hY.domain,hXZ.domain,vf_identity_map_gamma _ (fun _ => rfl) hY.domain⟩
  have a2 := GammaNamed.gamma_vf_iso_contraction_comparison hc D G hGD hΞG hGen hNamesG hGeneric γ hγG hγ1
    X' _ hX' hXZ _ (hb.trans hc D hr) ES EZ hES hEZ
  have a3 := GammaNamed.gamma_weighted_zero_contraction hc D G hGD hΞG hGen hNamesG hGeneric γ hγG hγ1
    X hX ⟨ZD,hZD⟩ hXZ E0 EZ hE0 hEZ
  have hAll := ((hL.trans hc a2).trans hc a3).trans hc ((hR.symm hc).posZeroProd hc ⟨ZD,hZD⟩)
  exact CommonContextVolumeEquivalent.of_extend_context hD (hAll.reduce (closureBaseReduction Bx))

include hγ1 in
/-- **Zero head integrals commute with weighted degree-zero coefficients** (almost everywhere,
degree-zero functions). -/
theorem presentation_head_zero_zero_ae (hγ : γ ∈ Ξ) (Z : HK.GammaZeroRVObjects 𝔅 𝔖) (F : ZeroPresentation C Ξ hΞ (n+1)) :
    AEEquivalent hc C Ξ hΞ ((F.zeroCoef hc C Ξ hΞ Z).headIntegral hc C Ξ hΞ hGenerated)
      ((F.headIntegral hc C Ξ hΞ hGenerated).zeroCoef hc C Ξ hΞ Z) := by
  apply presentation_ae_of_generic_rows hc C Ξ hΞ
  intro x hx
  apply (gammaVolumeBlowupClass_eq_iff hc _ _).mp
  refine Eq.trans ?_ (gamma_weighted_zero_row_class hc (F.headIntegral hc C Ξ hΞ hGenerated).gamma Z x).symm
  exact (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
    ((head_zero_zero_common hc C Ξ hΞ hGenerated γ hγ1 hγ Z F x hx).descend hc _
      (row_context_names 𝔇 𝔅 (gamma_named_code_context_names C Ξ hΞ) x))

end IntegrationInACVF.Section7.GammaFun
