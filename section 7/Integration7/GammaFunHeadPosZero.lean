import Integration7.GammaFunHeadZeroFunctions
import Integration7.GammaFunJacobianPosZero
import Integration7.FiniteCoefficientContractionProductCharts
import Integration7.FiniteCoefficientSpecialPreparations
import Integration7.HKZeroFinitePositiveCoefficientRowIsomorphisms
import Integration7.UnaryPreparedFiniteHeadObjects

/-! **Head integrals commute with positive coefficients on degree-zero functions.** At VF points
generic over the Gamma-named base, in the frozen generated context over the closure of the row
base: the head fibre of the coefficient product is compared by Gamma Lemma 7.5 with the finite
coefficient family of the fibre's full VF object, whose contraction is the coefficient times the
prepared finite head; the prepared head is a raw standard object, hence a Gamma contraction
object of the fibre, hence the zero-head row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV GammaChainDefinable headImage SpecialBijection)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {n a b d p : ℕ}

theorem mem_head_fibre_zero_family_positive_product {C D : BaseContext M}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : HK.ZeroVFVolumeFamily C (n+1) a) (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (q : Point (M := M) 1 ((a+U.underlying.obj.arity)+(p+1))) :
    q ∈ (((HK.selectedZeroFamilyPositiveProduct U F).headFibre x).extendContext hD).domain.carrier ↔
      q ∈ (HK.selectedZeroFamilyPositiveProduct (U.extend hCD) ((F.headFibre x).extendContext hD)).domain.carrier := by
  change (Fin.cons (q.1 0) x,q.2) ∈ (HK.selectedZeroFamilyPositiveProduct U F).domain.carrier ↔ _
  rw [mem_zero_family_positive_product,mem_zero_family_positive_product]
  rfl

theorem head_fibre_zero_family_positive_product_row_class (hc : CanonicalStructure.IsCanonical (M := M))
    {C D : BaseContext M} {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p}
    {F : HK.ZeroVFVolumeFamily C (n+1) a} (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (h₁ : (((HK.selectedZeroFamilyPositiveProduct U F).headFibre x).extendContext hD).Gamma G)
    (h₂ : (HK.selectedZeroFamilyPositiveProduct (U.extend hCD) ((F.headFibre x).extendContext hD)).Gamma G)
    (y : Fin 1 → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext D y) (rowGammaBase G y)
        ⟨(((HK.selectedZeroFamilyPositiveProduct U F).headFibre x).extendContext hD).rowInContext y,h₁.row hc y⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext D y) (rowGammaBase G y)
        ⟨(HK.selectedZeroFamilyPositiveProduct (U.extend hCD) ((F.headFibre x).extendContext hD)).rowInContext y,
          h₂.row hc y⟩ := by
  refine gamma_class_eq_of_select hc _ _ _ _ id
    (fun t ht => (mem_head_fibre_zero_family_positive_product U F x hD hCD (y,t)).mp ht)
    (fun s hs => ⟨s,(mem_head_fibre_zero_family_positive_product U F x hD hCD (y,s)).mpr hs,rfl⟩)
    (fun _ _ _ _ h => h) (fun _ => rfl) (fun t => ?_)
  have hL := zero_family_positive_product_density (U.extend hCD) ((F.headFibre x).extendContext hD)
    ⟨(y,t.val),(mem_head_fibre_zero_family_positive_product U F x hD hCD (y,t.val)).mp t.property⟩
  have hR := zero_family_positive_product_density U F ⟨(Fin.cons (y 0) x,t.val),t.property⟩
  change (HK.selectedZeroFamilyPositiveProduct (U.extend hCD) ((F.headFibre x).extendContext hD)).form.value
      ⟨(y,t.val),_⟩ = (HK.selectedZeroFamilyPositiveProduct U F).form.value ⟨(Fin.cons (y 0) x,t.val),t.property⟩
  rw [hL,hR]
  rfl

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

/-- The finite coefficient family of a Gamma unary VF object by a Gamma native coefficient is Gamma. -/
theorem gamma_finite_volume_coefficient_family (X : PositiveVFVolumeObject (M := M) (C.base : Set M) 0)
    (hX : VFVolumeObjectGamma X G) (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (hRΓ : GammaSetDefinable G (carrier R)) (σ : Fin (p+1) → Fin d) (ε : Fin d)
    (hR : ∀ t : Fin (p+1) → RV (M := M), {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) :
    (finiteVolumeCoefficientFamily hc C X.densityGraph.domain X.densityGraph.finite_labels X.densityGraph.form
      R σ ε hR hε).Gamma G := by
  have hA : GammaSetDefinable G (carrier (nativeMixedVolumeDomain hc X.densityGraph.domain)) := hX.densityGraph
  have hRl := gamma_raw_contraction_labels_set hc C R hRΓ
  have hωdg := gamma_coordinate_volume_density_graph hc hA X.densityGraph.form (Fin.last X.arity)
    (densityGraph_form_last X)
  have hν := (GammaNamed.native_coordinate_density_volume_object_gamma hc C G R hRΓ σ ε hR hε).density
  exact ⟨gamma_mixed_rv_factor_domain hX.densityGraph hRl,
    density_graph_of_volume_form_graph _ (gamma_mixed_rv_factor_form_graph hc X.densityGraph.form _ hX.densityGraph hRl
      (volume_form_graph_of_density_graph X.densityGraph.form hωdg) hν)⟩

set_option maxHeartbeats 1600000 in
/-- Rows of the finite coefficient family of a zero family: zero row times coefficient. -/
theorem gamma_finite_coefficient_row_class {F : HK.ZeroVFVolumeFamily C (n+1) a} (hF : F.Gamma G)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (hRΓ : GammaSetDefinable G (carrier R)) (σ : Fin (p+1) → Fin d) (ε : Fin d)
    (hR : ∀ t : Fin (p+1) → RV (M := M), {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) (x : Fin (n+1) → VFType (M := M))
    (hJ : (finiteVolumeCoefficientFamily hc C F.fullVFObject.densityGraph.domain
      F.fullVFObject.densityGraph.finite_labels F.fullVFObject.densityGraph.form R σ ε hR hε).Gamma G) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ⟨(finiteVolumeCoefficientFamily hc C F.fullVFObject.densityGraph.domain
          F.fullVFObject.densityGraph.finite_labels F.fullVFObject.densityGraph.form R σ ε hR hε).rowInContext x,
          hJ.row hc x⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ⟨HK.zeroProduct (F.rowInContext x)
          (positiveRowCoefficient ⟨_,GammaNamed.native_coordinate_density_volume_object_gamma hc C G R hRΓ σ ε hR hε⟩ x).val,
          VolumeObjectGamma.zeroProd hc (hF.row x)
            (positiveRowCoefficient ⟨_,GammaNamed.native_coordinate_density_volume_object_gamma hc C G R hRΓ σ ε hR hε⟩ x).property⟩ := by
  let D := vfParameterVolumeContext C x
  let e1 := HK.zeroFinitePositiveCoefficientRowIso hc C F R σ ε hR hε x
  let e2 := HK.zeroFamilyPositiveCoefficientRowIso hc F (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε) x
  let e := e1.trans hc D e2
  have hv1 : ∀ w, (finiteIsoMap e1.iso w).val =
      w.val ∘ Fin.append (m := a) (n := d) (Fin.castAdd d ∘ Fin.castAdd 1) (Fin.natAdd (a+1)) := fun w => rfl
  have hv2 : ∀ w, (finiteIsoMap e2.iso w).val = w.val :=
    fun w => congrArg Subtype.val (finiteIsoMap_apply_symm e2.iso.symm w)
  have hv : ∀ w, (finiteIsoMap e.iso w).val =
      w.val ∘ Fin.append (m := a) (n := d) (Fin.castAdd d ∘ Fin.castAdd 1) (Fin.natAdd (a+1)) := by
    intro w
    change (finiteIsoMap (e1.iso.trans e2.iso) w).val = _
    rw [finiteIsoMap_trans]
    exact (hv2 _).trans (hv1 w)
  have hdom := gamma_essential_volume_domain _ (hJ.row hc x).coordinates
  apply (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
  exact GammaVolumeBlowupEquivalent.of_iso _ _ e (gamma_rv_coordinate_map hc _ _ hdom hv)

/-- A Gamma special preparation of a retained unary set lifts to its finite coefficient family. -/
theorem gamma_finite_coefficient_preparation_exists (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) 1 a) (C.base : Set M))
    (hA : ∀ x : Fin 1 → VFType (M := M), {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ A.carrier}.Finite)
    (ω : VolumeForm A) (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (σ : Fin (p+1) → Fin d) (ε : Fin d)
    (hR : ∀ t : Fin (p+1) → RV (M := M), {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) (δ : Fin a) (hω : ∀ q : A, ω.value q=q.val.2 δ)
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc A) B) (hT : GammaChainDefinable G T.chain)
    (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
    (hJ : (finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).Gamma G) :
    Nonempty (RVLabelConstraintSpecialPreparation T
      (nativeMixedVolumeDomain hc (finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).densityGraph.domain)
      (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d) G) := by
  have hH := hJ.native_domain hc
  rw [finite_coefficient_density_graph_source hc C A hA ω R σ ε hR hε Ξ hNames δ hω] at hH ⊢
  exact gamma_rv_label_constraint_special_preparation_exists T hT hB _ hH _ _
    (constrained_unary_source_mem C Ξ hNames _ _ _)

/-- The finite coefficient chart is Gamma-definable. -/
theorem finite_coefficient_contraction_product_iso_gamma (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) 1 a) (C.base : Set M))
    (hA : ∀ x : Fin 1 → VFType (M := M), {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ A.carrier}.Finite)
    (ω : VolumeForm A) (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (σ : Fin (p+1) → Fin d) (ε : Fin d)
    (hR : ∀ t : Fin (p+1) → RV (M := M), {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) (δ : Fin a) (hδ : ∀ q ∈ A.carrier, (q.2 δ).val ≠ iRVZero)
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc A) B)
    (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
    (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (L : RVLabelConstraintSpecialPreparation T
      (nativeMixedVolumeDomain hc (finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).densityGraph.domain)
      (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d)
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hSource : VolumeObjectGamma ((finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).standardAppendObject hc Ξ
      (unarySpecialStandardContraction L.special L.pullback)) G)
    (hL : GammaSetDefinable G (carrier (headImage L.target))) :
    (finiteCoefficientContractionProductIso hc C Ξ hNames A hA ω R σ ε hR hε δ hδ T hB hT L).GammaDefinable G := by
  unfold finiteCoefficientContractionProductIso
  dsimp only
  refine RVVolumeIso.GammaDefinable.trans hc C G (gamma_volume_iso_of_label_identity hc _ hSource rfl (fun _ => rfl)) ?_
  exact native_rv_product_volume_chart_iso_gamma hc C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL

/-- The prepared finite head chart is Gamma-definable. -/
theorem unary_prepared_finite_head_iso_gamma (Ξ : Set (Values.Gamma (M := M)))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection A B) (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
    (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain) (hTG : GammaChainDefinable G T.chain)
    (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) :
    (unaryPreparedFiniteHeadIso hc C Ξ T hB hT hfin δ hδ).GammaDefinable G := by
  have hSel := GammaNamed.selected_standard_volume_object_gamma hc C Ξ G A (Fin.elim0 : Fin 0 → Fin a) δ hδ
    (fun x _ => (hfin x).subset (fun _ h => h.1)) (unarySpecialStandardContraction T hB)
    (gamma_unary_special_standard_contraction T hB hTG)
  unfold unaryPreparedFiniteHeadIso
  dsimp only
  refine RVVolumeIso.GammaDefinable.trans hc C G ?_ ?_
  · exact (gamma_volume_iso_of_label_identity hc
      (unaryRawSelectedVolumeIso hc C Ξ A hfin δ hδ (unarySpecialStandardContraction T hB)) hSel rfl
      (fun _ => rfl)).symm hc C G
  · exact gamma_volume_iso_of_label_identity hc _ hSel rfl (fun _ => rfl)

include hc in
set_option maxHeartbeats 1600000 in
/-- Raw standard objects of a unary VF object's density graph are Gamma contraction objects. -/
theorem raw_standard_vf_contraction (D : BaseContext M) (G : Base (M := M)) (hGD : G.real ⊆ (D.base : Set M))
    (hΞG : Cardinal.mk G.gamma < D.κ) (hGen : VFGammaGeneratedBase G) (hNamesG : commonRealNames G ⊆ (D.base : Set M))
    (hGeneric : ∀ {p : ℕ} (y : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) y →
      AlgebraicIndependent (vfParameterField (D.base : Set M)) y)
    (γ : Values.Gamma (M := M)) (hγG : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (X : PositiveVFVolumeObject (M := M) (D.base : Set M) 0) (hX : VFVolumeObjectGamma X G)
    (T : StandardContraction (nativeMixedVolumeDomain hc X.densityGraph.domain) (Equiv.refl _))
    (hT : GammaProgramDefinable G T.program)
    (E : StandardContraction (nativeMixedVolumeDomain hc X.densityGraph.domain) (Equiv.refl _))
    (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G D
      ⟨rawStandardVolumeObject hc D G.gamma (nativeMixedVolumeDomain hc X.densityGraph.domain)
        X.densityGraph.finite_labels (Fin.last X.arity) (unary_density_graph_label_nonzero X) T,
        GammaNamed.raw_standard_volume_object_gamma hc D G hGD (nativeMixedVolumeDomain hc X.densityGraph.domain)
          hX.densityGraph X.densityGraph.finite_labels (Fin.last X.arity)
          (unary_density_graph_label_nonzero X) T hT⟩
      ⟨X.standardContractionObject hc D G.gamma E,GammaNamed.standard_contraction_object_gamma hc D G hGD _ hX E hE⟩ := by
  let A := nativeMixedVolumeDomain hc X.densityGraph.domain
  have hA : GammaSetDefinable G (carrier A) := hX.densityGraph
  have h3 := GammaNamed.raw_standard_volume_normalization hc D G hGD A hA X.densityGraph.finite_labels (Fin.last X.arity)
    (unary_density_graph_label_nonzero X) T hT
  let ω := mixedRetainedLabelVolumeForm (SpecialTransformations.Section9.rawSpecialSet hc A) (Fin.last X.arity)
    (fun p => unary_density_graph_label_nonzero X p.val p.property)
  let U1 := nativeMixedVFVolumeObject hc A X.densityGraph.finite_labels ω
  have hU1 : VFVolumeObjectGamma U1 G :=
    VFVolumeObjectGamma.of_density_graph (gamma_coordinate_volume_density_graph hc hA ω (Fin.last X.arity) (fun _ => rfl))
  obtain ⟨E1,hE1,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) D.saturated D.model00
    ((Cardinal.mk_le_mk_of_subset hGD).trans_lt D.small) hGen hGD (nativeMixedVolumeDomain hc U1.densityGraph.domain)
    hU1.densityGraph (Equiv.refl _)
  have h4 := GammaNamed.retained_density_graph_contraction_comparison hc D G hGD hΞG hGeneric γ hγG hγ1 A hA
    X.densityGraph.finite_labels ω (Fin.last X.arity) (fun _ => rfl) T hT hU1 E1 hE1
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
  exact (h3.trans hc h4).trans hc a2

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

variable (γ : Values.Gamma (M := M)) (hγ1 : 1 < γ)

include hγ1 in
set_option maxHeartbeats 3200000 in
/-- **Rows of heads of positive coefficient products of degree-zero functions** at generic points. -/
theorem head_pos_zero_common (hγ : γ ∈ Ξ) (U : GammaVolumeObjects 𝔅 𝔖 p) (F : ZeroPresentation C Ξ hΞ (n+1))
    (x : Fin (n+1) → VFType (M := M)) (hx : AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) x) :
    CommonContextVolumeEquivalent (rowGammaBase 𝔅 x) (vfParameterVolumeContext 𝔇 x)
      ⟨((F.posCoef hc C Ξ hΞ U).headIntegral hc C Ξ hΞ hGenerated).family.rowInContext x,
        ((F.posCoef hc C Ξ hΞ U).headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x⟩
      ((rowCoefficient C Ξ hΞ U x).prod hc
        ⟨(F.headIntegral hc C Ξ hΞ hGenerated).family.rowInContext x,
          (F.headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x⟩) := by
  let S := F.posCoef hc C Ξ hΞ U
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
  have hNamesD : commonRealNames (⟨(D.base : Set M),G.gamma⟩ : Base (M := M)) ⊆ (D.base : Set M) := by
    rintro d (hd | hd)
    · exact hd
    · exact hNamesG (Or.inr hd)
  -- the coefficient in the frozen context
  let UD : PositiveRVVolumeObject (M := M) (D.base : Set M) p := U.val.extend hCD
  have hUD : VolumeObjectGamma UD G := (U.property.extend hCD).baseMono h𝔅G hBG.2
  -- the degree-zero fibre and its full VF object
  let F0 := (F.family.headFibre x).extendContext hD
  have hF0 : F0.Gamma G := by
    have h := F.gamma.headFibre hc x hD
    exact ⟨h.domain.mono hBG.1 hBG.2,h.densityGraph.mono hBG.1 hBG.2⟩
  let X := F0.fullVFObject
  have hX : VFVolumeObjectGamma X G := hF0.fullVFObject
  have hsmall : Cardinal.mk G.real < D.κ := (Cardinal.mk_le_mk_of_subset hGD).trans_lt D.small
  obtain ⟨E0,hE0,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) D.saturated D.model00 hsmall hGen hGD
    (nativeMixedVolumeDomain hc X.densityGraph.domain) hX.densityGraph (Equiv.refl _)
  -- a Gamma unary special preparation of the retained fibre
  obtain ⟨b,BT,TF,hTF,hBT⟩ := gamma_field_unary_special_preparation D G (vfParameterCoefficientBase_field x) hGD
    (nativeMixedVolumeDomain hc X.densityGraph.domain) hX.densityGraph
  have hTF' : GammaChainDefinable (⟨(D.base : Set M),G.gamma⟩ : Base (M := M)) TF.chain :=
    gamma_chain_mono (P' := ⟨(D.base : Set M),G.gamma⟩) hGD (Set.Subset.refl _) _ hTF
  -- the finite coefficient family
  let R := rvCoordinateDensityNativeDomain hc D UD
  have hRΓ : GammaSetDefinable G (carrier R) := gamma_rv_coordinate_density_native_domain hc D hUD
  let σR : Fin (p+1) → Fin ((p+1)+(UD.underlying.obj.arity+1)) := Fin.castAdd (UD.underlying.obj.arity+1)
  let εR := Fin.natAdd (p+1) (Fin.last UD.underlying.obj.arity)
  let J := finiteVolumeCoefficientFamily hc D X.densityGraph.domain X.densityGraph.finite_labels X.densityGraph.form
    R σR εR (rv_coordinate_density_native_finite hc D UD) (rv_coordinate_density_native_nonzero hc D UD)
  have hJ : J.Gamma G := gamma_finite_volume_coefficient_family hc D X hX R hRΓ σR εR
    (rv_coordinate_density_native_finite hc D UD) (rv_coordinate_density_native_nonzero hc D UD)
  obtain ⟨L0⟩ := gamma_finite_coefficient_preparation_exists hc D G.gamma hNamesD X.densityGraph.domain
    X.densityGraph.finite_labels X.densityGraph.form R σR εR (rv_coordinate_density_native_finite hc D UD)
    (rv_coordinate_density_native_nonzero hc D UD) (Fin.last X.arity) (densityGraph_form_last X) TF hTF hBT hJ
  let L := L0.monoBase (P' := ⟨(D.base : Set M),G.gamma⟩) hGD (Set.Subset.refl _)
  let E2 := unarySpecialStandardContraction L.special L.pullback
  have hE2 : GammaProgramDefinable G E2.program := gamma_unary_special_standard_contraction L0.special L0.pullback L0.gamma
  -- the head fibre of the coefficient product
  let Φ1 := (S.family.headFibre x).extendContext hD
  have hΦ1 : Φ1.Gamma G := by
    have h := S.gamma.headFibre hc x hD
    exact ⟨h.domain.mono hBG.1 hBG.2,h.densityGraph.mono hBG.1 hBG.2⟩
  let R1 := headFibreStandardContraction hc 𝔇 D S.family (S.headPrep hc C Ξ hΞ hGenerated) x hD
  have hR1 : GammaProgramDefinable G R1.program :=
    gamma_program_mono hBG.1 hBG.2 _ (gamma_head_fibre_standard_contraction hc 𝔇 D S.family _
      (S.headPrep_map hc C Ξ hΞ hGenerated) (S.headPrep_target hc C Ξ hΞ hGenerated) x hD)
  have hV : VolumeObjectGamma (rvCoordinateDensityNativeObject hc D UD) G := VolumeObjectGamma.rvCoordinateDensityNative hc D hUD
  have hRows : ∀ y, GammaRowsEquivalent hc D G hΦ1 hJ y := by
    intro y
    let Dy := vfParameterVolumeContext D y
    have hDy : (D.base : Set M) ⊆ (Dy.base : Set M) := fun _ h => vfParameterVolumeContext_contains D y (Or.inl h)
    have hΨ := hF0.positiveProduct hc hUD
    have eA := head_fibre_zero_family_positive_product_row_class hc (U := U.val) (F := F.family) x hD hCD hΦ1 hΨ y
    have eB := gamma_zero_family_positive_product_row_class hc hF0 ⟨UD,hUD⟩ y
    have eC := gamma_finite_coefficient_row_class hc D hF0 R hRΓ σR εR (rv_coordinate_density_native_finite hc D UD)
      (rv_coordinate_density_native_nonzero hc D UD) y hJ
    have hf : ((((rvCoordinateDensityNativeIso hc D UD).symm hc D).extend hDy)).GammaDefinable (rowGammaBase G y) :=
      (((rv_coordinate_density_native_iso_gamma hc D hUD).symm hc D G).extend hDy).baseMono
        Set.subset_union_left (Set.Subset.refl _)
    have hZ := hF0.row y
    have hprod : GammaVolumeBlowupEquivalent (rowGammaBase G y) (Dy.base : Set M) p
        ⟨HK.zeroProduct (F0.rowInContext y) (positiveRowCoefficient ⟨_,hV⟩ y).val,
          VolumeObjectGamma.zeroProd hc hZ (positiveRowCoefficient ⟨_,hV⟩ y).property⟩
        ⟨HK.zeroProduct (F0.rowInContext y) (positiveRowCoefficient ⟨UD,hUD⟩ y).val,
          VolumeObjectGamma.zeroProd hc hZ (positiveRowCoefficient ⟨UD,hUD⟩ y).property⟩ :=
      GammaVolumeBlowupEquivalent.of_iso Dy _ (HK.zeroProductIso hc Dy (HK.ZeroRVVolumeIso.refl _) _)
        (gamma_zero_product_iso hc Dy (positiveRowCoefficient ⟨_,hV⟩ y).property
          (positiveRowCoefficient ⟨UD,hUD⟩ y).property hZ hZ (hZ.refl_iso) hf)
    have eD := (gammaVolumeBlowupClass_eq_iff hc Dy _).mpr hprod
    exact (gammaVolumeBlowupClass_eq_iff hc Dy _).mp (eA.trans (eB.trans (eC.trans eD).symm))
  have h75 := gamma_family_lemma_7_5 hc D G hGD hΞG γ hγG hγ1 hΦ1 hJ hRows R1 E2 hR1 hE2
  have hRowS := ((S.headIntegral hc C Ξ hΞ hGenerated).gamma.row hc x).extend hD
  have hA : CommonContextVolumeEquivalent G D ⟨_,hRowS.baseMono hBG.1 hBG.2⟩
      ⟨Φ1.standardAppendObject hc G.gamma R1,standard_append_volume_object_gamma_of hc D G.gamma G _ _ _ _ _ R1 hR1⟩ :=
    CommonContextVolumeEquivalent.of_iso (headFibreIntegralVolumeIso hc 𝔇 D Ξ S.family _ x hD)
      ((head_fibre_integral_volume_iso_gamma hc 𝔇 D Ξ S.family _ x hD hRowS).baseMono hBG.1 hBG.2)
  have hUPH : VolumeObjectGamma (unaryPreparedFiniteHeadObject hc D G.gamma TF hBT hTF' X.densityGraph.finite_labels
      (Fin.last X.arity) (unary_density_graph_label_nonzero X)) G :=
    GammaNamed.native_coordinate_density_volume_object_gamma hc D G _
      (gamma_headImage BT (GammaChainDefinable.target G TF.chain hTF)) _ _ _ _
  have hLT : GammaSetDefinable G (carrier (headImage L.target)) :=
    gamma_headImage L0.target (GammaChainDefinable.target G L0.special.chain L0.gamma)
  have hC : CommonContextVolumeEquivalent G D
      ⟨J.standardAppendObject hc G.gamma E2,standard_append_volume_object_gamma_of hc D G.gamma G _ _ _ _ _ E2 hE2⟩
      ⟨_,hV.prod hc hUPH⟩ :=
    CommonContextVolumeEquivalent.of_iso _
      (finite_coefficient_contraction_product_iso_gamma hc D G.gamma hNamesD X.densityGraph.domain
        X.densityGraph.finite_labels X.densityGraph.form R σR εR (rv_coordinate_density_native_finite hc D UD)
        (rv_coordinate_density_native_nonzero hc D UD) (Fin.last X.arity) (unary_density_graph_label_nonzero X)
        TF hBT hTF' L (standard_append_volume_object_gamma_of hc D G.gamma G _ _ _ _ _ E2 hE2) hLT)
  have hD1 : CommonContextVolumeEquivalent G D ⟨_,hV⟩ ⟨UD,hUD⟩ :=
    CommonContextVolumeEquivalent.of_iso ((rvCoordinateDensityNativeIso hc D UD).symm hc D)
      ((rv_coordinate_density_native_iso_gamma hc D hUD).symm hc D G)
  let ET := unarySpecialStandardContraction TF hBT
  have hET : GammaProgramDefinable G ET.program := gamma_unary_special_standard_contraction TF hBT hTF
  have hD2 : CommonContextVolumeEquivalent G D ⟨_,hUPH⟩
      ⟨rawStandardVolumeObject hc D G.gamma (nativeMixedVolumeDomain hc X.densityGraph.domain)
        X.densityGraph.finite_labels (Fin.last X.arity) (unary_density_graph_label_nonzero X) ET,
        GammaNamed.raw_standard_volume_object_gamma hc D G hGD (nativeMixedVolumeDomain hc X.densityGraph.domain)
          hX.densityGraph X.densityGraph.finite_labels (Fin.last X.arity) (unary_density_graph_label_nonzero X) ET hET⟩ :=
    CommonContextVolumeEquivalent.of_iso ((unaryPreparedFiniteHeadIso hc D G.gamma TF hBT hTF'
      X.densityGraph.finite_labels (Fin.last X.arity) (unary_density_graph_label_nonzero X)).symm hc D)
      ((unary_prepared_finite_head_iso_gamma hc D G.gamma TF hBT hTF' hTF X.densityGraph.finite_labels
        (Fin.last X.arity) (unary_density_graph_label_nonzero X)).symm hc D G)
  have hD3 := raw_standard_vf_contraction hc D G hGD hΞG hGen hNamesG hGeneric γ hγG hγ1 X hX ET hET E0 hE0
  have hD4 := zero_head_row_contraction hc C Ξ hΞ hGenerated γ hγ1 F x D hD G hGD hΞG hGen hNamesG hGeneric hγG
    hBG.1 hBG.2 hX E0 hE0
  have hHead := (hD2.trans hc hD3).trans hc (hD4.symm hc)
  have hAll := ((hA.trans hc h75).trans hc hC).trans hc (hD1.prod hc hHead)
  exact CommonContextVolumeEquivalent.of_extend_context hD (hAll.reduce (closureBaseReduction Bx))

include hγ1 in
/-- **Head integrals commute with positive coefficients on degree-zero functions** (almost everywhere). -/
theorem presentation_head_pos_zero_ae (hγ : γ ∈ Ξ) (U : GammaVolumeObjects 𝔅 𝔖 p) (F : ZeroPresentation C Ξ hΞ (n+1)) :
    AEEquivalent hc C Ξ hΞ ((F.posCoef hc C Ξ hΞ U).headIntegral hc C Ξ hΞ hGenerated)
      ((F.headIntegral hc C Ξ hΞ hGenerated).leftProduct hc C Ξ hΞ U) := by
  apply presentation_ae_of_generic_rows hc C Ξ hΞ
  intro x hx
  apply (gammaVolumeBlowupClass_eq_iff hc _ _).mp
  refine Eq.trans ?_ (presentation_left_product_row_class hc C Ξ hΞ U (F.headIntegral hc C Ξ hΞ hGenerated) x).symm
  exact (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
    ((head_pos_zero_common hc C Ξ hΞ hGenerated γ hγ1 hγ U F x hx).descend hc _
      (row_context_names 𝔇 𝔅 (gamma_named_code_context_names C Ξ hΞ) x))

end IntegrationInACVF.Section7.GammaFun
