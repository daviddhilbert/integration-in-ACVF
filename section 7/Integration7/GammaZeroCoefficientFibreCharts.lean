import Integration7.GammaCoefficientFibreCharts
import Integration7.HKZeroCoefficientContractionProductCharts
import Integration7.HKZeroRVNativeDensityPresentations
import Integration7.GammaFunZeroCoefficients
import Integration7.GammaNamedZeroBlowupProducts

/-! **Gamma charts for weighted degree-zero coefficients of unary families.** Native presentations
of Gamma weighted degree-zero objects, the lift of a Gamma special preparation to the native
zero-coefficient family, and the zero-coefficient contraction chart are Gamma-definable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier headImage SpecialBijection GammaChainDefinable GammaSetDefinable Point gammaLogicInput)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M}
variable {a b d k l r : ℕ}

theorem gamma_native_zero_density_object (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d) (hRΓ : GammaSetDefinable G (carrier R))
    (ε : Fin d) (hR : (rawVolumeContractionLabels hc R).carrier.Finite) (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) :
    (HK.nativeZeroDensityObject hc C R ε hR hε).Gamma G :=
  ⟨gamma_raw_contraction_labels_set hc C R hRΓ,
    gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (fun _ : Fin 1 => ε))
      (gamma_raw_contraction_labels_set hc C R hRΓ) (fun _ => rfl)⟩

theorem gamma_append_zero_rv_density (hc : CanonicalStructure.IsCanonical (M := M))
    {Z : HK.ZeroRVVolumeObject (M := M) S} (hZ : Z.Gamma G) : RVMapGamma (HK.appendZeroRVDensity Z) G := by
  have hid : RVMapGamma (Map.id Z.underlying.obj.domain).toUniv G :=
    (RVMapGamma.identity hc hZ.domain).congr (fun _ => rfl)
  exact (hid.append hZ.density).congr (fun _ => rfl)

theorem HK.ZeroRVVolumeObject.Gamma.densityGraph (hc : CanonicalStructure.IsCanonical (M := M))
    {Z : HK.ZeroRVVolumeObject (M := M) S} (hZ : Z.Gamma G) : Z.densityGraph.Gamma G := by
  have hA := gamma_append_zero_rv_density hc hZ
  have hD : GammaSetDefinable G {p : Point (M := M) 0 (Z.underlying.obj.arity+1) |
      p.2 ∈ Z.densityGraph.underlying.obj.domain.carrier} := by
    have h := (gammaLogicInput G).image_graph hA
    convert h using 1
    ext q
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨(Fin.elim0,u.val),⟨u,rfl,hu⟩⟩
    · rintro ⟨p,⟨u,_,hu⟩⟩
      exact ⟨u,hu⟩
  have hInv : RVMapGamma ((HK.appendZeroRVDensity Z).toImage.inverse (HK.append_zero_rv_density_bijective Z)) G := by
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput G).swap_graph hA)
    intro q p
    constructor
    · rintro ⟨u,hu,hq⟩
      refine ⟨(HK.appendZeroRVDensity Z).toImage u,hq,?_⟩
      change ((HK.appendZeroRVDensity Z).toImage.inverse _ ((HK.appendZeroRVDensity Z).toImage u)).val = p.2
      rw [Map.inverse_apply]
      exact hu
    · rintro ⟨v,hv,hp⟩
      refine ⟨(HK.appendZeroRVDensity Z).toImage.inverse (HK.append_zero_rv_density_bijective Z) v,hp,?_⟩
      exact (congrArg Subtype.val (Map.apply_inverse (HK.appendZeroRVDensity Z).toImage
        (HK.append_zero_rv_density_bijective Z) v)).trans hv
  exact ⟨hD,(hInv.comp hZ.density).congr (fun _ => rfl)⟩

theorem gamma_zero_rv_native_density_domain (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)} (hZ : Z.Gamma G) :
    GammaSetDefinable G (carrier (HK.zeroRVNativeDensityDomain hc C Z)) := by
  have h := (hZ.densityGraph hc).domain
  have he : carrier (HK.zeroRVNativeDensityDomain hc C Z) =
      {p : Point (M := M) 0 (Z.underlying.obj.arity+1) | p.2 ∈ Z.densityGraph.underlying.obj.domain.carrier} := by
    ext p
    change (p.1 ∈ Set.univ ∧ p.2 ∈ Z.densityGraph.underlying.obj.domain.carrier) ↔ _
    simp only [Set.mem_univ,true_and]
    rfl
  rw [he]
  exact h

theorem HK.ZeroRVVolumeObject.Gamma.zeroRVNativeDensity (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)} (hZ : Z.Gamma G) :
    (HK.zeroRVNativeDensityObject hc C Z).Gamma G :=
  gamma_native_zero_density_object hc C _ (gamma_zero_rv_native_density_domain hc C hZ) _ _ _

theorem zero_rv_native_density_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)} (hZ : Z.Gamma G) :
    (HK.zeroRVNativeDensityIso hc C Z).GammaDefinable G := by
  have h1 : (HK.zeroRVDensityGraphIso Z).GammaDefinable G := (gamma_append_zero_rv_density hc hZ).congr (fun _ => rfl)
  refine HK.ZeroRVVolumeIso.GammaDefinable.trans h1 ?_
  exact gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real id) (hZ.densityGraph hc).domain (fun _ => rfl)

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

/-- A Gamma special preparation of a retained unary family lifts to its native zero-coefficient family. -/
theorem gamma_native_zero_coefficient_preparation_exists (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C 1 a k)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d) (ε : Fin d)
    (hR : (rawVolumeContractionLabels hc R).carrier.Finite) (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B) (hT : GammaChainDefinable G T.chain)
    (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
    (hJ : (HK.nativeZeroCoefficientFamily hc C F R ε hR hε).Gamma G) :
    Nonempty (RVLabelConstraintSpecialPreparation T
      (nativeMixedVolumeDomain hc (HK.nativeZeroCoefficientFamily hc C F R ε hR hε).densityGraph.domain)
      (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d) G) := by
  have hH := hJ.native_domain hc
  rw [HK.native_zero_coefficient_density_graph_source hc C F R ε hR hε Ξ hNames δ hF] at hH ⊢
  exact gamma_rv_label_constraint_special_preparation_exists T hT hB _ hH _ _
    (constrained_unary_source_mem C Ξ hNames _ _ _)

/-- Native zero-coefficient product charts are Gamma-definable (they are coordinate selections). -/
theorem native_zero_rv_product_volume_chart_iso_gamma
    (Q : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 r)
    (f : SpecialTransformations.Section5.Map Q (SpecialTransformations.Section5.PresentedSet.prod R Z))
    (hf : Function.Bijective f) (κ : Fin r → Fin l) (hκ : ∀ q : Q, (f q).val.2.2=q.val.2 ∘ κ)
    (δ : Fin d) (hR : (rawVolumeContractionLabels hc R).carrier.Finite) (hδ : ∀ q : R, (q.val.2 δ).val ≠ iRVZero)
    (τ : Fin (k+1) → Fin r) (ε : Fin r)
    (hZ : ∀ t : Fin (k+1) → RV (M := M), {s : Fin r → RV (M := M) | (Fin.elim0,s) ∈ carrier Z ∧ s ∘ τ=t}.Finite)
    (hε : ∀ q : Z, (q.val.2 ε).val ≠ iRVZero)
    (ι : Fin d → Fin l) (hι : ∀ q : Q, (f q).val.1.2=q.val.2 ∘ ι)
    (hQ : GammaSetDefinable G (carrier Q)) :
    (HK.nativeZeroRVProductVolumeChartIso hc C Q R Z f hf κ hκ δ hR hδ τ ε hZ hε).GammaDefinable G := by
  have hD := gamma_raw_contraction_labels_set hc C Q hQ
  have hCoord : RVMapGamma (HK.nativeZeroRVProductVolumeChart hc C Q R Z f hf κ hκ δ hR hδ τ ε hZ hε).underlying.obj.volume G :=
    gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (κ ∘ τ)) hD (fun _ => rfl)
  refine gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (Fin.append ι κ))
    (gamma_essential_volume_domain _ hCoord) (fun u => ?_)
  change (nativeRVProductMapTransfer hc f ⟨u.val,SpecialTransformations.Section9.rvEssentialLabels_subset _ u.property⟩).val =
    u.val ∘ Fin.append ι κ
  rw [native_rv_product_map_transfer_value]
  simp only []
  rw [hι,hκ]
  funext j
  cases j using Fin.addCases <;> simp only [Function.comp_apply,Fin.append_left,Fin.append_right]

/-- The zero-coefficient contraction chart is Gamma-definable. -/
theorem zero_coefficient_contraction_product_iso_gamma (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C 1 a k)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d) (ε : Fin d)
    (hR : (rawVolumeContractionLabels hc R).carrier.Finite) (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) (δ : Fin a)
    (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B)
    (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
    (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (L : RVLabelConstraintSpecialPreparation T
      (nativeMixedVolumeDomain hc (HK.nativeZeroCoefficientFamily hc C F R ε hR hε).densityGraph.domain)
      (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d)
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hSource : VolumeObjectGamma ((HK.nativeZeroCoefficientFamily hc C F R ε hR hε).standardAppendObject hc Ξ
      (unarySpecialStandardContraction L.special L.pullback)) G)
    (hL : GammaSetDefinable G (carrier (headImage L.target))) :
    (HK.zeroCoefficientContractionProductIso hc C Ξ hNames F R ε hR hε δ hδ T hB hT L).GammaDefinable G := by
  unfold HK.zeroCoefficientContractionProductIso
  dsimp only
  refine RVVolumeIso.GammaDefinable.trans hc C G (gamma_volume_iso_of_label_identity hc _ hSource rfl (fun _ => rfl)) ?_
  refine native_zero_rv_product_volume_chart_iso_gamma hc C _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (L.headParameters ∘ (Fin.castAdd 1 ∘ Fin.natAdd a)) ?_ hL
  intro q
  exact independent_rv_graph_factorization_coefficient_labels C Ξ hNames a R _ (L.headParameterMap q)

end IntegrationInACVF.Section7
