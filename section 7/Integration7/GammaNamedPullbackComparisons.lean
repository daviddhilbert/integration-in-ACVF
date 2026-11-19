import Integration7.GammaNamedUnaryChains
import Integration7.PullbackUnaryChainVolumeComparison

/-! Gamma-named comparisons for actual RV pullbacks with a retained
coordinate density: the coordinate-density RV object agrees with every
standard contraction of the original VF volume object, and Gamma unary chains
with Gamma volume data compare the pullbacks at both ends. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a b : ℕ}

/-- A density given by an RV coordinate of a Gamma domain has a Gamma density graph. -/
theorem gamma_coordinate_volume_density_graph (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} (hA : GammaSetDefinable G (carrier A))
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ p, ω.value p = p.val.2 δ) :
    GammaSetDefinable G (volumeDensityGraph ω).carrier := by
  let τ : Fin (a+1) → Fin a := Fin.lastCases δ id
  have h := (gammaLogicInput G).image_real
    (mixedCoordinatePointMap (id : Fin n → Fin n) τ G.real) hA
  have hcond : ∀ q : Point (M := M) n (a+1), q ∈ (volumeDensityGraph ω).carrier ↔
      (q.1,q.2 ∘ Fin.castAdd 1) ∈ carrier A ∧ q.2 (Fin.last a) = q.2 (Fin.castAdd 1 δ) := by
    intro q
    rw [mem_volumeDensityGraph_iff]
    constructor
    · rintro ⟨h0,hq⟩
      refine ⟨h0,?_⟩
      have hv := hω ⟨_,h0⟩
      have h2 := congrArg (fun z : Point (M := M) n (a+1) => z.2) hq
      have hl : q.2 (Fin.last a) = (ω.map ⟨_,h0⟩).val 0 := by
        rw [congrFun h2 (Fin.last a)]
        change Fin.append (q.2 ∘ Fin.castAdd 1) (ω.map ⟨_,h0⟩).val (Fin.natAdd a 0) = _
        rw [Fin.append_right]
      rw [hl]
      exact hv
    · rintro ⟨h0,hl⟩
      refine ⟨h0,?_⟩
      have hv := hω ⟨_,h0⟩
      refine Prod.ext rfl ?_
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · change q.2 (Fin.last a) = Fin.append (q.2 ∘ Fin.castAdd 1) (ω.map ⟨_,h0⟩).val (Fin.natAdd a 0)
        rw [Fin.append_right,hl]
        exact hv.symm
      · change q.2 (Fin.castAdd 1 i) = Fin.append (q.2 ∘ Fin.castAdd 1) (ω.map ⟨_,h0⟩).val (Fin.castAdd 1 i)
        rw [Fin.append_left]
        rfl
  have he : {q | ∃ x : PresentedSet.univ (pointSpace (M := M) n a) G.real, x.val ∈ carrier A ∧
      (mixedCoordinatePointMap (id : Fin n → Fin n) τ G.real x).val = q} = (volumeDensityGraph ω).carrier := by
    ext q
    rw [Set.mem_setOf_eq,hcond]
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [mixedCoordinatePointMap_value]
      refine ⟨?_,?_⟩
      · have hx' : (x.val.1 ∘ id,(x.val.2 ∘ τ) ∘ Fin.castAdd 1) = x.val := by
          refine Prod.ext rfl ?_
          funext i
          change x.val.2 (Fin.lastCases (motive := fun _ => Fin a) δ id (Fin.castSucc i)) = x.val.2 i
          rw [Fin.lastCases_castSucc]
          rfl
        rw [hx']
        exact hx
      · change x.val.2 (Fin.lastCases (motive := fun _ => Fin a) δ id (Fin.last a)) =
          x.val.2 (Fin.lastCases (motive := fun _ => Fin a) δ id (Fin.castSucc δ))
        rw [Fin.lastCases_last,Fin.lastCases_castSucc]
        rfl
    · rintro ⟨h0,hl⟩
      refine ⟨⟨(q.1,q.2 ∘ Fin.castAdd 1),Set.mem_univ _⟩,h0,?_⟩
      rw [mixedCoordinatePointMap_value]
      refine Prod.ext rfl ?_
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · change q.2 (Fin.castAdd 1 (Fin.lastCases (motive := fun _ => Fin a) δ id (Fin.last a))) = q.2 (Fin.last a)
        rw [Fin.lastCases_last]
        exact hl.symm
      · change q.2 (Fin.castAdd 1 (Fin.lastCases (motive := fun _ => Fin a) δ id (Fin.castSucc i))) =
          q.2 (Fin.castSucc i)
        rw [Fin.lastCases_castSucc]
        rfl
  exact he ▸ h

namespace GammaNamed

theorem retained_density_graph_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ p, ω.value p = p.val.2 δ)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable G T.program) :
    let U := nativeMixedVFVolumeObject hc A hfin ω
    let hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := fun p =>
      (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨p.val,p.property⟩ ((hω ⟨p.val,p.property⟩).trans hz))
    ∀ (hU : VFVolumeObjectGamma U G) (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
      (hE : GammaProgramDefinable G E.program),
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hc C hGC A hA hfin δ hδ T hT)
      ⟨U.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC U hU E hE⟩ := by
  intro U hδ hU E hE
  let B := nativeMixedVolumeDomain hc U.densityGraph.domain
  let e := volumeDensityGraphBijection hc C U
  let g : Map A B := nativeMixedVolumeMap hc e.map
  have hg : Function.Bijective g := native_mixed_volume_map_bijective hc e.map e.bijective
  have hm : PreservesVFVolume ω U.densityGraph.form (rawSpecialMap hc g) := e.preserves
  have hi : UnaryRelative g (σ 0) := fun _ _ _ => rfl
  have hgΓ : GammaGraphDefinable G (pointMapGraph g) := by
    apply GammaGraphDefinable.congr ((gammaLogicInput G).swap_graph hU.projection_graph)
    intro p q
    constructor
    · rintro ⟨hq,rfl⟩
      obtain ⟨hq0,hqe⟩ := (mem_volumeDensityGraph_iff U.form q).mp hq
      exact ⟨⟨_,hq0⟩,rfl,hqe.symm⟩
    · rintro ⟨u,rfl,rfl⟩
      refine ⟨((appendDensityMap U.form).toImage ⟨u.val,u.property⟩).property,?_⟩
      change u.val = ((appendDensityMap U.form ⟨u.val,u.property⟩).val.1,
        (appendDensityMap U.form ⟨u.val,u.property⟩).val.2 ∘ Fin.castAdd 1)
      rw [appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext i
      exact (Fin.append_left _ _ i).symm
  exact finite_relative_volume_comparison_of_generic_extension (B := G) hc C C.uncountable.le
    C.saturated ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hGC hΞ γ hγ hγ1 hGeneric
    A B hA hU.densityGraph hfin U.densityGraph.finite_labels g hg hgΓ
    ω U.densityGraph.form hm hi T E hT hE δ (Fin.last U.arity) hω (densityGraph_form_last U)

theorem pullback_original_volume_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (hA : GammaSetDefinable G (carrier A))
    (hPull : IsRVPullback (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ p, ω.value p = p.val.2 δ) :
    let U := nativeMixedVFVolumeObject hc A hfin ω
    let hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := fun p =>
      (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨p.val,p.property⟩ ((hω ⟨p.val,p.property⟩).trans hz))
    ∀ (hU : VFVolumeObjectGamma U G) {υ : Equiv.Perm (Fin (n+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) υ)
    (hE : GammaProgramDefinable G E.program),
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C hGC A hA hAF δ hδ)
      ⟨U.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC U hU E hE⟩ := by
  intro U hδ hU υ E hE
  have hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  obtain ⟨T,hT,D,hCD,hCanon⟩ := pullback_canonical_contraction_volume_exists (G := G)
    C.uncountable.le C.saturated hreal hc C hGC A hA hPull hfin hAF δ hδ
  let B := nativeMixedVolumeDomain hc U.densityGraph.domain
  obtain ⟨F,hF,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    hreal hGenerated hGC B hU.densityGraph (Equiv.refl _)
  have hCanonical : CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C hGC A hA hAF δ hδ)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C
        hGC A hA hfin δ hδ T hT) := ⟨D,hCD,hCanon⟩
  have hGraph := retained_density_graph_contraction_comparison hc C G hGC hΞ hGeneric γ hγ hγ1
    A hA hfin ω δ hω T hT hU F hF
  have hOrders := standard_volume_contraction_order_independent hc C G hGC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 U hU F E hF hE
  exact hCanonical.trans hc (hGraph.trans hc hOrders)

theorem pullback_unary_chain_volume_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (B : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hA : GammaSetDefinable G (carrier A)) (hB : GammaSetDefinable G (carrier B))
    (hAP : IsRVPullback (carrier A)) (hBP : IsRVPullback (carrier B))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (hBF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject B)))
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b) (hω : ∀ p, ω.value p = p.val.2 δ) (hπ : ∀ p, π.value p = p.val.2 ε)
    (T : UnaryChain (C.base : Set M) (n+1) A B) (hT : GammaUnaryChainDefinable G T)
    (hData : gammaUnaryChainVolumeData hc G T ω π) :
    let hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := fun p =>
      (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨p.val,p.property⟩ ((hω ⟨p.val,p.property⟩).trans hz))
    let hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero := fun p =>
      (rv_nonzero_iff_raw _).mp (fun hz => π.nonzero ⟨p.val,p.property⟩ ((hπ ⟨p.val,p.property⟩).trans hz))
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C hGC A hA hAF δ hδ)
      (pullbackCoordinateGammaObject hc C hGC B hB hBF ε hε) := by
  intro hδ hε
  have hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  have hωΓ := gamma_coordinate_volume_density_graph hc hA ω δ hω
  have hπΓ := gamma_coordinate_volume_density_graph hc hB π ε hπ
  let U := nativeMixedVFVolumeObject hc A hfinA ω
  let V := nativeMixedVFVolumeObject hc B hfinB π
  have hU : VFVolumeObjectGamma U G := VFVolumeObjectGamma.of_density_graph hωΓ
  have hV : VFVolumeObjectGamma V G := VFVolumeObjectGamma.of_density_graph hπΓ
  obtain ⟨D,hD,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    hreal hGenerated hGC (nativeMixedVolumeDomain hc U.densityGraph.domain) hωΓ (Equiv.refl _)
  obtain ⟨E,hE,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    hreal hGenerated hGC (nativeMixedVolumeDomain hc V.densityGraph.domain) hπΓ (Equiv.refl _)
  have hLeft := pullback_original_volume_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 A hA hAP hfinA hAF ω δ hω hU D hD
  have hRight := pullback_original_volume_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 B hB hBP hfinB hBF π ε hπ hV E hE
  have hMiddle := unary_chain_volume_contractions_compare hc C G hGC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 T hT ω π hωΓ hπΓ hData hfinA hfinB hU hV D E hD hE
  exact hLeft.trans hc (hMiddle.trans hc (hRight.symm hc))

end GammaNamed
end IntegrationInACVF.Section7
