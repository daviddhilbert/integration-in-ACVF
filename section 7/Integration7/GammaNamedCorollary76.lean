import Integration7.GammaNamedArbitraryOrders
import Integration7.GammaNamedRelativeSchemaComparisons
import Integration7.GammaNamedDensityGraphs
import Integration7.RelativeVolumeArbitraryContractions

/-! Gamma-named Corollary 7.6 and contraction-order independence for actual
positive VF volume objects whose domains and density graphs are
Gamma-definable over an arbitrary Gamma base `G`, coded in a context
containing the common names of `G`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem standard_contraction_object_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (hU : VFVolumeObjectGamma U G)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (hT : GammaProgramDefinable G T.program) :
    VolumeObjectGamma (U.standardContractionObject hc C G.gamma T) G :=
  gamma_coordinate_density_object_graphs (M := M) (B := G) (e := k) (k := 0) hc C
    (FiniteRV.gammaFiniteContraction C.uncountable.le C.saturated
      ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hGC hU.densityGraph
      U.densityGraph.finite_labels T hT) (Set.Subset.refl _)
    (FiniteRV.contractionOldLabelIndex T (Fin.last U.arity)) (U.standardContractionDensity_nonzero hc G.gamma T)

theorem gamma_native_density_graph_map
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (G : Base (M := M))
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (hU : VFVolumeObjectGamma U G) (hV : VFVolumeObjectGamma V G)
    (f : VFVolumeBijection U V) (hf : GammaGraphDefinable G (vfMixedMapGraph f.map)) :
    GammaGraphDefinable G (pointMapGraph (nativeMixedVolumeMap hc (f.onDensityGraphs hc C).map)) := by
  apply GammaGraphDefinable.congr (gamma_on_density_graphs hc C hU hV f hf)
  intro p q
  constructor
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩

set_option maxHeartbeats 3200000 in
theorem corollary_7_6
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (hU : VFVolumeObjectGamma U G) (hV : VFVolumeObjectGamma V G)
    (f : VFVolumeBijection U V) (hf : GammaGraphDefinable G (vfMixedMapGraph f.map))
    {σ : Equiv.Perm (Fin (k+1))}
    (hi : ∀ p : U.domain, ∀ j, j ≠ σ 0 → (f.map p).val.1 j = p.val.1 j)
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) σ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨U.standardContractionObject hc C G.gamma T,standard_contraction_object_gamma hc C G hGC U hU T hT⟩
      ⟨V.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC V hV E hE⟩ := by
  have hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  let Z := nativeMixedVolumeDomain hc V.densityGraph.domain
  let fD := f.onDensityGraphs hc C
  let g := nativeMixedVolumeMap hc fD.map
  have hg : Function.Bijective g := native_mixed_volume_map_bijective hc fD.map fD.bijective
  have hgΓ : GammaGraphDefinable G (pointMapGraph g) := gamma_native_density_graph_map hc C G hU hV f hf
  have hA : GammaSetDefinable G (carrier A) := hU.densityGraph
  have hZ : GammaSetDefinable G (carrier Z) := hV.densityGraph
  have hm : PreservesVFVolume U.densityGraph.form V.densityGraph.form (rawSpecialMap hc g) := fD.preserves
  have hGeom := standard_relative_volume_schema_comparison hc C C.uncountable.le
    C.saturated hreal hΞ γ hγ hγ1 hGC hGeneric
    A Z hA hZ U.densityGraph.finite_labels V.densityGraph.finite_labels g hg hgΓ
    U.densityGraph.form V.densityGraph.form (Fin.last U.arity) (Fin.last V.arity)
    (densityGraph_form_last U) (densityGraph_form_last V) hm
    (f.onDensityGraphs_relative hc C (σ 0) hi) T E hT hE
  exact finite_standard_volume_comparison_of_geometric_rows hc C C.uncountable.le C.saturated hreal
    hGC A Z hA hZ U.densityGraph.finite_labels V.densityGraph.finite_labels
    T E hT hE (Fin.last U.arity) (Fin.last V.arity)
    (fun q => (rv_nonzero_iff_raw _).mp (fun h => U.densityGraph.form.nonzero q ((densityGraph_form_last U q).trans h)))
    (fun q => (rv_nonzero_iff_raw _).mp (fun h => V.densityGraph.form.nonzero q ((densityGraph_form_last V q).trans h))) hGeom

theorem standard_volume_contraction_order_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (hU : VFVolumeObjectGamma U G)
    {σ υ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) υ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨U.standardContractionObject hc C G.gamma T,standard_contraction_object_gamma hc C G hGC U hU T hT⟩
      ⟨U.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC U hU E hE⟩ := by
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  have hδ : ∀ p ∈ carrier A, (p.2 (Fin.last U.arity)).val ≠ iRVZero := by
    intro p hp
    apply (rv_nonzero_iff_raw _).mp
    intro h
    exact U.densityGraph.form.nonzero ⟨p,hp⟩ ((densityGraph_form_last U ⟨p,hp⟩).trans h)
  exact retained_density_arbitrary_order_contractions_compare hc C G hGC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 A hU.densityGraph U.densityGraph.finite_labels (Fin.last U.arity) hδ σ υ T E hT hE

theorem relative_volume_contractions_all_orders
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (hU : VFVolumeObjectGamma U G) (hV : VFVolumeObjectGamma V G)
    (f : VFVolumeBijection U V) (hf : GammaGraphDefinable G (vfMixedMapGraph f.map))
    (i : Fin (k+1)) (hi : ∀ p : U.domain, ∀ j, j ≠ i → (f.map p).val.1 j = p.val.1 j)
    {σ υ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) υ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨U.standardContractionObject hc C G.gamma T,standard_contraction_object_gamma hc C G hGC U hU T hT⟩
      ⟨V.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC V hV E hE⟩ := by
  have hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  let B := nativeMixedVolumeDomain hc V.densityGraph.domain
  let ρ : Equiv.Perm (Fin (k+1)) := Equiv.swap 0 i
  obtain ⟨D,hD,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    hreal hGenerated hGC A hU.densityGraph ρ
  obtain ⟨F,hF,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    hreal hGenerated hGC B hV.densityGraph ρ
  have hLeft := standard_volume_contraction_order_independent hc C G hGC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 U hU T D hT hD
  have hRight := standard_volume_contraction_order_independent hc C G hGC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 V hV F E hF hE
  have hMiddle := corollary_7_6 hc C G hGC hΞ hGeneric γ hγ hγ1 U V hU hV f hf
    (by simpa only [ρ,Equiv.swap_apply_left] using hi) D F hD hF
  exact hLeft.trans hc (hMiddle.trans hc hRight)

end IntegrationInACVF.Section7.GammaNamed
