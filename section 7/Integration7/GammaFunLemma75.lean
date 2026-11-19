import Integration7.GammaFunFamilies
import Integration7.PositiveSelectedContractionObjects
import Integration7.SelectedFamilyStandardVolumeComparison

/-! **Gamma Lemma 7.5 for families.** Two Gamma selected VF volume families
whose rows are Gamma blowup equivalent at every VF point (over the row Gamma
base, coded over the row context) have Gamma blowup equivalent contraction
objects, in a common larger context. The Gamma base `G` and the code context
`C` are independent: `G.real ⊆ C.base`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)}
variable {n a b k : ℕ}

theorem standard_append_volume_object_gamma_of
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (G : Base (M := M))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin n → SpecialTransformations.Section5.VF (M := M)) (t : Fin (k+1) → SpecialTransformations.Section5.RV (M := M)),
      {r : Fin a → SpecialTransformations.Section5.RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) (hT : GammaProgramDefinable G T.program) :
    VolumeObjectGamma (standardAppendVolumeObject hc C Ξ U ρ δ hδ hfin T) G := by
  have hTarget := gamma_program_final_set T.program hT
  have hD : GammaSetDefinable G {p : Point (M := M) 0 T.arity |
      p.2 ∈ (rawVolumeContractionLabels hc T.target).carrier} := by
    have he : carrier T.target = {p : Point (M := M) 0 T.arity |
        p.2 ∈ (rawVolumeContractionLabels hc T.target).carrier} := by
      ext p
      have hp : p = (Fin.elim0,p.2) := Prod.ext (funext (fun i => Fin.elim0 i)) rfl
      change p ∈ carrier T.target ↔ p.2 ∈ (rawVolumeContractionLabels hc T.target).carrier
      rw [mem_rawVolumeContractionLabels hc T.target p.2,← hp]
    exact he ▸ hTarget
  exact ⟨gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (orderedAppendVolumeIndex T.program ρ))
      hD (fun _ => rfl),
    gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real
      (fun _ : Fin 1 => orderedAppendDensityIndex T.program δ)) hD (fun _ => rfl)⟩

theorem standard_append_volume_object_schema_row_of
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (G : Base (M := M))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin n → SpecialTransformations.Section5.VF (M := M)) (t : Fin (k+1) → SpecialTransformations.Section5.RV (M := M)),
      {r : Fin a → SpecialTransformations.Section5.RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) (hT : GammaProgramDefinable G T.program) :
    RVVolumeSchemaRow (standardAppendVolumeObject hc C Ξ U ρ δ hδ hfin T)
      (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
        (orderedAppendVolumeIndex T.program ρ) (orderedAppendDensityIndex T.program δ))
      (fun j : Fin 0 => (Fin.elim0 j : SpecialTransformations.Section5.VF (M := M)).val) := by
  have hTarget := gamma_program_final_set T.program hT
  have hNZ := ordered_append_retained_density_nonzero T.program δ
    (vf_permuted_retained_density_nonzero U σ δ hδ)
  constructor
  · intro r y
    have h := gammaSelectedLabelSchema_volume T.target hTarget (orderedAppendVolumeIndex T.program ρ)
      (Fin.elim0 : Fin 0 → SpecialTransformations.Section5.VF (M := M)) r y
    constructor
    · intro hr
      obtain ⟨hmem,hv⟩ := h.mp hr
      exact ⟨⟨r,(mem_rawVolumeContractionLabels hc T.target r).mpr hmem⟩,rfl,hv⟩
    · rintro ⟨u,hu,hv⟩
      apply h.mpr
      exact ⟨hu ▸ (mem_rawVolumeContractionLabels hc T.target u.val).mp u.property,
        (congrArg (fun r => r ∘ orderedAppendVolumeIndex T.program ρ) hu).symm.trans hv⟩
  · intro r w
    have h := gammaSelectedVolumeSchema_density T.target hTarget (orderedAppendVolumeIndex T.program ρ)
      (orderedAppendDensityIndex T.program δ) hNZ (Fin.elim0 : Fin 0 → SpecialTransformations.Section5.VF (M := M)) r w
    constructor
    · intro hr
      obtain ⟨hmem,hw⟩ := h.mp hr
      exact ⟨⟨r,(mem_rawVolumeContractionLabels hc T.target r).mpr hmem⟩,rfl,hw⟩
    · rintro ⟨u,hu,hw⟩
      apply h.mpr
      refine ⟨hu ▸ (mem_rawVolumeContractionLabels hc T.target u.val).mp u.property,?_⟩
      change (fun _ : Fin 1 => r (orderedAppendDensityIndex T.program δ)) = w
      change (fun _ : Fin 1 => u.val (orderedAppendDensityIndex T.program δ)) = w at hw
      rw [hu] at hw
      exact hw

/-- The native density-graph domain of a Gamma family is Gamma. -/
theorem SelectedVFVolumeFamily.Gamma.native_domain (hc : CanonicalStructure.IsCanonical (M := M))
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) :
    GammaSetDefinable G (carrier (nativeMixedVolumeDomain hc F.densityGraph.domain)) := by
  rw [nativeMixedVolumeDomain_carrier]
  exact hF.densityGraph

/-- Rows of the density graph of a Gamma family are Gamma. -/
theorem SelectedVFVolumeFamily.Gamma.densityGraph_row (hc : CanonicalStructure.IsCanonical (M := M))
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) (x : Fin n → VFType (M := M)) :
    VolumeObjectGamma (F.densityGraph.rowInContext x) (rowGammaBase G x) := by
  have hD : GammaSetDefinable (rowGammaBase G x) {p : Point (M := M) 0 (a+1) |
      p.2 ∈ (F.densityGraph.rowInContext x).underlying.obj.domain.carrier} :=
    gamma_vf_fibre hF.densityGraph x
  refine ⟨gamma_rv_coordinate_map hc _ F.densityGraph.selected hD (fun _ => rfl),?_⟩
  apply (gamma_rv_coordinate_map hc ((rvCoordinateSelectMap _ (fun _ : Fin 1 => Fin.last a)).restrict
    (Set.subset_univ _) : Map (F.densityGraph.rowInContext x).underlying.obj.domain _)
    (fun _ : Fin 1 => Fin.last a) hD (fun _ => rfl)).congr
  intro r
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  exact (F.densityGraph_form_last ⟨(x,r.val),r.property⟩).symm

/-- The row identification with the density-graph row is Gamma. -/
theorem SelectedVFVolumeFamily.Gamma.densityGraphRowIso (hc : CanonicalStructure.IsCanonical (M := M))
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) (x : Fin n → VFType (M := M)) :
    (F.densityGraphRowIso hc x).GammaDefinable (rowGammaBase G x) := by
  have hS := gamma_vf_fibre hF.densityGraph x
  let L := gammaLogicInput (rowGammaBase G x)
  have hgraph := L.swap_graph (L.restrict_graph hS (gamma_drop_last_rv_graph (G := rowGammaBase G x) (n := 0) (a := a)))
  apply gamma_volume_iso_of_preserving_coordinates_full hc (vfParameterVolumeContext C x) _
    (F.densityGraphRowMap_coordinates x) (F.densityGraphRowMap_density x)
    (gamma_essential_volume_domain _ (hF.row hc x).coordinates)
  apply GammaGraphDefinable.congr hgraph
  intro p q
  constructor
  · rintro ⟨hq,hp⟩
    have hmem : p.2 ∈ (F.rowInContext x).underlying.obj.domain.carrier := by
      rw [show p.2 = q.2 ∘ Fin.castAdd 1 from congrArg Prod.snd hp]
      obtain ⟨h0,_⟩ := (mem_volumeDensityGraph_iff F.form (x,q.2)).mp hq
      exact h0
    refine ⟨⟨p.2,hmem⟩,rfl,?_⟩
    obtain ⟨h0,hqe⟩ := (mem_volumeDensityGraph_iff F.form (x,q.2)).mp hq
    have hq2 := congrArg Prod.snd hqe
    change q.2 = Fin.append (q.2 ∘ Fin.castAdd 1) (F.form.map ⟨_,h0⟩).val at hq2
    change Fin.append p.2 ((F.rowObject x).form.map ⟨p.2,hmem⟩).val = q.2
    rw [hq2]
    have hpq : p.2 = q.2 ∘ Fin.castAdd 1 := congrArg Prod.snd hp
    have he : (⟨(x,q.2 ∘ Fin.castAdd 1),h0⟩ : F.domain) = ⟨(x,p.2),hmem⟩ := Subtype.ext (Prod.ext rfl hpq.symm)
    rw [he]
    congr 1
  · rintro ⟨u,hu,hq⟩
    refine ⟨?_,?_⟩
    · change (x,q.2) ∈ (volumeDensityGraph F.form).carrier
      rw [← hq]
      exact (F.densityGraphRowMap x ⟨u.val,u.property⟩).property
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      rw [← hq, ← hu]
      funext j
      exact (Fin.append_left _ _ j).symm

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)}
variable {n a b k : ℕ}

theorem SelectedVFVolumeFamily.densityGraph_schema_rows_of (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C n a k)
    (hU : GammaSetDefinable G (carrier (nativeMixedVolumeDomain hc F.densityGraph.domain)))
    (x : Fin n → SpecialTransformations.Section5.VF (M := M)) :
    RVVolumeSchemaRow (F.densityGraph.rowInContext x)
      (gammaSelectedVolumeSchema (nativeMixedVolumeDomain hc F.densityGraph.domain) hU F.densityGraph.selected
        (Fin.last a)) (fun j => (x j).val) := by
  let U := nativeMixedVolumeDomain hc F.densityGraph.domain
  constructor
  · intro r t
    change (gammaSelectedLabelSchema U hU F.densityGraph.selected).rowVolume _ r t ↔ _
    rw [gammaSelectedLabelSchema_volume]
    exact ⟨fun h => ⟨⟨r,h.1⟩,rfl,h.2⟩,by rintro ⟨u,rfl,rfl⟩; exact ⟨u.property,rfl⟩⟩
  · intro r y
    change (gammaSelectedVolumeSchema U hU F.densityGraph.selected (Fin.last a)).rowDensity _ r y ↔ _
    rw [gammaSelectedVolumeSchema_density U hU F.densityGraph.selected (Fin.last a)
      (fun q hq => F.densityGraph_label_nonzero q hq)]
    constructor
    · rintro ⟨hr,hy⟩
      refine ⟨⟨r,hr⟩,rfl,?_⟩
      funext i
      have hd := F.densityGraph_form_last ⟨(x,r),hr⟩
      have hi := congrFun hy i
      fin_cases i
      exact hd.trans hi
    · rintro ⟨u,rfl,rfl⟩
      refine ⟨u.property,?_⟩
      funext i
      fin_cases i
      exact (F.densityGraph_form_last ⟨(x,u.val),u.property⟩).symm

/-- Gamma row equivalence of two Gamma families at a VF point. -/
def GammaRowsEquivalent (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (G : Base (M := M))
    {F : SelectedVFVolumeFamily C n a k} {H : SelectedVFVolumeFamily C n b k}
    (hF : F.Gamma G) (hH : H.Gamma G) (x : Fin n → VFType (M := M)) : Prop :=
  GammaVolumeBlowupEquivalent (rowGammaBase G x) ((vfParameterVolumeContext C x).base : Set M) k
    ⟨F.rowInContext x,hF.row hc x⟩ ⟨H.rowInContext x,hH.row hc x⟩

set_option maxHeartbeats 2400000 in
/-- **Gamma Lemma 7.5 for families.** -/
theorem gamma_family_lemma_7_5 (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {F : SelectedVFVolumeFamily C n a k} {H : SelectedVFVolumeFamily C n b k}
    (hF : F.Gamma G) (hH : H.Gamma G) (hCommon : ∀ x, GammaRowsEquivalent hc C G hF hH x)
    {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc H.densityGraph.domain) σ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨F.standardAppendObject hc G.gamma T,standard_append_volume_object_gamma_of hc C G.gamma G _ _ _ _ _ T hT⟩
      ⟨H.standardAppendObject hc G.gamma E,standard_append_volume_object_gamma_of hc C G.gamma G _ _ _ _ _ E hE⟩ := by
  let U := nativeMixedVolumeDomain hc F.densityGraph.domain
  let V := nativeMixedVolumeDomain hc H.densityGraph.domain
  have hU : GammaSetDefinable G (carrier U) := hF.native_domain hc
  have hV : GammaSetDefinable G (carrier V) := hH.native_domain hc
  have hPoint : ∀ x : Fin n → SpecialTransformations.Section5.VF (M := M),
      (gammaSelectedVolumeSchema U hU F.densityGraph.selected (Fin.last a)).commonByGammaGeometry
        (gammaSelectedVolumeSchema V hV H.densityGraph.selected (Fin.last b)) (fun j => (x j).val) := by
    intro x
    let Cx := vfParameterVolumeContext C x
    have h1 := GammaVolumeBlowupEquivalent.of_iso Cx (rowGammaBase G x)
      (U := ⟨F.densityGraph.rowInContext x,hF.densityGraph_row hc x⟩) (V := ⟨F.rowInContext x,hF.row hc x⟩)
      ((F.densityGraphRowIso hc x).symm hc Cx) ((hF.densityGraphRowIso hc x).symm hc Cx _)
    have h2 := GammaVolumeBlowupEquivalent.of_iso Cx (rowGammaBase G x)
      (U := ⟨H.rowInContext x,hH.row hc x⟩) (V := ⟨H.densityGraph.rowInContext x,hH.densityGraph_row hc x⟩)
      (H.densityGraphRowIso hc x) (hH.densityGraphRowIso hc x)
    exact ⟨Cx,⟨F.densityGraph.rowInContext x,hF.densityGraph_row hc x⟩,
      ⟨H.densityGraph.rowInContext x,hH.densityGraph_row hc x⟩,rfl,rfl,
      F.densityGraph_schema_rows_of hc hU x,H.densityGraph_schema_rows_of hc hV x,
      (h1.trans hc Cx _ (hCommon x)).trans hc Cx _ h2⟩
  have hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  have hTotal := lemma_7_5_standard_geometric hc C C.uncountable.le C.saturated C.model00 hreal hgamma γ hγ hγ1
    hGC U V hU hV F.densityGraph.selected H.densityGraph.selected (Fin.last a) (Fin.last b)
    (fun p hp => F.densityGraph_label_nonzero p hp) (fun p hp => H.densityGraph_label_nonzero p hp)
    F.densityGraph.finite_selected H.densityGraph.finite_selected hPoint T E hT hE
  let z : Fin 0 → M := fun i => (Fin.elim0 i : SpecialTransformations.Section5.VF (M := M)).val
  have hBase : (⟨G.real ∪ Set.range z,G.gamma⟩ : Base (M := M)) = G := by
    change (⟨G.real ∪ Set.range z,G.gamma⟩ : Base (M := M)) = ⟨G.real,G.gamma⟩
    rw [Set.range_eq_empty,Set.union_empty]
  have hUo := standard_append_volume_object_gamma_of hc C G.gamma G U F.densityGraph.selected (Fin.last a)
    (fun p hp => F.densityGraph_label_nonzero p hp) F.densityGraph.finite_selected T hT
  have hVo := standard_append_volume_object_gamma_of hc C G.gamma G V H.densityGraph.selected (Fin.last b)
    (fun p hp => H.densityGraph_label_nonzero p hp) H.densityGraph.finite_selected E hE
  have hU' : VolumeObjectGamma (F.standardAppendObject hc G.gamma T) ⟨G.real ∪ Set.range z,G.gamma⟩ := hBase.symm ▸ hUo
  have hV' : VolumeObjectGamma (H.standardAppendObject hc G.gamma E) ⟨G.real ∪ Set.range z,G.gamma⟩ := hBase.symm ▸ hVo
  have hBC : G.real ∪ Set.range z ⊆ (C.base : Set M) := by
    simpa only [Set.range_eq_empty,Set.union_empty] using hGC
  obtain ⟨D,hCD,h⟩ := GammaRVVolumeSchema.commonByGammaGeometry_on_objects hc C _ _ _ _ z
    (standard_append_volume_object_schema_row_of hc C G.gamma G U F.densityGraph.selected (Fin.last a)
      (fun p hp => F.densityGraph_label_nonzero p hp) F.densityGraph.finite_selected T hT)
    (standard_append_volume_object_schema_row_of hc C G.gamma G V H.densityGraph.selected (Fin.last b)
      (fun p hp => H.densityGraph_label_nonzero p hp) H.densityGraph.finite_selected E hE)
    hU' hV' hBC (hTotal Fin.elim0)
  exact ⟨D,hCD,h.rebase hBase⟩

end IntegrationInACVF.Section7
