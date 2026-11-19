import Integration7.GammaVFProducts
import Integration7.VFVolumeIntegralPermutationCovariance
import Integration7.PermutedRawContractionVolumeCharts

/-! **Gamma VF permutation covariance.** For a Gamma positive VF volume object `X` and a
permutation `σ` of its VF coordinates, Gamma standard contractions of the permuted object
`X.permuteVF σ` are common-context equivalent to the `σ`-permutation of Gamma standard
contractions of `X`. This is the Gamma form of the covariance of integration under VF coordinate
permutations; no hypothesis puts common names into the code set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {k n a : ℕ}

theorem gamma_mixed_vf_permutation_domain
    {A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n a) S}
    (hA : GammaSetDefinable G A.carrier) (σ : Equiv.Perm (Fin n)) :
    GammaSetDefinable G (mixedVFPermutationDomain A σ).carrier := by
  convert gamma_mixed_coordinate_preimage hA (σ.symm : Fin n → Fin n) (id : Fin a → Fin a) using 1
  ext p
  exact mem_mixed_vf_permutation_domain A σ p.1 p.2

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem permuted_vf_density_graph_bijection_value (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (σ : Equiv.Perm (Fin (k+1))) (q : (U.permuteVF σ).domain) :
    ((permutedVFDensityGraphBijection hc C U σ).map q).val = (appendDensityMap (U.permuteVF σ).form q).val := by
  have hv := mixed_vf_permutation_inverse_value U.domain σ q
  let i := (mixedVFPermutationBijection U.domain σ).inverse (mixed_vf_permutation_bijective U.domain σ)
  change (((appendDensityMap U.form) (i q)).val.1 ∘ σ,((appendDensityMap U.form) (i q)).val.2) = _
  rw [appendDensityMap_value,appendDensityMap_value]
  refine Prod.ext ?_ ?_
  · funext t
    change (i q).val.1 (σ t) = q.val.1 t
    have h1 := congrArg Prod.fst hv
    rw [show (i q).val.1 = q.val.1 ∘ σ.symm from h1]
    simp
  · have h2 : (i q).val.2 = q.val.2 := by
      have := congrArg Prod.snd hv
      exact this
    change Fin.append (i q).val.2 (U.form.map (i q)).val = Fin.append q.val.2 (U.form.map (i q)).val
    rw [h2]

include hc in
theorem permuted_vf_density_graph_carrier (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (σ : Equiv.Perm (Fin (k+1))) :
    (volumeDensityGraph (U.permuteVF σ).form).carrier = (U.densityGraph.permuteVF σ).domain.carrier := by
  let f := permutedVFDensityGraphBijection hc C U σ
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    have h := (f.map p).property
    have e := permuted_vf_density_graph_bijection_value hc C U σ p
    rw [e] at h
    exact h
  · intro hq
    obtain ⟨p,hp⟩ := f.bijective.2 ⟨q,hq⟩
    refine ⟨p,?_⟩
    have := permuted_vf_density_graph_bijection_value hc C U σ p
    rw [hp] at this
    exact this.symm

include hc in
/-- **VF permutations of Gamma objects are Gamma.** -/
theorem VFVolumeObjectGamma.permuteVF {U : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (hU : VFVolumeObjectGamma U G) (σ : Equiv.Perm (Fin (k+1))) : VFVolumeObjectGamma (U.permuteVF σ) G := by
  refine ⟨gamma_mixed_vf_permutation_domain hU.domain σ,?_⟩
  rw [permuted_vf_density_graph_carrier hc C U σ]
  exact gamma_mixed_vf_permutation_domain hU.densityGraph σ

/-- The density-graph bijection of a permuted Gamma object is a Gamma isomorphism. -/
theorem permuted_vf_density_graph_iso_gamma {U : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (hU : VFVolumeObjectGamma U G) (σ : Equiv.Perm (Fin (k+1))) :
    (VFVolumeIso.of_bijection (permutedVFDensityGraphBijection hc C U σ)).GammaDefinable G := by
  have hσ := hU.permuteVF hc C σ
  refine ⟨hσ.domain,gamma_mixed_vf_permutation_domain hU.densityGraph σ,?_⟩
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_volume_density_graph_iso hc C hσ).graph
  intro p q
  constructor
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨u,rfl,permuted_vf_density_graph_bijection_value hc C U σ u⟩
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨u,rfl,(permuted_vf_density_graph_bijection_value hc C U σ u).symm⟩

/-- The native chart of a permuted density graph is a Gamma isomorphism. -/
theorem native_permuted_vf_volume_iso_gamma {U : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (hU : GammaSetDefinable G U.domain.carrier) (σ : Equiv.Perm (Fin (k+1))) :
    (VFVolumeIso.of_bijection (nativePermutedVFVolumeBijection hc C U σ)).GammaDefinable G := by
  have hS := gamma_mixed_vf_permutation_domain hU σ
  have hT : GammaSetDefinable G (nativePermutedVFVolumeObject hc U σ).domain.carrier := by
    rw [show (nativePermutedVFVolumeObject hc U σ).domain.carrier = (U.permuteVF σ).domain.carrier from
      (raw_native_vf_permutation_carrier hc U.domain σ).symm]
    exact hS
  exact ⟨hS,hT,vf_identity_map_gamma _ (fun _ => rfl) hS⟩

/-- The permuted raw standard contraction chart is Gamma. -/
theorem permuted_raw_contraction_volume_iso_gamma (hGC : G.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable G T.program) :
    (permutedRawContractionVolumeIso hc C G.gamma A hfin δ hδ T).GammaDefinable G :=
  gamma_volume_iso_of_label_identity hc _
    ((GammaNamed.raw_standard_volume_object_gamma hc C G hGC A hA hfin δ hδ T hT).permuteVolume hc σ) rfl (fun _ => rfl)

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k n a : ℕ}

set_option maxHeartbeats 3200000 in
/-- A Gamma raw standard contraction of a coordinate-density domain is common-context equivalent to
every Gamma standard contraction of its native VF volume object. -/
theorem gamma_native_raw_standard_contraction (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ p, ω.value p = p.val.2 δ)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable G T.program)
    (hU : VFVolumeObjectGamma (nativeMixedVFVolumeObject hc A hfin ω) G) {υ : Equiv.Perm (Fin (n+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc (nativeMixedVFVolumeObject hc A hfin ω).densityGraph.domain) υ)
    (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨rawStandardVolumeObject hc C G.gamma A hfin δ hδ T,raw_standard_volume_object_gamma hc C G hGC A hA hfin δ hδ T hT⟩
      ⟨(nativeMixedVFVolumeObject hc A hfin ω).standardContractionObject hc C G.gamma E,
        standard_contraction_object_gamma hc C G hGC _ hU E hE⟩ := by
  let U := nativeMixedVFVolumeObject hc A hfin ω
  obtain ⟨E1,hE1,_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hGenerated hGC
    (nativeMixedVolumeDomain hc U.densityGraph.domain) hU.densityGraph σ
  have hNorm := raw_standard_volume_normalization hc C G hGC A hA hfin δ hδ T hT
  have hRet := retained_density_graph_contraction_comparison hc C G hGC hΞ hGeneric γ hγ hγ1 A hA hfin ω δ hω T hT
    hU E1 hE1
  have hSame := gamma_vf_iso_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 U U hU hU
    (VFVolumeIso.refl hc C U) (hU.refl_iso hc C) E1 E hE1 hE
  exact (hNorm.trans hc hRet).trans hc hSame

set_option maxHeartbeats 6400000 in
/-- **Gamma VF permutation covariance.** -/
theorem gamma_vf_permutation_covariance (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (X : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (hX : VFVolumeObjectGamma X G)
    (σ : Equiv.Perm (Fin (k+1))) {υ υ' : Equiv.Perm (Fin (k+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc X.densityGraph.domain) υ)
    (E' : StandardContraction (nativeMixedVolumeDomain hc (X.permuteVF σ).densityGraph.domain) υ')
    (hE : GammaProgramDefinable G E.program) (hE' : GammaProgramDefinable G E'.program) :
    CommonContextVolumeEquivalent G C
      ⟨(X.permuteVF σ).standardContractionObject hc C G.gamma E',
        standard_contraction_object_gamma hc C G hGC _ (hX.permuteVF hc C σ) E' hE'⟩
      (GammaVolumeObjects.permuteVolume hc C
        ⟨X.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC _ hX E hE⟩ σ) := by
  have hXσ := hX.permuteVF hc C σ
  let A := nativeMixedVolumeDomain hc X.densityGraph.domain
  have hA : GammaSetDefinable G (carrier A) := hX.densityGraph
  let W := nativeMixedVFVolumeObject hc A X.densityGraph.finite_labels X.densityGraph.form
  let δ := Fin.last X.arity
  have hω : ∀ p, W.form.value p = p.val.2 δ := fun p => densityGraph_form_last X ⟨p.val,p.property⟩
  have hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun hz => W.form.nonzero ⟨p,hp⟩ ((hω ⟨p,hp⟩).trans hz))
  have hW : VFVolumeObjectGamma W G :=
    VFVolumeObjectGamma.of_density_graph (gamma_coordinate_volume_density_graph hc hA W.form δ hω)
  have hreal := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  obtain ⟨T,hT,_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 hreal hGenerated hGC A hA σ
  obtain ⟨EW,hEW,_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 hreal hGenerated hGC (nativeMixedVolumeDomain hc W.densityGraph.domain) hW.densityGraph
    (Equiv.refl _)
  have h1 := gamma_native_raw_standard_contraction hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A hA X.densityGraph.finite_labels W.form δ hω hδ T hT hW EW hEW
  have h1' := gamma_vf_iso_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 X W hX hW
    (VFVolumeIso.of_bijection (volumeDensityGraphBijection hc C X)) (gamma_volume_density_graph_iso hc C hX) E EW hE hEW
  -- the permuted side
  let A' := vfPermutationImage A σ
  have hA' : GammaSetDefinable G (carrier A') := gamma_vfPermutationImage A hA σ
  let T' := identityContractionOnPermutedSource T
  have hT' : GammaProgramDefinable G T'.program := gamma_standardFromProgram _ _ T.program _ hT
  let W' := nativePermutedVFVolumeObject hc X.densityGraph σ
  have hω' : ∀ p, W'.form.value p = p.val.2 δ :=
    native_permuted_vf_coordinate_density hc X.densityGraph σ δ (densityGraph_form_last X)
  have hδ' : ∀ p ∈ carrier A', (p.2 δ).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun hz => W'.form.nonzero ⟨p,hp⟩ ((hω' ⟨p,hp⟩).trans hz))
  have hW' : VFVolumeObjectGamma W' G :=
    VFVolumeObjectGamma.of_density_graph (gamma_coordinate_volume_density_graph hc hA' W'.form δ hω')
  obtain ⟨EW',hEW',_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 hreal hGenerated hGC (nativeMixedVolumeDomain hc W'.densityGraph.domain) hW'.densityGraph
    (Equiv.refl _)
  have h2 := gamma_native_raw_standard_contraction hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A' hA' (vfPermutation_finite_rv_fibres A σ X.densityGraph.finite_labels) W'.form δ hω' hδ' T' hT' hW' EW' hEW'
  let f : VFVolumeIso (X.permuteVF σ) W' :=
    (VFVolumeIso.of_bijection (permutedVFDensityGraphBijection hc C X σ)).trans hc C
      (VFVolumeIso.of_bijection (nativePermutedVFVolumeBijection hc C X.densityGraph σ))
  have hf : f.GammaDefinable G :=
    (permuted_vf_density_graph_iso_gamma hc C hX σ).trans hc C
      (native_permuted_vf_volume_iso_gamma hc C hX.densityGraph σ)
  have h2' := gamma_vf_iso_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    (X.permuteVF σ) W' hXσ hW' f hf E' EW' hE' hEW'
  have h3 := CommonContextVolumeEquivalent.of_iso
    (U := GammaVolumeObjects.permuteVolume hc C
      ⟨rawStandardVolumeObject hc C G.gamma A X.densityGraph.finite_labels δ hδ T,
        raw_standard_volume_object_gamma hc C G hGC A hA X.densityGraph.finite_labels δ hδ T hT⟩ σ)
    (V := ⟨rawStandardVolumeObject hc C G.gamma A' (vfPermutation_finite_rv_fibres A σ X.densityGraph.finite_labels)
        δ hδ' T',
      raw_standard_volume_object_gamma hc C G hGC A' hA' _ δ hδ' T' hT'⟩)
    (permutedRawContractionVolumeIso hc C G.gamma A X.densityGraph.finite_labels δ hδ T)
    (permuted_raw_contraction_volume_iso_gamma hc C hGC A hA X.densityGraph.finite_labels δ hδ T hT)
  obtain ⟨D,hCD,h4⟩ := (h1.trans hc (h1'.symm hc))
  have h4' : CommonContextVolumeEquivalent G C
      (GammaVolumeObjects.permuteVolume hc C
        ⟨rawStandardVolumeObject hc C G.gamma A X.densityGraph.finite_labels δ hδ T,
          raw_standard_volume_object_gamma hc C G hGC A hA X.densityGraph.finite_labels δ hδ T hT⟩ σ)
      (GammaVolumeObjects.permuteVolume hc C
        ⟨X.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC _ hX E hE⟩ σ) :=
    ⟨D,hCD,h4.permuteVolume hc D σ⟩
  exact ((h2'.trans hc (h2.symm hc)).trans hc (h3.symm hc)).trans hc h4'

end IntegrationInACVF.Section7.GammaNamed
