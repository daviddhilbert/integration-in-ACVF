import Integration7.UnaryContractionCommonVolumeSchemata
import Integration7.ZeroPrefixVolumeSliceRows
import Integration7.GammaVolumeSliceCommonUniformity

/-! The unary instance of Corollary 7.6, with actual common forward
blowups of the chosen contraction objects. Both endpoint densities are
their original retained labels, and all charts keep the original Gamma
base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B₀ : Base (M := M)} {a b : ℕ}

set_option maxHeartbeats 3200000 in
theorem gamma_unary_contraction_volume_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B₀.real < κ) (hgamma : Cardinal.mk B₀.gamma < κ)
    (hBC : B₀.real ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B₀.gamma) (hγ1 : 1 < γ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b)
    (hA : GammaSetDefinable B₀ (carrier A)) (hB : GammaSetDefinable B₀ (carrier B))
    (hfinA : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin 1 → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (hfΓ : GammaGraphDefinable B₀ (pointMapGraph f))
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    {σ τ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) (E : StandardContraction B τ)
    (hT : GammaProgramDefinable B₀ T.program) (hE : GammaProgramDefinable B₀ E.program) :
    let U := FiniteRV.gammaFiniteContraction hκ hs hreal hBC hA hfinA T hT
    let V := FiniteRV.gammaFiniteContraction hκ hs hreal hBC hB hfinB E hE
    ∃ (hδ : ∀ u : rvObjectDomain U.object, (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero)
      (hε : ∀ v : rvObjectDomain V.object, (v.val (FiniteRV.contractionOldLabelIndex E ε)).val ≠ iRVZero),
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B₀ (D.base : Set M) 0
        ⟨(gammaCoordinateDensityObject (e := 0) (k := 0) hc C U (Set.Subset.refl _) _ hδ).extend hCD,
          (gamma_coordinate_density_object_graphs (M := M) (B := B₀) (e := 0) (k := 0) hc C U (Set.Subset.refl _) _ hδ).extend hCD⟩
        ⟨(gammaCoordinateDensityObject (e := 0) (k := 0) hc C V (Set.Subset.refl _) _ hε).extend hCD,
          (gamma_coordinate_density_object_graphs (M := M) (B := B₀) (e := 0) (k := 0) hc C V (Set.Subset.refl _) _ hε).extend hCD⟩ := by
  intro U V
  have hδ : ∀ u : rvObjectDomain U.object,
      (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero :=
    normalized_contraction_retained_density_nonzero T δ (fun q =>
      (rv_nonzero_iff_raw _).mp (fun h => ω.nonzero q ((hω q).trans h)))
  have hε : ∀ v : rvObjectDomain V.object,
      (v.val (FiniteRV.contractionOldLabelIndex E ε)).val ≠ iRVZero :=
    normalized_contraction_retained_density_nonzero E ε (fun q =>
      (rv_nonzero_iff_raw _).mp (fun h => π.nonzero q ((hπ q).trans h)))
  obtain ⟨NF,hNF⟩ := gammaVolumeSliceDensitySchema_uniform_bound (e := 0) (k := 0)
    hκ hs hreal hgamma U _ hδ
  obtain ⟨NG,hNG⟩ := gammaVolumeSliceDensitySchema_uniform_bound (e := 0) (k := 0)
    hκ hs hreal hgamma V _ hε
  refine ⟨hδ,hε,?_⟩
  apply gamma_volume_slice_density_common_gamma_uniformity (e := 0) (k := 0)
    hc hκ hs hreal hgamma C U V (Set.Subset.refl _) (Set.Subset.refl _) _ _ hδ hε NF NG
  intro t
  let F := ((gammaVolumeSliceDensitySchema (e := 0) (k := 0) U (FiniteRV.contractionOldLabelIndex T δ)).withBound NF)
  let G := ((gammaVolumeSliceDensitySchema (e := 0) (k := 0) V (FiniteRV.contractionOldLabelIndex E ε)).withBound NG)
  have hBC' : B₀.real ∪ Set.range (rvValues t) ⊆ (C.base : Set M) := by
    simpa only [Set.range_eq_empty,Set.union_empty] using hBC
  have hA' : GammaSetDefinable ⟨B₀.real ∪ Set.range (rvValues t),B₀.gamma⟩ (carrier A) := by
    simpa only [Set.range_eq_empty,Set.union_empty] using hA
  have hB' : GammaSetDefinable ⟨B₀.real ∪ Set.range (rvValues t),B₀.gamma⟩ (carrier B) := by
    simpa only [Set.range_eq_empty,Set.union_empty] using hB
  have hf' : GammaGraphDefinable ⟨B₀.real ∪ Set.range (rvValues t),B₀.gamma⟩ (pointMapGraph f) := by
    simpa only [Set.range_eq_empty,Set.union_empty] using hfΓ
  have hT' : GammaProgramDefinable ⟨B₀.real ∪ Set.range (rvValues t),B₀.gamma⟩ T.program := by
    simpa only [Set.range_eq_empty,Set.union_empty] using hT
  have hE' : GammaProgramDefinable ⟨B₀.real ∪ Set.range (rvValues t),B₀.gamma⟩ E.program := by
    simpa only [Set.range_eq_empty,Set.union_empty] using hE
  have h := unary_contraction_common_volume_schema hc C hκ hs hreal hgamma (rvValues t)
    (fun i => Fin.elim0 i) hBC' γ hγ hγ1 A B hA' hB' hfinA hfinB f hf hf' ω π δ ε hω hπ hm
    T E hT' hE' F G (hNF t) (hNG t)
  simp only [Set.range_eq_empty,Set.union_empty] at h
  exact h hδ hε (gamma_zero_prefix_density_schema_row hc C U (Set.Subset.refl _) _ hδ NF t)
    (gamma_zero_prefix_density_schema_row hc C V (Set.Subset.refl _) _ hε NG t)

end IntegrationInACVF.Section7
