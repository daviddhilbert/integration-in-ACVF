module

public import Integration7.UnaryContractionGammaVolumeComparison
public import Integration7.FiniteContractionNormalizationVolumeIso
public import Integration7.VolumeContextJoins

@[expose] public section

/-! Unary Corollary 7.6 on the raw final labels, in any prescribed
containing context. Normalization charts preserve the complete volume
coordinate and the original retained density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B₀ : Base (M := M)} {a b : ℕ}

set_option maxHeartbeats 3200000 in
theorem gamma_unary_raw_finite_volume_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C C₀ : BaseContext M)
    (hCC₀ : (C.base : Set M) ⊆ (C₀.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B₀.real < κ) (hgamma : Cardinal.mk B₀.gamma < κ)
    (hBC : B₀.real ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B₀.gamma) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) 1 a) (B : DefSet (M := M) (C.base : Set M) 1 b)
    (hA : GammaSetDefinable B₀ (carrier A)) (hB : GammaSetDefinable B₀ (carrier B))
    (hfinA : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin 1 → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (f : Map A B) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B₀ (pointMapGraph f))
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    {σ τ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) (E : StandardContraction B τ)
    (hT : GammaProgramDefinable B₀ T.program) (hE : GammaProgramDefinable B₀ E.program) :
    let U := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hA hfinA T hT
    let V := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hB hfinB E hE
    ∃ (hδ : ∀ u : rvObjectDomain U.object, (u.val (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero)
      (hε : ∀ v : rvObjectDomain V.object, (v.val (suffixIndex E.program.rvArity_le ε)).val ≠ iRVZero),
    ∃ (D : BaseContext M) (hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B₀ (D.base : Set M) 0
        ⟨(gammaCoordinateDensityObject (e := 0) (k := 0) hc C₀ U hCC₀ _ hδ).extend hC₀D,
          (gamma_coordinate_density_object_graphs (M := M) (B := B₀) (e := 0) (k := 0) hc C₀ U hCC₀ _ hδ).extend hC₀D⟩
        ⟨(gammaCoordinateDensityObject (e := 0) (k := 0) hc C₀ V hCC₀ _ hε).extend hC₀D,
          (gamma_coordinate_density_object_graphs (M := M) (B := B₀) (e := 0) (k := 0) hc C₀ V hCC₀ _ hε).extend hC₀D⟩ := by
  intro U V
  have hδA : ∀ q : A, (q.val.2 δ).val ≠ iRVZero := fun q =>
    (rv_nonzero_iff_raw _).mp (fun h => ω.nonzero q ((hω q).trans h))
  have hεB : ∀ q : B, (q.val.2 ε).val ≠ iRVZero := fun q =>
    (rv_nonzero_iff_raw _).mp (fun h => π.nonzero q ((hπ q).trans h))
  obtain ⟨hTN,hEN,N,hCN,hCommon⟩ := gamma_unary_contraction_volume_comparison hc C hκ hs hreal hgamma
    hBC γ hγ hγ1 A B hA hB hfinA hfinB f hf hfΓ ω π δ ε hω hπ hm T E hT hE
  obtain ⟨J,hNJ,hC₀J⟩ := volume_context_join_exists N C₀
  let hCJ := hCN.trans hNJ
  obtain ⟨hU,K,hJK,eU,heU⟩ := finite_contraction_normalization_volume_iso hc C J hCJ
    hκ hs hreal hBC A hA hfinA T hT δ hδA
  let hCK := hCJ.trans hJK
  obtain ⟨hV,D,hKD,eV,heV⟩ := finite_contraction_normalization_volume_iso hc C K hCK
    hκ hs hreal hBC B hB hfinB E hE ε hεB
  let hND := hNJ.trans (hJK.trans hKD)
  refine ⟨hU,hV,D,hC₀J.trans (hJK.trans hKD),GammaVolumeBlowupEquivalent.trans hc D B₀ ?_
    ((hCommon.extend hND).trans hc D B₀ ?_)⟩
  · exact GammaVolumeBlowupEquivalent.of_iso D B₀ (eU.extend hKD) (heU.extend hKD)
  · exact GammaVolumeBlowupEquivalent.of_iso D B₀ (eV.symm hc D) (heV.symm hc D B₀)

end IntegrationInACVF.Section7
