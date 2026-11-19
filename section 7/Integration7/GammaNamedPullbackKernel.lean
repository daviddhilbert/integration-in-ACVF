import Integration7.GammaNamedUnaryPartitions
import Integration7.PullbackVolumeAEKernel
import Integration7.GammaNativePreparedMixedPartitions

/-! The Gamma-named common-blowup kernel for an actual almost-everywhere VF
volume isomorphism between RV pullbacks with retained coordinate densities.
All data are Gamma-definable over an arbitrary Gamma base `G`, coded in a
context containing the common names of `G`. The Gamma volume-transport input
supplies the Gamma intermediate densities of the Section 5.6 factor chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 (vfDim rawRVSpace vfDim_eq_of_bijective)
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ} {ι : Type} [Fintype ι]

theorem native_prepared_mixed_partition_exists (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hGenerated : VFGammaGeneratedBase G)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (hA : GammaSetDefinable G (carrier A))
    (hAP : IsRVPullback (carrier A))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a) (hD : ∀ i, GammaSetDefinable G (carrier (D i)))
    (hDA : ∀ i, carrier (D i) ⊆ carrier A)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hCover : carrier A = nativeMixedFiniteUnionSet D Finset.univ) :
    ∃ P : NativePreparedMixedPartition A D,
      GammaChainDefinable G P.special.chain ∧ ∀ i, GammaChainDefinable G (P.pieceSpecial i).chain := by
  obtain ⟨r,B,T,hT,hBP,hFlags⟩ := gamma_prepare_finite_membership_all_arity (P := G)
    C.saturated C.model00 ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small)
    (generatedBaseVFField hGenerated) hGC A hAP hA D Finset.univ (fun i _ => hD i)
  exact gamma_native_prepared_partition_of_membership A D hDA hDisj hCover hD T hT hBP
    (fun i => hFlags i (Finset.mem_univ i))

theorem prepared_subdomain_volume_chain_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (G : Base (M := M))
    (hTransport : GammaVolumeTransportInput hc G (C.base : Set M))
    {A L : DefSet (M := M) (C.base : Set M) (n+1) a}
    {B K : DefSet (M := M) (C.base : Set M) (n+1) b}
    (hLA : carrier L ⊆ carrier A) (hKB : carrier K ⊆ carrier B)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b) (hω : ∀ p, ω.value p = p.val.2 δ) (hπ : ∀ p, π.value p = p.val.2 ε)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (Q : NativeVolumeUnaryPartition hc C L K (ω.restrict hLA) (π.restrict hKB))
    (hQ : ∀ i, GammaUnaryChainDefinable G (Q.chain i)) :
    letI := Q.finite
    ∀ (P : NativePreparedMixedPartition A (nativeCompletedPartition A L Q.source))
      (R : NativePreparedMixedPartition B (nativeCompletedPartition B K Q.target))
      (hP : ∀ j, GammaChainDefinable G (P.pieceSpecial j).chain)
      (hR : ∀ j, GammaChainDefinable G (R.pieceSpecial j).chain) (i : Q.index),
    let ψ := specialRetainedVolumeForm hc P.special δ hδ
    let χ := specialRetainedVolumeForm hc R.special ε hε
    ∃ T : UnaryChain (C.base : Set M) (n+1) (P.pieces (some i)) (R.pieces (some i)),
      GammaUnaryChainDefinable G T ∧
      gammaUnaryChainVolumeData hc G T (ψ.restrict (P.subset (some i))) (χ.restrict (R.subset (some i))) := by
  letI := Q.finite
  intro P R hP hR i ψ χ
  let ωD : VolumeForm (rawSpecialSet hc (Q.source i)) := ω.restrict ((Q.sourceSubset i).trans hLA)
  let πE : VolumeForm (rawSpecialSet hc (Q.target i)) := π.restrict ((Q.targetSubset i).trans hKB)
  let ψP : VolumeForm (rawSpecialSet hc (P.pieces (some i))) := ψ.restrict (P.subset (some i))
  let χR : VolumeForm (rawSpecialSet hc (R.pieces (some i))) := χ.restrict (R.subset (some i))
  have hψP : GammaSetDefinable G (volumeDensityGraph ψP).carrier :=
    gamma_coordinate_volume_density_graph hc (GammaChainDefinable.target G _ (hP (some i))) ψP
      (suffixIndex (special_chain_rvArity_le P.special.chain) δ) (fun _ => rfl)
  apply special_conjugate_volume_chain_exists hc C hTransport (P.pieceSpecial (some i)) (R.pieceSpecial (some i))
    (hP (some i)) (hR (some i)) ωD πE ψP χR hψP ?_ ?_ (fun x => (hfinA x).subset (fun _ h => hLA (Q.sourceSubset i h)))
    (Q.chain i) (hQ i) (Q.volume i)
  · intro p
    change ω.value ⟨p.val,hLA (Q.sourceSubset i p.property)⟩ =
      ((rawSpecialMap hc (P.pieceSpecial (some i)).toMap) p).val.2
        (suffixIndex (special_chain_rvArity_le P.special.chain) δ)
    rw [hω]
    exact (special_oldLabels (P.pieceSpecial (some i)) ⟨p.val,p.property⟩ δ).symm
  · intro p
    change π.value ⟨p.val,hKB (Q.targetSubset i p.property)⟩ =
      ((rawSpecialMap hc (R.pieceSpecial (some i)).toMap) p).val.2
        (suffixIndex (special_chain_rvArity_le R.special.chain) ε)
    rw [hπ]
    exact (special_oldLabels (R.pieceSpecial (some i)) ⟨p.val,p.property⟩ ε).symm

theorem prepared_subdomain_volume_gluing
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (hTransport : GammaVolumeTransportInput hc G (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {A L : DefSet (M := M) (C.base : Set M) (n+1) a}
    {B K : DefSet (M := M) (C.base : Set M) (n+1) b}
    (hLA : carrier L ⊆ carrier A) (hKB : carrier K ⊆ carrier B)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b) (hω : ∀ p, ω.value p = p.val.2 δ) (hπ : ∀ p, π.value p = p.val.2 ε)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (hsmallL : vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) (rawSpecialSet hc (nativeMixedDifference A L)) < n+1)
    (hsmallK : vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) (rawSpecialSet hc (nativeMixedDifference B K)) < n+1)
    (Q : NativeVolumeUnaryPartition hc C L K (ω.restrict hLA) (π.restrict hKB))
    (hQ : ∀ i, GammaUnaryChainDefinable G (Q.chain i)) :
    letI := Q.finite
    ∀ (P : NativePreparedMixedPartition A (nativeCompletedPartition A L Q.source))
      (R : NativePreparedMixedPartition B (nativeCompletedPartition B K Q.target))
      (hPs : GammaChainDefinable G P.special.chain) (hRs : GammaChainDefinable G R.special.chain)
      (hP : ∀ j, GammaChainDefinable G (P.pieceSpecial j).chain)
      (hR : ∀ j, GammaChainDefinable G (R.pieceSpecial j).chain),
    CommonContextVolumeEquivalent G C
      (specialPullbackVolumeGammaObject hc C G hGC P.special hPs P.pullback hfinA δ hδ)
      (specialPullbackVolumeGammaObject hc C G hGC R.special hRs R.pullback hfinB ε hε) := by
  classical
  letI := Q.finite
  intro P R hPs hRs hP hR
  let ψ := specialRetainedVolumeForm hc P.special δ hδ
  let χ := specialRetainedVolumeForm hc R.special ε hε
  let δP := suffixIndex (special_chain_rvArity_le P.special.chain) δ
  let εR := suffixIndex (special_chain_rvArity_le R.special.chain) ε
  have hδP := special_retained_density_nonzero P.special δ hδ
  have hεR := special_retained_density_nonzero R.special ε hε
  have hfinP := special_target_finite_labels C G.gamma P.special hfinA
  have hfinR := special_target_finite_labels C G.gamma R.special hfinB
  have hPF := special_pullback_volume_finite C G.gamma P.special P.pullback hfinA
  have hRF := special_pullback_volume_finite C G.gamma R.special R.pullback hfinB
  have hPpieces : ∀ j, GammaSetDefinable G (carrier (P.pieces j)) :=
    fun j => GammaChainDefinable.target G _ (hP j)
  have hRpieces : ∀ j, GammaSetDefinable G (carrier (R.pieces j)) :=
    fun j => GammaChainDefinable.target G _ (hR j)
  have hPieces : ∀ i, CommonContextVolumeEquivalent G C
      (finitePullbackVolumePiece hc C G hGC P.target hPF P.pieces hPpieces P.subset δP hδP i)
      (finitePullbackVolumePiece hc C G hGC R.target hRF R.pieces hRpieces R.subset εR hεR i) := by
    intro i
    cases i with
    | none =>
      apply CommonContextVolumeEquivalent.of_empty_essential hc C
      · apply pullback_volume_essential_empty_of_small_dimension hc C (P.pieces none) (P.piecePullback none)
          (pullback_finite_of_subset (P.subset none) hPF) δP (fun p => hδP ⟨p.val,P.subset none p.property⟩)
        have he := vfDim_eq_of_bijective (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
          (rawSpecialMap hc (P.pieceSpecial none).toMap) (P.pieceSpecial none).bijective
        exact he ▸ hsmallL
      · apply pullback_volume_essential_empty_of_small_dimension hc C (R.pieces none) (R.piecePullback none)
          (pullback_finite_of_subset (R.subset none) hRF) εR (fun p => hεR ⟨p.val,R.subset none p.property⟩)
        have he := vfDim_eq_of_bijective (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
          (rawSpecialMap hc (R.pieceSpecial none).toMap) (R.pieceSpecial none).bijective
        exact he ▸ hsmallK
    | some i =>
      obtain ⟨T,hTΓ,hT⟩ := prepared_subdomain_volume_chain_exists hc C G hTransport hLA hKB ω π δ ε hω hπ
        hδ hε hfinA Q hQ P R hP hR i
      exact pullback_unary_chain_volume_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
        (P.pieces (some i)) (R.pieces (some i)) (hPpieces (some i)) (hRpieces (some i))
        (P.piecePullback (some i)) (R.piecePullback (some i))
        (fun x => (hfinP x).subset (fun _ h => P.subset (some i) h))
        (fun x => (hfinR x).subset (fun _ h => R.subset (some i) h))
        (pullback_finite_of_subset (P.subset (some i)) hPF) (pullback_finite_of_subset (R.subset (some i)) hRF)
        (ψ.restrict (P.subset (some i))) (χ.restrict (R.subset (some i)))
        δP εR (fun _ => rfl) (fun _ => rfl) T hTΓ hT
  exact finite_pullback_volume_partition_gluing hc C G hGC P.target R.target
    (GammaChainDefinable.target G _ hPs) (GammaChainDefinable.target G _ hRs) hPF hRF
    P.pieces R.pieces hPpieces hRpieces P.subset R.subset P.disjoint R.disjoint P.piecePullback R.piecePullback
    δP εR hδP hεR hPieces Finset.univ P.cover R.cover

theorem pullback_volume_ae_kernel
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (hTransport : GammaVolumeTransportInput hc G (C.base : Set M))
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
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (f : VFVolumeIso (nativeMixedVFVolumeObject hc A hfinA ω) (nativeMixedVFVolumeObject hc B hfinB π))
    (hf : f.GammaDefinable G) :
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C hGC A hA hAF δ hδ)
      (pullbackCoordinateGammaObject hc C hGC B hB hBF ε hε) := by
  classical
  let L := nativeMixedVolumeDomain hc f.source
  let K := nativeMixedVolumeDomain hc f.target
  have hLA : carrier L ⊆ carrier A := f.source_subset
  have hKB : carrier K ⊆ carrier B := f.target_subset
  let ωL : VolumeForm (rawSpecialSet hc L) := ω.restrict hLA
  let πK : VolumeForm (rawSpecialSet hc K) := π.restrict hKB
  let g : Map L K := nativeMixedVolumeMap hc f.bijection.map
  have hgΓ : GammaGraphDefinable G (pointMapGraph g) := by
    apply GammaGraphDefinable.congr hf.graph
    intro p q
    constructor
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩
  obtain ⟨Q,_,_,hQ⟩ := native_volume_unary_partition_exists hc C G hGC hNames γ hγ1 g
    (native_mixed_volume_map_bijective hc f.bijection.map f.bijection.bijective) hgΓ ωL πK f.bijection.preserves
  letI := Q.finite
  have hQs := fun i => gamma_unary_chain_source (Q.chain i) (hQ i)
  have hQt := fun i => gamma_unary_chain_target (Q.chain i) (hQ i)
  have hCompA : ∀ j, GammaSetDefinable G (carrier (nativeCompletedPartition A L Q.source j)) := by
    intro j
    cases j with
    | none => exact (gammaLogicInput G).sdiff hA hf.source
    | some i => exact hQs i
  have hCompB : ∀ j, GammaSetDefinable G (carrier (nativeCompletedPartition B K Q.target j)) := by
    intro j
    cases j with
    | none => exact (gammaLogicInput G).sdiff hB hf.target
    | some i => exact hQt i
  obtain ⟨P,hPs,hP⟩ := native_prepared_mixed_partition_exists C G hGC hGenerated A hA hAP
    (nativeCompletedPartition A L Q.source) hCompA
    (native_completed_partition_subset A L Q.source hLA Q.sourceSubset)
    (native_completed_partition_disjoint A L Q.source Q.sourceSubset Q.sourceDisjoint)
    (native_completed_partition_cover A L Q.source hLA Q.sourceSubset Q.sourceCover)
  obtain ⟨R,hRs,hR⟩ := native_prepared_mixed_partition_exists C G hGC hGenerated B hB hBP
    (nativeCompletedPartition B K Q.target) hCompB
    (native_completed_partition_subset B K Q.target hKB Q.targetSubset)
    (native_completed_partition_disjoint B K Q.target Q.targetSubset Q.targetDisjoint)
    (native_completed_partition_cover B K Q.target hKB Q.targetSubset Q.targetCover)
  have hLeft := special_pullback_volume_comparison hc C G hGC hΞ hGenerated hNames hGeneric hTransport
    γ hγ hγ1 P.special hPs hAP P.pullback hfinA hAF ω δ hω hδ
  have hRight := special_pullback_volume_comparison hc C G hGC hΞ hGenerated hNames hGeneric hTransport
    γ hγ hγ1 R.special hRs hBP R.pullback hfinB hBF π ε hπ hε
  have hMiddle := prepared_subdomain_volume_gluing hc C G hGC hΞ hGenerated hNames hGeneric hTransport
    γ hγ hγ1 hLA hKB ω π δ ε hω hπ hδ hε hfinA hfinB
    f.source_complement_small f.target_complement_small Q hQ P R hPs hRs hP hR
  exact hLeft.trans hc (hMiddle.trans hc (hRight.symm hc))

end IntegrationInACVF.Section7.GammaNamed
