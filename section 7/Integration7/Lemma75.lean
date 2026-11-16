module

public import Integration7.PositiveSelectedContractionObjects
public import Integration7.SelectedVolumeProjectionFibres

@[expose] public section

/-! Lemma 7.5 with the accepted nonempty selected-coordinate hypothesis.
The fibrewise assumption is required only on the common VF projection.
The conclusion concerns the specified actual contraction objects. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a b k : ℕ}

theorem lemma_7_5
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hProjection : F.vfProjection = G.vfProjection)
    (hCommon : ∀ x ∈ F.vfProjection, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x))
    {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc G.densityGraph.domain) σ) :
    let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    let U := F.standardAppendObject hc Ξ T
    let V := G.standardAppendObject hc Ξ E
    ∃ (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B),
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B (D.base : Set M) (appendVolumeDegree n k)
        ⟨U.extend hCD,hU.extend hCD⟩ ⟨V.extend hCD,hV.extend hCD⟩ :=
  lemma_7_5_positive_objects hc C Ξ hΞ γ hγ hγ1 F G
    (selected_volume_common_on_projection hc F G hProjection hCommon) T E

theorem lemma_7_5_ordinary
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hProjection : F.vfProjection = G.vfProjection)
    (hCommon : ∀ x ∈ F.vfProjection, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x))
    {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc G.densityGraph.domain) σ) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      VolumeBlowupEquivalent ((F.standardAppendObject hc Ξ T).extend hCD)
        ((G.standardAppendObject hc Ξ E).extend hCD) := by
  obtain ⟨hU,hV,D,hCD,h⟩ := lemma_7_5 hc C Ξ hΞ γ hγ hγ1 F G hProjection hCommon T E
  exact ⟨D,hCD,h.toOrdinary hc D ⟨(C.base : Set M),Ξ⟩⟩

end IntegrationInACVF.Section7
