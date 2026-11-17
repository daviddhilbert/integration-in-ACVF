module

public import Integration7.Lemma75
public import Integration7.CommonContextVolumeDescent

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Fibrewise common volume blowups give equality of the actual
integral contraction objects over the original real parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_family_integral_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x))
    {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc G.densityGraph.domain) σ) :
    VolumeBlowupEquivalent (F.standardAppendObject hc Ξ T) (G.standardAppendObject hc Ξ E) := by
  obtain ⟨hU,hV,D,hCD,h⟩ := lemma_7_5_positive_objects hc C Ξ hΞ γ hγ hγ1 F G hCommon T E
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hGlobal : CommonContextVolumeEquivalent B C
      ⟨F.standardAppendObject hc Ξ T,hU⟩ ⟨G.standardAppendObject hc Ξ E,hV⟩ := ⟨D,hCD,h⟩
  exact (hGlobal.descend hc C hNames).toOrdinary hc C B

end IntegrationInACVF.Section7
