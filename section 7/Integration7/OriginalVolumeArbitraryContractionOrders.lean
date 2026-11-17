module

public import Integration7.RetainedDensityArbitraryOrderComparisons
public import Integration7.VFStandardVolumeContractionObjects

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Arbitrary-order independence for the standard contraction objects
of actual positive VF volume objects with their original forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem standard_volume_contraction_order_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) n)
    {σ υ : Equiv.Perm (Fin (n+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) υ) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    CommonContextVolumeEquivalent G C
      ⟨U.standardContractionObject hc C Ξ T,U.standardContractionObject_gamma hc C Ξ T⟩
      ⟨U.standardContractionObject hc C Ξ E,U.standardContractionObject_gamma hc C Ξ E⟩ := by
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  have hδ : ∀ p ∈ carrier A, (p.2 (Fin.last U.arity)).val ≠ iRVZero := by
    intro p hp
    apply (rv_nonzero_iff_raw _).mp
    intro h
    exact U.densityGraph.form.nonzero ⟨p,hp⟩ ((densityGraph_form_last U ⟨p,hp⟩).trans h)
  exact retained_density_arbitrary_order_contractions_compare hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    A U.densityGraph.finite_labels (Fin.last U.arity) hδ σ υ T E

end IntegrationInACVF.Section7
