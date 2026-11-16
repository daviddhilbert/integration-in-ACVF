module

public import Integration7.Corollary76

@[expose] public section

/-! Arbitrary same-order contractions compare, and the comparison is
unchanged by an actual VF-coordinate-preserving relabeling of the source. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem vf_coordinate_preserving_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (f : Map U.domain V.domain) (hf : Function.Bijective f)
    (hVF : ∀ p, (f p).val.1 = p.val.1)
    (hDensity : ∀ p, U.form.value p = V.form.value (f p))
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) σ) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (D.base : Set M) k
        ⟨(U.standardContractionObject hc C Ξ T).extend hCD,(U.standardContractionObject_gamma hc C Ξ T).extend hCD⟩
        ⟨(V.standardContractionObject hc C Ξ E).extend hCD,(V.standardContractionObject_gamma hc C Ξ E).extend hCD⟩ := by
  exact corollary_7_6 hc C Ξ hΞ γ hγ hγ1 U V
    (VFVolumeBijection.of_preserving_vf_and_density hc C f hf hVF hDensity)
    (fun p j _ => congrFun (hVF p) j) T E

theorem same_order_standard_volume_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    {σ : Equiv.Perm (Fin (k+1))}
    (T E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (D.base : Set M) k
        ⟨(U.standardContractionObject hc C Ξ T).extend hCD,(U.standardContractionObject_gamma hc C Ξ T).extend hCD⟩
        ⟨(U.standardContractionObject hc C Ξ E).extend hCD,(U.standardContractionObject_gamma hc C Ξ E).extend hCD⟩ :=
  corollary_7_6 hc C Ξ hΞ γ hγ hγ1 U U (VFVolumeBijection.refl hc C U) (fun _ _ _ => rfl) T E

end IntegrationInACVF.Section7
