module

public import Integration7.OrdinaryHeadIntegralVolumeCharts
public import Integration7.NativeAppendedVolumeIntegralFormula
public import Integration7.IntegrationCoordinateDensityFormula
public import Integration7.HKAEZeroIntegrals
public import Integration7.HKZeroFamilyHeadIntegrals

@[expose] public section

/-! Integrating the actual first-head family of an weighted-zero-valued
presentation and then its remaining VF coordinates gives its genuine
weighted total integral. The only cast is arithmetic total degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem zero_family_integral_contraction_formula
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : ZeroVFVolumeFamily C (n+1) a)
    {σ : Equiv.Perm (Fin (n+1))}
    (P : StandardContraction (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain) σ) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C F.fullVFObject) =
      positiveVolumeBlowupClass hc C
        (rawStandardVolumeObject hc C Ξ
          (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)
          F.fullVFObject.densityGraph.finite_labels (Fin.last a) F.densityGraph_label_nonzero P) := by
  let I := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := n)
  have hClass := (positiveVFVolumeIsoClass_eq_iff hc C).mpr
    ⟨VFVolumeIso.of_bijection (volumeDensityGraphBijection hc C F.fullVFObject)⟩
  have hFormula := positive_volume_integration_coordinate_density hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)
    F.fullVFObject.densityGraph.finite_labels F.fullVFObject.densityGraph.form
    (Fin.last a) (densityGraph_form_last F.fullVFObject) P
  exact (congrArg I hClass).trans hFormula

theorem zero_family_appended_head_fubini
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : ZeroVFVolumeFamily C ((n+1)+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)) :
    HEq (selectedFamilyIntegralValue hc C Ξ hGenerated (F.headIntegral hc Ξ T))
      (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C F.fullVFObject)) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  obtain ⟨D,hD⟩ := generated_base_standard_contraction_exists (B := B) C.saturated C.model00 C.small
    hGenerated (Set.Subset.refl _) T.contractedSet
    ((gammaLogicInput B).real_set _ (setDefinable T.contractedSet)) (Equiv.refl _)
  let δ := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a))
  have hHead := native_coordinate_family_appended_integral_formula (k := 0) hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (a+1)))
    (F.headIntegral hc Ξ T).finite_selected δ
    (head_retained_density_nonzero T (Fin.last a) F.densityGraph_label_nonzero) D
  have hIso := positiveVolumeBlowupClass_iso hc C
    (ordinaryHeadIntegralVolumeIso hc C Ξ
      (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)
      F.fullVFObject.densityGraph.finite_labels T (Fin.last a) F.densityGraph_label_nonzero
      (F.headIntegral hc Ξ T).finite_selected D)
  have hTotal := zero_family_integral_contraction_formula hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F
    (identityHeadTailStandardContraction T D)
  exact (heq_of_eq hHead).trans
    ((positive_volume_class_reindex_degree_heq hc C (head_tail_volume_degree (n+1)).symm _).symm.trans
      (heq_of_eq (hIso.trans hTotal.symm)))

end IntegrationInACVF.Section7.HK
