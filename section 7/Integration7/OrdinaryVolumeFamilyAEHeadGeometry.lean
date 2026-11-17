module

public import Integration7.OrdinaryFamilyGenericRowIsomorphisms
public import Integration7.GammaOrdinaryHeadComparisons

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! AE equal ordinary families have Gamma-geometrically equal
head integrals over generic retained VF tuples, on the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b : ℕ}

theorem ordinary_family_head_geometry_of_ae
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b)
    (hAE : AEOrdinaryRVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (E : HeadPreparation (nativeMixedVolumeDomain hc G.fullVFObject.densityGraph.domain))
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField (C.base : Set M)) x) :
    let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    let hTarget := (gammaLogicInput B).real_set _ (setDefinable T.target)
    let hETarget := (gammaLogicInput B).real_set _ (setDefinable E.target)
    (gammaSelectedVolumeSchema (k := 0) T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (a+1)))
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a)))).commonByGammaGeometry
    (gammaSelectedVolumeSchema (k := 0) E.contractedSet (gamma_headImage E.target hETarget)
      (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin (b+1)))
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) (Fin.last b)))) (fun j => (x j).val) := by
  intro B hTarget hETarget
  exact gamma_ordinary_head_common_comparison_at_generic hc C C.uncountable.le C.saturated
    C.small hΞ γ hγ hγ1 (Set.Subset.refl _)
    (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)
    (nativeMixedVolumeDomain hc G.fullVFObject.densityGraph.domain)
    ((gammaLogicInput B).real_set _ (setDefinable _))
    ((gammaLogicInput B).real_set _ (setDefinable _))
    (Fin.last a) (Fin.last b)
    (fun q => (congrArg (fun t : CanonicalRV.RVSort M => t.val)
      (F.densityGraph_label_one ⟨q.val,q.property⟩)).trans RVOperations.one_val)
    (fun q => (congrArg (fun t : CanonicalRV.RVSort M => t.val)
      (G.densityGraph_label_one ⟨q.val,q.property⟩)).trans RVOperations.one_val)
    F.fullVFObject.densityGraph.finite_labels G.fullVFObject.densityGraph.finite_labels
    (fun y hy => ordinary_family_ae_density_point_iso_at_generic hc Ξ F G hAE y hy)
    T E ((gammaLogicInput B).real_map_graph T.map) ((gammaLogicInput B).real_map_graph E.map)
    hTarget hETarget x hx

end IntegrationInACVF.Section7
