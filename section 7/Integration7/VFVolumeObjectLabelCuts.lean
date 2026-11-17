module

public import Integration7.SelectedVolumeFamilyLabelCuts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Retained-label cuts of finite-label VF volume objects commute with
their actual density graphs. These include genuine unary RV[0] fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k b : ℕ}

def PositiveVFVolumeObject.onRVLabels
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (τ : Fin b → Fin U.arity) (R : Set (Point (M := M) 0 b))
    (hR : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) R)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M)) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) k := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc U.domain
  let hA : GammaSetDefinable G (carrier A) := (SpecialTransformations.Section5.gammaLogicInput G).real_set _ (SpecialTransformations.Section5.setDefinable A)
  exact U.restrict (rawSpecialSet hc (rvLabelCut A hA τ R hR hNames)) (fun _ h => h.1)

theorem vf_volume_object_label_cut_density_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (τ : Fin b → Fin U.arity) (R : Set (Point (M := M) 0 b))
    (hR : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) R)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M)) :
    nativeMixedVolumeDomain hc (U.onRVLabels hc C Ξ τ R hR hNames).densityGraph.domain =
      rvLabelCut (nativeMixedVolumeDomain hc U.densityGraph.domain)
        ((SpecialTransformations.Section5.gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_set _
          (SpecialTransformations.Section5.setDefinable _)) (Fin.castAdd 1 ∘ τ) R hR hNames := by
  apply defSet_eq_of_carrier_eq
  ext q
  rcases q with ⟨x,r⟩
  change (x,r) ∈ (volumeDensityGraph (U.onRVLabels hc C Ξ τ R hR hNames).form).carrier ↔
    (x,r) ∈ (volumeDensityGraph U.form).carrier ∧ (Fin.elim0,r ∘ (Fin.castAdd 1 ∘ τ)) ∈ R
  rw [volume_density_graph_mem_iff,volume_density_graph_mem_iff]
  constructor
  · rintro ⟨h,hr⟩
    exact ⟨⟨h.1,hr⟩,h.2⟩
  · rintro ⟨⟨h,hr⟩,hR⟩
    exact ⟨⟨h,hR⟩,hr⟩
end IntegrationInACVF.Section7
