import Integration7.SelectedFamilyRestrictions
import Integration7.GammaRVLabelCuts
import Integration7.HeadFibreDensityGraphs

/-! Old RV-label cuts of an actual selected family commute with its
actual density graph. The original selected tuple and density are kept. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

def SelectedVFVolumeFamily.onRVLabels
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k)
    (τ : Fin b → Fin a) (R : Set (Point (M := M) 0 b))
    (hR : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) R)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M)) :
    SelectedVFVolumeFamily C n a k := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let U := nativeMixedVolumeDomain hc F.domain
  let hU : GammaSetDefinable G (carrier U) := (SpecialTransformations.Section5.gammaLogicInput G).real_set _ (SpecialTransformations.Section5.setDefinable U)
  let L := rawSpecialSet hc (rvLabelCut U hU τ R hR hNames)
  exact F.restrict L (fun _ h => h.1)

theorem selected_family_rv_label_cut_mem
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k)
    (τ : Fin b → Fin a) (R : Set (Point (M := M) 0 b))
    (hR : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) R)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (q : (rawMixedSpace (M := M) n a).Carrier) :
    q ∈ (F.onRVLabels hc Ξ τ R hR hNames).domain.carrier ↔
      q ∈ F.domain.carrier ∧ (Fin.elim0,q.2 ∘ τ) ∈ R := Iff.rfl

theorem selected_family_label_cut_density_graph
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k)
    (τ : Fin b → Fin a) (R : Set (Point (M := M) 0 b))
    (hR : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) R)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M)) :
    nativeMixedVolumeDomain hc (F.onRVLabels hc Ξ τ R hR hNames).densityGraph.domain =
      rvLabelCut (nativeMixedVolumeDomain hc F.densityGraph.domain)
        ((SpecialTransformations.Section5.gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_set _
          (SpecialTransformations.Section5.setDefinable _)) (Fin.castAdd 1 ∘ τ) R hR hNames := by
  apply defSet_eq_of_carrier_eq
  ext q
  rcases q with ⟨x,r⟩
  change (x,r) ∈ (volumeDensityGraph (F.onRVLabels hc Ξ τ R hR hNames).form).carrier ↔
    (x,r) ∈ (volumeDensityGraph F.form).carrier ∧ (Fin.elim0,r ∘ (Fin.castAdd 1 ∘ τ)) ∈ R
  rw [volume_density_graph_mem_iff,volume_density_graph_mem_iff]
  constructor
  · rintro ⟨h,hr⟩
    exact ⟨⟨h.1,hr⟩,h.2⟩
  · rintro ⟨⟨h,hr⟩,hR⟩
    exact ⟨⟨h,hR⟩,hr⟩
end IntegrationInACVF.Section7
