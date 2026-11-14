import Integration7.GammaEssentialVolumeGraphs
import Integration7.GammaRealRVMaps
import Integration7.BlowupHeadIsomorphism

/-! Restricting to essential labels and projecting away the final
volume coordinate retain the original Gamma coordinate graphs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaGraphDefinable gammaLogicInput PresentedSet pointSpace carrier setDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

theorem gamma_essential_coordinate_graph
    (U : PositiveRVVolumeObject (M := M) S k)
    (hU : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 (k+1)) =>
      U.underlying.obj.volume.graph p.2 q.2)) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 (k+1)) =>
      U.essential.obj.volume.graph p.2 q.2) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((gammaLogicInput B).restrict_graph (gamma_essential_volume_domain U hU) hU)
  intro p q
  constructor
  · rintro ⟨hp,⟨u,hu,hv⟩⟩
    exact ⟨⟨u.val,(congrArg (fun r => r ∈ U.essential.obj.domain.carrier) hu).mpr hp⟩,hu,hv⟩
  · rintro ⟨u,hu,hv⟩
    exact ⟨(congrArg (fun r => r ∈ U.essential.obj.domain.carrier) hu).mp u.property,
      ⟨⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩,hu,hv⟩⟩

theorem gamma_essential_density_graph
    (U : PositiveRVVolumeObject (M := M) S k)
    (hU : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 (k+1)) =>
      U.underlying.obj.volume.graph p.2 q.2))
    (hω : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 1) =>
      U.form.map.graph p.2 q.2)) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 1) =>
      U.essentialForm.map.graph p.2 q.2) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((gammaLogicInput B).restrict_graph (gamma_essential_volume_domain U hU) hω)
  intro p q
  constructor
  · rintro ⟨hp,⟨u,hu,hv⟩⟩
    exact ⟨⟨u.val,(congrArg (fun r => r ∈ U.essential.obj.domain.carrier) hu).mpr hp⟩,hu,hv⟩
  · rintro ⟨u,hu,hv⟩
    exact ⟨(congrArg (fun r => r ∈ U.essential.obj.domain.carrier) hu).mp u.property,
      ⟨⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩,hu,hv⟩⟩

theorem gamma_blowup_head_coordinate_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hAd : BlowupAdmissible U)
    (hU : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 (k+1)) =>
      U.underlying.obj.volume.graph p.2 q.2)) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 k) =>
      (blowupHeadObject C U hAd).obj.volume.graph p.2 q.2) := by
  let g := rvCoordinateSelectMap B.real (Fin.castSucc : Fin k → Fin (k+1))
  let P := PresentedSet.univ (pointSpace (M := M) 0 (k+1)) B.real
  have hg := gamma_real_rv_map_graph hc B g g
    ((gammaLogicInput B).real_set (carrier P) (setDefinable P)) (fun _ => rfl)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((gammaLogicInput B).comp_graph (gamma_essential_coordinate_graph U hU) hg)
  intro p q
  constructor
  · rintro ⟨m,⟨u,hu,hm⟩,⟨v,hv,hq⟩⟩
    refine ⟨u,hu,?_⟩
    exact (congrArg (fun r => r ∘ Fin.castSucc) (hv.trans hm.symm)).symm.trans hq
  · rintro ⟨u,hu,hq⟩
    exact ⟨(Fin.elim0,U.essential.obj.value u),⟨u,hu,rfl⟩,
      ⟨⟨U.essential.obj.value u,Set.mem_univ _⟩,rfl,hq⟩⟩

end IntegrationInACVF.Section7
