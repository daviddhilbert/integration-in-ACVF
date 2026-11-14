import Integration7.SelectedVolumeFamilies
import Integration7.OrderedPositiveVolumeContractions

/-! Actual positive selected-family contraction objects. Their volume
tuple retains every contracted VF tag and every selected original label;
their density is the retained density-graph label. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a l k : ℕ}

def SelectedVFVolumeFamily.orderedAugmentedLabelObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l}
    (T : Section5.OrderedContractionProgram (C.base : Set M)
      (nativeMixedVolumeDomain hc F.densityGraph.domain) U)
    (hT : Section5.GammaProgramDefinable (⟨(C.base : Set M), Ξ⟩ : Base (M := M)) T) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) (n + k) :=
  orderedPositiveVolumeObject hc C Ξ F.densityGraph.domain F.densityGraph.form
    F.densityGraph.selected (Fin.last a) F.densityGraph_form_last F.densityGraph.finite_selected T hT

theorem SelectedVFVolumeFamily.orderedAugmentedLabelObject_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l}
    (T : Section5.OrderedContractionProgram (C.base : Set M)
      (nativeMixedVolumeDomain hc F.densityGraph.domain) U)
    (hT : Section5.GammaProgramDefinable (⟨(C.base : Set M), Ξ⟩ : Base (M := M)) T)
    (u : rawVolumeContractionLabels hc U) :
    (F.orderedAugmentedLabelObject hc C Ξ T hT).underlying.obj.value u =
      u.val ∘ orderedPositiveVolumeSelector T F.densityGraph.selected := rfl

theorem SelectedVFVolumeFamily.orderedAugmentedLabelObject_density_transport
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l}
    (T : Section5.OrderedContractionProgram (C.base : Set M)
      (nativeMixedVolumeDomain hc F.densityGraph.domain) U)
    (hT : Section5.GammaProgramDefinable (⟨(C.base : Set M), Ξ⟩ : Base (M := M)) T)
    (p : nativeMixedVolumeDomain hc F.densityGraph.domain)
    (u : rawVolumeContractionLabels hc U) (hp : (T.toMap p).val.2 = u.val) :
    (F.orderedAugmentedLabelObject hc C Ξ T hT).form.value u =
      F.densityGraph.form.value ⟨p.val, p.property⟩ := by
  change u.val (Section5.suffixIndex T.rvArity_le (Fin.last a)) = _
  exact (congrArg (fun r => r (Section5.suffixIndex T.rvArity_le (Fin.last a))) hp).symm.trans
    ((T.oldLabels p (Fin.last a)).trans (F.densityGraph_form_last ⟨p.val, p.property⟩).symm)

theorem SelectedVFVolumeFamily.exists_orderedAugmentedProgram
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (FBase : VFFieldBase (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) :
    ∃ l, ∃ U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l,
      ∃ T : Section5.OrderedContractionProgram (C.base : Set M)
        (nativeMixedVolumeDomain hc F.densityGraph.domain) U,
        Section5.GammaProgramDefinable (⟨(C.base : Set M), Ξ⟩ : Base (M := M)) T := by
  let B : Base (M := M) := ⟨(C.base : Set M), Ξ⟩
  let A := nativeMixedVolumeDomain hc F.densityGraph.domain
  have hA : SpecialTransformations.Section5.GammaSetDefinable B
      (SpecialTransformations.Section5.carrier A) :=
    (SpecialTransformations.Section5.gammaLogicInput B).real_set _
      (SpecialTransformations.Section5.setDefinable A)
  exact Section5.gamma_ordered_contraction_program_certified C.saturated C.model00 B C.small
    FBase (Set.Subset.refl _) n A hA

end IntegrationInACVF.Section7
