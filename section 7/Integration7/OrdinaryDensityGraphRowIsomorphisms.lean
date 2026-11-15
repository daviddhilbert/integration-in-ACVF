import Integration7.OrdinaryVolumeFamilyRowIsomorphisms
import Integration7.OrdinaryVolumeFamilyHeadIntegrals
import IntegrationSection6.VFParameterFibreIsomorphisms

/-! Appending the unit density is an original-base Gamma chart on each
ordinary fibre. Equality of ordinary row classes therefore compares the
actual density-graph fibres, before any unary preparation is chosen. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (Point GammaIso gammaLogicInput pointMapGraph)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b : ℕ}

def ordinaryDensityGraphRowGammaIso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (x : Fin (n+1) → VFType (M := M)) :
    GammaIso (⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),∅⟩ : Base (M := M))
      (vfParameterFibre (p := n+1) (n := 0) F.domain.carrier x)
      (vfParameterFibre (p := n+1) (n := 0) F.fullVFObject.densityGraph.domain.carrier x) := by
  let B : Base (M := M) := ⟨(C.base : Set M),∅⟩
  let f := (appendDensityMap F.fullVFObject.form).toImage
  let g := nativeMixedVolumeMap hc f
  let e : GammaIso B F.domain.carrier F.fullVFObject.densityGraph.domain.carrier :=
    ⟨Equiv.ofBijective g (native_mixed_volume_map_bijective hc f
      (appendDensityMap_toImage_bijective F.fullVFObject.form)),(gammaLogicInput B).real_map_graph g⟩
  have hp : VFParametersPreserved (p := n+1) (n := 0) (m := 0) e := by
    intro u j
    rfl
  exact gammaVFParameterFibreIso (p := n+1) (n := 0) (m := 0) e hp x

theorem ordinary_density_graph_row_gamma_iso_of_class_eq
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b)
    (x : Fin (n+1) → VFType (M := M))
    (h : rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x)) :
    Nonempty (GammaIso (⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),∅⟩ : Base (M := M))
      (vfParameterFibre (p := n+1) (n := 0) F.fullVFObject.densityGraph.domain.carrier x)
      (vfParameterFibre (p := n+1) (n := 0) G.fullVFObject.densityGraph.domain.carrier x)) := by
  let Bx : Base (M := M) := ⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),∅⟩
  obtain ⟨e⟩ := ordinary_volume_family_row_gamma_iso hc F G x h
  let f := ordinaryDensityGraphRowGammaIso hc F x
  let g := ordinaryDensityGraphRowGammaIso hc G x
  exact ⟨((f.symm (gammaLogicInput Bx)).trans (gammaLogicInput Bx) e).trans (gammaLogicInput Bx) g⟩

end IntegrationInACVF.Section7
