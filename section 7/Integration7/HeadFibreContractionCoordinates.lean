module

public import Integration7.HeadFibreContractionSources
public import Integration7.OrderedAppendVolumeIndices
public import Integration7.HeadCoordinateFibreVolumeSelectors

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The inherited actual fibre contraction has exactly the head
integral's label domain, selected tuple and retained density coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
variable (F : SelectedVFVolumeFamily C (n+1) a k)
variable (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
variable (x : Fin n → VFType (M := M))
variable (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))

theorem head_fibre_contraction_label_domain (r : Fin (1+T.arity) → RV (M := M)) :
    (Fin.elim0,r) ∈ carrier (headFibreStandardContraction hc C D F T x hD).target ↔
      (x,r) ∈ carrier T.contractedSet :=
  head_coordinate_fibre_contraction_domain T x r

theorem head_fibre_contraction_append_index :
    orderedAppendVolumeIndex (headFibreStandardContraction hc C D F T x hD).program F.densityGraph.selected =
      headAppendVolumeIndex T F.densityGraph.selected := by
  let R := headFibreStandardContraction hc C D F T x hD
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have h := ordered_append_old_index R.program F.densityGraph.selected i
    have hi : Fin.cast (append_volume_length_eq 1 k).symm (Fin.castAdd 1 i) = Fin.castAdd 1 i := Fin.ext rfl
    rw [hi] at h
    simp only [headAppendVolumeIndex,Fin.append_left,headSelectedLabelIndex]
    change orderedAppendVolumeIndex R.program F.densityGraph.selected (Fin.castAdd 1 i) =
      Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (F.densityGraph.selected i))
    exact h.trans (head_coordinate_fibre_old_label_index T x (F.densityGraph.selected i))
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have h := ordered_append_vf_index R.program F.densityGraph.selected (0 : Fin 1)
    have hi : Fin.cast (append_volume_length_eq 1 k).symm (Fin.natAdd (k+1) (0 : Fin 1)) =
      Fin.natAdd (k+1) (0 : Fin 1) := Fin.ext rfl
    rw [hi] at h
    change orderedAppendVolumeIndex R.program F.densityGraph.selected (Fin.natAdd (k+1) (0 : Fin 1)) =
      Fin.append (headSelectedLabelIndex T F.densityGraph.selected) (fun j => Fin.castAdd T.arity j)
        (Fin.natAdd (k+1) (0 : Fin 1))
    rw [Fin.append_right,h]
    change (orderedCastSource _ _).volumeIndex 0 = Fin.castAdd T.arity (0 : Fin 1)
    rw [orderedCastSource_volumeIndex]
    exact ((headCoordinateFibreContraction T x).extendBase_volumeIndex
      (head_fibre_contraction_base_subset C D x hD) 0).trans (head_coordinate_fibre_volume_index T x)

theorem head_fibre_contraction_density_index :
    orderedAppendDensityIndex (headFibreStandardContraction hc C D F T x hD).program (Fin.last a) =
      Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a)) := by
  rw [ordered_append_density_index]
  exact head_coordinate_fibre_old_label_index T x (Fin.last a)

end IntegrationInACVF.Section7
