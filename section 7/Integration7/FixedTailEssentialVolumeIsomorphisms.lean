module

public import Integration7.FixedTailUnaryVolumeIsomorphisms
public import Integration7.FixedHeadEssentialVolumeIsomorphisms
public import Integration7.GammaVolumeLabelIdentities
public import Integration7.GradedVolumeProducts

@[expose] public section

/-! Essential restriction of the unary factor commutes with adjoining
a nonzero fixed tail volume coordinate. The volume map keeps all labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem fixed_tail_essential_carrier (U : RVFiniteObject (M := M) S 1)
    (r : CanonicalRV.RVSort M) (hr : r.val ∈ S) (hr0 : r.val ≠ iRVZero) :
    (appendFixedRVVolume U r hr (VolumeForm.one _)).essential.obj.domain.carrier =
      (rvFiniteEssential U).obj.domain.carrier := by
  ext z
  constructor
  · intro hz
    have hU := rvEssentialLabels_subset (appendFixedRVCoordinate U r hr).obj hz
    apply (mem_rvEssentialLabels U.obj ⟨z,hU⟩).mpr
    intro i
    have hi : i = 0 := Fin.ext (by have h := i.isLt; omega)
    subst i
    exact (appendFixedRVVolume U r hr (VolumeForm.one _)).essential_nonzero ⟨z,hz⟩ 0
  · intro hz
    have hU := rvEssentialLabels_subset U.obj hz
    apply (mem_rvEssentialLabels (appendFixedRVCoordinate U r hr).obj ⟨z,hU⟩).mpr
    intro i
    fin_cases i
    · exact rvEssential_value_nonzero U.obj ⟨z,hz⟩ 0
    · exact hr0

def fixedTailEssentialVolumeUnderlyingIso (U : RVFiniteObject (M := M) S 1)
    (r : CanonicalRV.RVSort M) (hr : r.val ∈ S) (hr0 : r.val ≠ iRVZero) :
    (appendFixedRVVolume U r hr (VolumeForm.one _)).essential ≅
      (appendFixedRVVolume (rvFiniteEssential U) r hr (VolumeForm.one _)).essential := by
  let L := appendFixedRVVolume U r hr (VolumeForm.one _)
  let R := appendFixedRVVolume (rvFiniteEssential U) r hr (VolumeForm.one _)
  have he : L.essential.obj.domain.carrier = R.essential.obj.domain.carrier := by
    rw [fixed_tail_essential_carrier U r hr hr0,
      fixed_tail_essential_carrier (rvFiniteEssential U) r hr hr0,rv_finite_essential_carrier_idempotent]
  let F : Map L.essential.obj.domain R.essential.obj.domain := Map.inclusion he.le
  have hF : Function.Bijective F := by
    constructor
    · intro p q h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro q
      exact ⟨⟨q.val,he.ge q.property⟩,Subtype.ext rfl⟩
  exact finiteIsoOfNondegenerateBijection F hF L.essential_nonzero R.essential_nonzero

def fixedTailEssentialVolumeIso (U : RVFiniteObject (M := M) S 1)
    (r : CanonicalRV.RVSort M) (hr : r.val ∈ S) (hr0 : r.val ≠ iRVZero) :
    RVVolumeIso (appendFixedRVVolume U r hr (VolumeForm.one _))
      (appendFixedRVVolume (rvFiniteEssential U) r hr (VolumeForm.one _)) :=
  constantTailVolumeIso (fixedTailEssentialVolumeUnderlyingIso U r hr hr0) r
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem fixed_tail_essential_volume_iso_gamma {B : Base (M := M)}
    (U : RVFiniteObject (M := M) S 1) (r : CanonicalRV.RVSort M) (hr : r.val ∈ S) (hr0 : r.val ≠ iRVZero)
    (hUE : GammaSetDefinable B {p : Point (M := M) 0 U.obj.arity |
      p.2 ∈ (rvFiniteEssential U).obj.domain.carrier}) :
    (fixedTailEssentialVolumeIso U r hr hr0).GammaDefinable B := by
  have hD : GammaSetDefinable B {p : Point (M := M) 0 U.obj.arity |
      p.2 ∈ (appendFixedRVVolume U r hr (VolumeForm.one _)).essential.obj.domain.carrier} := by
    simpa only [fixed_tail_essential_carrier U r hr hr0] using hUE
  exact gamma_volume_iso_label_identity B (fixedTailEssentialVolumeIso U r hr hr0) hD (fun _ => rfl)

end IntegrationInACVF.Section7
