module

public import Integration7.VFVolumeBijections
public import Section4.ParameterInvariance

@[expose] public section

/-! The actual VF-small exceptional set and volume equation persist
when finitely or arbitrarily many real parameters are added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S T : Set M} {n a b : ℕ}

theorem VFAlmostEverywhere.extend
    {A : DefSet (rawMixedSpace (M := M) n a) S} {P : A → Prop}
    (hST : S ⊆ T) (h : VFAlmostEverywhere A P) :
    VFAlmostEverywhere (A.extend hST) (fun p => P ⟨p.val,p.property⟩) := by
  obtain ⟨D, hDA, hd, hP⟩ := h
  exact ⟨D.extend hST, hDA, (vfDim_extend_le _ hST D).trans_lt hd, hP⟩

theorem PreservesVFVolume.extend
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) n b) S}
    {ω : VolumeForm A} {π : VolumeForm B} {f : Map A B}
    (hST : S ⊆ T) (h : PreservesVFVolume ω π f) :
    PreservesVFVolume (ω.extend hST) (π.extend hST) (f.extend hST) :=
  VFAlmostEverywhere.extend hST h

end IntegrationInACVF.Section7
