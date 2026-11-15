import Integration7.RawVFVolumeComposition
import Section4.UnionMapLaws

/-! Cancellation of a genuine volume bijection in a composite volume
equation. Its inverse and the original definable maps are used literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b c : ℕ}

theorem preservesVFVolume_cancel_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    {D : DefSet (rawMixedSpace (M := M) n c) (C.base : Set M)}
    (ω : VolumeForm A) (π : VolumeForm B) (ρ : VolumeForm D)
    (f : Map A B) (g : Map B D) (hf : Function.Bijective f)
    (hF : PreservesVFVolume ω π f) (hGF : PreservesVFVolume ω ρ (g.comp f)) :
    PreservesVFVolume π ρ g := by
  have hi := preservesVFVolume_inverse hc C hn ω π f hf hF
  have H := preservesVFVolume_comp hc C hn π ω ρ (f.inverse hf) (g.comp f)
    (Map.inverse_injective f hf) hi hGF
  have he : (g.comp f).comp (f.inverse hf) = g := by
    apply Map.ext
    intro p
    change g (f (f.inverse hf p)) = g p
    rw [Map.apply_inverse]
  rwa [he] at H

end IntegrationInACVF.Section7
