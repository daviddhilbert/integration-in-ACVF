import Integration7.VolumeAlmostEverywhere
import Section4.RVParameterInvariance

/-! Adding real parameters retains a witnessed exceptional locus of smaller
RV dimension. No generation property of the enlarged base is asserted. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S T : Set M} {a n : ℕ}

theorem RVAlmostEverywhere.extend {A : DefSet (rawRVSpace (M := M) a) S}
    {P : A → Prop} (hST : S ⊆ T) (h : RVAlmostEverywhere A n P) :
    RVAlmostEverywhere (A.extend hST) n (fun x => P ⟨x.val,x.property⟩) := by
  obtain ⟨D,hDA,hd,hP⟩ := h
  exact ⟨D.extend hST,hDA,(rvDim_extend_le hST D).trans_lt hd,hP⟩

end IntegrationInACVF.Section7
