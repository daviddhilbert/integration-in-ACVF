import Integration7.CommonContextVolumeEquivalences
import Integration7.GammaPermutedVolumeObjects

/-! A common degree cast or coordinate permutation can be made before
or after passing to the containing comparison context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {C : BaseContext M} {a b : ℕ}

theorem CommonContextVolumeEquivalent.reindexDegree
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : GammaVolumeObjects G (C.base : Set M) b}
    (h : CommonContextVolumeEquivalent G C U V) (e : a=b) :
    CommonContextVolumeEquivalent G C (U.reindexDegree e) (V.reindexDegree e) := by
  obtain ⟨D,hCD,h⟩ := h
  exact ⟨D,hCD,h.reindexDegree hc D e⟩

theorem CommonContextVolumeEquivalent.permuteVolume
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : GammaVolumeObjects G (C.base : Set M) b}
    (h : CommonContextVolumeEquivalent G C U V) (e : Equiv.Perm (Fin (b+1))) :
    CommonContextVolumeEquivalent G C
      ⟨U.val.permuteVolume e,U.property.permuteVolume hc e⟩
      ⟨V.val.permuteVolume e,V.property.permuteVolume hc e⟩ := by
  obtain ⟨D,hCD,h⟩ := h
  exact ⟨D,hCD,h.permuteVolume hc D e⟩

end IntegrationInACVF.Section7
