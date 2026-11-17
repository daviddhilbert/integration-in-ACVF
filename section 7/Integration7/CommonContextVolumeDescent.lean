module

public import Integration7.GammaVolumeBlowupCommonNameRebasing
public import Integration7.CommonContextVolumeEquivalences

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Original-Gamma finite volume blowup witnesses descend to any
original context containing their common names, with exact chain lengths. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k n : ℕ}

theorem GammaIteratedVolumeBlowup.overCommonNames
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    {U V : GammaVolumeObjects G (D.base : Set M) k}
    (h : GammaIteratedVolumeBlowup G (D.base : Set M) k n U V) :
    GammaIteratedVolumeBlowup G (C.base : Set M) k n
      (U.overCommonNames hc hNames) (V.overCommonNames hc hNames) := by
  induction h with
  | refl U => exact .refl _
  | @step n U V W b rest ih =>
    obtain ⟨b,hb⟩ := b
    exact .step ⟨volumeBlowupOverCommonNames hc C D hCD hNames U V b hb,
      gamma_volume_blowup_over_common_names_graph hc C D hCD hNames U V b hb⟩ ih

theorem GammaVolumeBlowupEquivalent.overCommonNames
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    {U V : GammaVolumeObjects G (D.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent G (D.base : Set M) k U V) :
    GammaVolumeBlowupEquivalent G (C.base : Set M) k
      (U.overCommonNames hc hNames) (V.overCommonNames hc hNames) := by
  obtain ⟨m,n,U',V',hU,hV,e,he⟩ := h
  exact ⟨m,n,U'.overCommonNames hc hNames,V'.overCommonNames hc hNames,
    hU.overCommonNames hc C D hCD hNames,hV.overCommonNames hc C D hCD hNames,
    gammaVolumeIsoOverCommonNames hc C D hCD hNames U' V' e he,
    gamma_volume_iso_over_common_names_graph hc C D hCD hNames U' V' e he⟩

theorem CommonContextVolumeEquivalent.descend
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    {U V : GammaVolumeObjects G (C.base : Set M) k}
    (h : CommonContextVolumeEquivalent G C U V) :
    GammaVolumeBlowupEquivalent G (C.base : Set M) k U V := by
  obtain ⟨D,hCD,h⟩ := h
  exact h.overCommonNames hc C D hCD hNames

end IntegrationInACVF.Section7
