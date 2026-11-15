import Integration7.GammaVolumeCommonNameRebasing

/-! Original-Gamma algebraicity of the blowup center becomes genuine
original-real-base algebraicity once the common names are contained there. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S T : Set M} {k : ℕ}

theorem gamma_blowup_admissible_over_common_names
    (hc : CanonicalStructure.IsCanonical (M := M)) (hNames : commonRealNames G ⊆ T)
    (U : GammaVolumeObjects G S k) (hAd : BlowupAdmissible U.val) (hCenter : GammaBlowupCenter U.val G) :
    BlowupAdmissible (U.overCommonNames hc hNames).val := by
  refine ⟨fun u => hAd.nonzero ⟨u.val,u.property⟩,?_⟩
  intro u
  obtain ⟨A,hA,hfin,hu⟩ := hCenter ⟨u.val,u.property⟩
  refine ⟨A,hA.common_names.mono ?_,hfin,hu⟩
  intro x hx
  rcases hx with (hx | hx) | hx
  · exact Or.inl (hNames (Or.inl hx))
  · exact Or.inr hx
  · exact Or.inl (hNames (Or.inr hx))

end IntegrationInACVF.Section7
