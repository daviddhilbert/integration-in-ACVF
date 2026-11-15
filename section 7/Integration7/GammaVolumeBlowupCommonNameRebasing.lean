import Integration7.GammaElementaryCommonNameRebasing
import Integration7.GammaVolumeCommonNameIsomorphisms
import Integration7.GammaVolumeBlowupAddition

/-! Rebase every actual locus, remainder, elementary chart and volume
isomorphism of an original-Gamma volume blowup to the original real base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k : ℕ}

def volumeBlowupOverCommonNames
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (U W : GammaVolumeObjects G (D.base : Set M) k)
    (b : VolumeBlowup U.val W.val) (hb : b.GammaDefinable G) :
    VolumeBlowup (U.overCommonNames hc hNames).val (W.overCommonNames hc hNames).val := by
  let A : GammaVolumeObjects G (D.base : Set M) k := ⟨b.locus,hb.locus⟩
  let R : GammaVolumeObjects G (D.base : Set M) k := ⟨b.complement,hb.complement⟩
  let B : GammaVolumeObjects G (D.base : Set M) k := ⟨b.blownLocus,hb.blown⟩
  exact {
    locus := (A.overCommonNames hc hNames).val
    complement := (R.overCommonNames hc hNames).val
    blownLocus := (B.overCommonNames hc hNames).val
    elementary := elementaryBlowupOverCommonNames hc hNames A B b.elementary hb.elementary hb.centerAlgebraic
    sourceIso := gammaVolumeIsoOverCommonNames hc C D hCD hNames U (A.coprod R) b.sourceIso hb.source
    targetIso := gammaVolumeIsoOverCommonNames hc C D hCD hNames W (B.coprod R) b.targetIso hb.target }

theorem gamma_volume_blowup_over_common_names_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (U W : GammaVolumeObjects G (D.base : Set M) k)
    (b : VolumeBlowup U.val W.val) (hb : b.GammaDefinable G) :
    (volumeBlowupOverCommonNames hc C D hCD hNames U W b hb).GammaDefinable G := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact (GammaVolumeObjects.overCommonNames hc hNames ⟨b.locus,hb.locus⟩).property
  · exact (GammaVolumeObjects.overCommonNames hc hNames ⟨b.complement,hb.complement⟩).property
  · exact (GammaVolumeObjects.overCommonNames hc hNames ⟨b.blownLocus,hb.blown⟩).property
  · exact hb.elementary
  · exact hb.centerAlgebraic
  · exact hb.source
  · exact hb.target

end IntegrationInACVF.Section7
