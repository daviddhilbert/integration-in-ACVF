import Integration7.CorrectedBlowupJacobian
import Integration7.BlowupHeadJacobianAlmostEverywhere

/-! Elementary blowups of isomorphic volume objects are isomorphic.
The head and full Jacobians come from actual generic-existence theorems;
the correction identifies their volume values outside a small exception. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def elementaryBlowupIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V WU WV : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U V) (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV) :
    RVVolumeIso WU WV := by
  let hhead := ElementaryBlowup.exists_headJacobian_after_blowup hc C b c f
  let J := Classical.choose hhead
  have hJ := Classical.choose_spec hhead
  let e := b.correctedIso c f J
  refine ⟨e, b.correctedIso_gamma c f J, ?_⟩
  obtain ⟨ω, D, hD, hd, hω⟩ := exists_definable_generic_RVJacobian hc C (Nat.zero_lt_succ k)
    e WU.essential_nonzero WV.essential_nonzero
  have hdefined : RVAlmostEverywhere WU.essential.obj.domain (k + 1) (fun w =>
      IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
        (WU.essential.obj.value w) (WV.essential.obj.value (finiteIsoMap e w)) ((ω w).val 0)) :=
    ⟨D, hD, hd, hω⟩
  apply RVAlmostEverywhere.mono (hJ.and hc C hdefined)
  rintro w ⟨hJ, hω⟩
  have he := b.correctedJacobian_eq_volumeRatio C c f J w hJ hω
  rw [← he]
  exact hω

end IntegrationInACVF.Section7
