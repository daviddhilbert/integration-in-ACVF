module

public import Integration7.GammaTermContextVolumeGeometry
public import Integration7.DefinableVolumeBaseReduction
public import Integration7.CommonContextVolumeDescent
public import Integration7.PositiveVolumeClassExtensions
public import Section3.VFDefinableClosure

@[expose] public section

/-! Naming elements already definable over the original real context
does not identify new positive volume classes. Actual common blowup
chains descend, with their original lengths and volume equations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem VolumeBlowupEquivalent.descend_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (hD : ∀ d ∈ (D.base : Set M), (C.base : Set M).Definable₁ LRV {d})
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent (U.extend hCD) (V.extend hCD)) :
    VolumeBlowupEquivalent U V := by
  let B : Base (M := M) := ⟨(C.base : Set M),∅⟩
  let E : Base (M := M) := ⟨(D.base : Set M),∅⟩
  let H : GammaDefinableBaseReduction E B := {
    real_subset := hCD
    real_definable := fun d hd σ hσ => real_definableAtBase B σ _
      ((definableClosureAt_iff_raw hc (C.base : Set M) σ d).mpr ⟨hD d hd,hσ⟩)
    gamma_definable := fun _ h => False.elim h }
  have hg := volume_common_gamma_in_term_context (B := E) hc D
    (by simp [E]) h
  have hr := (H.volumeCommon hg).overCommonNames hc C D hCD
    (by simp [B,commonRealNames])
  exact hr.toOrdinary hc C B

theorem positive_volume_class_extend_injective_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (hD : ∀ d ∈ (D.base : Set M), (C.base : Set M).Definable₁ LRV {d}) :
    Function.Injective (positiveVolumeClassExtend hc C D hCD (k := k)) := by
  intro u v huv
  induction u using Quotient.inductionOn with
  | h U =>
    induction v using Quotient.inductionOn with
    | h V =>
      exact (positiveVolumeBlowupClass_eq_iff hc C).mpr
        (VolumeBlowupEquivalent.descend_definable hc C D hCD hD
          ((positiveVolumeBlowupClass_eq_iff hc D).mp huv))

end IntegrationInACVF.Section7
