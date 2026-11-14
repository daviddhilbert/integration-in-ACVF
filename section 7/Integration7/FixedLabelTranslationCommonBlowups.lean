import Integration7.FixedLabelContractionVolumeObjects
import Integration7.FixedLabelTranslationContractionComparisons
import Integration7.GammaRelativeTranslations
import Integration7.OriginalBaseRelativeVolumeComparisons

/-! Corollary7.6 compares arbitrary specified contractions before and
following an actual translation, with every old label and the literal
retained density fixed. This is over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {n d : ℕ}

set_option maxHeartbeats 1200000 in
theorem fixed_label_translation_contraction_common_blowup {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk P.real < κ) (hgamma : Cardinal.mk P.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (hPC : P.real ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField P.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (A : DefSet (M := M) (C.base : Set M) (n+1) 0) (hA : GammaSetDefinable P (carrier A))
    (i : Fin (n+1))
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (hcΓ : GammaScalarGraphDefinable P (fun p a => ∃ q : A, q.val = p ∧ (c q).val 0 = a))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
    {σ : Equiv.Perm (Fin (n+1))} (hσ : σ 0 = i)
    (T : StandardContraction (fixedRVLabelDomain A z hz) σ)
    (E : StandardContraction (fixedRVLabelDomain (relativeTranslationImage A i c) z hz) σ)
    (hT : GammaProgramDefinable P T.program) (hE : GammaProgramDefinable P E.program) :
    let U := fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT
    let X := relativeTranslationImage A i c
    let hX := gamma_relative_translation_image A i c hcΓ
    let V := fixedLabelContractionGammaObject hκ hs hreal hc C hPC X hX z hz hzΓ j η hj hη0 E hE
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent P (D.base : Set M) n (U.extend hCD) (V.extend hCD) := by
  intro U X hX V
  have hGeom := fixed_label_translation_contraction_geometry hc C hκ hs hreal hgamma γ hγ hγ1 hPC hGeneric
    A hA i c hC hcΓ z hz hzΓ j η hj hη0 hσ T E hT hE
  exact finite_standard_volume_comparison_of_geometric_rows hc C hκ hs hreal hPC
    (fixedRVLabelDomain A z hz) (fixedRVLabelDomain X z hz)
    (gamma_fixed_rv_label_domain A hA z hz hzΓ) (gamma_fixed_rv_label_domain X hX z hz hzΓ)
    (fixed_pure_rv_label_fibres_finite A z hz) (fixed_pure_rv_label_fibres_finite X z hz)
    T E hT hE (Fin.natAdd 0 j) (Fin.natAdd 0 j)
    (fun p => raw_fixed_rv_label_density_nonzero hc A z hz j η hj hη0 ⟨p.val,p.property⟩)
    (fun p => raw_fixed_rv_label_density_nonzero hc X z hz j η hj hη0 ⟨p.val,p.property⟩) hGeom

end IntegrationInACVF.Section7
