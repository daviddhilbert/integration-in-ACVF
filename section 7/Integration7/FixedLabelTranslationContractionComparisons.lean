import Integration7.FixedLabelTranslationDensityForms
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
theorem fixed_label_translation_contraction_geometry {κ : Cardinal}
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
    (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT) T.volumeIndex
      (suffixIndex T.program.rvArity_le (Fin.natAdd 0 j))).commonByGammaGeometry
    (gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program hE) E.volumeIndex
      (suffixIndex E.program.rvArity_le (Fin.natAdd 0 j)))
      (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  let X := relativeTranslationImage A i c
  have hX := gamma_relative_translation_image A i c hcΓ
  let f := fixedRVLabelMap (relativeTranslationToImage A i c) z hz
  have hf : Function.Bijective f := fixed_rv_label_map_bijective _
    (relative_translation_to_image_bijective A i c hC) z hz
  have hfΓ := gamma_fixed_rv_label_map (relativeTranslationToImage A i c) hA hX
    (gamma_relative_translation_to_image_graph A i c hcΓ) z hz hzΓ
  have hi : UnaryRelative f (σ 0) := by
    rw [hσ]
    exact fixed_rv_label_map_relative (relativeTranslationToImage A i c)
      (relative_translation_unary_relative A i c) z hz
  exact standard_relative_volume_schema_comparison_of_generic_extension hc C hκ hs hreal hgamma γ hγ hγ1
    hPC hGeneric (fixedRVLabelDomain A z hz) (fixedRVLabelDomain X z hz)
    (gamma_fixed_rv_label_domain A hA z hz hzΓ) (gamma_fixed_rv_label_domain X hX z hz hzΓ)
    (fixed_pure_rv_label_fibres_finite A z hz) (fixed_pure_rv_label_fibres_finite X z hz)
    f hf hfΓ (fixedRVLabelDensityForm hc A z hz j η hj hη0)
    (fixedRVLabelDensityForm hc X z hz j η hj hη0) (Fin.natAdd 0 j) (Fin.natAdd 0 j)
    (fun _ => rfl) (fun _ => rfl)
    (fixed_rv_label_translation_preserves_literal_density hc C (by omega) A i c hC z hz j η hj hη0)
    hi T E hT hE

end IntegrationInACVF.Section7
