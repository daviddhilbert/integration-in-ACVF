import Integration7.GammaRelativeTranslations
import Integration7.NativeRelativeTranslationVolumes
import Integration7.RetainedDensityContractionObjects
import Integration7.MixedRetainedLabelVolumeForms
import Integration7.OriginalBaseRelativeVolumeComparisons
import IntegrationSection6.GammaFiniteMixedBijections

/-! Relative translations of arbitrary finite-label mixed domains
preserve their specified active-first contraction class. Finite target
label fibres and the original literal density are proved internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k a : ℕ}

theorem relative_translation_retained_density_nonzero
    (A : DefSet (M := M) S (k+1) a) (i : Fin (k+1))
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    ∀ q : relativeTranslationImage A i c, (q.val.2 δ).val ≠ iRVZero := by
  rintro ⟨q,p,rfl⟩
  exact hδ p

set_option maxHeartbeats 1600000 in
theorem mixed_translation_contraction_common_blowup {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField B.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (A : DefSet (M := M) (C.base : Set M) (k+1) a) (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (i : Fin (k+1)) (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (hcΓ : GammaScalarGraphDefinable B (fun p z => ∃ q : A, q.val = p ∧ (c q).val 0 = z))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (k+1))} (hOrder : σ 0 = i)
    (T : StandardContraction A σ) (E : StandardContraction (relativeTranslationImage A i c) σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    let Y := relativeTranslationImage A i c
    let f := relativeTranslationToImage A i c
    let hf := relative_translation_to_image_bijective A i c hC
    let hF := gamma_relative_translation_to_image_graph A i c hcΓ
    let hY := gamma_relative_translation_image A i c hcΓ
    let hfinY := finite_rv_fibres_of_gamma_bijection hκ hs hreal f hf hF hfin
    let hε := relative_translation_retained_density_nonzero A i c δ hδ
    let U := retainedDensityContractionGammaObject hκ hs hreal hc C hBC A hA hfin δ hδ T hT
    let V := retainedDensityContractionGammaObject hκ hs hreal hc C hBC Y hY hfinY δ hε E hE
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B (D.base : Set M) k (U.extend hCD) (V.extend hCD) := by
  intro Y f hf hF hY hfinY hε U V
  let ω := mixedRetainedLabelVolumeForm (rawSpecialSet hc A) δ (fun p => hδ ⟨p.val,p.property⟩)
  let π := mixedRetainedLabelVolumeForm (rawSpecialSet hc Y) δ (fun q => hε ⟨q.val,q.property⟩)
  have hm : PreservesVFVolume ω π (rawSpecialMap hc f) :=
    native_relative_translation_preserves_volume hc C (Nat.zero_lt_succ k) A i c hC ω π (fun _ => rfl)
  have hi : UnaryRelative f (σ 0) := by
    rw [hOrder]
    exact relative_translation_unary_relative A i c
  have hGeom := standard_relative_volume_schema_comparison_of_generic_extension hc C hκ hs hreal hgamma γ hγ hγ1
    hBC hGeneric A Y hA hY hfin hfinY f hf hF ω π δ δ (fun _ => rfl) (fun _ => rfl) hm hi T E hT hE
  exact finite_standard_volume_comparison_of_geometric_rows hc C hκ hs hreal hBC A Y hA hY hfin hfinY
    T E hT hE δ δ hδ hε hGeom

end IntegrationInACVF.Section7
