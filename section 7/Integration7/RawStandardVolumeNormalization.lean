import Integration7.RawStandardVolumeObjects
import Integration7.RetainedDensityContractionObjects
import Integration7.CommonContextVolumeEquivalences

/-! The literal raw contraction volume object and the normalized object
in Lemma 7.7 are related by a genuine original-Gamma volume isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem raw_standard_volume_normalization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    CommonContextVolumeEquivalent G C
      ⟨rawStandardVolumeObject hc C Ξ A hfin δ hδ T,
        raw_standard_volume_object_gamma hc C Ξ A hfin δ hδ T⟩
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated C.small hc C
        (Set.Subset.refl _) A ((gammaLogicInput G).real_set _ (setDefinable A)) hfin δ
        (fun p => hδ p.val p.property) T (gamma_program_over_real_base G T.program)) := by
  intro G
  obtain ⟨hZ,D,hCD,e,he⟩ := finite_contraction_normalization_volume_iso hc C C (Set.Subset.refl _)
    C.uncountable.le C.saturated C.small (Set.Subset.refl _) A
    ((gammaLogicInput G).real_set _ (setDefinable A)) hfin T (gamma_program_over_real_base G T.program)
    δ (fun p => hδ p.val p.property)
  exact CommonContextVolumeEquivalent.of_extended_iso hCD e he

end IntegrationInACVF.Section7
