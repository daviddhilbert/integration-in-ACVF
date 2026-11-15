import Integration7.FrozenGeneratedVolumeContexts
import Integration7.DefinableVolumeRowReduction
import Integration7.GeometricRowsFromContractionVolumes
import Integration7.TwoVFStandardContractionComparisons

/-! The full VF-two theorem applies to actual frozen programs. The
generated closure and its additional Gamma names are eliminated again,
leaving exactly the original frozen base and literal contraction rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ}

set_option maxHeartbeats 3600000 in
theorem frozen_two_vf_standard_contraction_rows
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (hGenerated : VFGammaGeneratedBase B)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (y : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) y →
        AlgebraicIndependent (vfParameterField (C.base : Set M)) y)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (A : DefSet (M := M) ((C.base : Set M) ∪ Set.range (fun j => (x j).val)) 2 a)
    (hA : GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ (carrier A))
    (hfin : ∀ y : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (y,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ q : A, (q.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction A σ) (W : StandardContraction A τ)
    (hT : GammaProgramDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ T.program)
    (hW : GammaProgramDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ W.program) :
    (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
      T.volumeIndex (suffixIndex T.program.rvArity_le δ)).commonByGammaGeometry
      (gammaSelectedVolumeSchema W.target (gamma_program_final_set W.program hW)
        W.volumeIndex (suffixIndex W.program.rvArity_le δ))
      (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  let Bx : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
  let P := vfParameterCoefficientBase B x
  let D := frozenGeneratedVolumeContext hc C B hBC hgamma x
  let hSD := frozen_generated_context_contains hc C hBC hgamma x
  have hPN := frozen_generated_context_contains_names hc C hBC hNames hgamma x
  have hPD : P.real ⊆ (D.base : Set M) := fun _ h => hPN (Or.inl h)
  let AD := SpecialTransformations.Section5.extendBase A hSD
  have hAD : GammaSetDefinable P (carrier AD) :=
    hA.mono (subset_closureBase Bx).1 (subset_closureBase Bx).2
  let R := T.extendBase hSD
  let S := W.extendBase hSD
  have hR : GammaProgramDefinable P R.program := gamma_program_mono
    (subset_closureBase Bx).1 (subset_closureBase Bx).2 _ (T.program.extendBase_gamma hSD hT)
  have hS : GammaProgramDefinable P S.program := gamma_program_mono
    (subset_closureBase Bx).1 (subset_closureBase Bx).2 _ (W.program.extendBase_gamma hSD hW)
  have hδD : ∀ q : AD, (q.val.2 δ).val ≠ iRVZero := fun q => hδ ⟨q.val,q.property⟩
  have hNorm := two_vf_standard_contractions_compare hc D hPD hPN
    (vfParameterCoefficientBase_gamma_small C.uncountable
      ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hgamma x)
    (vfParameterCoefficientBase_generated hGenerated x) γ (vfParameterCoefficientBase_gamma_contains x hγ) hγ1
    (fun z hz => frozen_generated_context_preserves_independence hc C hBC hgamma hGeneric x hx z hz)
    AD hAD hfin δ hδD R S hR hS
  have hGeom := geometric_rows_of_contraction_volume_comparison hc D D.uncountable.le D.saturated
    ((Cardinal.mk_le_mk_of_subset hPD).trans_lt D.small) hPD AD AD hAD hAD hfin hfin
    δ δ hδD hδD R S hR hS hNorm
  have H : GammaDefinableBaseReduction
      ⟨P.real ∪ Set.range (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val),P.gamma⟩
      ⟨Bx.real ∪ Set.range (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val),Bx.gamma⟩ := by
    have hP : (⟨P.real ∪ Set.range (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val),P.gamma⟩ : Base (M := M)) = P :=
      gammaBase_eq_of_components (by rw [Set.range_eq_empty,Set.union_empty]) rfl
    have hB : (⟨Bx.real ∪ Set.range (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val),Bx.gamma⟩ : Base (M := M)) = Bx :=
      gammaBase_eq_of_components (by rw [Set.range_eq_empty,Set.union_empty]) rfl
    exact Eq.mpr (congrArg₂ GammaDefinableBaseReduction hP hB) (closureBaseReduction Bx)
  have hTV : R.volumeIndex = T.volumeIndex := funext (T.extendBase_volumeIndex hSD)
  have hWV : S.volumeIndex = W.volumeIndex := funext (W.extendBase_volumeIndex hSD)
  have hδT : ∀ q ∈ carrier T.target, (q.2 (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero := by
    intro q hq
    obtain ⟨u,hu⟩ := (T.program.surjective.comp (vfPermutationBijection_bijective A σ).2) ⟨q,hq⟩
    have hold := T.program.oldLabels (vfPermutationBijection A σ u) δ
    change (T.toMap u).val.2 _ = u.val.2 δ at hold
    change T.toMap u = ⟨q,hq⟩ at hu
    have hv := congrArg (fun v : T.target => v.val.2 (suffixIndex T.program.rvArity_le δ)) hu
    exact fun hz => hδ u ((congrArg Subtype.val hold).symm.trans ((congrArg Subtype.val hv).trans hz))
  have hδW : ∀ q ∈ carrier W.target, (q.2 (suffixIndex W.program.rvArity_le δ)).val ≠ iRVZero := by
    intro q hq
    obtain ⟨u,hu⟩ := (W.program.surjective.comp (vfPermutationBijection_bijective A τ).2) ⟨q,hq⟩
    have hold := W.program.oldLabels (vfPermutationBijection A τ u) δ
    change (W.toMap u).val.2 _ = u.val.2 δ at hold
    change W.toMap u = ⟨q,hq⟩ at hu
    have hv := congrArg (fun v : W.target => v.val.2 (suffixIndex W.program.rvArity_le δ)) hu
    exact fun hz => hδ u ((congrArg Subtype.val hold).symm.trans ((congrArg Subtype.val hv).trans hz))
  apply GammaRVVolumeSchema.commonByGammaGeometry_reduce_rows H ?_ ?_ ?_ ?_ hGeom
  · intro r y
    refine (gammaSelectedLabelSchema_volume R.target (gamma_program_final_set R.program hR)
      R.volumeIndex (Fin.elim0 : Fin 0 → VF (M := M)) r y).trans (Iff.trans ?_
        (gammaSelectedLabelSchema_volume T.target (gamma_program_final_set T.program hT)
          T.volumeIndex (Fin.elim0 : Fin 0 → VF (M := M)) r y).symm)
    exact and_congr Iff.rfl (Iff.of_eq (congrArg (fun ρ => r ∘ ρ = y) hTV))
  · intro r w
    rw [gammaSelectedVolumeSchema_density _ _ _ _ (show ∀ q ∈ carrier R.target,
        (q.2 (suffixIndex R.program.rvArity_le δ)).val ≠ iRVZero from hδT),
      gammaSelectedVolumeSchema_density _ _ _ _ hδT]
    rfl
  · intro r y
    refine (gammaSelectedLabelSchema_volume S.target (gamma_program_final_set S.program hS)
      S.volumeIndex (Fin.elim0 : Fin 0 → VF (M := M)) r y).trans (Iff.trans ?_
        (gammaSelectedLabelSchema_volume W.target (gamma_program_final_set W.program hW)
          W.volumeIndex (Fin.elim0 : Fin 0 → VF (M := M)) r y).symm)
    exact and_congr Iff.rfl (Iff.of_eq (congrArg (fun ρ => r ∘ ρ = y) hWV))
  · intro r w
    rw [gammaSelectedVolumeSchema_density _ _ _ _ (show ∀ q ∈ carrier S.target,
        (q.2 (suffixIndex S.program.rvArity_le δ)).val ≠ iRVZero from hδW),
      gammaSelectedVolumeSchema_density _ _ _ _ hδW]
    rfl

end IntegrationInACVF.Section7
