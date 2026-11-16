module

public import Integration7.OrderedRelativeVolumeSchemaComparison
public import Integration7.PermutedVFVolumeForms
public import Integration7.GammaPermutedSelectedVolumeFamilies
public import Integration7.SelectedVolumeCoordinatePermutations
public import Integration7.HeadTailVolumeSelectors
public import Integration7.GlobalRelativeVolumeContractions
public import Integration7.OrderedAppendVolumeFiniteness
public import Integration7.SelectedVolumeDegreeTransport
public import Integration7.GenericRelativeHeadVolumeComparison
public import Integration7.GenericOrderedAppendVolumeContractions
public import Integration7.RelativeHeadVolumeComparison
public import Integration7.OrderedAppendVolumeContractions

@[expose] public section

/-! Relative volume comparisons retain the original Gamma base when
a containing presentation context preserves original VF independence.
This allows the real codes of Gamma names without naming them in the result. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b l r : ℕ}

set_option maxHeartbeats 2400000 in
theorem ordered_relative_volume_comparison_of_generic_extension {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M)) (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {s : Fin a → RV (M := M) | (x,s) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {s : Fin b → RV (M := M) | (x,s) ∈ carrier V}.Finite)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0)
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hE : GammaGraphDefinable B (pointMapGraph E.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    {U₀ : DefSet (M := M) (C.base : Set M) 0 l} {V₀ : DefSet (M := M) (C.base : Set M) 0 r}
    (tail : OrderedContractionProgram (C.base : Set M) T.contractedSet U₀)
    (etail : OrderedContractionProgram (C.base : Set M) E.contractedSet V₀)
    (htail : GammaProgramDefinable B tail) (hetail : GammaProgramDefinable B etail) :
    ∀ x : Fin 0 → VF (M := M),
      (gammaSelectedVolumeSchema U₀ (gamma_program_final_set tail htail)
        (orderedAppendVolumeIndex (k := 0) tail (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)))
        (orderedAppendDensityIndex tail (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)))).commonByGammaGeometry
      (gammaSelectedVolumeSchema V₀ (gamma_program_final_set etail hetail)
        (orderedAppendVolumeIndex (k := 0) etail (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)))
        (orderedAppendDensityIndex etail (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε))))
      (fun j => (x j).val) := by
  have hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => ω.nonzero ⟨p,hp⟩ ((hω ⟨p,hp⟩).trans h))
  have hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => π.nonzero ⟨p,hp⟩ ((hπ ⟨p,hp⟩).trans h))
  have hfinU₀ (y : Fin (n+1) → VF (M := M)) (t : Fin 0 → RV (M := M)) :
      {s : Fin a → RV (M := M) | (y,s) ∈ carrier U ∧ s ∘ Fin.elim0 = t}.Finite :=
    (hfinU y).subset (fun _ h => h.1)
  have hfinV₀ (y : Fin (n+1) → VF (M := M)) (t : Fin 0 → RV (M := M)) :
      {s : Fin b → RV (M := M) | (y,s) ∈ carrier V ∧ s ∘ Fin.elim0 = t}.Finite :=
    (hfinV y).subset (fun _ h => h.1)
  exact lemma_7_5_ordered_geometric_at_generic (k := 0) hc C hκ hs C.model00 hreal hgamma γ hγ hγ1 hBC
    T.contractedSet E.contractedSet (gamma_headImage T.target hTarget) (gamma_headImage E.target hETarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε))
    (head_retained_density_nonzero T δ hδ) (head_retained_density_nonzero E ε hε)
    (head_selected_fibres_finite hκ hs hreal T hT hTarget Fin.elim0 hfinU₀)
    (head_selected_fibres_finite hκ hs hreal E hE hETarget Fin.elim0 hfinV₀)
    (fun x hx => gamma_relative_head_volume_comparison_at_generic_base hc C hκ hs hreal hgamma γ hγ hγ1 hBC
      U V hU hV hfinU hfinV f hf hfΓ hi ω π δ ε hω hπ hm T E hT hE hTarget hETarget x
      (hGeneric x hx))
    tail etail htail hetail


set_option maxHeartbeats 2400000 in
theorem ordered_relative_volume_schema_comparison_of_generic_extension {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M)) (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {s : Fin a → RV (M := M) | (x,s) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {s : Fin b → RV (M := M) | (x,s) ∈ carrier V}.Finite)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0)
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    {U₀ : DefSet (M := M) (C.base : Set M) 0 l} {V₀ : DefSet (M := M) (C.base : Set M) 0 r}
    (P : OrderedContractionProgram (C.base : Set M) U U₀)
    (Q : OrderedContractionProgram (C.base : Set M) V V₀)
    (hP : GammaProgramDefinable B P) (hQ : GammaProgramDefinable B Q) :
    (gammaSelectedVolumeSchema U₀ (gamma_program_final_set P hP) P.volumeIndex
      (suffixIndex P.rvArity_le δ)).commonByGammaGeometry
    (gammaSelectedVolumeSchema V₀ (gamma_program_final_set Q hQ) Q.volumeIndex
      (suffixIndex Q.rvArity_le ε)) (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  have hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => ω.nonzero ⟨p,hp⟩ ((hω ⟨p,hp⟩).trans h))
  have hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => π.nonzero ⟨p,hp⟩ ((hπ ⟨p,hp⟩).trans h))
  cases P with
  | step T tail =>
    cases Q with
    | step E etail =>
      have h := ordered_relative_volume_comparison_of_generic_extension hc C hκ hs hreal hgamma γ hγ hγ1 hBC hGeneric
        U V hU hV hfinU hfinV f hf hfΓ hi ω π δ ε hω hπ hm T E
        hP.1 hQ.1 hP.2.1 hQ.2.1 tail etail hP.2.2 hQ.2.2 (Fin.elim0 : Fin 0 → VF (M := M))
      have hδ' := ordered_append_retained_density_nonzero (OrderedContractionProgram.step T tail) δ hδ
      have hε' := ordered_append_retained_density_nonzero (OrderedContractionProgram.step E etail) ε hε
      rw [ordered_append_density_index] at hδ' hε'
      rw [head_tail_append_density_index,head_tail_append_density_index] at h
      apply selected_volume_geometry_reindex (head_tail_volume_degree n)
        U₀ V₀ (gamma_program_final_set (OrderedContractionProgram.step T tail) hP) (gamma_program_final_set (OrderedContractionProgram.step E etail) hQ)
        (orderedAppendVolumeIndex (k := 0) tail (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)))
        (orderedAppendVolumeIndex (k := 0) etail (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)))
        (OrderedContractionProgram.step T tail).volumeIndex (OrderedContractionProgram.step E etail).volumeIndex ?_ ?_
        (suffixIndex (OrderedContractionProgram.step T tail).rvArity_le δ) (suffixIndex (OrderedContractionProgram.step E etail).rvArity_le ε)
        hδ' hε' (Fin.elim0 : Fin 0 → VF (M := M)) h
      · funext i
        have hi : (finCongr (congrArg Nat.succ (head_tail_volume_degree n))).symm i =
            Fin.cast (congrArg Nat.succ (head_tail_volume_degree n)).symm i := Fin.ext rfl
        exact (congrArg (orderedAppendVolumeIndex (k := 0) tail
          (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))) hi).trans
          (head_tail_append_volume_index T tail i)
      · funext i
        have hi : (finCongr (congrArg Nat.succ (head_tail_volume_degree n))).symm i =
            Fin.cast (congrArg Nat.succ (head_tail_volume_degree n)).symm i := Fin.ext rfl
        exact (congrArg (orderedAppendVolumeIndex (k := 0) etail
          (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))) hi).trans
          (head_tail_append_volume_index E etail i)


set_option maxHeartbeats 2400000 in
theorem standard_relative_volume_schema_comparison_of_generic_extension {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M)) (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {s : Fin a → RV (M := M) | (x,s) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {s : Fin b → RV (M := M) | (x,s) ∈ carrier V}.Finite)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    {σ : Equiv.Perm (Fin (n+1))} (hi : UnaryRelative f (σ 0))
    (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT) T.volumeIndex
      (suffixIndex T.program.rvArity_le δ)).commonByGammaGeometry
    (gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program hE) E.volumeIndex
      (suffixIndex E.program.rvArity_le ε)) (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  let Uσ := vfPermutationImage U σ
  let Vσ := vfPermutationImage V σ
  let g := vfPermutedMap f σ
  have hUσ := gamma_vfPermutationImage U hU σ
  have hVσ := gamma_vfPermutationImage V hV σ
  have hfinUσ : ∀ x : Fin (n+1) → VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier Uσ}.Finite := by
    intro x
    exact (hfinU (x ∘ σ.symm)).subset (fun r hr => (vfPermutationImage_row U σ x r).mp hr)
  have hfinVσ : ∀ x : Fin (n+1) → VF (M := M),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier Vσ}.Finite := by
    intro x
    exact (hfinV (x ∘ σ.symm)).subset (fun r hr => (vfPermutationImage_row V σ x r).mp hr)
  have h := ordered_relative_volume_schema_comparison_of_generic_extension hc C hκ hs hreal hgamma γ hγ hγ1 hBC hGeneric
    Uσ Vσ hUσ hVσ hfinUσ hfinVσ g (vfPermutedMap_bijective f hf σ)
    (gamma_vfPermutedMap f hU hV hfΓ σ) (vfPermutedMap_relative f σ hi)
    (permutedVFVolumeForm hc U ω σ) (permutedVFVolumeForm hc V π σ) δ ε
    (permuted_vf_volume_form_retained hc U ω σ δ hω)
    (permuted_vf_volume_form_retained hc V π σ ε hπ)
    (preserves_vf_volume_conjugate_permutation hc f σ ω π hm) T.program E.program hT hE
  have hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨p,hp⟩ ((hω ⟨p,hp⟩).trans hz))
  have hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun hz => π.nonzero ⟨p,hp⟩ ((hπ ⟨p,hp⟩).trans hz))
  have hδ' := ordered_append_retained_density_nonzero T.program δ (vf_permuted_retained_density_nonzero U σ δ hδ)
  have hε' := ordered_append_retained_density_nonzero E.program ε (vf_permuted_retained_density_nonzero V σ ε hε)
  rw [ordered_append_density_index] at hδ' hε'
  exact selected_volume_geometry_permute hc T.target E.target
    (gamma_program_final_set T.program hT) (gamma_program_final_set E.program hE)
    T.program.volumeIndex E.program.volumeIndex (suffixIndex T.program.rvArity_le δ)
    (suffixIndex E.program.rvArity_le ε) hδ' hε' (Fin.elim0 : Fin 0 → VF (M := M)) σ.symm h

end IntegrationInACVF.Section7
