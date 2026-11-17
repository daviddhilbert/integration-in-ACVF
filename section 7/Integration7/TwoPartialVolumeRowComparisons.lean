module

public import Integration7.FrozenTwoVFContractionRows
public import Integration7.PrefixContractionVolumeSelectors
public import Integration7.HeadTailVolumeSelectors

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Two actual partial programs compare over a generic frozen VF tuple.
The source relation is a literal permutation of their two active
coordinates. Their full coordinate and density rows retain exactly the
original frozen parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a l r : ℕ}

set_option maxHeartbeats 3600000 in
theorem two_partial_volume_rows_at_generic
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (hGenerated : VFGammaGeneratedBase B)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (y : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) y →
        AlgebraicIndependent (vfParameterField (C.base : Set M)) y)
    {U W : DefSet (M := M) (C.base : Set M) (n+2) a}
    {V : DefSet (M := M) (C.base : Set M) n l} {Z : DefSet (M := M) (C.base : Set M) n r}
    (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    (δ : Fin a) (hδU : ∀ q : U, (q.val.2 δ).val ≠ iRVZero)
    (hδW : ∀ q : W, (q.val.2 δ).val ≠ iRVZero)
    (T : PartialContractionProgram (C.base : Set M) n (n := 2) U V)
    (E : PartialContractionProgram (C.base : Set M) n (n := 2) W Z)
    (hT : GammaPartialProgramDefinable B T) (hE : GammaPartialProgramDefinable B E)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (τ : Equiv.Perm (Fin 2))
    (hSource : vfPrefixFibre (p := 2) W x = vfPermutationImage (vfPrefixFibre (p := 2) U x) τ) :
    (gammaSelectedVolumeSchema V (gamma_partial_program_final_set T hT) T.volumeIndex
      (suffixIndex T.rvArity_le δ)).commonByGammaGeometry
      (gammaSelectedVolumeSchema Z (gamma_partial_program_final_set E hE) (E.volumeIndex ∘ τ.symm)
        (suffixIndex E.rvArity_le δ)) (fun j => (x j).val) := by
  let A := vfPrefixFibre (p := 2) U x
  have hA := gamma_vfPrefixFibre (p := 2) U hU x
  let R := standardFromProgram A (Equiv.refl _) (restrictPartialToPrefix T x) (vfPermutationImage_id_eq A).symm
  let S := standardFromProgram A τ (restrictPartialToPrefix E x) hSource
  have hR := gamma_standardFromProgram A (Equiv.refl _) (restrictPartialToPrefix T x)
    (vfPermutationImage_id_eq A).symm (gamma_restrictPartialToPrefix T hT x)
  have hS := gamma_standardFromProgram A τ (restrictPartialToPrefix E x) hSource
    (gamma_restrictPartialToPrefix E hE x)
  have hfinA : ∀ y : Fin 2 → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier A}.Finite :=
    fun y => hfinU (vfPrefixTuple x y)
  have hδA : ∀ q : A, (q.val.2 δ).val ≠ iRVZero :=
    fun q => hδU ⟨vfPrefixInsert x q.val,q.property⟩
  have hGeom := frozen_two_vf_standard_contraction_rows hc C hBC hNames hgamma hGenerated
    γ hγ hγ1 hGeneric x hx A hA hfinA δ hδA R S hR hS
  have hRV : R.volumeIndex = T.volumeIndex := by
    funext i
    exact (standard_from_program_volume_index (Equiv.refl _) _ _ i).trans
      (congrFun (restrict_partial_prefix_volume_index T x) i)
  have hSV : S.volumeIndex = E.volumeIndex ∘ τ.symm := by
    funext i
    exact (standard_from_program_volume_index τ _ _ i).trans
      (congrFun (restrict_partial_prefix_volume_index E x) (τ.symm i))
  have hRT : suffixIndex R.program.rvArity_le δ = suffixIndex T.rvArity_le δ := Fin.ext rfl
  have hSE : suffixIndex S.program.rvArity_le δ = suffixIndex E.rvArity_le δ := Fin.ext rfl
  have hV := gamma_partial_program_final_set T hT
  have hZ := gamma_partial_program_final_set E hE
  have hδV : ∀ q ∈ carrier V, (q.2 (suffixIndex T.rvArity_le δ)).val ≠ iRVZero :=
    fun q hq => partial_retained_density_nonzero T δ hδU ⟨q,hq⟩
  have hδZ : ∀ q ∈ carrier Z, (q.2 (suffixIndex E.rvArity_le δ)).val ≠ iRVZero :=
    fun q hq => partial_retained_density_nonzero E δ hδW ⟨q,hq⟩
  have hδR : ∀ q ∈ carrier R.target, (q.2 (suffixIndex R.program.rvArity_le δ)).val ≠ iRVZero := by
    intro q hq
    exact Eq.mpr (congrArg (fun i => (q.2 i).val ≠ iRVZero) hRT)
      (hδV (vfPrefixInsert x q) hq)
  have hδS : ∀ q ∈ carrier S.target, (q.2 (suffixIndex S.program.rvArity_le δ)).val ≠ iRVZero := by
    intro q hq
    exact Eq.mpr (congrArg (fun i => (q.2 i).val ≠ iRVZero) hSE)
      (hδZ (vfPrefixInsert x q) hq)
  have hMemR (s : Fin l → RV (M := M)) :
      (Fin.elim0,s) ∈ carrier R.target ↔ (x,s) ∈ carrier V := by
    change (vfPrefixTuple x Fin.elim0,s) ∈ carrier V ↔ (x,s) ∈ carrier V
    rw [vfPrefixTuple_zero]
  have hMemS (s : Fin r → RV (M := M)) :
      (Fin.elim0,s) ∈ carrier S.target ↔ (x,s) ∈ carrier Z := by
    change (vfPrefixTuple x Fin.elim0,s) ∈ carrier Z ↔ (x,s) ∈ carrier Z
    rw [vfPrefixTuple_zero]
  have hRange : Set.range (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) = (∅ : Set M) :=
    Set.range_eq_empty _
  have hBase : (⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪
      Set.range (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val),B.gamma⟩ : Base (M := M)) =
      ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ :=
    gammaBase_eq_of_components (by rw [hRange,Set.union_empty]) rfl
  apply GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
    (F' := gammaSelectedVolumeSchema V hV T.volumeIndex (suffixIndex T.rvArity_le δ))
    (G' := gammaSelectedVolumeSchema Z hZ (E.volumeIndex ∘ τ.symm) (suffixIndex E.rvArity_le δ))
    (t := fun j => (x j).val) hBase ?_ ?_ ?_ ?_ hGeom
  · intro s y
    refine (gammaSelectedLabelSchema_volume R.target (gamma_program_final_set R.program hR)
      R.volumeIndex (Fin.elim0 : Fin 0 → VF (M := M)) s y).trans (Iff.trans ?_
        (gammaSelectedLabelSchema_volume V hV T.volumeIndex x s y).symm)
    exact and_congr (hMemR s) (Iff.of_eq (congrArg (fun ρ => s ∘ ρ = y) hRV))
  · intro s w
    refine (gammaSelectedVolumeSchema_density R.target (gamma_program_final_set R.program hR)
      R.volumeIndex _ hδR Fin.elim0 s w).trans (Iff.trans ?_
        (gammaSelectedVolumeSchema_density V hV T.volumeIndex _ hδV x s w).symm)
    exact and_congr (hMemR s) (Iff.of_eq (congrArg (fun i => (fun _ : Fin 1 => s i) = w) hRT))
  · intro s y
    refine (gammaSelectedLabelSchema_volume S.target (gamma_program_final_set S.program hS)
      S.volumeIndex (Fin.elim0 : Fin 0 → VF (M := M)) s y).trans (Iff.trans ?_
        (gammaSelectedLabelSchema_volume Z hZ (E.volumeIndex ∘ τ.symm) x s y).symm)
    exact and_congr (hMemS s) (Iff.of_eq (congrArg (fun ρ => s ∘ ρ = y) hSV))
  · intro s w
    refine (gammaSelectedVolumeSchema_density S.target (gamma_program_final_set S.program hS)
      S.volumeIndex _ hδS Fin.elim0 s w).trans (Iff.trans ?_
        (gammaSelectedVolumeSchema_density Z hZ (E.volumeIndex ∘ τ.symm) _ hδZ x s w).symm)
    exact and_congr (hMemS s) (Iff.of_eq (congrArg (fun i => (fun _ : Fin 1 => s i) = w) hSE))

end IntegrationInACVF.Section7
