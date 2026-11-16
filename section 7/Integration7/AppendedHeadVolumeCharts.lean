module

public import Integration7.HeadTailSelectedVolumeSelectors
public import Integration7.SelectedStandardVolumeObjects
public import Integration7.CommonContextVolumeReindexing

@[expose] public section

/-! Contracting the remaining VF coordinates after a fixed head gives
the same actual volume object after one explicit common permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d : ℕ}

theorem appended_head_volume_object_degree (n d : ℕ) : d+(n+1) = (1+d)+n := by omega

def appendedHeadVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+2) a)
    (σ : Equiv.Perm (Fin (n+2))) (T : HeadPreparation (vfPermutationImage A σ))
    (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+2) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hδT : ∀ p ∈ carrier T.contractedSet,
      (p.2 (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))).val ≠ iRVZero)
    (hfinT : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (1+d) → RV (M := M)),
      {r : Fin (1+T.arity) → RV (M := M) | (x,r) ∈ carrier T.contractedSet ∧ r ∘ headVolumeIndex T ρ = t}.Finite)
    (τ : Equiv.Perm (Fin (n+1))) (D : StandardContraction T.contractedSet τ) :
    let R := selectedStandardVolumeObject hc C Ξ T.contractedSet (headVolumeIndex T ρ)
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) hδT hfinT D
    RVVolumeIso ((R.reindexDegree (appended_head_volume_object_degree n d)).permuteVolume
      (headVolumeOrderPermutation d σ))
      (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin (headTailAppendedStandardProgram σ T τ D)) := by
  intro R
  let U := (R.reindexDegree (appended_head_volume_object_degree n d)).permuteVolume (headVolumeOrderPermutation d σ)
  let F := headTailAppendedStandardProgram σ T τ D
  let V := selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin F
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.inclusion (fun _ h => h)
  have hf : Function.Bijective f := ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
    fun v => ⟨⟨v.val,v.property⟩,rfl⟩⟩
  have hSel := head_tail_selected_volume_index_rotated σ T D ρ F.volumeIndex F.program.rvArity_le
    (head_tail_appended_volume_head σ T τ D) (head_tail_appended_volume_tail σ T τ D)
    (head_tail_appended_old_index σ T τ D)
  have hcoord : ∀ u, V.underlying.obj.value (f u) = U.underlying.obj.value u := by
    intro u
    change u.val ∘ selectedStandardVolumeIndex F ρ =
      ((u.val ∘ selectedStandardVolumeIndex D (headVolumeIndex T ρ)) ∘
        finCongr (congrArg Nat.succ (appended_head_volume_object_degree n d))) ∘ headVolumeOrderPermutation d σ
    funext i
    exact (congrArg u.val (congrFun hSel i)).symm
  have hφ : ∀ u, V.form.value (f u) = U.form.value u := by
    intro u
    change u.val (suffixIndex F.program.rvArity_le δ) = u.val
      (suffixIndex D.program.rvArity_le (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)))
    exact congrArg u.val (head_tail_appended_old_index σ T τ D δ).symm
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hcoord)) hcoord hφ

end IntegrationInACVF.Section7
