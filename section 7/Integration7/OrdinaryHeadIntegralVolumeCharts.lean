module

public import Integration7.OrdinaryVolumeFamilyHeadIntegrals
public import Integration7.AppendedHeadIntegralPrograms
public import Integration7.HeadTailVolumeSelectors
public import Integration7.VolumeClassDegreeReindexing

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The first head tag followed by the tail contraction tags is the
full VF volume tuple. This chart has no old selected coordinates and
uses no empty-selected version of Lemma 7.5. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

def ordinaryHeadIntegralVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (T : HeadPreparation A) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfinT : ∀ (x : Fin n → VF (M := M)) (t : Fin 1 → RV (M := M)),
      {r : Fin (1+T.arity) → RV (M := M) |
        (x,r) ∈ carrier T.contractedSet ∧
        r ∘ headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a) = t}.Finite)
    (D : StandardContraction T.contractedSet (Equiv.refl _)) :
    RVVolumeIso
      ((standardAppendVolumeObject (n := n) (k := 0) hc C Ξ T.contractedSet
        (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
        (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))
        (head_retained_density_nonzero T δ hδ) hfinT D).reindexDegree
          (head_tail_volume_degree n).symm)
      (rawStandardVolumeObject hc C Ξ A hfin δ hδ (identityHeadTailStandardContraction T D)) := by
  let P := identityHeadTailStandardContraction T D
  let U := (standardAppendVolumeObject (n := n) (k := 0) hc C Ξ T.contractedSet
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))
    (head_retained_density_nonzero T δ hδ) hfinT D).reindexDegree
      (head_tail_volume_degree n).symm
  let V := rawStandardVolumeObject hc C Ξ A hfin δ hδ P
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.id _
  have hf : Function.Bijective f := Function.bijective_id
  have hIndex (i : Fin (n+1)) :
      orderedAppendVolumeIndex (k := 0) D.program (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
        (Fin.cast (congrArg Nat.succ (head_tail_volume_degree n)).symm i) = P.volumeIndex i := by
    have h := head_tail_append_volume_index T
      (orderedCastSource D.program (vfPermutationImage_id_eq T.contractedSet)) i
    rw [ordered_cast_source_appended_index] at h
    rw [h]
    change _ = (orderedCastSource _ _).volumeIndex ((Equiv.refl _).symm i)
    rw [orderedCastSource_volumeIndex]
    rfl
  have hCoord : ∀ u, V.underlying.obj.value (f u) = U.underlying.obj.value u := by
    intro u
    funext i
    exact congrArg u.val (hIndex i).symm
  have hDensity : orderedAppendDensityIndex D.program
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) =
      suffixIndex P.program.rvArity_le δ := by
    rw [ordered_append_density_index]
    apply Fin.ext
    have hD := D.program.rvArity_le
    have hT := specialRelative_rvArity_le T.special
    change D.arity-(1+T.arity)+(1+(T.arity-a+δ.val)) = D.arity-a+δ.val
    omega
  have hForm : ∀ u, V.form.value (f u) = U.form.value u := by
    intro u
    exact congrArg u.val hDensity.symm
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm

end IntegrationInACVF.Section7
