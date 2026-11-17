module

public import Integration7.VolumeFamilyHeadIntegrals
public import IntegrationSection6.StandardProgramPresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A specified head preparation followed by a specified identity-order
tail contraction gives a genuine identity-order contraction of the whole
source. Its appended coordinates and retained density agree literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4
open SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a l k : ℕ}

theorem ordered_cast_source_appended_index
    {A B : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A V) (h : A=B) (ρ : Fin (k+1) → Fin a) :
    orderedAppendVolumeIndex (orderedCastSource T h) ρ = orderedAppendVolumeIndex T ρ := by
  cases h
  rfl

theorem ordered_cast_source_density_index
    {A B : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A V) (h : A=B) (δ : Fin a) :
    orderedAppendDensityIndex (orderedCastSource T h) δ = orderedAppendDensityIndex T δ := by
  cases h
  rfl

def identityHeadTailStandardContraction
    {A : DefSet (M := M) S (n+1) a} (T : HeadPreparation A)
    (D : StandardContraction T.contractedSet (Equiv.refl _)) : StandardContraction A (Equiv.refl _) :=
  standardFromProgram A (Equiv.refl _)
    (.step T (orderedCastSource D.program (vfPermutationImage_id_eq T.contractedSet)))
    (vfPermutationImage_id_eq A).symm

def appendedHeadIntegralVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (SpecialTransformations.Section3.Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (T : HeadPreparation A)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hfinT : ∀ (x : Fin n → VF (M := M)) (t : Fin ((k+1)+1) → RV (M := M)),
      {r : Fin (1+T.arity) → RV (M := M) |
        (x,r) ∈ carrier T.contractedSet ∧ r ∘ headAppendVolumeIndex T ρ = t}.Finite)
    (D : StandardContraction T.contractedSet (Equiv.refl _)) :
    RVVolumeIso
      (standardAppendVolumeObject (n := n) (k := k+1) hc C Ξ T.contractedSet (headAppendVolumeIndex T ρ)
        (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))
        (head_retained_density_nonzero T δ hδ) hfinT D)
      (standardAppendVolumeObject (n := n+1) (k := k) hc C Ξ A ρ δ hδ hfin (identityHeadTailStandardContraction T D)) := by
  let U := standardAppendVolumeObject (n := n) (k := k+1) hc C Ξ T.contractedSet (headAppendVolumeIndex T ρ)
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))
    (head_retained_density_nonzero T δ hδ) hfinT D
  let V := standardAppendVolumeObject (n := n+1) (k := k) hc C Ξ A ρ δ hδ hfin (identityHeadTailStandardContraction T D)
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.id _
  have hf : Function.Bijective f := Function.bijective_id
  have hIndex : orderedAppendVolumeIndex (identityHeadTailStandardContraction T D).program ρ =
      orderedAppendVolumeIndex D.program (headAppendVolumeIndex T ρ) := by
    change orderedAppendVolumeIndex (orderedCastSource _ _) ρ = _
    rw [ordered_cast_source_appended_index]
    change orderedAppendVolumeIndex (orderedCastSource D.program _) (headAppendVolumeIndex T ρ) = _
    rw [ordered_cast_source_appended_index]
  have hDensity : orderedAppendDensityIndex (identityHeadTailStandardContraction T D).program δ =
      orderedAppendDensityIndex D.program
        (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) := by
    change orderedAppendDensityIndex (orderedCastSource _ _) δ = _
    rw [ordered_cast_source_density_index]
    change orderedAppendDensityIndex (orderedCastSource D.program _) _ = _
    rw [ordered_cast_source_density_index]
  have hCoord : ∀ u, V.underlying.obj.value (f u) = U.underlying.obj.value u := by
    intro u
    change u.val ∘ orderedAppendVolumeIndex (identityHeadTailStandardContraction T D).program ρ = _
    rw [hIndex]
    rfl
  have hForm : ∀ u, V.form.value (f u) = U.form.value u := by
    intro u
    change u.val (orderedAppendDensityIndex (identityHeadTailStandardContraction T D).program δ) = _
    rw [hDensity]
    rfl
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm

end IntegrationInACVF.Section7
