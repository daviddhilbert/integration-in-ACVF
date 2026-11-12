import IntegrationSection6.GammaVolumeProjections
import IntegrationSection6.GammaNativeRawObjects
import IntegrationSection6.GammaSelectedVolumeObjects

/-! Swap the two blocks of an actual finite volume tuple. This also
places selected old RV labels before the contracted VF volume labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n e : ℕ}

def gammaSwapVolumeBlocks (U : GammaRVFiniteObject B (n+e)) : GammaRVFiniteObject B (e+n) where
  toGammaRVObject := gammaProjectVolumeObject U.toGammaRVObject (@finAddFlip e n)
  finite_volume := by
    intro t
    apply (U.finite_volume ⟨t.val ∘ (@finAddFlip n e),Set.mem_univ _⟩).subset
    intro u hu
    apply Subtype.ext
    funext j
    have h := congrFun (congrArg Subtype.val hu) ((@finAddFlip n e) j)
    change gammaVolumeValue U.toGammaRVObject u ((@finAddFlip e n) ((@finAddFlip n e) j)) =
      t.val ((@finAddFlip n e) j) at h
    have he : (@finAddFlip e n) ((@finAddFlip n e) j) = j := by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
        simp only [finAddFlip_apply_castAdd,finAddFlip_apply_natAdd]
    rw [he] at h
    exact h

theorem gammaSwapVolumeBlocks_value (U : GammaRVFiniteObject B (n+e)) (u : rvObjectDomain U.object) :
    gammaVolumeValue (gammaSwapVolumeBlocks U).toGammaRVObject u =
      gammaVolumeValue U.toGammaRVObject u ∘ (@finAddFlip e n) := rfl

def gammaPrependSelectedVolume (U : GammaRVObject B n)
    (ρ : Fin e → Fin (rvObjectArity U.object))
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin (rvObjectArity U.object) → RV (M := M) | (x,r) ∈ U.lift ∧ r ∘ ρ = t}.Finite) :
    GammaRVFiniteObject B (e+n) := gammaSwapVolumeBlocks (gammaFiniteSelectedVolume U ρ hfin)

theorem gammaPrependSelectedVolume_value (U : GammaRVObject B n)
    (ρ : Fin e → Fin (rvObjectArity U.object))
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin (rvObjectArity U.object) → RV (M := M) | (x,r) ∈ U.lift ∧ r ∘ ρ = t}.Finite)
    (u : rvObjectDomain U.object) :
    gammaVolumeValue (gammaPrependSelectedVolume U ρ hfin).toGammaRVObject u =
      Fin.append (u.val ∘ ρ) (@gammaVolumeValue M sM hM B n U u) := by
  change Fin.append (@gammaVolumeValue M sM hM B n U u) (u.val ∘ ρ) ∘ (@finAddFlip e n) = _
  exact append_finAddFlip _ _

end IntegrationInACVF.Section6
