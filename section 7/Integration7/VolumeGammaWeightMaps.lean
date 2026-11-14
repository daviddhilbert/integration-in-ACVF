import Integration7.VolumeGammaWeightTuples
import Section4.RVAppend

/-! The actual coordinate-and-density map on essential labels has finite
fibres, since its coordinate prefix is the original finite volume map. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def volumeGammaWeightMap (U : PositiveRVVolumeObject (M := M) S k) :
    Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) ((k+1)+1)) S) :=
  (rvAppendMap S (k+1) 1).comp ((U.essential.obj.volume.pair U.essentialForm.map).toUniv)

@[simp] theorem volumeGammaWeightMap_value (U : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) : (volumeGammaWeightMap U u).val = volumeGammaWeightTuple U u := by
  change Fin.append (U.essential.obj.value u) (U.essentialForm.map u).val =
    Fin.snoc (U.essential.obj.value u) (U.essentialForm.value u)
  rw [Fin.append_right_eq_snoc]
  rfl

theorem volumeGammaWeightMap_finite (U : PositiveRVVolumeObject (M := M) S k) :
    (volumeGammaWeightMap U).FiniteFibres := by
  intro w
  let t : DefSet.univ (rawRVSpace (M := M) (k+1)) S := ⟨w.val ∘ Fin.castAdd 1,Set.mem_univ _⟩
  apply (U.essential.property t).subset
  intro u hu
  apply Subtype.ext
  funext i
  change U.essential.obj.value u i = w.val i.castSucc
  have h := congrArg (fun z : DefSet.univ (rawRVSpace (M := M) ((k+1)+1)) S => z.val i.castSucc) hu
  rw [volumeGammaWeightMap_value] at h
  simpa only [volumeGammaWeightTuple,Fin.snoc_castSucc] using h

end IntegrationInACVF.Section7
