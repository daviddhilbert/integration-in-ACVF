import IntegrationSection6.GammaElementaryStructure
import IntegrationSection6.ElementaryRightProduct

/-! Values of the actual old-volume/parameter program, including the
absorbing-zero case and an unchanged index-volume prefix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {k d : ℕ}

theorem oldVolumeParameterBlowupMap_append (S : Set M) (i : Fin k)
    (v : Fin k → CanonicalRV.RVSort M) (s : Fin 1 → CanonicalRV.RVSort M) :
    (oldVolumeParameterBlowupMap S i ⟨Fin.append v s,Set.mem_univ _⟩).val = blowupValue i v (s 0) := by
  change blowupValue i (fun j => Fin.append v s (Fin.castAdd 1 j)) (Fin.append v s (Fin.natAdd k 0)) = _
  simp only [Fin.append_left,Fin.append_right]

theorem oldVolumeParameterBlowupMap_prefix (S : Set M) (i : Fin k)
    (r : Fin d → CanonicalRV.RVSort M) (v : Fin k → CanonicalRV.RVSort M)
    (s : Fin 1 → CanonicalRV.RVSort M) :
    (oldVolumeParameterBlowupMap S (Fin.natAdd d i) ⟨Fin.append (Fin.append r v) s,Set.mem_univ _⟩).val =
      Fin.append r (oldVolumeParameterBlowupMap S i ⟨Fin.append v s,Set.mem_univ _⟩).val := by
  rw [oldVolumeParameterBlowupMap_append,oldVolumeParameterBlowupMap_append]
  exact blowupValue_append_right i v r (s 0)

end IntegrationInACVF.Section6
