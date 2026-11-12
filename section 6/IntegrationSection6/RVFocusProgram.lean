import IntegrationSection6.RVCoordinateRatio

/-! The global RV-coordinate program for the length-one blowup diagram.
It uses no named RV parameters or representatives of Gamma parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n m : ℕ}

def focusRelabelProgram (S : Set M) (i : Fin n) :
    Map (DefSet.univ (rawRVSpace (M := M) (n+(n+m))) S)
      (DefSet.univ (rawRVSpace (m+1)) S) :=
  Map.comp (rvPack (DefSet.univ (rawRVSpace m) S) (DefSet.univ (rawRVSpace 1) S))
    (Map.pair
      (selectRVTuple (fun j => Fin.natAdd n (Fin.natAdd n j))
        (DefSet.univ (rawRVSpace (n+(n+m))) S))
      (rvCoordinateRatioMap S (Fin.castAdd (n+m) i) (Fin.natAdd n (Fin.castAdd m i))))

@[simp] theorem focusRelabelProgram_value (S : Set M) (i : Fin n)
    (a : DefSet.univ (rawRVSpace (M := M) (n+(n+m))) S) :
    (focusRelabelProgram (m := m) S i a).val =
      rvAppend (fun j => a.val (Fin.natAdd n (Fin.natAdd n j)))
        (fun _ : Fin 1 => a.val (Fin.castAdd (n+m) i) / a.val (Fin.natAdd n (Fin.castAdd m i))) := rfl

end IntegrationInACVF.Section6
