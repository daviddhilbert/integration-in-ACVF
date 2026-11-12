import IntegrationSection6.ElementaryRightProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def elementaryRightProductIndex (a b : ℕ) : Fin (a+(b+1)) → Fin ((a+b)+1) :=
  Fin.addCases (fun j => Fin.castAdd 1 (Fin.castAdd b j))
    (Fin.addCases (fun j => Fin.castAdd 1 (Fin.natAdd a j)) (fun j => Fin.natAdd (a+b) j))

theorem elementaryRightProductMap_labels (R : RVObject (M := M) S l) (U : RVObject (M := M) S k)
    (i : Fin k) (x : (elementary (rvProductObject R U) (Fin.natAdd l i)).domain) :
    (elementaryRightProductMap R U i x).val = fun j => x.val (elementaryRightProductIndex R.arity U.arity j) := by
  obtain ⟨ru,s,rfl⟩ := exists_rvPackPair (rvProductObject R U).domain (positiveRV S) x
  obtain ⟨r,u,rfl⟩ := exists_rvPackPair R.domain U.domain ru
  rw [elementaryRightProductMap_pair]
  change Fin.append r.val (Fin.append u.val s.val) =
    fun j => Fin.append (Fin.append r.val u.val) s.val (elementaryRightProductIndex R.arity U.arity j)
  funext j
  cases j using Fin.addCases with
  | left j => simp only [elementaryRightProductIndex,Fin.addCases_left,Fin.append_left]
  | right j =>
    cases j using Fin.addCases <;>
      simp only [elementaryRightProductIndex,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]

end IntegrationInACVF.Section6
