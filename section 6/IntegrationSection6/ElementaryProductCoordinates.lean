import IntegrationSection6.ProductGeometry

/-! Literal rearrangement of (U,R,s) into (U,s,R). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def elementaryProductIndex (a b : ℕ) : Fin ((a+1)+b) → Fin ((a+b)+1) :=
  Fin.addCases
    (Fin.addCases (fun j => Fin.castAdd 1 (Fin.castAdd b j)) (fun j => Fin.natAdd (a+b) j))
    (fun j => Fin.castAdd 1 (Fin.natAdd a j))

theorem elementaryProductMap_labels (U : RVObject (M := M) S k) (R : RVObject (M := M) S l)
    (i : Fin k) (x : (elementary (rvProductObject U R) (Fin.castAdd l i)).domain) :
    (elementaryProductMap U R i x).val = fun j => x.val (elementaryProductIndex U.arity R.arity j) := by
  obtain ⟨ur,s,rfl⟩ := exists_rvPackPair (rvProductObject U R).domain (positiveRV S) x
  obtain ⟨u,r,rfl⟩ := exists_rvPackPair U.domain R.domain ur
  rw [elementaryProductMap_pair]
  funext j
  change Fin.append (Fin.append u.val s.val) r.val j =
    Fin.append (Fin.append u.val r.val) s.val (elementaryProductIndex U.arity R.arity j)
  cases j using Fin.addCases with
  | left j =>
    cases j using Fin.addCases <;>
      simp only [elementaryProductIndex,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]
  | right j =>
    change Fin.append (Fin.append u.val s.val) r.val (Fin.natAdd (U.arity+1) j) =
      Fin.append (Fin.append u.val r.val) s.val
        (elementaryProductIndex U.arity R.arity (Fin.natAdd (U.arity+1) j))
    simp only [elementaryProductIndex,Fin.addCases_right,Fin.append_left,Fin.append_right]

end IntegrationInACVF.Section6
