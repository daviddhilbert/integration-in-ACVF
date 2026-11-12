import IntegrationSection5.GammaCoordinateFibres
import IntegrationSection5.HeadPreparation
import IntegrationSection5.RelativeLabelPreservation
import IntegrationSection6.GammaRealImages

/-! Coordinate identities for freezing the complementary VF tuple during
one head preparation. The named base contains exactly that tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m : ℕ}

def headFrozenTuple (x : Fin n → VF (M := M)) : Fin (n+1) → VF (M := M) := Fin.cons 0 x

theorem coordinateInsert_head (x : Fin n → VF (M := M)) (p : Point (M := M) 1 m) :
    coordinateInsert 0 (headFrozenTuple x) p = (Fin.cons (vfAt p 0) x,p.2) := by
  refine Prod.ext ?_ rfl
  funext j
  cases j using Fin.cases with
  | zero => simp [coordinateInsert,headFrozenTuple,vfAt]
  | succ j => simp [coordinateInsert,headFrozenTuple,vfAt]

theorem coordinateGammaBase_head (x : Fin n → VF (M := M)) :
    coordinateGammaBase B 0 (headFrozenTuple x) =
      ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ := by
  unfold coordinateGammaBase coordinateFibreBase
  congr 1
  apply congrArg (B.real ∪ ·)
  ext z
  constructor
  · rintro ⟨j,rfl⟩
    obtain ⟨j,hj⟩ := Fin.exists_succ_eq.mpr j.property
    exact ⟨j,by simp [headFrozenTuple,← hj]⟩
  · rintro ⟨j,rfl⟩
    exact ⟨⟨j.succ,Fin.succ_ne_zero j⟩,by simp [headFrozenTuple]⟩

theorem headFibre_canonical_carrier {A : DefSet (M := M) S (n+1) m}
    (T : HeadPreparation A) (x : Fin n → VF (M := M))
    (q : Point (M := M) 1 (1+T.arity)) :
    q ∈ carrier (canonicalImage (coordinateFibre T.target 0 (headFrozenTuple x))) ↔
      (x,q.2) ∈ carrier T.contractedSet ∧ q.2 (Fin.castAdd T.arity 0) = rv (vfAt q 0) := by
  rw [coordinateCanonical_fibre_carrier]
  change coordinateInsert 0 (headFrozenTuple x) q ∈ carrier T.liftSet ↔ _
  rw [T.liftSet_exact]
  have he : dropHead id (coordinateInsert 0 (headFrozenTuple x) q) = (x,q.2) := by
    rw [coordinateInsert_head]
    rfl
  rw [he]
  simp only [coordinateInsert,vfAt,Function.update_self]

end IntegrationInACVF.Section6
