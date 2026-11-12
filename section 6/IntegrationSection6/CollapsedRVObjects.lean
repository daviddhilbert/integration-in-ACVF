import IntegrationSection6.CanonicalNormalization
import Section4.CanonicalLift

/-! An RV presentation over a twice-normalized model has the same actual
labels, volume function and parameters over the once-normalized model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] {S : Set M} {k : ℕ}

def collapseRVObject
    (U : @RVObject M (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM)) S k) :
    @RVObject M (@CanonicalStructure.normalize M sM) S k := by
  letI := @CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM)
  let r : ℕ := U.arity
  let C : Set (Fin r → CanonicalRV.RVSort M) := U.domain.carrier
  let T : Set (Fin r → M) :=
    @Space.preimage LRV M (@CanonicalStructure.normalize M sM)
      (@rawRVSpace M (@CanonicalStructure.normalize M sM) r) C
  have hd : @Set.Definable M S LRV
      (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM)) (Fin r) T :=
    U.domain.definable
  have hd' : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin r) T :=
    Eq.mp (congrArg (fun s : LRV.Structure M => @Set.Definable M S LRV s (Fin r) T)
      (@normalized_structure_idempotent M sM)) hd
  let D : @DefSet LRV M (@CanonicalStructure.normalize M sM)
      (@rawRVSpace M (@CanonicalStructure.normalize M sM) r) S :=
    @DefSet.mk LRV M (@CanonicalStructure.normalize M sM) _ S C hd'
  let G : Set ((Fin r ⊕ Fin k) → M) :=
    @Space.relation LRV M
      (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM))
      (@rawRVSpace M (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM)) r)
      (@rawRVSpace M (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM)) k)
      (fun x y => ∃ u : U.domain, u.val = x ∧ (U.volume u).val = y)
  have hg : @Set.Definable M S LRV
      (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM))
      (Fin r ⊕ Fin k) G := U.volume.graph_definable
  have hg' : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM)
      (Fin r ⊕ Fin k) G :=
    Eq.mp (congrArg (fun s : LRV.Structure M => @Set.Definable M S LRV s (Fin r ⊕ Fin k) G)
      (@normalized_structure_idempotent M sM)) hg
  refine @RVObject.mk M (@CanonicalStructure.normalize M sM) S k r D ?_
  refine @Map.mk LRV M (@CanonicalStructure.normalize M sM) _ _ S _ _
    (fun a => ⟨(U.volume ⟨a.val,a.property⟩).val,Set.mem_univ _⟩) ?_
  exact hg'

@[simp] theorem collapseRVObject_arity
    (U : @RVObject M (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM)) S k) :
    @RVObject.arity M (@CanonicalStructure.normalize M sM) S k (collapseRVObject U) =
      @RVObject.arity M (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM)) S k U := rfl

end IntegrationInACVF.Section6
