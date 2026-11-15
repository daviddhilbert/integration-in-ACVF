import Integration7.CanonicalFiniteRVObjects
import Integration7.GammaVolumeObjectGraphs

/-! Actual raw RV objects admit normalized presentations with exactly
the same label tuples and coordinate values. This is the inverse bridge
to the existing canonical presentation, preserving finite fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {a b n : ℕ}

def normalizedActualRVDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) a) S) :
    @DefSet LRV M (@CanonicalStructure.normalize M sM) (@rawRVSpace M (@CanonicalStructure.normalize M sM) a) S := by
  let T := @Space.preimage LRV M sM (@rawRVSpace M sM a) A.carrier
  have h : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin a) T :=
    Eq.mp (congrArg (fun I : LRV.Structure M => @Set.Definable M S LRV I (Fin a) T)
      (normalize_eq_of_isCanonical hc).symm) A.definable
  exact @DefSet.mk LRV M (@CanonicalStructure.normalize M sM)
    (@rawRVSpace M (@CanonicalStructure.normalize M sM) a) S A.carrier h

def normalizedActualRVMap (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (f : Map A B) :
    @Map LRV M (@CanonicalStructure.normalize M sM) _ _ S
      (normalizedActualRVDomain hc A) (normalizedActualRVDomain hc B) := by
  let T := @Space.relation LRV M sM (@rawRVSpace M sM a) (@rawRVSpace M sM b)
    (fun x y => ∃ u : A, u.val = x ∧ (f u).val = y)
  have h : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin a ⊕ Fin b) T :=
    Eq.mp (congrArg (fun I : LRV.Structure M => @Set.Definable M S LRV I (Fin a ⊕ Fin b) T)
      (normalize_eq_of_isCanonical hc).symm) f.graph_definable
  exact @Map.mk LRV M (@CanonicalStructure.normalize M sM) _ _ S _ _
    (fun x => ⟨(f ⟨x.val,x.property⟩).val,(f ⟨x.val,x.property⟩).property⟩) h

def normalizedActualRVObject (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVObject (M := M) S n) : @RVObject M (@CanonicalStructure.normalize M sM) S n :=
  @RVObject.mk M (@CanonicalStructure.normalize M sM) S n
    (@RVObject.arity M sM S n U)
    (normalizedActualRVDomain hc (@RVObject.domain M sM S n U))
    (@Map.toUniv LRV M (@CanonicalStructure.normalize M sM) _ _ S _ _
      (normalizedActualRVMap hc (@RVObject.volume M sM S n U)))

def normalizedActualFiniteRVObject (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVFiniteObject (M := M) S n) : @RVFiniteObject M (@CanonicalStructure.normalize M sM) S n :=
  ⟨normalizedActualRVObject hc U.obj,fun t => U.property ⟨t.val,Set.mem_univ _⟩⟩

end IntegrationInACVF.Section7
