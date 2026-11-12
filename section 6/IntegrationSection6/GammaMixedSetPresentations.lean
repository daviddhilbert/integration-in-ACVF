import IntegrationSection6.FiniteGammaLiftGluing
import Section5.GammaInvariantLogic
import Section7.GammaScissors

/-! Mixed original-Gamma sets have real presentations over an internal
code universe; only the finitely many representatives in their formulas
are named, and no smallness bound is placed on the code universe. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_mixed_set_real_specialize (A : Set (Point (M := M) n a))
    (hA : GammaSetDefinable B A) :
    ∃ d, ∃ t : Fin d → Code (M := M), SetDefinable (pointSpace n a)
      (B.real ∪ Set.range (rawTuple t)) A := by
  let e := gammaIso_reflexive A hA
  obtain ⟨d,t,hg⟩ := e.graph.real_specialize
  have h := @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.exists_right LRV M N
    (pointSpace (M := M) n a) (pointSpace (M := M) n a) _ _ hg
  refine ⟨d,t,?_⟩
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨(e.equiv ⟨p,hp⟩).val,⟨p,hp⟩,rfl,rfl⟩
  · rintro ⟨_,x,hx,_⟩
    exact hx ▸ x.property

def gammaMixedUniversalDefSet (A : Set (Point (M := M) n a)) (hA : GammaSetDefinable B A) :
    DefSet (M := M) (Set.univ : Set M) n a := by
  let h := Classical.choose_spec (gamma_mixed_set_real_specialize A hA)
  let t := Classical.choose h
  let ht := Classical.choose_spec h
  exact PresentedSet.mk A (SetDefinable.mono (pointSpace n a) ht (Set.subset_univ _))

theorem gammaMixedUniversalDefSet_carrier (A : Set (Point (M := M) n a)) (hA : GammaSetDefinable B A) :
    carrier (gammaMixedUniversalDefSet A hA) = A := rfl

end IntegrationInACVF.Section6
