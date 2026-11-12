import IntegrationSection6.GammaFiniteCompression
import IntegrationSection6.GammaGlobalRestriction
import Section4.LiftPadding

/-! A real-definable RV-label map extends to mixed points by identity
on all VF coordinates, with its complete graph and the same real base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

def typedVFSuccessorPaddingMap (S : Set M) (n a : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n a) S)
      (PresentedSet.univ (pointSpace (n+1) a) S) := by
  let A := PresentedSet.univ (pointSpace (M := M) n a) S
  let F := @vfPadding M N (@CanonicalStructure.normalized_model M sM hM) n (n+1)
    (Nat.le_succ n) (@SpecialTransformations.Section4.rawRVSpace M N a) S
  exact Map.comp (fromRawPointMap (PresentedSet.univ (rawPointSpace (n+1) a) S))
    (Map.comp F (rawPointMap A))

namespace FiniteRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
variable {B : Base (M := M)} {n : ℕ}

def gammaLiftPaddingIsoAt (U : GammaObjectAt B S n) :
    GammaIso B U.toGamma.lift (gammaPadAt U).toGamma.lift := by
  let F := @rvLiftPaddingMap M N (@CanonicalStructure.normalized_model M sM hM) S n U.object.obj
  refine ⟨Equiv.ofBijective F (@rvLiftPaddingMap_bijective M N (@CanonicalStructure.normalized_model M sM hM) S n U.object.obj),?_⟩
  apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph U.toGamma.toGammaRVObject.lift_definable
    ((gammaLogicInput B).real_map_graph (typedVFSuccessorPaddingMap B.real n (rvObjectArity U.object.obj))))
  intro p q
  constructor
  · rintro ⟨hp,x,hx,hq⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    change (padVF (Nat.le_succ n) p.1,p.2) = q
    exact (congrArg (fun z : Point (M := M) n (rvObjectArity U.object.obj) =>
      (padVF (Nat.le_succ n) z.1,z.2)) hx).symm.trans hq
  · rintro ⟨x,hx,hq⟩
    exact ⟨hx ▸ x.property,⟨x.val,Set.mem_univ _⟩,hx,hq⟩

end FiniteRV
end IntegrationInACVF.Section6
