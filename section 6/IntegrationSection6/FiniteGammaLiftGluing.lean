import IntegrationSection6.FiniteGammaCoproductLifts

/-! Definable gluing of lift isomorphisms in the finite RV categories.
Both tagged components retain their complete original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {n m : ℕ}

def gammaIso_reflexive (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A) : GammaIso B A A := by
  let G := Map.id (PresentedSet.univ (pointSpace (M := M) n m) B.real)
  let e := gammaIso_realImage A hA G Function.injective_id
  apply e.congr rfl
  ext p
  constructor
  · rintro ⟨a,ha⟩
    exact ha ▸ a.property
  · intro hp
    exact ⟨⟨p,hp⟩,rfl⟩

namespace FiniteRV
variable {S : Set M} {n : ℕ}

def gammaCoprodLiftIso {U V U' V' : GammaObjectAt B S n}
    (e : GammaIso B U.toGamma.lift U'.toGamma.lift)
    (f : GammaIso B V.toGamma.lift V'.toGamma.lift) :
    GammaIso B (gammaCoprodAt U V).toGamma.lift (gammaCoprodAt U' V').toGamma.lift := by
  let L := gammaLogicInput B
  let eU := gammaIso_leftTag U.toGamma.lift U.toGamma.toGammaRVObject.lift_definable (rvObjectArity V.object.obj)
  let eU' := gammaIso_leftTag U'.toGamma.lift U'.toGamma.toGammaRVObject.lift_definable (rvObjectArity V'.object.obj)
  let eV := gammaIso_rightTag V.toGamma.lift V.toGamma.toGammaRVObject.lift_definable (rvObjectArity U.object.obj)
  let eV' := gammaIso_rightTag V'.toGamma.lift V'.toGamma.toGammaRVObject.lift_definable (rvObjectArity U'.object.obj)
  let left := ((eU.symm L).trans L e).trans L eU'
  let right := ((eV.symm L).trans L f).trans L eV'
  let F := gammaIso_disjointUnion left right (tagged_sets_disjoint _ _) (tagged_sets_disjoint _ _)
  exact F.congr (gammaCoprodAt_lift U V).symm (gammaCoprodAt_lift U' V').symm

end FiniteRV
end IntegrationInACVF.Section6
