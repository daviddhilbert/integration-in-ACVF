import IntegrationSection6.FiniteGammaFormulaIsos
import IntegrationSection6.PresentationCoordinates
import IntegrationSection6.LiftComplement

/-! Literal lift presentations and unchanged complements have Gamma
comparison charts, with finite volume inherited from the input object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaPresentationAt (U : GammaObjectAt B S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN S n U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A)) : GammaObjectAt B S n :=
  gammaPullbackAt U.real_contains A hA
    ((@finite_volume_iso M N hN S n (pullbackObject A) U.object.obj (pullbackPresentationIso h)).mpr U.object.property)

def gammaPresentationIsoAt (U : GammaObjectAt B S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN S n U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A)) : GammaIsoAt (gammaPresentationAt U h hA) U := by
  let Q := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
    (@rawRVSpace M N (n+rvObjectArity U.object.obj)) B.real
  apply GammaIsoAt.ofAmbientFormula (pullbackPresentationIso h)
    (@selectRVTuple M N B.real (n+rvObjectArity U.object.obj) (rvObjectArity U.object.obj) (Fin.natAdd n) Q)
  exact pullbackPresentationIso_labels h

end IntegrationInACVF.Section6.FiniteRV
