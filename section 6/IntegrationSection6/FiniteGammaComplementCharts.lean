import IntegrationSection6.FiniteGammaPresentationCharts
import IntegrationSection6.FiniteGammaRestrictions
import IntegrationSection6.ComplementCoordinates

/-! Original-Gamma charts for the unchanged complementary lift piece. -/
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
variable (U : GammaObjectAt B S n)

variable {A C E : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.object.obj)}

variable (h : @PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U.object.obj (normalizedPointSet A))

variable (hpart : carrier A = carrier C ∪ carrier E) (hCE : Disjoint (carrier C) (carrier E))

variable (hC : IsRVPullback (carrier C)) (hE : IsRVPullback (carrier E))

variable (hL : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
    p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ S (liftLabelLocus C)})
variable (hEΓ : GammaSetDefinable B (carrier E))

def gammaComplementPresentationAt : GammaObjectAt B S n :=
  gammaPullbackAt U.real_contains E hEΓ
    ((@finite_volume_iso M N hN S n (pullbackObject E)
      (gammaComplementAt U (liftLabelLocus C) hL).object.obj (liftComplementIso h hpart hCE hC hE)).mpr
        (gammaComplementAt U (liftLabelLocus C) hL).object.property)

def gammaComplementIsoAt : GammaIsoAt (gammaComplementPresentationAt U h hpart hCE hC hE hL hEΓ)
    (gammaComplementAt U (liftLabelLocus C) hL) := by
  let Q := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
    (@rawRVSpace M N (n+rvObjectArity U.object.obj)) B.real
  apply GammaIsoAt.ofAmbientFormula (liftComplementIso h hpart hCE hC hE)
    (@selectRVTuple M N B.real (n+rvObjectArity U.object.obj) (rvObjectArity U.object.obj) (Fin.natAdd n) Q)
  exact liftComplementIso_labels h hpart hCE hC hE

end IntegrationInACVF.Section6.FiniteRV
