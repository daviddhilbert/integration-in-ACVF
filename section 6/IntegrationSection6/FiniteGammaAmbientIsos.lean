import IntegrationSection6.FiniteGammaWeightedIsos

/-! An actual ambient isomorphism between finite objects, together with
its original-Gamma graph, gives an isomorphism in RV[k] with that graph. -/
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

def GammaIsoAt.ofAmbient {U V : GammaObjectAt B S n}
    (e : @CategoryTheory.Iso (@RVObject M N S n) (@SpecialTransformations.Section4.instCategoryRVObject M N S n) U.object.obj V.object.obj)
    (hΓ : GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj))
        (q : Point (M := M) 0 (rvObjectArity V.object.obj)) =>
        ∃ u : rvObjectDomain U.object.obj, u.val = p.2 ∧
          (@RVHom.map M N S n U.object.obj V.object.obj e.hom u).val = q.2)) : GammaIsoAt U V where
  iso := @rvFiniteIsoOfAmbient M N S n U.object V.object e
  graph := hΓ

end IntegrationInACVF.Section6.FiniteRV
