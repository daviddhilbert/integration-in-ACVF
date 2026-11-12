import IntegrationSection6.FiniteGammaRestrictions
import IntegrationSection6.FiniteGammaAmbientIsos
import IntegrationSection6.GammaRVRestrictions

/-! Images of Gamma-definable finite RV subobjects and their actual charts. -/
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
variable {U V : GammaObjectAt B S n}

theorem gamma_subobjectImage (e : GammaIsoAt U V)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A}) :
    GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity V.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S
        (@subobjectImage M N S n U.object.obj V.object.obj (isoAtAmbient e.iso) A hA)} := by
  let F := @SpecialTransformations.DefinableGeometry.Map.restrict LRV M N _ _ S _ _ A (isoAtMap e.iso) hA
  exact gamma_rv_map_image F (gamma_rv_graph_restrict_source (isoAtMap e.iso) F hA hΓ e.graph (fun _ => rfl))

def gammaSubobjectImageAt (e : GammaIsoAt U V)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A}) : GammaObjectAt B S n :=
  gammaRestrictAt V (@subobjectImage M N S n U.object.obj V.object.obj (isoAtAmbient e.iso) A hA)
    (@subobjectImage_subset M N hN S n U.object.obj V.object.obj (isoAtAmbient e.iso) A hA)
    (gamma_subobjectImage e A hA hΓ)

def gammaSubobjectImageIsoAt (e : GammaIsoAt U V)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A}) :
    GammaIsoAt (gammaRestrictAt U A hA hΓ) (gammaSubobjectImageAt e A hA hΓ) := by
  let E := @subobjectImageIso M N hN S n U.object.obj V.object.obj (isoAtAmbient e.iso) A hA
  apply GammaIsoAt.ofAmbient E
  exact gamma_rv_graph_restrict_source (isoAtMap e.iso)
    (@RVHom.map M N S n (gammaRestrictAt U A hA hΓ).object.obj (gammaSubobjectImageAt e A hA hΓ).object.obj E.hom) hA hΓ e.graph (fun _ => rfl)

def gammaComplementImageIsoAt (e : GammaIsoAt U V)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A}) :
    GammaIsoAt (gammaComplementAt U A hΓ)
      (gammaComplementAt V (@subobjectImage M N S n U.object.obj V.object.obj (isoAtAmbient e.iso) A hA)
        (gamma_subobjectImage e A hA hΓ)) := by
  let E := @complementImageIso M N hN S n U.object.obj V.object.obj (isoAtAmbient e.iso) A hA
  apply GammaIsoAt.ofAmbient E
  exact gamma_rv_graph_restrict_source (isoAtMap e.iso)
    (@RVHom.map M N S n (gammaComplementAt U A hΓ).object.obj
      (gammaComplementAt V (@subobjectImage M N S n U.object.obj V.object.obj (isoAtAmbient e.iso) A hA)
        (gamma_subobjectImage e A hA hΓ)).object.obj E.hom) (@complement_subset M N hN S n U.object.obj A)
    ((gammaLogicInput B).sdiff U.domain_graph hΓ) e.graph (fun _ => rfl)

end IntegrationInACVF.Section6.FiniteRV
