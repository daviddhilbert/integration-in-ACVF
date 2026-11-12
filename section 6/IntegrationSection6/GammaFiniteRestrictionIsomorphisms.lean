import IntegrationSection6.GammaCompressionIsomorphisms
import IntegrationSection6.FiniteGammaAmbientIsos
import Section4.RVPaddingSplit
import IntegrationSection6.GammaWeightStrata
import Section4.RVFinitePadding
import IntegrationSection6.FiniteGammaIsoLaws

/-! Original-Gamma RV[k] data at a fixed internal real presentation.
The parameter set S describes codes only; every domain and volume graph
is still certified over the original Base B. -/
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

def gammaRestrictIsoAt {U V : GammaObjectAt B S n} (e : GammaIsoAt U V)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (C : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity V.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hC : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S C) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain V.object.obj)))
    (hΓA : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) | p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A})
    (hΓC : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity V.object.obj) | p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S C})
    (hCompat : ∀ u : rvObjectDomain U.object.obj,
      u.val ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A ↔
        (isoAtMap e.iso u).val ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S C) :
    GammaIsoAt (gammaRestrictAt U A hA hΓA) (gammaRestrictAt V C hC hΓC) := by
  let E := isoAtAmbient e.iso
  let f := @RVHom.restrict M N S n U.object.obj V.object.obj E.hom A hA C hC
    (fun u => (hCompat ⟨u.val,hA u.property⟩).mp u.property)
  have hi (v : C) : (@RVHom.map M N S n V.object.obj U.object.obj E.inv ⟨v.val,hC v.property⟩).val ∈
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A := by
    apply (hCompat _).mpr
    have he := isoAtMap_hom_inv e.iso ⟨v.val,hC v.property⟩
    exact (congrArg (fun z : rvObjectDomain V.object.obj => z.val) he).symm ▸ v.property
  let g := @RVHom.restrict M N S n V.object.obj U.object.obj E.inv C hC A hA hi
  let ei : (@RVObject M N S n) := @RVObject.restrict M N S n U.object.obj A hA
  let ej : (@RVObject M N S n) := @RVObject.restrict M N S n V.object.obj C hC
  let er : ei ≅ ej := {
    hom := f
    inv := g
    hom_inv_id := by
      apply @RVHom.ext M N S n ei ei
      apply @SpecialTransformations.DefinableGeometry.Map.ext LRV M N _ _ S _ _
      intro u
      apply Subtype.ext
      exact congrArg (fun z : rvObjectDomain U.object.obj => z.val) (isoAtMap_inv_hom e.iso ⟨u.val,hA u.property⟩)
    inv_hom_id := by
      apply @RVHom.ext M N S n ej ej
      apply @SpecialTransformations.DefinableGeometry.Map.ext LRV M N _ _ S _ _
      intro v
      apply Subtype.ext
      exact congrArg (fun z : rvObjectDomain V.object.obj => z.val) (isoAtMap_hom_inv e.iso ⟨v.val,hC v.property⟩) }
  exact GammaIsoAt.ofAmbient er (gamma_rv_graph_restrict_source (isoAtMap e.iso)
    (@RVHom.map M N S n ei ej er.hom) hA hΓA e.graph (fun _ => rfl))

end IntegrationInACVF.Section6.FiniteRV
