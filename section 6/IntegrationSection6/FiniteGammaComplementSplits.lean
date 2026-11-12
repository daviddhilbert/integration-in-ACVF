import IntegrationSection6.FiniteGammaPartitionCharts
import IntegrationSection6.FiniteGammaFormulaIsos
import IntegrationSection6.FiniteGammaCoproductMaps

/-! The difference and exterior charts for two Gamma-definable RV loci. -/
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

def gammaSplitComplementAt (U : GammaObjectAt B S n)
    (A C : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hC : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S C) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A})
    (hCΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S C}) :
    GammaIsoAt (gammaComplementAt U A hAΓ)
      (gammaCoprodAt
        (gammaRestrictAt U (@SpecialTransformations.DefinableGeometry.DefSet.sdiff LRV M N _ S C A)
          (fun _ h => hC h.1) ((gammaLogicInput B).sdiff hCΓ hAΓ))
        (gammaComplementAt U (@SpecialTransformations.DefinableGeometry.DefSet.union LRV M N _ S A C)
          ((gammaLogicInput B).union hAΓ hCΓ))) := by
  let D := @SpecialTransformations.DefinableGeometry.DefSet.sdiff LRV M N _ S C A
  let J := @SpecialTransformations.DefinableGeometry.DefSet.union LRV M N _ S A C
  have hDΓ := (gammaLogicInput B).sdiff hCΓ hAΓ
  let R := gammaComplementAt U A hAΓ
  have hd : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S D) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain R.object.obj)) :=
    fun _ h => ⟨hC h.1,h.2⟩
  let Q := gammaRestrictAt U D (fun _ h => hC h.1) hDΓ
  let E := gammaComplementAt U J ((gammaLogicInput B).union hAΓ hCΓ)
  let X := gammaRestrictAt R D hd hDΓ
  let Y := gammaComplementAt R D hDΓ
  have he : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain Y.object.obj)) =
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain E.object.obj)) := by
    ext x
    constructor
    · rintro ⟨⟨hu,hna⟩,hn⟩
      refine ⟨hu,?_⟩
      rintro (ha | hc)
      · exact hna ha
      · exact hn ⟨hc,hna⟩
    · rintro ⟨hu,hn⟩
      exact ⟨⟨hu,fun ha => hn (Or.inl ha)⟩,fun h => hn (Or.inr h.1)⟩
  let eX := @rvIsoOfCarrierEq M N S n (rvObjectArity U.object.obj)
    (rvObjectDomain X.object.obj) (rvObjectDomain Q.object.obj) (rvObjectVolume X.object.obj) (rvObjectVolume Q.object.obj) rfl (fun _ => rfl)
  let eY := @rvIsoOfCarrierEq M N S n (rvObjectArity U.object.obj)
    (rvObjectDomain Y.object.obj) (rvObjectDomain E.object.obj) (rvObjectVolume Y.object.obj) (rvObjectVolume E.object.obj) he (fun _ => rfl)
  let Z := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) B.real
  let G := @SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real Z
  let fX : GammaIsoAt X Q := GammaIsoAt.ofAmbientFormula eX G (fun _ => rfl)
  let fY : GammaIsoAt Y E := GammaIsoAt.ofAmbientFormula eY G (fun _ => rfl)
  exact (gammaPartitionIsoAt R D hd hDΓ).symm.trans (gammaCoprodIsoAt fX fY)

end IntegrationInACVF.Section6.FiniteRV
