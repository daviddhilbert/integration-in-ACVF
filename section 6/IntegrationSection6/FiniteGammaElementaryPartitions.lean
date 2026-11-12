import IntegrationSection6.FiniteGammaCoproductGluing
import IntegrationSection6.FiniteGammaElementaryAt
import IntegrationSection6.FiniteGammaRestrictions
import IntegrationSection6.ElementarySubobjectCoordinates

/-! Elementary blowups distribute over actual Gamma-definable partitions
in RV[k], without imposing a cardinal bound on internal real codes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaAdmissible_restrictAt (U : GammaObjectAt B S n) {i : Fin n}
    (h : GammaAdmissible U.toGamma.toGammaRVObject i)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A}) :
    GammaAdmissible (gammaRestrictAt U A hA hΓ).toGamma.toGammaRVObject i where
  nonzero a := h.nonzero ⟨a.val,hA a.property⟩
  algebraic a := h.algebraic ⟨a.val,hA a.property⟩

def gammaElementarySubobjectHomAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S n) (i : Fin n)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A}) :
    gammaElementaryAt hκ hs h00 hsmall  (gammaRestrictAt U A hA hΓ) i (gammaAdmissible_restrictAt U hAd A hA hΓ) ⟶
      gammaElementaryAt hκ hs h00 hsmall  U i hAd := by
  let R := gammaElementaryAt hκ hs h00 hsmall  (gammaRestrictAt U A hA hΓ) i (gammaAdmissible_restrictAt U hAd A hA hΓ)
  let W := gammaElementaryAt hκ hs h00 hsmall  U i hAd
  let F := @elementarySubobjectMap M N hN S n U.object.obj i A hA
  refine {
    hom := @homOfDefinableMap M N S n R.object W.object F ?_
    graph := ?_ }
  · intro a
    exact (congrArg (@rvWeight M N n) (@elementarySubobjectMap_volume M N hN S n U.object.obj i A hA a)).symm.le
  · let Q := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
      (@rawRVSpace M N (rvObjectArity U.object.obj+1)) B.real
    apply gamma_rv_graph_of_global_formula F (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real Q) R.domain_graph
    exact @elementarySubobjectMap_labels M N hN S n U.object.obj i A hA

def gammaElementaryPartitionIsoAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S n) (i : Fin n)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A}) :
    GammaIsoAt
      (gammaCoprodAt
        (gammaElementaryAt hκ hs h00 hsmall  (gammaRestrictAt U A hA hΓ) i (gammaAdmissible_restrictAt U hAd A hA hΓ))
        (gammaElementaryAt hκ hs h00 hsmall  (gammaComplementAt U A hΓ) i
          (gammaAdmissible_restrictAt U hAd (@complement M N S n U.object.obj A)
            (@complement_subset M N hN S n U.object.obj A) ((gammaLogicInput B).sdiff U.domain_graph hΓ))))
      (gammaElementaryAt hκ hs h00 hsmall  U i hAd) := by
  let C := @complement M N S n U.object.obj A
  have hc := @complement_subset M N hN S n U.object.obj A
  have hC := (gammaLogicInput B).sdiff U.domain_graph hΓ
  let f := gammaElementarySubobjectHomAt hκ hs h00 hsmall  U i hAd A hA hΓ
  let g := gammaElementarySubobjectHomAt hκ hs h00 hsmall  U i hAd C hc hC
  apply gammaCoprodIsoOfSum f g
  · constructor
    · apply Sum.elim_injective.mpr
      refine ⟨@elementarySubobjectMap_injective M N hN S n U.object.obj i A hA,
        @elementarySubobjectMap_injective M N hN S n U.object.obj i C hc,?_⟩
      intro u v he
      have hd := @elementarySubobjects_disjoint M N hN S n U.object.obj i A hA
      exact Set.disjoint_left.mp hd ⟨u,rfl⟩ ⟨v,(congrArg (fun x => x.val) he).symm⟩
    · intro w
      have hw := (Set.ext_iff.mp (@elementarySubobjects_cover M N hN S n U.object.obj i A hA) w.val).mpr w.property
      rcases hw with ⟨u,hu⟩ | ⟨v,hv⟩
      · exact ⟨Sum.inl u,Subtype.ext hu⟩
      · exact ⟨Sum.inr v,Subtype.ext hv⟩
  · intro u
    exact (congrArg (@rvWeight M N n) (@elementarySubobjectMap_volume M N hN S n U.object.obj i A hA u)).symm
  · intro v
    exact (congrArg (@rvWeight M N n) (@elementarySubobjectMap_volume M N hN S n U.object.obj i C hc v)).symm

end IntegrationInACVF.Section6.FiniteRV
