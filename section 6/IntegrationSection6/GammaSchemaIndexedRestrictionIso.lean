import IntegrationSection6.GammaSchemaIndexedPresentations
import IntegrationSection6.FiniteGammaUniversalCharts
import IntegrationSection6.FiniteGammaRestrictions
import IntegrationSection6.FiniteGammaFormulaIsos

/-! Restricting the index base agrees with restricting the actual indexed
object. The label identity preserves the full volume tuple whenever the
new base volume agrees on its actual domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Milestone0.sortEval
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T E : Set (Fin p → RV (M := M))}
variable {R S : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
open FiniteRV

def GammaFiniteRVSchema.indexedRestrictionIso
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (BQ : GammaFiniteGraphPresentation B p d E S)
    (hBase : ∀ t ∈ E, BQ.totalVolume t = BP.totalVolume t)
    (P : F.IndexedPresentation BP) (Q : F.IndexedPresentation BQ)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (p+a)) (Set.univ : Set M))
    (hSub : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A ⊆
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ
        (rvObjectDomain (gammaUniversalObject P.toGamma).object.obj))
    (hA : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A =
      indexedDomain E (fun t => F.rowDomain (fun j => (t j).val)))
    (hΓ : GammaSetDefinable B {w : Point (M := M) 0 (p+a) |
      w.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A}) :
    GammaIsoAt (gammaRestrictAt (gammaUniversalObject P.toGamma) A hSub hΓ) (gammaUniversalObject Q.toGamma) := by
  let U := gammaRestrictAt (gammaUniversalObject P.toGamma) A hSub hΓ
  let V := gammaUniversalObject Q.toGamma
  have hD : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj) =
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain V.object.obj) :=
    hA.trans Q.domain_eq.symm
  let e := @rvIsoOfCarrierEq M N Set.univ (d+k) (p+a)
    (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj)
    (rvObjectVolume U.object.obj) (rvObjectVolume V.object.obj) hD (by
      intro u
      let q : Q.domain := ⟨u.val,hD.le u.property⟩
      let v : P.domain := ⟨u.val,hSub u.property⟩
      change (Q.volume q).val = (P.volume v).val
      have hQ := ((Q.graph_iff q.val (Q.volume q).val).mp ⟨q,rfl,rfl⟩).2.2.symm
      have hP := ((P.graph_iff v.val (P.volume v).val).mp ⟨v,rfl,rfl⟩).2.2.symm
      rw [hQ,hP]
      have hu := (Set.ext_iff.mp hA u.val).mp u.property
      change Fin.append (BQ.totalVolume (indexedLeft u.val)) _ = Fin.append (BP.totalVolume (indexedLeft u.val)) _
      rw [hBase _ hu.1])
  let Z := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N (p+a)) B.real
  exact GammaIsoAt.ofAmbientFormula e (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real Z) (fun _ => rfl)

end IntegrationInACVF.Section6
