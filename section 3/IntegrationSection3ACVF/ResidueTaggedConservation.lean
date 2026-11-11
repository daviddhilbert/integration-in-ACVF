import IntegrationSection3ACVF.ResidueFieldConservation
import IntegrationSection3.TaggedCofiniteConservation

/-! Conservation for actual residue-field affine lines whose full graph
is given as an actual RV-definable set. Native ball-quotient interpretation
is a separate step. The canonical-totalization hypothesis stays visible. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.TaggedLineMaps

namespace IntegrationInACVF.Section3ACVF.ResidueTaggedConservation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem components_and_holes (hcan : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (A : DefSet (rawRVSpace (M := M) 4) S)
    (P Q : Finset (ModelResidue M)) (F G : Finset (Fin 2 → ModelResidue M))
    (hF : (F : Set (Fin 2 → ModelResidue M)) ⊆ space P)
    (hG : (G : Set (Fin 2 → ModelResidue M)) ⊆ space Q)
    (f : (Fin 2 → ModelResidue M) → (Fin 2 → ModelResidue M))
    (hGraph : ∀ x y : Fin 2 → ModelResidue M,
      (Fin.addCases (fun i => residueRV (x i)) (fun i => residueRV (y i)) :
        Fin (2+2) → CanonicalRV.RVSort M) ∈ A.carrier ↔
        x ∈ space P \ F ∧ y = f x)
    (hbij : Set.BijOn f (space P \ F) (space Q \ G)) : P.card = Q.card ∧ F.card = G.card := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  exact TaggedCofiniteConservation.components_and_holes Set.univ P Q F G hF hG f
    (ResidueFieldConservation.graph_definable hcan A (space P \ F) f hGraph) hbij

end IntegrationInACVF.Section3ACVF.ResidueTaggedConservation
