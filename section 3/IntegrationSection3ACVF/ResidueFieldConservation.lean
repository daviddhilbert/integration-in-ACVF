import IntegrationSection3.CofiniteDefinableBijection
import Section4.ResidueNormalization
import Section4.MapParameters
import VFAlgClosed

/-! Transfer of actual RV graph definability to the native residue field,
and finite-complement conservation there. The canonical-structure premise
is explicit in this bridge; native ball-quotient assembly is not asserted. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.ResidueFieldConservation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem residue_pullback_definable (hcan : CanonicalStructure.IsCanonical (M := M))
    {n : ℕ} {S : Set M} (A : DefSet (rawRVSpace (M := M) n) S) :
    (Set.univ : Set (ModelResidue M)).Definable Language.ring
      {x : Fin n → ModelResidue M | (fun i => residueRV (x i)) ∈ A.carrier} := by
  let B : LRV.Substructure M := ⊤
  let E : Subfield (ModelResidue M) := ⊤
  have hBase : S ⊆ residueExtendedBase B E := by
    intro x _
    exact Or.inl (Set.mem_univ x)
  let A' := A.extend hBase
  let s : Fin n → CanonicalRV.RVSort M := fun _ => 1
  have hs (i : Fin n) : s i ∈ extendedCoefficients B E :=
    extendedCoefficients_base B E (Set.mem_univ _)
  have hd := normalizedResidueSet_definable hcan B E le_top A' s hs
  have hSet : normalizedResidueSet A' s =
      {x : Fin n → ModelResidue M | (fun i => residueRV (x i)) ∈ A.carrier} := by
    ext x
    change ((fun i => (1 : CanonicalRV.RVSort M) * residueRV (x i)) ∈ A.carrier ∧
      ∀ i, (1 : CanonicalRV.RVSort M) = 0 → x i = 0) ↔ _
    simp only [one_mul,one_ne_zero,false_implies,implies_true,and_true,Set.mem_ofPred_eq]
  rw [hSet] at hd
  exact hd.mono (Set.subset_univ _)

theorem graph_definable (hcan : CanonicalStructure.IsCanonical (M := M))
    {n : ℕ} {S : Set M} (A : DefSet (rawRVSpace (M := M) (n+n)) S)
    (X : Set (Fin n → ModelResidue M)) (f : (Fin n → ModelResidue M) → (Fin n → ModelResidue M))
    (hGraph : ∀ x y : Fin n → ModelResidue M,
      Fin.addCases (fun i => residueRV (x i)) (fun i => residueRV (y i)) ∈ A.carrier ↔
        x ∈ X ∧ y = f x) :
    (Set.univ : Set (ModelResidue M)).Definable Language.ring
      {z : Fin n ⊕ Fin n → ModelResidue M | z ∘ Sum.inl ∈ X ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)} := by
  have hd := (residue_pullback_definable hcan A).preimage_comp
    (finSumFinEquiv.symm : Fin (n+n) → Fin n ⊕ Fin n)
  convert hd using 1
  ext z
  change (z ∘ Sum.inl ∈ X ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)) ↔
    (fun i => residueRV (z (finSumFinEquiv.symm i))) ∈ A.carrier
  have he : (fun i => residueRV (z (finSumFinEquiv.symm i))) =
      Fin.addCases (fun i => residueRV (z (.inl i))) (fun i => residueRV (z (.inr i))) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [finSumFinEquiv_symm_apply_castAdd,Fin.addCases_left]
    · rw [finSumFinEquiv_symm_apply_natAdd,Fin.addCases_right]
  rw [he]
  exact (hGraph (z ∘ Sum.inl) (z ∘ Sum.inr)).symm

theorem cofinite_bijection_card (hcan : CanonicalStructure.IsCanonical (M := M))
    {n : ℕ} {S : Set M} (A : DefSet (rawRVSpace (M := M) (n+n)) S)
    (X : Set (Fin n → ModelResidue M)) (F G : Finset (Fin n → ModelResidue M))
    (hF : (F : Set (Fin n → ModelResidue M)) ⊆ X)
    (hG : (G : Set (Fin n → ModelResidue M)) ⊆ X)
    (f : (Fin n → ModelResidue M) → (Fin n → ModelResidue M))
    (hGraph : ∀ x y : Fin n → ModelResidue M,
      Fin.addCases (fun i => residueRV (x i)) (fun i => residueRV (y i)) ∈ A.carrier ↔
        x ∈ X \ F ∧ y = f x)
    (hbij : Set.BijOn f (X \ F) (X \ G)) : F.card = G.card := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  exact CofiniteDefinableBijection.complements_card_eq Set.univ X F G hF hG f
    (graph_definable hcan A (X \ F) f hGraph) hbij

end IntegrationInACVF.Section3ACVF.ResidueFieldConservation
