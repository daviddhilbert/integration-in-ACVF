import IntegrationSection6.DefinableFamilyOperations
import IntegrationSection6.GammaMixedProductIsomorphisms
import IntegrationSection6.GammaVFCoordinateIsomorphisms

/-! Multiplication by a constant RV representative corresponds to the
literal Cartesian product of its lift and the total family lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def familyProductAssociator (p k l : ℕ) : Fin (p+(k+l)) ≃ Fin ((p+k)+l) := finCongr (Nat.add_assoc p k l).symm

theorem familyLiftDomain_constant_product (A : Set (Point (M := M) p 0))
    (F : GammaFiniteRVSchema B p a k) (U : GammaObjectAt B Set.univ l) :
    familyLiftDomain A (F.productFormula (constantRVSchema U p)) =
      {q | (q.1 ∘ (familyProductAssociator p k l).symm,q.2) ∈ mixedProductSet (familyLiftDomain A F) U.toGamma.lift} := by
  ext q
  let w : Fin ((p+k)+l) → VF (M := M) := q.1 ∘ (familyProductAssociator p k l).symm
  have hb : (w ∘ Fin.castAdd l) ∘ Fin.castAdd k = q.1 ∘ Fin.castAdd (k+l) := by
    funext j
    exact congrArg q.1 (Fin.ext rfl)
  have hf : (w ∘ Fin.castAdd l) ∘ Fin.natAdd p = (q.1 ∘ Fin.natAdd p) ∘ Fin.castAdd l := by
    funext j
    exact congrArg q.1 (Fin.ext rfl)
  have hg : w ∘ Fin.natAdd (p+k) = (q.1 ∘ Fin.natAdd p) ∘ Fin.natAdd k := by
    funext j
    apply congrArg q.1
    apply Fin.ext
    simp [familyProductAssociator,Nat.add_assoc]
  have hv := F.product_row_volume (constantRVSchema U p) (q.1 ∘ Fin.castAdd (k+l)) q.2
    (tupleRV (q.1 ∘ Fin.natAdd p))
  have hc := constantRVSchema_volume U (q.1 ∘ Fin.castAdd (k+l))
    (q.2 ∘ Fin.natAdd a) ((tupleRV (q.1 ∘ Fin.natAdd p)) ∘ Fin.natAdd k)
  apply Iff.trans (and_congr_right (fun _ => hv.trans (and_congr_right (fun _ => hc))))
  change (_ ∧ (_ ∧ _)) ↔ ((((w ∘ Fin.castAdd l) ∘ Fin.castAdd k,Fin.elim0) ∈ A ∧
    F.rowVolume (fun j => (((w ∘ Fin.castAdd l) ∘ Fin.castAdd k) j).val)
      (q.2 ∘ Fin.castAdd (rvObjectArity U.object.obj)) (tupleRV ((w ∘ Fin.castAdd l) ∘ Fin.natAdd p))) ∧
    (∃ u : rvObjectDomain U.object.obj, u.val = q.2 ∘ Fin.natAdd a ∧
      (rvObjectVolume U.object.obj u).val = @tupleRV M N hN l (w ∘ Fin.natAdd (p+k))))
  rw [hb,hf,hg,normalized_tupleRV]
  exact and_assoc.symm

def gammaFamilyConstantProductIso (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (U : GammaObjectAt B Set.univ l) :
    GammaIso B (mixedProductSet (familyLiftDomain A F) U.toGamma.lift)
      (familyLiftDomain A (F.productFormula (constantRVSchema U p))) :=
  (gammaVFCoordinateIso _ (gamma_mixed_product_set (gamma_family_lift_definable A hA F)
    U.toGamma.toGammaRVObject.lift_definable) (familyProductAssociator p k l)).congr rfl
      (familyLiftDomain_constant_product A F U).symm

end IntegrationInACVF.Section6
