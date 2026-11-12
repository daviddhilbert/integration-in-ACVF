import IntegrationSection6.GammaHeadFibreLiftMaps
import IntegrationSection6.GammaSelectedLabelFibrePresentations
import IntegrationSection5.GammaOrderedContraction

/-! One head contraction preserves the exact selected-volume finiteness
needed for RV[k]. The proof freezes only the complementary VF tuple and
uses the actual unary lift, including the absorbing RV value. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m k : ℕ}
variable {A : DefSet (M := M) S (n+1) m}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def headVolumeIndex (T : HeadPreparation A) (ρ : Fin k → Fin m) : Fin (1+k) → Fin (1+T.arity) :=
  Fin.append (fun j : Fin 1 => Fin.castAdd T.arity j) (headSelectedLabelIndex T ρ)

theorem head_selected_fibres_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (T : HeadPreparation A) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (ρ : Fin k → Fin m)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite) :
    ∀ (x : Fin n → VF (M := M)) (t : Fin (1+k) → RV (M := M)),
      {r : Fin (1+T.arity) → RV (M := M) |
        (x,r) ∈ carrier T.contractedSet ∧ r ∘ headVolumeIndex T ρ = t}.Finite := by
  intro x t
  let Q := coordinateGammaBase B 0 (headFrozenTuple x)
  have hQ : Cardinal.mk Q.real < κ := by
    rw [show Q = ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ from coordinateGammaBase_head x]
    exact small_union_range hκ B.real hreal (fun j => (x j).val)
  let f := gammaHeadFibreLiftIso T hT hTarget x
  have hF := finite_selected_rv_fibres_of_gammaIso hκ hs hQ f ρ (headSelectedLabelIndex T ρ)
    (gammaHeadFibreLiftIso_labels T hT hTarget x ρ) (by
      intro z v
      have he : {r : Fin m → RV (M := M) |
          (z,r) ∈ carrier (coordinateFibre A 0 (headFrozenTuple x)) ∧ r ∘ ρ = v} =
          {r | (Fin.cons (z 0) x,r) ∈ carrier A ∧ r ∘ ρ = v} := by
        ext r
        change (coordinateInsert 0 (headFrozenTuple x) (z,r) ∈ carrier A ∧ _) ↔ _
        rw [coordinateInsert_head]
        rfl
      rw [he]
      exact hfin _ v)
  obtain ⟨z,hz⟩ := @tupleRV_surjective M N hN 1 (t ∘ Fin.castAdd k)
  have hz0 : @rv M sM hM (z 0) = t (Fin.castAdd k 0) := by
    have he := (@normalized_tupleRV M sM hM 1 z).symm.trans hz
    exact congrFun he 0
  apply (hF z (t ∘ Fin.natAdd 1)).subset
  intro r hr
  have hh : r (Fin.castAdd T.arity 0) = t (Fin.castAdd k 0) := by
    simpa only [Function.comp_apply,headVolumeIndex,Fin.append_left] using congrFun hr.2 (Fin.castAdd k 0)
  have ht : r ∘ headSelectedLabelIndex T ρ = t ∘ Fin.natAdd 1 := by
    funext j
    simpa only [Function.comp_apply,headVolumeIndex,Fin.append_right] using congrFun hr.2 (Fin.natAdd 1 j)
  exact ⟨(headFibre_canonical_carrier T x (z,r)).mpr ⟨hr.1,hh.trans hz0.symm⟩,ht⟩

end IntegrationInACVF.Section6
