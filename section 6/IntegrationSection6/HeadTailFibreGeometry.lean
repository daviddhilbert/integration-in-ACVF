import IntegrationSection6.HeadTailPermutations
import IntegrationSection6.GammaHeadFibreParameters
import IntegrationSection6.GammaPermutedFibrePresentations
import IntegrationSection5.RelativeSpecialRestriction

/-! Reordering the frozen VF tail preserves the actual unary head fibre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

theorem vfPermutationImage_trans (U : DefSet (M := M) S n a) (σ τ : Equiv.Perm (Fin n)) :
    vfPermutationImage (vfPermutationImage U σ) τ = vfPermutationImage U (τ.trans σ) := by
  apply defSet_eq_of_carrier_eq
  ext q
  change (q.1,q.2) ∈ carrier (vfPermutationImage (vfPermutationImage U σ) τ) ↔
    (q.1,q.2) ∈ carrier (vfPermutationImage U (τ.trans σ))
  rw [vfPermutationImage_row,vfPermutationImage_row,vfPermutationImage_row]
  rfl

theorem headTailPerm_cons {Y : Type*} (τ : Equiv.Perm (Fin n)) (z : Y) (x : Fin n → Y) :
    Fin.cons z x ∘ (headTailPerm τ).symm = Fin.cons z (x ∘ τ.symm) := by
  funext j
  cases j using Fin.cases <;> simp [headTailPerm_symm]

theorem headTailFibre_carrier (U : DefSet (M := M) S (n+1) a) (τ : Equiv.Perm (Fin n))
    (x : Fin n → VF (M := M)) :
    carrier (coordinateFibre (vfPermutationImage U (headTailPerm τ)) 0 (headFrozenTuple x)) =
      carrier (coordinateFibre U 0 (headFrozenTuple (x ∘ τ.symm))) := by
  ext q
  change coordinateInsert 0 (headFrozenTuple x) q ∈ carrier (vfPermutationImage U (headTailPerm τ)) ↔
    coordinateInsert 0 (headFrozenTuple (x ∘ τ.symm)) q ∈ carrier U
  rw [coordinateInsert_head,coordinateInsert_head,vfPermutationImage_row,headTailPerm_cons]

end IntegrationInACVF.Section6
