import IntegrationSection5.MixedScalarFamilies
import IntegrationSection5.VFPermutation

/-! Equality of precisely the VF coordinates complementary to one selected
coordinate, together with all old RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m p : ℕ}

def SameCoordinateContext (i : Fin n) (a b : Point (M := M) n m) : Prop :=
  (∀ j : Fin n, j ≠ i → a.1 j = b.1 j) ∧ a.2 = b.2

theorem sameCoordinateContext_refl (i : Fin n) (a : Point (M := M) n m) :
    SameCoordinateContext i a a := ⟨fun _ _ => rfl,rfl⟩

theorem sameCoordinateContext_zero_iff (a b : Point (M := M) (p+1) m) :
    SameCoordinateContext 0 a b ↔ MixedScalarFamilies.context a = MixedScalarFamilies.context b := by
  constructor
  · rintro ⟨hv,hr⟩
    apply congrArg gammaPointCode
    exact Prod.ext (funext fun j => hv j.succ (Fin.succ_ne_zero j)) hr
  · intro h
    have ht := gammaPointCode_injective h
    refine ⟨?_,congrArg (fun q : Point (M := M) p m => q.2) ht⟩
    intro j hj
    cases j using Fin.cases with
    | zero => exact (hj rfl).elim
    | succ j => exact congrArg (fun q : Point (M := M) p m => q.1 j) ht

theorem sameCoordinateContext_permutation (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (a b : Point (M := M) n m) :
    SameCoordinateContext i (vfPermutation σ a) (vfPermutation σ b) ↔
      SameCoordinateContext (σ i) a b := by
  constructor
  · rintro ⟨hv,hr⟩
    refine ⟨?_,hr⟩
    intro j hj
    have hji : σ.symm j ≠ i := fun h => hj ((congrArg σ h).symm.trans (σ.apply_symm_apply j)).symm
    simpa only [vfPermutation,Function.comp_apply,Equiv.apply_symm_apply] using hv (σ.symm j) hji
  · rintro ⟨hv,hr⟩
    exact ⟨fun j hj => hv (σ j) (fun h => hj (σ.injective h)),hr⟩

end IntegrationInACVF.Section5
