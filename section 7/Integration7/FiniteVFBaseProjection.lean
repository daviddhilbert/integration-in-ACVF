module

public import IntegrationSection6.MixedCoordinatePointMaps
public import Integration7.FiniteFibreJacobianOneOperations

@[expose] public section

/-! A finite RV family projects definably and finite-to-one to its VF
base. This supplies the actual projection used in prepared volume maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
variable {S : Set M} {n a : ℕ}
variable (A : SpecialTransformations.Section5.DefSet (M := M) S n a)
variable (B : SpecialTransformations.Section5.DefSet (M := M) S n 0)
variable (hBase : ∀ p : A, (p.val.1,Fin.elim0) ∈ carrier B)

def vfBaseProjection : SpecialTransformations.Section5.Map A B := by
  let F : SpecialTransformations.Section5.Map A (PresentedSet.univ (pointSpace n 0) S) :=
    @Map.comp LRV M N _ _ _ S A _ _
      (mixedCoordinatePointMap (M := M) (n := n) (m := a) id (Fin.elim0 : Fin 0 → Fin a) S)
      (@Map.inclusion LRV M N _ S _ A (Set.subset_univ _))
  exact @Map.corestrict LRV M N _ _ S A _ B F (by
      intro p
      have he : (p.val.1 ∘ id,p.val.2 ∘ (Fin.elim0 : Fin 0 → Fin a)) = (p.val.1,Fin.elim0) :=
        Prod.ext rfl (funext fun j => Fin.elim0 j)
      change (p.val.1 ∘ id,p.val.2 ∘ (Fin.elim0 : Fin 0 → Fin a)) ∈ carrier B
      rw [he]
      exact hBase p)

theorem vfBaseProjection_value (p : A) :
    (vfBaseProjection A B hBase p).val = (p.val.1,Fin.elim0) :=
  Prod.ext rfl (funext fun j => Fin.elim0 j)

theorem vfBaseProjection_finiteFibres
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S A B
      (vfBaseProjection A B hBase) := by
  intro b
  apply (hfin b.val.1).of_injOn (f := fun p : A => p.val.2)
  · intro p hp
    have hx := congrArg (fun q : B => q.val.1) hp
    change p.val.1 = b.val.1 at hx
    exact hx ▸ p.property
  · intro p hp q hq he
    have hx := congrArg (fun r : B => r.val.1) hp
    have hy := congrArg (fun r : B => r.val.1) hq
    change p.val.1 = b.val.1 at hx
    change q.val.1 = b.val.1 at hy
    exact Subtype.ext (Prod.ext (hx.trans hy.symm) he)

end IntegrationInACVF.Section7
