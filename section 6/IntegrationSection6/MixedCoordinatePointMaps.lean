import IntegrationSection6.GammaGlobalRestriction

/-! Real-definable simultaneous projections of VF and RV coordinate
blocks, retaining their actual sorted point spaces. -/
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
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m u w : ℕ}

def mixedCoordinatePointMap (σ : Fin u → Fin n) (τ : Fin w → Fin m) (S : Set M) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace (M := M) u w) S) :=
  Map.ofCodes _ (fun p => (p.1 ∘ σ,p.2 ∘ τ))
    (fun z => Sum.elim (fun i => z (.inl (σ i))) (fun i => z (.inr (τ i))))
    (by intro i; cases i with
        | inl i => exact rawProj S (.inl (σ i) : Fin n ⊕ Fin m)
        | inr i => exact rawProj S (.inr (τ i) : Fin n ⊕ Fin m))
    (by intro c; exact ⟨fun i => c.property.1 (σ i),fun i => c.property.2 (τ i)⟩)
    (by intro c; exact Prod.ext rfl rfl)

theorem mixedCoordinatePointMap_value (σ : Fin u → Fin n) (τ : Fin w → Fin m) (S : Set M)
    (x : PresentedSet.univ (pointSpace (M := M) n m) S) :
    (mixedCoordinatePointMap σ τ S x).val = (x.val.1 ∘ σ,x.val.2 ∘ τ) := rfl

end IntegrationInACVF.Section6
