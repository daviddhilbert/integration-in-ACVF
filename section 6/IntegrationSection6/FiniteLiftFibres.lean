import IntegrationSection6.LiftPresentations

/-! Finite volume is exactly finiteness of the RV-label fibres of the
actual lift. This uses the actual surjective RV map, including RV zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem finite_volume_of_finite_lift_fibres (U : @RVObject M N S n)
    (hfin : ∀ x : Fin n → VF (M := M),
      {r : Fin (rvObjectArity U) → RV (M := M) | (x,r) ∈ carrier (rawLift U)}.Finite) :
    Map.FiniteFibres (rvObjectVolume U) := by
  intro t
  obtain ⟨x,hx⟩ := @tupleRV_surjective M N hN n t.val
  apply (hfin x).of_injOn (f := fun u : rvObjectDomain U => u.val)
  · intro u hu
    exact ⟨u,rfl,(congrArg Subtype.val hu).trans hx.symm⟩
  · intro u v _ _ he
    exact Subtype.ext he

theorem finite_lift_fibres_of_finite_volume (U : @RVObject M N S n)
    (hfin : Map.FiniteFibres (rvObjectVolume U)) (x : Fin n → VF (M := M)) :
    {r : Fin (rvObjectArity U) → RV (M := M) | (x,r) ∈ carrier (rawLift U)}.Finite := by
  have h := (hfin ⟨@tupleRV M N hN n x,Set.mem_univ _⟩).image (fun u : rvObjectDomain U => u.val)
  apply h.subset
  rintro r ⟨u,hu,hvol⟩
  exact ⟨u,Subtype.ext hvol,hu⟩

theorem finite_volume_iff_finite_lift_fibres (U : @RVObject M N S n) :
    Map.FiniteFibres (rvObjectVolume U) ↔
      ∀ x : Fin n → VF (M := M), {r : Fin (rvObjectArity U) → RV (M := M) | (x,r) ∈ carrier (rawLift U)}.Finite :=
  ⟨finite_lift_fibres_of_finite_volume U,finite_volume_of_finite_lift_fibres U⟩

end IntegrationInACVF.Section6
