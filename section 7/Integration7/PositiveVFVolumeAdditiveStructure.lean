module

public import Integration7.PositiveVolumeIntegrationEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The coproduct addition and actual empty VF object form the additive
commutative monoid identified by positive-degree integration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem positive_volume_lift_on_blowup_classes_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) :
    positiveVolumeLiftOnBlowupClasses hc C k Ξ hGenerated 0 = 0 := by
  apply positiveVFVolumeIsoClass_small hc C
  have he : (rvVolumeLift (PositiveRVVolumeObject.empty (M := M) (C.base : Set M) k)).domain =
      DefSet.empty _ (C.base : Set M) := DefSet.eq_of_carrier_eq (rvVolumeLift_empty_domain _ k)
  rw [he]
  exact (Dimension.dim_empty rawVFSpace
    (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
    (.rv (rvVolumeLift (PositiveRVVolumeObject.empty (M := M) (C.base : Set M) k)).arity)).trans_lt (Nat.zero_lt_succ k)

theorem positive_volume_integration_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (0 : PositiveVFVolumeIsoClasses hc C k) = 0 :=
  (proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (PositiveVFVolumeObject.empty (C.base : Set M) k) (PositiveRVVolumeObject.empty (C.base : Set M) k)).mpr
    (positive_volume_lift_on_blowup_classes_zero hc C Ξ hGenerated).symm

abbrev positiveVFVolumeAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    AddCommMonoid (PositiveVFVolumeIsoClasses hc C k) := by
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := k)
  have hE0 : E 0 = 0 := positive_volume_integration_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1
  exact {
    add := (·+·)
    zero := 0
    add_assoc := fun a b c => E.injective (by simp only [E.map_add,add_assoc])
    add_comm := fun a b => E.injective (by simp only [E.map_add,add_comm])
    zero_add := fun a => E.injective (by rw [E.map_add,hE0,zero_add])
    add_zero := fun a => E.injective (by rw [E.map_add,hE0,add_zero])
    nsmul := nsmulRec }

end IntegrationInACVF.Section7
