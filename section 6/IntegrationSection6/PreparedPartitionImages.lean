import IntegrationSection6.GammaUnaryChainOperations
import IntegrationSection6.GammaFiniteMembershipPreparation

/-! A prepared membership predicate makes the actual image of a source
piece an RV-pullback. Its Gamma isomorphism may use an equal-function
unary-chain presentation of the same special bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b : ℕ}

theorem prepared_partition_image_pullback {A D : DefSet (M := M) S n a} {C : DefSet (M := M) S n b}
    (T : SpecialBijection A C) (hC : IsRVPullback (carrier C)) (hDA : carrier D ⊆ carrier A)
    (hFlag : Contractible (Map.comp (membershipMap A D) T.inverseMap))
    (e : GammaIso B (carrier A) (carrier C)) (he : ∀ a : A, (e.equiv a).val = (T.toMap a).val) :
    IsRVPullback (gammaRestrictionTarget e (carrier D) hDA) := by
  apply (isRVPullback_iff _).mpr
  rintro p ⟨a,ha⟩ q hpq
  have hpC := (e.equiv ⟨a.val,hDA a.property⟩).property
  have hpC' : p ∈ carrier C := ha ▸ hpC
  have hqC := (isRVPullback_iff _).mp hC p hpC' q hpq
  let b : C := ⟨p,hpC'⟩
  let c : C := ⟨q,hqC⟩
  have hab : T.toMap ⟨a.val,hDA a.property⟩ = b := Subtype.ext ((he _).symm.trans ha)
  have hOld : (T.inverseMap b).val ∈ carrier D := by
    rw [← hab,T.inverse_apply]
    exact a.property
  have hFlags := congrFun (((sameRV_iff _ _).mp (hFlag b c hpq)).2) 0
  have hcD := ((membershipMap_eq_iff A D (T.inverseMap b) (T.inverseMap c)).mp hFlags).mp hOld
  refine ⟨⟨(T.inverseMap c).val,hcD⟩,?_⟩
  change (e.equiv ⟨(T.inverseMap c).val,hDA hcD⟩).val = q
  have hsub : (⟨(T.inverseMap c).val,hDA hcD⟩ : A) = T.inverseMap c := Subtype.ext rfl
  rw [hsub,he]
  exact congrArg (fun z : C => z.val) (T.apply_inverse c)

end IntegrationInACVF.Section6
