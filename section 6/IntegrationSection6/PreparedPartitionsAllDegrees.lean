import IntegrationSection6.PreparedMixedPartitions

/-! Simultaneous preparation also includes VF degree zero, where every
subset is already an RV-pullback and the identity program suffices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ} {ι : Type} [Fintype ι]

theorem zero_vf_set_pullback (A : Set (Point (M := M) 0 a)) : IsRVPullback A := by
  apply (isRVPullback_iff _).mpr
  intro p hp q hpq
  have he : p = q := Prod.ext (funext fun i => Fin.elim0 i) ((sameRV_iff _ _).mp hpq).2
  exact he ▸ hp

theorem prepared_mixed_partition_all_degrees {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
    (A : DefSet (M := M) Set.univ n a) (hA : GammaSetDefinable B (carrier A))
    (hAP : IsRVPullback (carrier A))
    (D : ι → DefSet (M := M) Set.univ n a) (hD : ∀ i, GammaSetDefinable B (carrier (D i)))
    (hDA : ∀ i, carrier (D i) ⊆ carrier A)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hCover : carrier A = mixedFiniteUnionSet D Finset.univ) : Nonempty (PreparedMixedPartition (B := B) A D) := by
  cases n with
  | zero => exact ⟨⟨a,A,SpecialBijection.refl A,hA,hAP,D,hD,
      fun i => zero_vf_set_pullback (carrier (D i)),hDA,hDisj,hCover,fun i => .nil (carrier (D i)) (hD i)⟩⟩
  | succ n => exact prepared_mixed_partition_exists (Nat.zero_lt_succ n) hs h00 hreal FBase A hA hAP D hD hDA hDisj hCover

end IntegrationInACVF.Section6
