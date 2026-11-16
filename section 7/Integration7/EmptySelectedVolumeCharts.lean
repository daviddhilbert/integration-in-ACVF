module

public import Integration7.RawStandardVolumeObjects
public import Integration7.NativeCoordinateDensityVolumeIsomorphisms

@[expose] public section

/-! With no old selected RV coordinates, the selected standard object
is genuinely volume isomorphic to the full raw contraction object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

theorem empty_selected_volume_finite (A : SpecialTransformations.Section5.DefSet (M := M) S n a)
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (x : Fin n → VF (M := M)) (t : Fin 0 → RV (M := M)) :
    {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ (Fin.elim0 : Fin 0 → Fin a) = t}.Finite :=
  (hfin x).subset (fun _ h => h.1)

def emptySelectedRawVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    RVVolumeIso
      ((selectedStandardVolumeObject hc C Ξ A (Fin.elim0 : Fin 0 → Fin a) δ hδ
        (empty_selected_volume_finite A hfin) T).reindexDegree ((Nat.zero_add n).symm))
      (rawStandardVolumeObject hc C Ξ A hfin δ hδ T) := by
  let U := (selectedStandardVolumeObject hc C Ξ A (Fin.elim0 : Fin 0 → Fin a) δ hδ
    (empty_selected_volume_finite A hfin) T).reindexDegree ((Nat.zero_add n).symm)
  let V := rawStandardVolumeObject hc C Ξ A hfin δ hδ T
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.inclusion (fun _ h => h)
  have hf : Function.Bijective f := ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
    fun v => ⟨⟨v.val,v.property⟩,rfl⟩⟩
  have hcoord : ∀ u, V.underlying.obj.value (f u) = U.underlying.obj.value u := by
    intro u
    funext i
    change u.val (T.volumeIndex i) = u.val
      (Fin.append T.volumeIndex (suffixIndex T.program.rvArity_le ∘ (Fin.elim0 : Fin 0 → Fin a))
        (finCongr (Nat.add_comm 0 (n+1))
          (finCongr (congrArg Nat.succ ((Nat.zero_add n).symm)) i)))
    have hi : finCongr (Nat.add_comm 0 (n+1))
        (finCongr (congrArg Nat.succ ((Nat.zero_add n).symm)) i) = Fin.castAdd 0 i := Fin.ext rfl
    rw [hi,Fin.append_left]
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hcoord)) hcoord (fun _ => rfl)

end IntegrationInACVF.Section7
