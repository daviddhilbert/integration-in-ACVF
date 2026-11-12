import IntegrationSection6.PartialFamilyParameterPreservation
import IntegrationSection6.VFPrefixMaps
import IntegrationSection6.MixedVFParameterDomains

/-! Insert a named VF parameter prefix and identify literal fibres with
fixed-prefix subsets of the total space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {p n a : ℕ}

def vfParameterInsert (x : Fin p → VF (M := M)) (q : Point (M := M) n a) : Point (M := M) (p+n) a :=
  (Fin.append x q.1,q.2)

theorem activeFrozenShuffle_symm_active (p n : ℕ) (j : Fin n) :
    (activeFrozenShuffle p n).symm (Fin.natAdd p j) = activeIndex p n j := by
  have h := congrArg (activeFrozenShuffle p n).symm (activeFrozenShuffle_active p n j)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

theorem vfPrefixTuple_unshuffle (x : Fin p → VF (M := M)) (y : Fin n → VF (M := M)) :
    vfPrefixTuple x y ∘ (activeFrozenShuffle p n).symm = Fin.append x y := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · change vfPrefixTuple x y ((activeFrozenShuffle p n).symm (Fin.castAdd n i)) = _
    rw [activeFrozenShuffle_symm_prefix]
    have hi : frozenIndex p n i = (⟨n+i.val,by omega⟩ : Fin (p+n)) := Fin.ext (frozenIndex_val p n i)
    rw [hi]
    exact (vfPrefixTuple_tail x y i).trans (Fin.append_left x y i).symm
  · change vfPrefixTuple x y ((activeFrozenShuffle p n).symm (Fin.natAdd p i)) = _
    rw [activeFrozenShuffle_symm_active]
    exact (vfPrefixTuple_head x y i).trans (Fin.append_right x y i).symm

def vfParameterInsertMap (S : Set M) (x : Fin p → VF (M := M)) (n a : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n a) (S ∪ Set.range (fun j => (x j).val)))
      (PresentedSet.univ (pointSpace (M := M) (p+n) a) (S ∪ Set.range (fun j => (x j).val))) :=
  Map.comp (vfCoordinateMap (S ∪ Set.range (fun j => (x j).val)) (activeFrozenShuffle p n).symm a)
    (vfPrefixInsertMap S x n a)

theorem vfParameterInsertMap_value (S : Set M) (x : Fin p → VF (M := M))
    (q : PresentedSet.univ (pointSpace (M := M) n a) (S ∪ Set.range (fun j => (x j).val))) :
    (vfParameterInsertMap S x n a q).val = vfParameterInsert x q.val := by
  change (vfPrefixTuple x q.val.1 ∘ (activeFrozenShuffle p n).symm,q.val.2) = (Fin.append x q.val.1,q.val.2)
  exact Prod.ext (vfPrefixTuple_unshuffle x q.val.1) rfl

theorem vfParameterPoint_pack (x : Fin p → VF (M := M)) (q : Point (M := M) (p+n) a)
    (hx : q.1 ∘ Fin.castAdd n = x) :
    vfParameterInsert x (q.1 ∘ Fin.natAdd p,q.2) = q := by
  change (Fin.append x (q.1 ∘ Fin.natAdd p),q.2) = (q.1,q.2)
  apply Prod.ext
  · exact (congrArg (fun f => Fin.append f (q.1 ∘ Fin.natAdd p)) hx.symm).trans Fin.append_castAdd_natAdd
  · rfl

theorem vfParameterInsert_injective (x : Fin p → VF (M := M)) :
    Function.Injective (vfParameterInsert (n := n) (a := a) x) := by
  intro q r he
  apply Prod.ext
  · funext j
    have h := congrFun (congrArg (fun z : Point (M := M) (p+n) a => z.1) he) (Fin.natAdd p j)
    simpa only [vfParameterInsert,Fin.append_right] using h
  · exact congrArg (fun z : Point (M := M) (p+n) a => z.2) he

def vfParameterFibreEquiv (U : Set (Point (M := M) (p+n) a)) (x : Fin p → VF (M := M)) :
    vfParameterFibre U x ≃ {u : U | u.val.1 ∘ Fin.castAdd n = x} where
  toFun q := ⟨⟨vfParameterInsert x q.val,q.property⟩,funext (fun j => Fin.append_left _ _ j)⟩
  invFun u := ⟨(u.val.val.1 ∘ Fin.natAdd p,u.val.val.2),by
    change vfParameterInsert x (u.val.val.1 ∘ Fin.natAdd p,u.val.val.2) ∈ U
    exact (vfParameterPoint_pack x u.val.val u.property).symm ▸ u.val.property⟩
  left_inv q := by
    apply Subtype.ext
    change (Fin.append x q.val.1 ∘ Fin.natAdd p,q.val.2) = (q.val.1,q.val.2)
    apply Prod.ext
    · exact funext (fun j => Fin.append_right _ _ j)
    · rfl
  right_inv u := Subtype.ext (Subtype.ext (vfParameterPoint_pack x u.val.val u.property))

end IntegrationInACVF.Section6
