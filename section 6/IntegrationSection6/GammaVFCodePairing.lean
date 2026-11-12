import IntegrationSection6.GammaRVFiniteFamilyCodes

/-! Finite RV codes for predicates on pairs of VF parameter tuples.
Conjunction is implemented by the actual definable pairing map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ}

def GammaVFRowCode (B : Base (M := M)) (p : ℕ)
    (P : (Fin p → M) → (Fin p → M) → Prop) : Prop :=
  ∃ d : ℕ, ∃ g : Map (PresentedSet.univ (pointSpace (M := M) p 0) B.real)
      (PresentedSet.univ (pointSpace (M := M) 0 d) B.real),
    GammaGraphDefinable B (pointMapGraph g) ∧
    ∀ x y, g x = g y → P (fun j => (x.val.1 j).val) (fun j => (y.val.1 j).val)

theorem GammaVFRowCode.mono {P Q : (Fin p → M) → (Fin p → M) → Prop}
    (h : GammaVFRowCode B p P) (hPQ : ∀ z t, P z t → Q z t) : GammaVFRowCode B p Q := by
  obtain ⟨d,g,hg,h⟩ := h
  exact ⟨d,g,hg,fun x y hxy => hPQ _ _ (h x y hxy)⟩

theorem GammaVFRowCode.and {P Q : (Fin p → M) → (Fin p → M) → Prop}
    (hP : GammaVFRowCode B p P) (hQ : GammaVFRowCode B p Q) :
    GammaVFRowCode B p (fun z t => P z t ∧ Q z t) := by
  obtain ⟨d,g,hg,hP⟩ := hP
  obtain ⟨e,f,hf,hQ⟩ := hQ
  let h := pairRVMaps (M := M) (sM := sM) (hM := hM) g f
  exact ⟨d+e,h,(gammaLogicInput B).real_map_graph h,
    fun x y hxy => ⟨hP x y (pairRVMaps_eq_left g f hxy),hQ x y (pairRVMaps_eq_right g f hxy)⟩⟩

theorem GammaVFRowCode.true : GammaVFRowCode B p (fun _ _ => True) := by
  let g := constantRVMap (M := M) (sM := sM) (hM := hM)
    (PresentedSet.univ (pointSpace (M := M) p 0) B.real) 0
  exact ⟨0,g,(gammaLogicInput B).real_map_graph g,fun _ _ _ => trivial⟩

theorem GammaVFRowCode.finset {ι : Type} (J : Finset ι)
    (P : ι → (Fin p → M) → (Fin p → M) → Prop)
    (h : ∀ i ∈ J, GammaVFRowCode B p (P i)) :
    GammaVFRowCode B p (fun z t => ∀ i ∈ J, P i z t) := by
  induction J using Finset.induction_on with
  | empty => exact GammaVFRowCode.true.mono (fun _ _ _ i hi => by simpa using hi)
  | @insert i J hi ih =>
    have hI := h i (Finset.mem_insert_self i J)
    have hJ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact (hI.and hJ).mono (fun z t hh j hj => by
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hh.1
      · exact hh.2 j hj)

end IntegrationInACVF.Section6
