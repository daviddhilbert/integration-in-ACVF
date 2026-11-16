module

public import Integration7.NativeRelativeTranslations
public import IntegrationSection4.BalancedFibres
public import IntegrationSection6.StandardProgramPresentations

@[expose] public section

/-! Complete translated RV fibres become saturated in their active
coordinate. Swapping the two VF coordinates converts horizontal
saturation to the head saturation required by a contraction program. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

set_option maxHeartbeats 1000000 in
theorem translated_rv_coordinate_saturated (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (hFibres : ∀ q : A, ∃ t : RV (M := M),
      {y : VF (M := M) | replace i q.val y ∈ carrier A} =
        BalancedFibres.translatedRV t ((c q).val 0)) :
    ∀ p ∈ carrier (relativeTranslationImage A i c), ∀ x : VF (M := M),
      rv x = rv (vfAt p i) → replace i p x ∈ carrier (relativeTranslationImage A i c) := by
  let c₀ : A → VF (M := M) := fun q => (c q).val 0
  rintro p ⟨q,rfl⟩ x hx
  obtain ⟨t,hFibre⟩ := hFibres q
  have hReplace : replace i q.val (vfAt q.val i) = q.val := Prod.ext (Function.update_eq_self i q.val.1) rfl
  have hq : vfAt q.val i ∈ BalancedFibres.translatedRV t (c₀ q) := by
    apply (Set.ext_iff.mp hFibre _).mp
    change replace i q.val (vfAt q.val i) ∈ carrier A
    rw [hReplace]
    exact q.property
  change rv (vfAt q.val i-c₀ q) = t at hq
  change rv x = rv (Function.update q.val.1 i (vfAt q.val i-c₀ q) i) at hx
  rw [Function.update_self] at hx
  let y := x+c₀ q
  have hy : replace i q.val y ∈ carrier A := by
    apply (Set.ext_iff.mp hFibre y).mpr
    change rv (x+c₀ q-c₀ q) = t
    rw [add_sub_cancel_right,hx,hq]
  let b : A := ⟨replace i q.val y,hy⟩
  have he : erase i b.val = erase i q.val := Prod.ext (Function.update_idem _ _ _) rfl
  have hcb : c₀ b = c₀ q := hC b q he
  refine ⟨b,?_⟩
  change replace i (replace i q.val y) ((show VF (M := M) from Function.update q.val.1 i y i)-c₀ b) =
    replace i (replace i q.val (vfAt q.val i-c₀ q)) x
  rw [Function.update_self,hcb]
  have hyx : y-c₀ q = x := add_sub_cancel_right x _
  rw [hyx]
  exact Prod.ext (by simp only [replace,Function.update_idem]) rfl

theorem swapped_horizontal_saturated (A : DefSet (M := M) S 2 a)
    (hA : ∀ p ∈ carrier A, ∀ x : VF (M := M),
      rv x = rv (vfAt p 1) → replace 1 p x ∈ carrier A) :
    HeadSaturated (carrier (vfPermutationImage A (Equiv.swap 0 1))) := by
  rintro p ⟨q,rfl⟩ x hx
  change rv x = rv (vfAt q.val 1) at hx
  let b : A := ⟨replace 1 q.val x,hA q.val q.property x hx⟩
  refine ⟨b,?_⟩
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

end IntegrationInACVF.Section7
