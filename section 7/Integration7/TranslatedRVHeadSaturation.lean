module

public import Integration7.NativeRelativeTranslations
public import IntegrationSection4.BalancedFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Translating complete vertical RV fibres by their actual centres
makes the image head-saturated, uniformly in all VF and RV parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

set_option maxHeartbeats 800000 in
theorem translated_rv_head_saturated (A : DefSet (M := M) S (n+1) a)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hC : ∀ p q : A, erase 0 p.val = erase 0 q.val → (c p).val 0 = (c q).val 0)
    (t : A → RV (M := M))
    (hFibres : ∀ q : A, {y : VF (M := M) | replace 0 q.val y ∈ carrier A} =
      BalancedFibres.translatedRV (t q) ((c q).val 0)) :
    HeadSaturated (carrier (relativeTranslationImage A 0 c)) := by
  let c₀ : A → VF (M := M) := fun q => (c q).val 0
  rintro p ⟨q,rfl⟩ x hx
  have hReplace : replace 0 q.val (vfAt q.val 0) = q.val := Prod.ext (Function.update_eq_self 0 q.val.1) rfl
  have hq : vfAt q.val 0 ∈ BalancedFibres.translatedRV (t q) (c₀ q) := by
    apply (Set.ext_iff.mp (hFibres q) _).mp
    change replace 0 q.val (vfAt q.val 0) ∈ carrier A
    rw [hReplace]
    exact q.property
  change rv (vfAt q.val 0-c₀ q) = t q at hq
  change rv x = rv (vfAt q.val 0-c₀ q) at hx
  let y := x+c₀ q
  have hy : replace 0 q.val y ∈ carrier A := by
    apply (Set.ext_iff.mp (hFibres q) y).mpr
    change rv (x+c₀ q-c₀ q) = t q
    rw [add_sub_cancel_right,hx,hq]
  let b : A := ⟨replace 0 q.val y,hy⟩
  have he : erase 0 b.val = erase 0 q.val := Prod.ext (Function.update_idem _ _ _) rfl
  have hcb : c₀ b = c₀ q := hC b q he
  refine ⟨b,?_⟩
  change replace 0 (replace 0 q.val y) (y-c₀ b) =
    replace 0 (replace 0 q.val (vfAt q.val 0-c₀ q)) x
  rw [hcb]
  have hyx : y-c₀ q = x := add_sub_cancel_right x _
  rw [hyx]
  exact Prod.ext (by simp only [replace,Function.update_idem]) rfl

end IntegrationInACVF.Section7
