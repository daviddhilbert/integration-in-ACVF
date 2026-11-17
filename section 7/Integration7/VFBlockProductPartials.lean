module

public import Integration7.VFBlockProductCoordinates
public import Section9.VFJacobian

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The four actual partial-derivative blocks of a Cartesian product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r : ℕ}
local notation "VF" => VFType (M := M)

theorem vf_partial_zero_of_coordinate_unchanged
    (F : (Fin n → VF) → Fin r → VF) (a : Fin n → VF) (j : Fin n) (i : Fin r)
    (h : ∀ t, F (a+Pi.single j t) i = F a i) : HasVFPartialAt F a j i 0 := by
  intro ε
  refine ⟨1,fun t ht _ => ?_⟩
  rw [h,sub_self,zero_mul,sub_zero,map_zero]
  exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε) (fun hz => ht ((vfValue_eq_zero_iff t).mp hz)))

theorem vf_block_product_partial_left_left
    (F : (Fin n → VF) → Fin n → VF) (G : (Fin m → VF) → Fin m → VF)
    (a : Fin n → VF) (b : Fin m → VF) (j i : Fin n) (d : VF)
    (hF : HasVFPartialAt F a j i d) :
    HasVFPartialAt (tupleBlockProduct F G) (Fin.append a b) (Fin.castAdd m j) (Fin.castAdd m i) d := by
  have hbase : Fin.append a b ∘ Fin.castAdd m = a := by funext q; exact Fin.append_left a b q
  intro ε
  obtain ⟨δ,hδ⟩ := hF ε
  refine ⟨δ,fun t ht hnear => ?_⟩
  simpa only [tupleBlockProduct,Fin.append_left,append_perturb_left_left,hbase] using hδ t ht hnear

theorem vf_block_product_partial_right_right
    (F : (Fin n → VF) → Fin n → VF) (G : (Fin m → VF) → Fin m → VF)
    (a : Fin n → VF) (b : Fin m → VF) (j i : Fin m) (d : VF)
    (hG : HasVFPartialAt G b j i d) :
    HasVFPartialAt (tupleBlockProduct F G) (Fin.append a b) (Fin.natAdd n j) (Fin.natAdd n i) d := by
  have hbase : Fin.append a b ∘ Fin.natAdd n = b := by funext q; exact Fin.append_right a b q
  intro ε
  obtain ⟨δ,hδ⟩ := hG ε
  refine ⟨δ,fun t ht hnear => ?_⟩
  simpa only [tupleBlockProduct,Fin.append_right,append_perturb_right_right,hbase] using hδ t ht hnear

theorem vf_block_product_partial_left_right
    (F : (Fin n → VF) → Fin n → VF) (G : (Fin m → VF) → Fin m → VF)
    (a : Fin n → VF) (b : Fin m → VF) (j : Fin m) (i : Fin n) :
    HasVFPartialAt (tupleBlockProduct F G) (Fin.append a b) (Fin.natAdd n j) (Fin.castAdd m i) 0 := by
  apply vf_partial_zero_of_coordinate_unchanged
  intro t
  have hbase : Fin.append a b ∘ Fin.castAdd m = a := by funext q; exact Fin.append_left a b q
  simp only [tupleBlockProduct,Fin.append_left,append_perturb_right_left,hbase]

theorem vf_block_product_partial_right_left
    (F : (Fin n → VF) → Fin n → VF) (G : (Fin m → VF) → Fin m → VF)
    (a : Fin n → VF) (b : Fin m → VF) (j : Fin n) (i : Fin m) :
    HasVFPartialAt (tupleBlockProduct F G) (Fin.append a b) (Fin.castAdd m j) (Fin.natAdd n i) 0 := by
  apply vf_partial_zero_of_coordinate_unchanged
  intro t
  have hbase : Fin.append a b ∘ Fin.natAdd n = b := by funext q; exact Fin.append_right a b q
  simp only [tupleBlockProduct,Fin.append_right,append_perturb_left_right,hbase]

end IntegrationInACVF.Section7
