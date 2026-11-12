import IntegrationSection6.ElementaryBlowup

/-!
# The actual fibre bijection underlying Lemmas 6.9 and 6.12

Subtracting a nonzero centre in an RV fibre yields exactly the smaller
open ball, with the quotient RV parameter retained. The absorbing parameter
is included, so the centre itself is sent to (0,0).
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M
local notation "rv" => CanonicalRV.encodedRv

/-- The linked RV equality, with the paper's order reversed explicitly. -/
theorem equalRV_sub_small {a c : VF} (hc : c ≠ 0) (he : rv a = rv c) :
    RVOperations.absoluteHom (rv (a - c)) < RVOperations.absoluteHom (rv c) := by
  have hclose := (CanonicalRV.encoded_eq_iff_close a.property c.property
    (fun h => hc (Subtype.ext h))).mp (congrArg Subtype.val he)
  have horder := Values.valueEquiv_rv_le Values.presentationValuation
    Values.presentation_compatible (rv (a - c)) (rv c)
  change iLe (rv (a - c)).val (rv c).val ↔
    RVOperations.absoluteHom (rv c) ≤ RVOperations.absoluteHom (rv (a - c)) at horder
  exact lt_of_not_ge ((not_congr horder).mp hclose)

/-- Addition of a strictly smaller term does not change an RV class. -/
theorem small_add_equalRV (b c : VF) (hc : c ≠ 0)
    (hb : RVOperations.absoluteHom (rv b) < RVOperations.absoluteHom (rv c)) :
    rv (b + c) = rv c := by
  have horder := Values.valueEquiv_rv_le Values.presentationValuation
    Values.presentation_compatible (rv b) (rv c)
  change iLe (rv b).val (rv c).val ↔
    RVOperations.absoluteHom (rv c) ≤ RVOperations.absoluteHom (rv b) at horder
  have hclose : ¬ iLe (rv b).val (rv c).val :=
    (not_congr horder).mpr (not_le_of_gt hb)
  apply Subtype.ext
  apply (CanonicalRV.encoded_eq_iff_close (b + c).property c.property
    (fun h => hc (Subtype.ext h))).mpr
  change ¬ iLe (rv ((b + c) - c)).val (rv c).val
  simpa only [add_sub_cancel_right] using hclose

/-- The target fibre with its actual quotient RV parameter. -/
def translatedFibre (t : RV) : Set (VF × RV) :=
  {q | rv q.1 = q.2 * t ∧ RVOperations.absoluteHom q.2 < 1}

/-- The pointwise lift of elementary blowup: b=a-c and s=rv(b)/rv(c).
This proves the bijection, including both inverse laws, rather than assuming
an isomorphism of fibres. Definability of a varying centre is separate. -/
def translatedFibreEquiv (c : VF) (hc : c ≠ 0) :
    {a : VF // rv a = rv c} ≃ translatedFibre (rv c) := by
  have ht : rv c ≠ (0 : RV) := (RVOperations.rv_ne_zero c).mpr hc
  have hv : RVOperations.absoluteHom (rv c) ≠ 0 := by
    intro he
    exact ht ((RVOperations.absolute_eq_zero (rv c)).mp he)
  have hvpos : 0 < RVOperations.absoluteHom (rv c) := lt_of_le_of_ne zero_le (Ne.symm hv)
  refine {
    toFun := fun a => ⟨(a.val - c, rv (a.val - c) / rv c), ?_⟩
    invFun := fun q => ⟨q.val.1 + c, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · constructor
    · exact (div_mul_cancel₀ _ ht).symm
    · rw [map_div₀]
      exact (div_lt_one₀ hvpos).mpr (equalRV_sub_small hc a.property)
  · apply small_add_equalRV q.val.1 c hc
    have he := congrArg RVOperations.absoluteHom q.property.1
    rw [map_mul] at he
    rw [he]
    simpa only [one_mul] using mul_lt_mul_of_pos_right q.property.2 hvpos
  · intro a
    apply Subtype.ext
    exact sub_add_cancel a.val c
  · intro q
    apply Subtype.ext
    apply Prod.ext
    · exact add_sub_cancel_right q.val.1 c
    · change rv ((q.val.1 + c) - c) / rv c = q.val.2
      rw [add_sub_cancel_right]
      exact (div_eq_iff ht).mpr q.property.1

end IntegrationInACVF.Section6
