import IntegrationSection3ACVF.RVDifferencePairs
import IntegrationSection3ACVF.AnnulusValueIntervals
import Section3.GammaCodeDefinability

/-! Uniform original-base ball syntax with radius and centre free.
Every proper RV representative of the radius is retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section3ACVF.UniformGammaBallSyntax

open RVDifferencePairs

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def le (x y : M) : Prop := @iLe M (@CanonicalStructure.normalize M sM) x y

def ball (r x c : M) : Prop := iVF x ∧ le r (difference x c) ∧ ¬ le (difference x c) r

theorem le_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {a : Fin 2 → M | le (a 0) (a 1)} := by
  apply FullBaseAtomicity.OverBase.of_real
  exact @raw_le_definable M (@CanonicalStructure.normalize M sM) B.real

theorem ball_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {a : Fin 3 → M | ball (a 0) (a 1) (a 2)} := by
  let ι := Fin 3 ⊕ Fin 1
  have hDiff := FullBaseAtomicity.OverBase.preimage_comp (difference_graph_definable B)
    (![.inl 1,.inl 2,.inr 0] : Fin 3 → ι)
  have hVF := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have hSort : FullBaseAtomicity.OverBase B {a : ι → M | iVF (a (.inl 1))} :=
    FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real hVF)
      (fun _ : Fin 1 => (Sum.inl 1 : ι))
  have hL := FullBaseAtomicity.OverBase.preimage_comp (le_definable B)
    (![.inl 0,.inr 0] : Fin 2 → ι)
  have hR := FullBaseAtomicity.OverBase.preimage_comp (le_definable B)
    (![.inr 0,.inl 0] : Fin 2 → ι)
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hDiff
    (FullBaseAtomicity.OverBase.inter hSort (FullBaseAtomicity.OverBase.inter hL (FullBaseAtomicity.OverBase.compl hR))))
  apply FullBaseAtomicity.OverBase.congr hd
  intro a
  change (∃ d : Fin 1 → M, d 0 = difference (a 1) (a 2) ∧
    iVF (a 1) ∧ le (a 0) (d 0) ∧ ¬ le (d 0) (a 0)) ↔ _
  constructor
  · rintro ⟨d,he,hx,hL,hR⟩
    rw [he] at hL hR
    exact ⟨hx,hL,hR⟩
  · rintro ⟨hx,hL,hR⟩
    exact ⟨![difference (a 1) (a 2)],rfl,hx,hL,hR⟩

theorem ball_iff (r : M) (hr : NonzeroRV r) (x c : VFType (M := M)) :
    ball r x.val c.val ↔ x.val ∈ GammaRadiusAtomicity.gammaBall c (codeValue r) true := by
  have hCode : (codeValue r).val = Values.vrv (⟨r,hr.1⟩ : CanonicalRV.RVSort M) := by
    simp only [codeValue,dite_eq_left hr]
    rfl
  let R : CanonicalRV.RVSort M := ⟨r,hr.1⟩
  let D : CanonicalRV.RVSort M := CanonicalRV.encodedRv (x-c)
  have hL : le r (difference x.val c.val) ↔ (codeValue r).val ≤ Values.vfValueHom (x-c) := by
    rw [difference_vf]
    have he := (@Values.vrv_le_iff M sM hM R D).symm
    change (@iLe M sM r (iRv (x-c).val)) ↔ Values.vrv R ≤ Values.vfValueHom (x-c) at he
    rw [← hCode] at he
    exact (@rv_le_normalize M sM r (iRv (x-c).val) hr.1 (rv_mem hM (x-c).property)).trans he
  have hR : le (difference x.val c.val) r ↔ Values.vfValueHom (x-c) ≤ (codeValue r).val := by
    rw [difference_vf]
    have he := (@Values.vrv_le_iff M sM hM D R).symm
    change (@iLe M sM (iRv (x-c).val) r) ↔ Values.vfValueHom (x-c) ≤ Values.vrv R at he
    rw [← hCode] at he
    exact (@rv_le_normalize M sM (iRv (x-c).val) r (rv_mem hM (x-c).property) hr.1).trans he
  rw [AnnulusValueIntervals.mem_open]
  change (iVF x.val ∧ le r (difference x.val c.val) ∧ ¬ le (difference x.val c.val) r) ↔ _
  rw [hL,hR]
  exact ⟨fun h => lt_of_not_ge h.2.2,fun h => ⟨x.property,h.le,not_le_of_gt h⟩⟩

end IntegrationInACVF.Section3ACVF.UniformGammaBallSyntax
