import IntegrationSection3ACVF.UniformGammaSlopeSyntax

/-! The exact actual equality of input/output difference values,
with a free proper RV code for the Gamma-linearity coefficient. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section3ACVF.GammaLinearValueRow

open RVDifferencePairs RVSlopeGraph UniformGammaSlopeSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def relation (s x y u v : M) : Prop := sameValue (difference v u) (multiply s (difference y x))

theorem definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {a : Fin 5 → M | relation (a 0) (a 1) (a 2) (a 3) (a 4)} := by
  let ι := Fin 5 ⊕ Fin 3
  have hIn := FullBaseAtomicity.OverBase.preimage_comp (difference_graph_definable B)
    (![.inl 2,.inl 1,.inr 0] : Fin 3 → ι)
  have hOut := FullBaseAtomicity.OverBase.preimage_comp (difference_graph_definable B)
    (![.inl 4,.inl 3,.inr 1] : Fin 3 → ι)
  have hMul := FullBaseAtomicity.OverBase.preimage_comp (multiply_definable B)
    (![.inl 0,.inr 0,.inr 2] : Fin 3 → ι)
  have hSame := FullBaseAtomicity.OverBase.preimage_comp (sameValue_definable B)
    (![.inr 1,.inr 2] : Fin 2 → ι)
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hIn
    (FullBaseAtomicity.OverBase.inter hOut (FullBaseAtomicity.OverBase.inter hMul hSame)))
  apply FullBaseAtomicity.OverBase.congr hd
  intro a
  change (∃ d : Fin 3 → M, d 0 = difference (a 2) (a 1) ∧ d 1 = difference (a 4) (a 3) ∧
    d 2 = multiply (a 0) (d 0) ∧ sameValue (d 1) (d 2)) ↔ _
  constructor
  · rintro ⟨d,h0,h1,h2,hSame⟩
    rw [h0] at h2
    rw [h1,h2] at hSame
    exact hSame
  · intro h
    exact ⟨![difference (a 2) (a 1),difference (a 4) (a 3),multiply (a 0) (difference (a 2) (a 1))],rfl,rfl,rfl,h⟩

theorem relation_iff (s : M) (hs : NonzeroRV s) (x y u v : VFType (M := M)) :
    relation s x.val y.val u.val v.val ↔
      Values.vfValueHom (v-u) = (codeValue s).val * Values.vfValueHom (y-x) := by
  unfold relation
  rw [difference_vf v u,difference_vf y x]
  exact product_value_iff s hs (CanonicalRV.encodedRv (v-u)) (CanonicalRV.encodedRv (y-x))

end IntegrationInACVF.Section3ACVF.GammaLinearValueRow
