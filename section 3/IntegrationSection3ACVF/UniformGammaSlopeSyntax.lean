import IntegrationSection3ACVF.UniformGammaBallSyntax
import IntegrationSection3ACVF.RVSlopeGraph

/-! Equality of actual GammaTop values, including zero differences,
and multiplication by every proper RV code of a Gamma coefficient. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section3ACVF.UniformGammaSlopeSyntax

open UniformGammaBallSyntax RVSlopeGraph

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def sameValue (a b : M) : Prop := iRV a ∧ iRV b ∧ le a b ∧ le b a

theorem sameValue_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {a : Fin 2 → M | sameValue (a 0) (a 1)} := by
  have hRV := ((@definableAt_iff_normalized_raw M sM hM B.real .rv _).mp
    (@definableAt_sort M sM B.real .rv)).1
  have h0 := FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hRV)
    (fun _ : Fin 1 => (0 : Fin 2))
  have h1 := FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hRV)
    (fun _ : Fin 1 => (1 : Fin 2))
  exact FullBaseAtomicity.OverBase.inter h0 (FullBaseAtomicity.OverBase.inter h1
    (FullBaseAtomicity.OverBase.inter (le_definable B)
      (FullBaseAtomicity.OverBase.preimage_comp (le_definable B) (![1,0] : Fin 2 → Fin 2))))

theorem sameValue_iff (a b : CanonicalRV.RVSort M) : sameValue a.val b.val ↔ Values.vrv a = Values.vrv b := by
  have hL := @rv_le_normalize M sM a.val b.val a.property b.property
  have hR := @rv_le_normalize M sM b.val a.val b.property a.property
  change (iRV a.val ∧ iRV b.val ∧ le a.val b.val ∧ le b.val a.val) ↔ _
  rw [show le a.val b.val ↔ iLe a.val b.val from hL,
    show le b.val a.val ↔ iLe b.val a.val from hR]
  exact ⟨fun h => (Values.vrv_eq_iff a b).mpr h.2.2,fun h => ⟨a.property,b.property,(Values.vrv_eq_iff a b).mp h⟩⟩

theorem multiply_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {a : Fin 3 → M | a 2 = multiply (a 0) (a 1)} := by
  apply FullBaseAtomicity.OverBase.of_real
  let N := @CanonicalStructure.normalize M sM
  letI := N
  have h : B.real.DefinableFun LRV (fun a : Fin 3 → M => iRVMul (a 0) (a 1)) := by
    have hh : B.real.DefinableFun LRV (Structure.funMap (L := LRV) Fn.rvMul) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 2 Fn.rvMul)
    exact hh.comp (fun i => by fin_cases i <;> exact Set.DefinableFun.proj LRV)
  exact (Set.DefinableFun.proj LRV).ofPred_eq h

theorem product_value_iff (s : M) (hs : NonzeroRV s) (a b : CanonicalRV.RVSort M) :
    sameValue a.val (multiply s b.val) ↔ Values.vrv a = (codeValue s).val * Values.vrv b := by
  let S : CanonicalRV.RVSort M := ⟨s,hs.1⟩
  let P : CanonicalRV.RVSort M := ⟨iRVMul s b.val,rv_mul_mem hM hs.1 b.property⟩
  have hCode : (codeValue s).val = Values.vrv S := by
    simp only [codeValue,dite_eq_left hs]
    rfl
  have hValue : Values.vrv P = (codeValue s).val * Values.vrv b := by
    rw [hCode]
    exact Values.vrv_mul S b
  rw [multiply_rv S b]
  exact (sameValue_iff a P).trans (by rw [hValue])

end IntegrationInACVF.Section3ACVF.UniformGammaSlopeSyntax
