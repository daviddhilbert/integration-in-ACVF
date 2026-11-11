import IntegrationSection3ACVF.DefinableGammaMatching
import IntegrationSection3ACVF.GammaFunctionSyntax

/-! A bijection between actual Gamma subtypes supplies an ordinary
partial function with exactly the same full definable graph. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaSubtypeFunctions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def extend (I J : Set (Values.Gamma (M := M))) (q : I → J)
    (x : Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  if hx : x ∈ I then (q ⟨x,hx⟩).val else 1

theorem apply_of_mem (I J : Set (Values.Gamma (M := M))) (q : I → J)
    (x : Values.Gamma (M := M)) (hx : x ∈ I) : extend I J q x = (q ⟨x,hx⟩).val := by
  simp only [extend,dite_eq_left hx]

theorem graph_iff (I J : Set (Values.Gamma (M := M))) (q : I → J)
    (a : Fin 2 → Values.Gamma (M := M)) :
    DefinableGammaMatching.graph I J q a ↔ GammaFunctionSyntax.graph I (extend I J q) a := by
  constructor
  · rintro ⟨x,y,hx,hy,hq⟩
    have hxI : a 0 ∈ I := hx ▸ x.property
    refine ⟨hxI,?_⟩
    rw [← hx,← hy,apply_of_mem I J q x.val x.property]
    exact congrArg Subtype.val hq.symm
  · rintro ⟨hx,he⟩
    let x : I := ⟨a 0,hx⟩
    refine ⟨x,q x,rfl,?_,rfl⟩
    exact (apply_of_mem I J q (a 0) hx).symm.trans he.symm

theorem exists_partial (B : FullBaseAtomicity.Base (M := M))
    (I J : Set (Values.Gamma (M := M))) (q : I → J) (hBij : Function.Bijective q)
    (hG : FullGammaSyntax.Definable B (DefinableGammaMatching.graph I J q)) :
    ∃ f : Values.Gamma (M := M) → Values.Gamma (M := M),
      FullGammaSyntax.Definable B (GammaFunctionSyntax.graph I f) ∧ Set.BijOn f I J := by
  let f := extend I J q
  refine ⟨f,hG.congr (graph_iff I J q),?_,?_,?_⟩
  · intro x hx
    change extend I J q x ∈ J
    rw [apply_of_mem I J q x hx]
    exact (q ⟨x,hx⟩).property
  · intro x hx y hy he
    change extend I J q x = extend I J q y at he
    rw [apply_of_mem I J q x hx,apply_of_mem I J q y hy] at he
    exact congrArg Subtype.val (hBij.1 (Subtype.ext he))
  · intro y hy
    obtain ⟨x,hx⟩ := hBij.2 (⟨y,hy⟩ : J)
    refine ⟨x.val,x.property,?_⟩
    change extend I J q x.val = y
    rw [apply_of_mem I J q x.val x.property]
    exact congrArg Subtype.val hx

end IntegrationInACVF.Section3ACVF.GammaSubtypeFunctions
