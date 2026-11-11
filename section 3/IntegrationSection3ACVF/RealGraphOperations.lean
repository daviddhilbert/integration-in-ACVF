import IntegrationSection3ACVF.FullBaseDefinability

/-! Real-base postcomposition of a map defined only on its given domain. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RealGraphOperations

variable {M : Type} [sM : LRV.Structure M]

theorem postcompose (S : Set M) {A : Set M} (f : M → M) (h : M → M → M)
    (hf : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn A f))
    (hh : @Set.DefinableFun M LRV (CanonicalStructure.normalize (M := M)) (Fin 2) S
      (fun z => h (z 0) (z 1))) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn A (fun x => h x (f x))) := by
  letI := @CanonicalStructure.normalize M sM
  have h3 : S.DefinableFun LRV (fun z : Fin 3 → M => h (z 0) (z 1)) :=
    Set.DefinableFun.comp (f := fun z => h (z 0) (z 1))
      (g := fun z => ![z 0,z 1]) (fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV) hh
  have hRel : S.Definable LRV {z : Fin 3 → M | z 2 = h (z 0) (z 1)} :=
    (Set.DefinableFun.proj LRV).ofPred_eq h3
  have hd := ((hf.preimage_comp (![.inl 0,.inr 0] : Fin 2 → Fin 2 ⊕ Fin 1)).inter
    (hRel.preimage_comp (![.inl 0,.inr 0,.inl 1] : Fin 3 → Fin 2 ⊕ Fin 1))).exists_of_finite
  convert hd using 1
  ext z
  change (z 0 ∈ A ∧ z 1 = h (z 0) (f (z 0))) ↔
    (∃ y : Fin 1 → M, (z 0 ∈ A ∧ y 0 = f (z 0)) ∧ z 1 = h (z 0) (y 0))
  exact ⟨fun ⟨ha,he⟩ => ⟨![f (z 0)],⟨ha,rfl⟩,he⟩,
    fun ⟨y,⟨ha,hy⟩,he⟩ => ⟨ha,hy ▸ he⟩⟩

end IntegrationInACVF.Section3ACVF.RealGraphOperations
