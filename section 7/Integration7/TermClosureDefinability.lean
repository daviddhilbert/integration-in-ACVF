import Integration7.FiniteVolumeParameterContexts
import Section3.DefinableConstants

/-! A term-generated substructure adds no definable sets over its
generators. This is raw first-order parameter elimination and needs no
field or VF/Gamma generation hypothesis. -/

noncomputable section
open FirstOrder FirstOrder.Language

namespace IntegrationInACVF.Section7

theorem definable_singleton_mem_termClosure {L : Language} {M : Type} [L.Structure M]
    {S : Set M} {x : M} (hx : x ∈ Substructure.closure L S) : S.Definable₁ L {x} := by
  refine Substructure.closure_induction (p := fun x => S.Definable₁ L {x}) hx ?_ ?_
  · intro x hx
    exact Set.Definable.singleton_of_mem L hx
  · intro n f v hv
    exact SpecialTransformations.DefinableConstants.function_symbol f v hv

theorem definable_termClosure_iff {L : Language} {M : Type} [L.Structure M]
    {S : Set M} {n : ℕ} {A : Set (Fin n → M)} :
    (Substructure.closure L S : Set M).Definable L A ↔ S.Definable L A := by
  constructor
  · intro hA
    exact SpecialTransformations.DefinableConstants.eliminate_parameters A
      (fun _ hx => definable_singleton_mem_termClosure hx) hA
  · exact fun hA => hA.mono Substructure.subset_closure

theorem definable_finiteVolumeParameterContext_iff
    {M : Type} [SpecialTransformations.Milestone0.LRV.Structure M]
    (C : SpecialTransformations.Section3.BaseContext M) (F : Set M) (hF : F.Finite)
    {n : ℕ} {A : Set (Fin n → M)} :
    ((finiteVolumeParameterContext C F hF).base : Set M).Definable
        SpecialTransformations.Milestone0.LRV A ↔
      ((C.base : Set M) ∪ F).Definable SpecialTransformations.Milestone0.LRV A :=
  definable_termClosure_iff

end IntegrationInACVF.Section7
