import IntegrationSection3ACVF.FullRVValueFibres

/-! Restrict an actual partial RV graph to an entire value fibre after
adjoining just that Gamma name. Every old parameter is retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullRVClassRestriction

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem graph_definable (B : FullBaseAtomicity.Base (M := M)) (U : Set M) (g : M → M)
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn U g))
    (γ : Values.Gamma (M := M)) (hSub : FullRVValueFibres.fibre γ ⊆ U) :
    FullBaseAtomicity.OverBase (B.adjoin (Sum.inr γ)) (ImaginaryBaseImages.graphOn (FullRVValueFibres.fibre γ) g) := by
  let C := B.adjoin (Sum.inr γ)
  have hGC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn U g) :=
    FullBaseAtomicity.OverBase.mono hG Set.Subset.rfl (Set.subset_insert _ _)
  have hγ : FullBaseAtomicity.OverBase C {z : Fin 1 → M | z 0 ∈ FullRVValueFibres.fibre γ} :=
    AdjoinGamma.named_scalar γ (Set.mem_insert _ _)
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hGC
    (FullBaseAtomicity.OverBase.preimage_comp hγ (fun _ => (0 : Fin 2))))
  intro z
  change ((z 0 ∈ U ∧ z 1 = g (z 0)) ∧ z 0 ∈ FullRVValueFibres.fibre γ) ↔
    (z 0 ∈ FullRVValueFibres.fibre γ ∧ z 1 = g (z 0))
  exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hSub h.1,h.2⟩,h.1⟩⟩

end IntegrationInACVF.Section3ACVF.FullRVClassRestriction
