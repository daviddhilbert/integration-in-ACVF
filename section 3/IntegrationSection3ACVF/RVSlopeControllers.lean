import IntegrationSection3ACVF.FullGammaControllers
import IntegrationSection3ACVF.RVSlopeGamma

/-! Finite order controllers for each actual RV-coefficient row. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVSlopeControllers

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem row_definable (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) (c : M) :
    FullGammaSyntax.Scalar (⟨insert c B.real,B.imaginary⟩ : FullBaseAtomicity.Base (M := M))
      {γ | RVSlopeGamma.relation A f γ c} := by
  let C : FullBaseAtomicity.Base (M := M) := ⟨insert c B.real,B.imaginary⟩
  have hG := RVSlopeGamma.graph_definable B hf
  have hGC : FullBaseAtomicity.OverBase C
      {z : Fin 2 → M | NonzeroRV (z 0) ∧ RVSlopeGamma.relation A f (codeValue (z 0)) (z 1)} :=
    FullBaseAtomicity.OverBase.mono hG (Set.subset_insert _ _) Set.Subset.rfl
  have hm : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 1) (Fin 2) C.real (fun z => ![z 0,c]) := by
    letI := CanonicalStructure.normalize (M := M)
    intro j
    fin_cases j
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const (Fin 1) (Set.mem_insert c B.real)
  have hrow := FullBaseAtomicity.OverBase.preimage_map hGC hm
  have hd : FullGammaSyntax.Definable C
      (fun a : Fin 1 → Values.Gamma (M := M) => RVSlopeGamma.relation A f (a 0) c) := by
    apply FullBaseAtomicity.OverBase.congr hrow
    intro z
    change (NonzeroRV (z 0) ∧ RVSlopeGamma.relation A f (codeValue (z 0)) c) ↔
      ((∀ j : Fin 1, NonzeroRV (z j)) ∧ RVSlopeGamma.relation A f (codeValue (z 0)) c)
    exact and_congr_left (fun _ => ⟨fun h j => by fin_cases j; exact h,fun h => h 0⟩)
  exact (FullGammaSyntax.scalar_definable_iff {γ | RVSlopeGamma.relation A f γ c}).mp hd

theorem row_controller (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M)) {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) (c : M) :
    ∃ F, FiniteOrder.Controls F {γ | RVSlopeGamma.relation A f γ c} := by
  exact FullGammaControllers.finite_controller h00 _ _ (row_definable B hf c)

end IntegrationInACVF.Section3ACVF.RVSlopeControllers
