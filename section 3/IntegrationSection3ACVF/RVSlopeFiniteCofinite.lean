import IntegrationSection3ACVF.RVSlopeGraph
import Section3.RVFibreGeometry

/-! Every fixed RV slope coefficient cuts each actual nonzero value
fibre into a finite or cofinite set. Finite imaginary-code specialization
is used only inside this proof and does not alter the original graph. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVSlopeGraph

namespace IntegrationInACVF.Section3ACVF.RVSlopeFiniteCofinite

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def row (A : Set M) (f : M → M) (c : M) : Set M :=
  {t | ![t,c] ∈ slopes A f}

theorem row_definable (B : FullBaseAtomicity.Base (M := M)) {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) (c : M) :
    ∃ Q : Set M, DefinableAt Q .rv (row A f c) := by
  have hs := slopes_definable B hf
  let p := @ParameterPresentation.presentation M sM hM
  have hex : ∃ F : Set M, F.Finite ∧
      @Set.Definable M (B.real ∪ F) LRV (CanonicalStructure.normalize (M := M))
        (Fin 2) (slopes A f) := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.specialize hs
  obtain ⟨F,_,hd⟩ := hex
  let Q := insert c (B.real ∪ F)
  have hsort : row A f c ⊆ {t | iRV t} := fun t ht => ht.1.1
  refine ⟨Q,(@definableAt_iff_normalized_raw M sM hM Q .rv (row A f c)).mpr ⟨?_,hsort⟩⟩
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hdQ := hd.mono (Set.subset_insert c (B.real ∪ F))
  have hm : Q.DefinableMap LRV (fun z : Fin 1 → M => ![z 0,c]) := by
    intro i
    fin_cases i
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const (Fin 1) (Set.mem_insert c _)
  exact hdQ.preimage_map hm

theorem finite_or_cofinite (B : FullBaseAtomicity.Base (M := M)) {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (c : M) (γ : Values.Gamma (M := M)) :
    (Values.fibre (row A f c) γ).Finite ∨
      {t : CanonicalRV.RVSort M | Values.vrv t = γ.val ∧ t.val ∉ row A f c}.Finite := by
  obtain ⟨Q,hQ⟩ := row_definable B hf c
  exact rv_value_fibre_finite_or_cofinite Q (row A f c) hQ γ

end IntegrationInACVF.Section3ACVF.RVSlopeFiniteCofinite
