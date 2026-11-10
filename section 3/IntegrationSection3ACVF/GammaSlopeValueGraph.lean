import IntegrationSection3ACVF.FullGammaControllers
import IntegrationSection3ACVF.RVSlopeGamma

/-! The Gamma value of the descended RV coefficient has a full definable
Gamma graph. Every fixed output row has a finite order controller over
real parameters obtained only inside its proof. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.GammaSlopeValueGraph

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def valueRelation (A : Set M) (f : M → M)
    (γ η : Values.Gamma (M := M)) : Prop := ∃ c : M, RVSlopeGamma.relation A f γ c ∧ codeValue c = η

theorem definable (B : FullBaseAtomicity.Base (M := M)) {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullGammaSyntax.Definable B (fun a : Fin 2 → Values.Gamma (M := M) => valueRelation A f (a 0) (a 1)) := by
  have hG := RVSlopeGamma.graph_definable B hf
  have hSame : FullBaseAtomicity.OverBase B {z : Fin 2 → M | SameScalar (z 0) (z 1)} := by
    apply FullBaseAtomicity.OverBase.of_real
    have he : {z : Fin 2 → M |
        @SameScalar M (CanonicalStructure.normalize (M := M)) (z 0) (z 1)} =
        {z | @SameScalar M sM (z 0) (z 1)} := Set.ext (fun z => same_scalar_normalize _ _)
    exact he ▸ @same_scalar_definable M (CanonicalStructure.normalize (M := M)) B.real
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hG
      (![.inl 0,.inr 0] : Fin 2 → Fin 2 ⊕ Fin 1))
    (FullBaseAtomicity.OverBase.preimage_comp hSame
      (![.inr 0,.inl 1] : Fin 2 → Fin 2 ⊕ Fin 1)))
  change FullBaseAtomicity.OverBase B _
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ c : Fin 1 → M, (NonzeroRV (z 0) ∧ RVSlopeGamma.relation A f (codeValue (z 0)) (c 0)) ∧
      SameScalar (c 0) (z 1)) ↔
    (GammaSyntax.Proper z ∧ ∃ c : M, RVSlopeGamma.relation A f (codeValue (z 0)) c ∧
      codeValue c = codeValue (z 1))
  constructor
  · rintro ⟨c,⟨ha,hc⟩,hSame⟩
    refine ⟨?_,c 0,hc,hSame.codeValue_eq⟩
    intro i
    fin_cases i
    · exact ha
    · exact hSame.2.1
  · rintro ⟨hz,c,hc,he⟩
    have hcNZ : NonzeroRV c := by
      obtain ⟨t,_,ht⟩ := hc
      exact ht.2.1
    exact ⟨![c],⟨hz 0,hc⟩,hcNZ,hz 1,
      (original_le_codeValue_iff c (z 1) hcNZ (hz 1)).mpr he.le,
      (original_le_codeValue_iff (z 1) c (hz 1) hcNZ).mpr he.symm.le⟩

theorem row_controller (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M)) {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (η : Values.Gamma (M := M)) :
    ∃ F, FiniteOrder.Controls F {γ | valueRelation A f γ η} := by
  let C := B.adjoin (Sum.inr η)
  have hP := definable B hf
  have hPC : FullGammaSyntax.Definable C
      (fun a : Fin 2 → Values.Gamma (M := M) => valueRelation A f (a 0) (a 1)) :=
    FullBaseAtomicity.OverBase.mono hP Set.Subset.rfl (Set.subset_insert _ _)
  have hη : FullGammaSyntax.Scalar C {η} := AdjoinGamma.named_scalar η (Set.mem_insert _ _)
  have hrow := FullGammaControllers.fix_last C hPC η hη
  have hrow' : FullGammaSyntax.Definable C
      (fun a : Fin 1 → Values.Gamma (M := M) => valueRelation A f (a 0) η) :=
    hrow.congr (fun _ => Iff.rfl)
  exact FullGammaControllers.finite_controller h00 C {γ | valueRelation A f γ η}
    ((FullGammaSyntax.scalar_definable_iff _).mp hrow')

end IntegrationInACVF.Section3ACVF.GammaSlopeValueGraph
