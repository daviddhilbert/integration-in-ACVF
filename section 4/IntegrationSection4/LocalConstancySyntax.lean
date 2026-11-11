import IntegrationSection3ACVF.OpenImageConfigurations
import IntegrationSection3ACVF.ParameterizedOpenImages
import IntegrationSection3ACVF.FullBaseLogic
import IntegrationSection4.RadiusPreparationGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.LocalConstancySyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def constantBall (A : Set M) (f : M → M) (q : Fin 4 → M) : Prop :=
  q ∈ BallKindPredicates.openCodes ∧ ∃ y : Fin 1 → M, ∀ x : Fin 1 → M,
    x 0 ∈ OpenImageConfigurations.body q → x 0 ∈ A ∧ y 0 = f (x 0)

def locus (A : Set M) (f : M → M) : Set M :=
  {x | ∃ q : Fin 4 → M, constantBall A f q ∧ x ∈ OpenImageConfigurations.body q}

theorem constantBall_definable (B : FullBaseAtomicity.Base (M := M)) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B {q | constantBall A f q} := by
  let ι := (Fin 4 ⊕ Fin 1) ⊕ Fin 1
  have hm := FullBaseAtomicity.OverBase.preimage_comp (OpenImageConfigurations.body_definable B)
    (Sum.elim (fun i => .inl (.inl i)) Sum.inr : Fin 4 ⊕ Fin 1 → ι)
  have hg := FullBaseAtomicity.OverBase.preimage_comp hf (![.inr 0,.inl (.inr 0)] : Fin 2 → ι)
  have h := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.implication B hm hg))
  have ho := FullBaseAtomicity.OverBase.of_real (B := B) (BallKindPredicates.chartCodes_definable B.real).1
  exact FullBaseAtomicity.OverBase.inter ho h

theorem locus_definable (B : FullBaseAtomicity.Base (M := M)) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ locus A f} := by
  let ι := Fin 1 ⊕ Fin 4
  have hc := FullBaseAtomicity.OverBase.preimage_comp (constantBall_definable B A f hf) (Sum.inr : Fin 4 → ι)
  have hm := FullBaseAtomicity.OverBase.preimage_comp (OpenImageConfigurations.body_definable B)
    (Sum.elim Sum.inr Sum.inl : Fin 4 ⊕ Fin 1 → ι)
  exact FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hc hm)

theorem mem_iff (A : Set M) (f : M → M) (x : M) : x ∈ locus A f ↔
    ∃ D : Set M, PaperBalls.IsOpenBall D ∧ x ∈ D ∧ D ⊆ A ∧ ∀ y ∈ D, f y = f x := by
  constructor
  · rintro ⟨q,⟨hq,v,hv⟩,hx⟩
    exact ⟨OpenImageConfigurations.body q,OpenImageConfigurations.body_open q hq,hx,
      fun y hy => (hv ![y] hy).1,fun y hy => (hv ![y] hy).2.symm.trans (hv ![x] hx).2⟩
  · rintro ⟨D,hD,hx,hDA,hConst⟩
    obtain ⟨q,hq,hbody⟩ := ParameterizedOpenImages.exists_open_code hD
    refine ⟨q,⟨hq,![f x],?_⟩,hbody.symm ▸ hx⟩
    intro y hy
    exact ⟨hDA (hbody ▸ hy),(hConst (y 0) (hbody ▸ hy)).symm⟩

theorem subset (A : Set M) (f : M → M) : locus A f ⊆ A := by
  intro x hx
  obtain ⟨D,_,hxD,hDA,_⟩ := (mem_iff A f x).mp hx
  exact hDA hxD

end IntegrationInACVF.Section4.LocalConstancySyntax
