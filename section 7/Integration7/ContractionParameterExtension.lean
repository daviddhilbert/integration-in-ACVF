module

public import IntegrationSection5.StandardContraction
public import IntegrationSection5.HeadPreparationExtension

@[expose] public section

/-! Parameter enlargement preserves the actual head preparations and
ordered/standard contraction programs. No new preparation is chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S R : Set M} {n a b : ℕ}

def OrderedContractionProgram.extendBase (hSR : S ⊆ R) :
    {n a b : ℕ} → {A : DefSet (M := M) S n a} → {U : DefSet (M := M) S 0 b} →
    OrderedContractionProgram S A U →
      OrderedContractionProgram R (SpecialTransformations.Section5.extendBase A hSR)
        (SpecialTransformations.Section5.extendBase U hSR)
  | _,_,_,_,_,.zero A => .zero (SpecialTransformations.Section5.extendBase A hSR)
  | _,_,_,_,_,.step T tail => .step (T.extendBase hSR) (tail.extendBase hSR)

theorem OrderedContractionProgram.extendBase_value (hSR : S ⊆ R)
    {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 b}
    (T : OrderedContractionProgram S A U) (p : SpecialTransformations.Section5.extendBase A hSR) :
    ((T.extendBase hSR).toMap p).val = (T.toMap ⟨p.val,p.property⟩).val := by
  induction T with
  | zero A => rfl
  | step T tail ih => exact ih _

theorem OrderedContractionProgram.extendBase_gamma {P : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
    (hSR : S ⊆ R) {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 b}
    (T : OrderedContractionProgram S A U) (hT : GammaProgramDefinable P T) :
    GammaProgramDefinable P (T.extendBase hSR) := by
  induction T with
  | zero A => exact hT
  | step T tail ih => exact ⟨hT.1,hT.2.1,ih hT.2.2⟩

theorem OrderedContractionProgram.extendBase_volumeIndex (hSR : S ⊆ R)
    {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 b}
    (T : OrderedContractionProgram S A U) (i : Fin n) :
    (T.extendBase hSR).volumeIndex i = T.volumeIndex i := by
  induction T with
  | zero A => exact Fin.elim0 i
  | step T tail ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih i

def StandardContraction.extendBase {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (hSR : S ⊆ R) :
    StandardContraction (SpecialTransformations.Section5.extendBase A hSR) σ where
  arity := T.arity
  target := SpecialTransformations.Section5.extendBase T.target hSR
  program := T.program.extendBase hSR

theorem StandardContraction.extendBase_value {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (hSR : S ⊆ R) (p : SpecialTransformations.Section5.extendBase A hSR) :
    ((T.extendBase hSR).toMap p).val = (T.toMap ⟨p.val,p.property⟩).val :=
  T.program.extendBase_value hSR _

theorem StandardContraction.extendBase_volumeIndex {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (hSR : S ⊆ R) (i : Fin n) :
    (T.extendBase hSR).volumeIndex i = T.volumeIndex i :=
  T.program.extendBase_volumeIndex hSR _

end IntegrationInACVF.Section5
