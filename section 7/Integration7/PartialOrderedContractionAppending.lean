module

public import IntegrationSection5.GammaPartialContraction
public import IntegrationSection5.GammaOrderedContraction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Append a full ordered contraction to a partial contraction on its
actual remaining VF coordinates, retaining the Gamma certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {p n a b l : ℕ}

def appendPartialOrderedProgram
    {A : DefSet (M := M) S (p+n) a} {B : DefSet (M := M) S p b} {U : DefSet (M := M) S 0 l}
    (T : PartialContractionProgram S p (n := n) A B) :
    OrderedContractionProgram S B U → OrderedContractionProgram S A U := by
  induction T with
  | zero A => exact id
  | step H tail ih => exact fun E => .step H (ih E)

theorem append_partial_ordered_program_to_map
    {A : DefSet (M := M) S (p+n) a} {B : DefSet (M := M) S p b} {U : DefSet (M := M) S 0 l}
    (T : PartialContractionProgram S p (n := n) A B) (E : OrderedContractionProgram S B U) (x : A) :
    ((appendPartialOrderedProgram T E).toMap x) = E.toMap (T.toMap x) := by
  induction T with
  | zero A => rfl
  | step H tail ih => exact ih E (H.contractionMap x)

theorem gamma_append_partial_ordered_program
    {A : DefSet (M := M) S (p+n) a} {B : DefSet (M := M) S p b} {U : DefSet (M := M) S 0 l}
    (T : PartialContractionProgram S p (n := n) A B) :
    ∀ (E : OrderedContractionProgram S B U) (hT : GammaPartialProgramDefinable G T)
      (hE : GammaProgramDefinable G E), GammaProgramDefinable G (appendPartialOrderedProgram T E) := by
  induction T with
  | zero A => intro E hT hE; exact hE
  | step H tail ih =>
    intro E hT hE
    exact ⟨hT.1,hT.2.1,ih E hT.2.2 hE⟩

end IntegrationInACVF.Section7
