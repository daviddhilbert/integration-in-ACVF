import IntegrationSection5.PartialNaturalMap
import IntegrationSection5.NaturalContractionGamma

/-! Uniform partial contractions retain their original Gamma base and
leave every complementary VF parameter fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {p n m l : ℕ}

def GammaPartialProgramDefinable (P : GammaParameters.Base (M := M))
    {a b c : ℕ} {X : DefSet (M := M) S (p+a) b} {Y : DefSet (M := M) S p c}
    (T : PartialContractionProgram S p (n := a) X Y) : Prop := by
  induction T with
  | zero A => exact GammaSetDefinable P (carrier A)
  | step T tail ih => exact GammaGraphDefinable P (pointMapGraph T.map) ∧
      GammaSetDefinable P (carrier T.target) ∧ ih

theorem gamma_partial_program_final_set {a b c : ℕ} {X : DefSet (M := M) S (p+a) b}
    {Y : DefSet (M := M) S p c} (T : PartialContractionProgram S p (n := a) X Y)
    (hT : GammaPartialProgramDefinable P T) : GammaSetDefinable P (carrier Y) := by
  induction T with
  | zero A => exact hT
  | step T tail ih => exact ih hT.2.2

theorem gamma_partial_program_contraction_graph {a b c : ℕ} {X : DefSet (M := M) S (p+a) b}
    {Y : DefSet (M := M) S p c} (T : PartialContractionProgram S p (n := a) X Y)
    (hT : GammaPartialProgramDefinable P T) : GammaGraphDefinable P (pointMapGraph T.toMap) := by
  induction T with
  | zero A => exact gamma_identity_graph A hT
  | step T tail ih =>
    exact gamma_composition_graph T.contractionMap tail.toMap
      (gamma_headContraction_graph T hT.1 hT.2.1) (ih hT.2.2)

theorem gamma_partial_program_natural_graph {a b c : ℕ} {X : DefSet (M := M) S (p+a) b}
    {Y : DefSet (M := M) S p c} (hPS : P.real ⊆ S) (T : PartialContractionProgram S p (n := a) X Y)
    (hT : GammaPartialProgramDefinable P T) : GammaGraphDefinable P (pointMapGraph T.naturalMap) := by
  induction T with
  | zero A =>
    apply GammaGraphDefinable.congr (gamma_identity_graph A hT)
    intro x y
    rfl
  | @step n m l A U T tail ih =>
    let g := postcomposeRealMap T.map
      (headPointMap (PresentedSet.univ (pointSpace (M := M) ((p+n)+1) T.arity) P.real)) hPS
    have hg : GammaGraphDefinable P (pointMapGraph g) :=
      gamma_postcompose_real (gammaLogicInput P) T.map hT.1 _ hPS
    have hh := gamma_composition_graph T.contractionMap tail.naturalMap
      (gamma_headContraction_graph T hT.1 hT.2.1) (ih hT.2.2)
    apply gamma_natural_head_tail (PartialContractionProgram.step T tail).naturalMap g
      (Map.comp tail.naturalMap T.contractionMap) hg hh
    · intro x
      rfl
    · intro x
      exact (dropHead_insertHead _ _).symm

/-- The number of active variables is finite; the frozen parameters remain
free in one actual original-base construction, without a compactness premise. -/
theorem gamma_partial_contraction_program {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (P : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk P.real < κ) (F : VFFieldBase P.real) (hPS : P.real ⊆ S) (p n : ℕ) :
    ∀ {m : ℕ} (A : DefSet (M := M) S (p+n) m), GammaSetDefinable P (carrier A) →
      ∃ l, ∃ U : DefSet (M := M) S p l, ∃ T : PartialContractionProgram S p (n := n) A U,
        GammaPartialProgramDefinable P T := by
  induction n with
  | zero =>
    intro m A hA
    exact ⟨m,A,.zero A,hA⟩
  | succ n ih =>
    intro m A hA
    obtain ⟨T,_,_,hB,hT⟩ := gamma_head_preparation hs h00 P hsmall F hPS A hA
    obtain ⟨l,U,R,hR⟩ := ih T.contractedSet (gamma_headImage T.target hB)
    exact ⟨l,U,.step T R,hT,hB,hR⟩

end IntegrationInACVF.Section5
