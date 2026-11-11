import IntegrationSection5.StandardContraction
import Section5.GammaLiftRelation

/-! Full original-Gamma graphs of the natural contraction bijections.
The proof retains the stage certificates and reconstructs a mixed tuple
from its head and tail, with no representatives added to the Gamma base. -/
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
variable {P : GammaParameters.Base (M := M)} {S : Set M} {n m l : ℕ}

def headPointMap (A : DefSet (M := M) S (n+1) m) :
    Map A (PresentedSet.univ (pointSpace 1 0) S) :=
  Map.ofCodes A (fun p => (![vfAt p 0],Fin.elim0))
    (fun z => Sum.elim (fun _ => z (.inl 0)) Fin.elim0)
    (by intro j; cases j with
        | inl j => exact rawProj S (.inl 0 : Fin (n+1) ⊕ Fin m)
        | inr j => exact j.elim0)
    (by intro c; exact ⟨fun _ => c.property.1 0,fun j => j.elim0⟩)
    (by intro c; refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext j; fin_cases j; rfl)

theorem gamma_natural_head_tail {a b : ℕ} {A : DefSet (M := M) S a b}
    (f : Map A (PresentedSet.univ (pointSpace (n+1) l) S))
    (g : Map A (PresentedSet.univ (pointSpace 1 0) S))
    (h : Map A (PresentedSet.univ (pointSpace n l) S))
    (hg : GammaGraphDefinable P (pointMapGraph g))
    (hh : GammaGraphDefinable P (pointMapGraph h))
    (hhead : ∀ x : A, (g x).val = (![vfAt (f x).val 0],Fin.elim0))
    (htail : ∀ x : A, (h x).val = dropHead id (f x).val) :
    GammaGraphDefinable P (pointMapGraph f) := by
  let I := Map.id (PresentedSet.univ (pointSpace (M := M) a b) P.real)
  let H := headPointMap (PresentedSet.univ (pointSpace (M := M) (n+1) l) P.real)
  let R := dropHeadMap id (PresentedSet.univ (pointSpace (M := M) (n+1) l) P.real)
  apply GammaGraphDefinable.congr ((hg.preimage_maps I H).inter (hh.preimage_maps I R))
  intro p q
  constructor
  · rintro ⟨⟨x,hx,hgq⟩,⟨y,hy,hhq⟩⟩
    have he : y = x := Subtype.ext (hy.trans hx.symm)
    subst y
    refine ⟨x,hx,?_⟩
    have hhead' : vfAt (f x).val 0 = vfAt q 0 := by
      have e := congrArg (fun z : Point (M := M) 1 0 => vfAt z 0) ((hhead x).symm.trans hgq)
      exact e
    have htail' : dropHead id (f x).val = dropHead id q := (htail x).symm.trans hhq
    exact (insertHead_dropHead (f x).val).symm.trans
      ((congrArg₂ insertHead hhead' htail').trans (insertHead_dropHead q))
  · rintro ⟨x,rfl,hfq⟩
    refine ⟨⟨x,rfl,?_⟩,⟨x,rfl,?_⟩⟩
    · exact (hhead x).trans (congrArg (fun z : Point (M := M) (n+1) l => (![vfAt z 0],Fin.elim0)) hfq)
    · exact (htail x).trans (congrArg (dropHead id) hfq)

/-- Every natural map retains a full graph over the original Gamma base. -/
theorem gamma_program_natural_graph {a b c : ℕ} {A : DefSet (M := M) S a b}
    {U : DefSet (M := M) S 0 c} (hPS : P.real ⊆ S)
    (T : OrderedContractionProgram S A U) (hT : GammaProgramDefinable P T) :
    GammaGraphDefinable P (pointMapGraph T.naturalMap) := by
  induction T with
  | zero A =>
    apply GammaGraphDefinable.congr (gamma_identity_graph A hT)
    intro p q
    rfl
  | @step n m l A U T tail ih =>
    let g := postcomposeRealMap T.map
      (headPointMap (PresentedSet.univ (pointSpace (M := M) (n+1) T.arity) P.real)) hPS
    have hg : GammaGraphDefinable P (pointMapGraph g) :=
      gamma_postcompose_real (gammaLogicInput P) T.map hT.1 _ hPS
    have hh := gamma_composition_graph T.contractionMap tail.naturalMap
      (gamma_headContraction_graph T hT.1 hT.2.1) (ih hT.2.2)
    apply gamma_natural_head_tail (OrderedContractionProgram.step T tail).naturalMap g
      (Map.comp tail.naturalMap T.contractionMap) hg hh
    · intro x
      rfl
    · intro x
      exact (dropHead_insertHead _ _).symm


/-- The natural lift in any VF order has an original-Gamma full graph. -/
theorem gamma_standard_natural_graph {a b : ℕ} {A : DefSet (M := M) S a b}
    {σ : Equiv.Perm (Fin a)} (hPS : P.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable P (carrier A)) (hC : GammaProgramDefinable P C.program) :
    GammaGraphDefinable P (pointMapGraph C.naturalMap) := by
  have h := gamma_composition_graph (vfPermutationBijection A σ) C.program.naturalMap
    (gamma_vfPermutation_graph A hA σ) (gamma_program_natural_graph hPS C.program hC)
  have h' := gamma_postcompose_real (gammaLogicInput P) _ h
    (vfPermutationMap (PresentedSet.univ (pointSpace (M := M) a C.arity) P.real) σ.symm) hPS
  apply GammaGraphDefinable.congr h'
  intro p q
  rfl

/-- The all-order producer also retains the full natural-map graph. -/
theorem standard_contraction_exists_with_natural_graph {κ : Cardinal}
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (P : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk P.real < κ) (F : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (A : DefSet (M := M) S n m) (hA : GammaSetDefinable P (carrier A)) (σ : Equiv.Perm (Fin n)) :
    ∃ C : StandardContraction A σ, GammaProgramDefinable P C.program ∧
      GammaSetDefinable P (carrier C.target) ∧
      GammaGraphDefinable P (pointMapGraph C.toMap) ∧
      GammaGraphDefinable P (pointMapGraph C.naturalMap) := by
  obtain ⟨l,U,T,hT⟩ := gamma_ordered_contraction_program_certified hs h00 P hsmall F hPS n
    (vfPermutationImage A σ) (gamma_vfPermutationImage A hA σ)
  let C : StandardContraction A σ := ⟨l,U,T⟩
  refine ⟨C,hT,gamma_program_final_set T hT,?_,gamma_standard_natural_graph hPS C hA hT⟩
  exact gamma_composition_graph (vfPermutationBijection A σ) T.toMap
    (gamma_vfPermutation_graph A hA σ) (gamma_program_contraction_graph T hT)

end IntegrationInACVF.Section5
