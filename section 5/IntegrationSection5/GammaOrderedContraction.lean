import IntegrationSection5.GammaHeadPreparation
import IntegrationSection5.OrderedContractionProgram

/-! Existence of the actual sequence of relatively special preparations in
the identity VF order, retaining original-Gamma sets and complete graphs. -/
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
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {n m : ℕ}

theorem gamma_headKey_graph (A : DefSet (M := M) S (n+1) m)
    (hA : GammaSetDefinable P (carrier A)) : GammaGraphDefinable P (pointMapGraph (headKeyMap A)) := by
  let X := PresentedSet.univ (pointSpace (M := M) (n+1) m) P.real
  apply GammaGraphDefinable.congr ((gammaLogicInput P).restrict_graph hA
    ((gammaLogicInput P).real_map_graph (headKeyMap X)))
  intro p q
  constructor
  · rintro ⟨hp,a,rfl,ha⟩
    refine ⟨⟨a.val,hp⟩,rfl,?_⟩
    exact (headKeyMap_apply A ⟨a.val,hp⟩).trans ((headKeyMap_apply X a).symm.trans ha)
  · rintro ⟨a,rfl,ha⟩
    refine ⟨a.property,⟨a.val,Set.mem_univ _⟩,rfl,?_⟩
    exact (headKeyMap_apply X ⟨a.val,Set.mem_univ _⟩).trans ((headKeyMap_apply A a).symm.trans ha)

theorem gamma_headImage (A : DefSet (M := M) S (n+1) m)
    (hA : GammaSetDefinable P (carrier A)) : GammaSetDefinable P (carrier (headImage A)) := by
  have h := (gammaLogicInput P).image_graph (gamma_headKey_graph A hA)
  convert h using 1
  ext q
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.val,a,rfl,ha⟩
  · rintro ⟨p,a,rfl,ha⟩
    exact ⟨a,ha⟩

theorem gamma_headContraction_graph {A : DefSet (M := M) S (n+1) m}
    (T : HeadPreparation A) (hT : GammaGraphDefinable P (pointMapGraph T.map))
    (hB : GammaSetDefinable P (carrier T.target)) :
    GammaGraphDefinable P (pointMapGraph T.contractionMap) := by
  have hKey : GammaGraphDefinable P (pointMapGraph (Map.toImage (headKeyMap T.target))) :=
    gamma_headKey_graph T.target hB
  exact gamma_composition_graph T.map _ hT hKey

def GammaProgramDefinable (P : GammaParameters.Base (M := M))
    {a b c : ℕ} {X : DefSet (M := M) S a b} {Y : DefSet (M := M) S 0 c} :
    OrderedContractionProgram S X Y → Prop
  | .zero A => GammaSetDefinable P (carrier A)
  | .step T tail => GammaGraphDefinable P (pointMapGraph T.map) ∧
      GammaSetDefinable P (carrier T.target) ∧ GammaProgramDefinable P tail

theorem gamma_program_final_set {a b c : ℕ} {X : DefSet (M := M) S a b} {Y : DefSet (M := M) S 0 c}
    (T : OrderedContractionProgram S X Y) (hT : GammaProgramDefinable P T) :
    GammaSetDefinable P (carrier Y) := by
  induction T with
  | zero A => exact hT
  | step T tail ih => exact ih hT.2.2

theorem gamma_program_contraction_graph {a b c : ℕ} {X : DefSet (M := M) S a b}
    {Y : DefSet (M := M) S 0 c} (T : OrderedContractionProgram S X Y)
    (hT : GammaProgramDefinable P T) : GammaGraphDefinable P (pointMapGraph T.toMap) := by
  induction T with
  | zero A => exact gamma_identity_graph A hT
  | step T tail ih =>
    exact gamma_composition_graph T.contractionMap tail.toMap
      (gamma_headContraction_graph T hT.1 hT.2.1) (ih hT.2.2)

/-- Every actual preparation stage retains its original-Gamma full graph. -/
theorem gamma_ordered_contraction_program_certified {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (P : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk P.real < κ) (F : VFFieldBase P.real)
    {S : Set M} (hPS : P.real ⊆ S) (n : ℕ) :
    ∀ {m : ℕ} (A : DefSet (M := M) S n m), GammaSetDefinable P (carrier A) →
      ∃ l, ∃ U : DefSet (M := M) S 0 l, ∃ T : OrderedContractionProgram S A U, GammaProgramDefinable P T := by
  induction n with
  | zero =>
    intro m A hA
    exact ⟨m,A,.zero A,hA⟩
  | succ n ih =>
    intro m A hA
    obtain ⟨T,_,_,hB,hT⟩ := gamma_head_preparation hs h00 P hsmall F hPS A hA
    obtain ⟨l,U,R,hR⟩ := ih T.contractedSet (gamma_headImage T.target hB)
    exact ⟨l,U,.step T R,hT,hB,hR⟩

/-- Genuine ordered preparation exists for every mixed finite arity. This
is the program part of5.5; the natural full lift is proved separately. -/
theorem gamma_ordered_contraction_program {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (P : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk P.real < κ) (F : VFFieldBase P.real)
    {S : Set M} (hPS : P.real ⊆ S) (n : ℕ) :
    ∀ {m : ℕ} (A : DefSet (M := M) S n m), GammaSetDefinable P (carrier A) →
      ∃ l, ∃ U : DefSet (M := M) S 0 l, ∃ T : OrderedContractionProgram S A U,
        GammaSetDefinable P (carrier U) ∧ GammaGraphDefinable P (pointMapGraph T.toMap) := by
  intro m A hA
  obtain ⟨l,U,T,hT⟩ := gamma_ordered_contraction_program_certified hs h00 P hsmall F hPS n A hA
  exact ⟨l,U,T,gamma_program_final_set T hT,gamma_program_contraction_graph T hT⟩

end IntegrationInACVF.Section5
