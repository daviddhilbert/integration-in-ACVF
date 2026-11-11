import IntegrationSection4.GammaOffsets
import IntegrationSection4.SpecialRVFibres
import IntegrationSection4.GammaDomainPreparation
import IntegrationSection4.RVLabelSlices

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.OneCellDecomposition

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def unaryFibre {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 1 m)} (P : GammaRVMap G A d) (a₀ : A) : Set (VF (M := M)) :=
  {x | ∃ a : A, vfAt a.val 0 = x ∧ P.toFun a = P.toFun a₀}

def relation {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 1 m)} (P : GammaRVMap G A d)
    (s : Point (M := M) 0 d) (q : Point (M := M) 1 0) : Prop :=
  ∃ a : A, P.toFun a = s.2 ∧ vfAt a.val 0 = vfAt q 0

theorem relation_definable {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 1 m)} (P : GammaRVMap G A d) :
    GammaGraphDefinable G (relation P) := by
  let F := GammaOffsets.dropRVMap G.real 1 m
  let hΓ := gammaLogicInput G
  have h := hΓ.comp_graph (hΓ.swap_graph P.graph) (hΓ.real_map_graph F)
  apply GammaGraphDefinable.congr h
  intro s q
  constructor
  · rintro ⟨p,⟨a,ha,hP⟩,b,hb,hq⟩
    have hba : b = ⟨a.val,Set.mem_univ _⟩ := Subtype.ext (hb.trans ha.symm)
    rw [hba] at hq
    exact ⟨a,hP,congrArg (fun p : Point (M := M) 1 0 => vfAt p 0) hq⟩
  · rintro ⟨a,hP,h₀⟩
    refine ⟨a.val,⟨a,rfl,hP⟩,⟨a.val,Set.mem_univ _⟩,rfl,?_⟩
    apply Prod.ext
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact h₀
    · exact Subsingleton.elim _ _

theorem fibre_definable {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 1 m)} (P : GammaRVMap G A d) (a₀ : A) :
    DefinableAtBase (RVLabelSlices.labelBase G (P.toFun a₀)) .vf (Cells.rawSet (unaryFibre P a₀)) := by
  have h := RVLabelSlices.vfSlice_definable G (relation P) (relation_definable P) (P.toFun a₀)
  have he : RVLabelSlices.vfSlice (relation P) (P.toFun a₀) =
      {z : Fin 1 → M | z 0 ∈ Cells.rawSet (unaryFibre P a₀)} := by
    ext z
    constructor
    · rintro ⟨q,⟨a,hP,hx⟩,hz⟩
      exact ⟨vfAt q 0,⟨a,hx,hP⟩,congrFun hz 0⟩
    · rintro ⟨x,⟨a,hx,hP⟩,he⟩
      refine ⟨(fun _ => x,Fin.elim0),⟨a,hP,hx⟩,funext fun i => ?_⟩
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      exact he
  rw [he] at h
  exact h

theorem special_fibre {G : GammaParameters.Base (M := M)} {m l : ℕ}
    {A : Set (Point (M := M) 1 m)} {E : Set (Point (M := M) 1 l)}
    (T : GammaSpecialBijection G A E) (a₀ : A) :
    unaryFibre (GammaRVMap.fromSpecial T) a₀ =
      InverseOneCells.typedBody T.special (T.special.toMap (GammaRVMap.specialSource T a₀)) := by
  ext x
  constructor
  · rintro ⟨a,hx,hP⟩
    have h := (Set.ext_iff.mp (GammaRVMap.fromSpecial_fibre T a₀) a.val).mp ⟨a,rfl,hP⟩
    change x.val ∈ InverseBodies.body T.special _
    exact hx ▸ h.1
  · rintro ⟨a,ha,hRV⟩
    let aA : A := ⟨a.val,(Set.ext_iff.mp T.source_eq a.val).mp a.property⟩
    refine ⟨aA,Subtype.ext ha,(GammaRVMap.fromSpecial_eq_iff T aA a₀).mpr ?_⟩
    exact hRV

/-- The one-cell decomposition observation immediately before 4.8,
including arbitrary old RV coordinates and full label-base definability. -/
theorem exists_map {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) {m : ℕ} (A : Set (Point (M := M) 1 m))
    (hA : GammaSetDefinable G A) :
    ∃ d : ℕ, ∃ P : GammaRVMap G A d,
      (∀ a b, P.toFun a = P.toFun b → a.val.2 = b.val.2) ∧
      ∀ a₀ : A, Cells.DefinableOneCell (RVLabelSlices.labelBase G (P.toFun a₀)) (unaryFibre P a₀) := by
  obtain ⟨l,E,T,hE⟩ := GammaDomainPreparation.prepare hs h00 G hsmall hGenerated A hA
  refine ⟨1+l,GammaRVMap.fromSpecial T,?_,?_⟩
  · intro a b he
    exact ((sameRV_iff _ _).mp (GammaRVMap.fromSpecial_reflects_rv T a b he)).2
  · intro a₀
    refine ⟨?_,fibre_definable _ a₀⟩
    rw [special_fibre]
    exact InverseOneCells.one_cell T.special
      (by simpa only [T.target_eq] using hE) _

end IntegrationInACVF.Section4.OneCellDecomposition
