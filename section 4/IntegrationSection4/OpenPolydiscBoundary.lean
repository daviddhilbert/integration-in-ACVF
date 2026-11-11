import IntegrationSection4.CellsFromFibres
import IntegrationSection4.DefinableParadigms
import IntegrationSection3ACVF.SeparationFunctions
import Section5.Assembly

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

namespace IntegrationInACVF.Section4.OpenPolydiscBoundary

open Cells BalancedFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

def domain : Set (VF (M := M)) := {1}
def position (_ : VF (M := M)) : VF (M := M) := 0
def paradigm : RV (M := M) := rv (1 : VF (M := M))
def boundaryCell : Set (VF (M := M) × VF (M := M)) := CellsFromFibres.relation domain position paradigm

theorem first_eq : first (boundaryCell (M := M)) = domain := CellsFromFibres.first_eq _ _ _

theorem raw_first : rawSet (first (boundaryCell (M := M))) = {(1 : VF (M := M)).val} := by
  rw [first_eq]
  ext z
  constructor
  · rintro ⟨x,hx,he⟩
    have hx' : x = (1 : VFType (M := M)) := hx
    rw [hx'] at he
    exact he.symm
  · intro hz
    exact ⟨(1 : VFType (M := M)),rfl,hz.symm⟩

theorem nonempty : (boundaryCell (M := M)).Nonempty := by
  refine ⟨(1,1),?_,?_⟩
  · rfl
  · change rv ((1 : VF (M := M))-0) = rv (1 : VF (M := M))
    rw [sub_zero]

theorem nonzero_paradigm : paradigm (M := M) ≠ rv (0 : VF (M := M)) := by
  intro h
  exact one_ne_zero ((rv_eq_zero_iff (1 : VF (M := M))).mp h)

theorem cellData : CellData (boundaryCell (M := M)) position paradigm := by
  apply CellsFromFibres.constant domain position paradigm (Or.inl ⟨1,rfl⟩) _ (fun _ _ _ _ => rfl)
  refine ⟨rv (1 : VF (M := M)),rv (1 : VF (M := M)),?_⟩
  intro p hp
  change p.1 = 1 ∧ rv (p.2-0) = rv (1 : VF (M := M)) at hp
  exact ⟨congrArg rv hp.1,by simpa only [sub_zero] using hp.2⟩

theorem pair_definable (G : GammaParameters.Base (M := M)) :
    DefinableOverBase G (fun _ : Fin 2 => .vf) (pairCodes (boundaryCell (M := M))) := by
  have hOne := @oneCode_definable M sM hM G.real (Fin 2)
  have hRVOne := rvConstant_definable (1 : VF (M := M)) hOne
  have hRV := @rvCode_definable M sM hM G.real (Fin 2) 1
  have hVF := ((@definableAt_iff_normalized_raw M sM hM G.real .vf _).mp
    (@definableAt_sort M sM G.real .vf)).1
  have hRaw : @Set.Definable M G.real LRV N (Fin 2)
      {z | z 0 = iVFOne ∧ iVF (z 1) ∧ rvCode (z 1) = paradigm.val} := by
    letI := N
    have hv := hVF.preimage_comp (fun _ : Fin 1 => (1 : Fin 2))
    exact ((Set.DefinableFun.proj LRV).ofPred_eq hOne).inter (hv.inter (hRV.ofPred_eq hRVOne))
  have hFull := FullBaseAtomicity.OverBase.of_real (B := GammaBaseBridge.fullBase G) hRaw
  have hFull' : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) (pairCodes (boundaryCell (M := M))) := by
    apply FullBaseAtomicity.OverBase.congr hFull
    intro z
    constructor
    · rintro ⟨hx,hv,hrv⟩
      let y : VF (M := M) := ⟨z 1,hv⟩
      have hy : rv y = paradigm := Subtype.ext (by
        change iRv (z 1) = paradigm.val
        rw [← rvCode_eq (z 1) hv]
        exact hrv)
      refine ⟨(1,y),⟨rfl,?_⟩,?_⟩
      · change rv (y-0) = paradigm
        simpa only [sub_zero] using hy
      · funext i
        fin_cases i
        · exact hx
        · rfl
    · rintro ⟨p,hp,hz⟩
      change p.1 = 1 ∧ rv (p.2-0) = paradigm at hp
      have hrv : rv p.2 = paradigm := by simpa only [sub_zero] using hp.2
      have h₀ := congrFun hz 0
      have h₁ := congrFun hz 1
      refine ⟨h₀.trans (congrArg Subtype.val hp.1),h₁.symm ▸ p.2.property,?_⟩
      rw [h₁]
      change rvCode p.2.val = paradigm.val
      rw [rvCode_eq p.2.val p.2.property]
      exact congrArg Subtype.val hrv
  apply GammaBaseDescent.to_gamma G _ _ hFull'
  rintro z ⟨p,hp,hz⟩ i
  fin_cases i
  · exact (congrFun hz 0).symm ▸ p.1.property
  · exact (congrFun hz 1).symm ▸ p.2.property

theorem position_definable (G : GammaParameters.Base (M := M)) :
    DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes (first (boundaryCell (M := M))) position) := by
  have hOne := @oneCode_definable M sM hM G.real (Fin 2)
  have hZero := @zeroCode_definable M sM hM G.real (Fin 2)
  have hRaw : @Set.Definable M G.real LRV N (Fin 2) {z | z 0 = iVFOne ∧ z 1 = iVFZero} := by
    letI := N
    exact ((Set.DefinableFun.proj LRV).ofPred_eq hOne).inter ((Set.DefinableFun.proj LRV).ofPred_eq hZero)
  have hFull := FullBaseAtomicity.OverBase.of_real (B := GammaBaseBridge.fullBase G) hRaw
  have hFull' : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G)
      (positionCodes (first (boundaryCell (M := M))) position) := by
    apply FullBaseAtomicity.OverBase.congr hFull
    intro z
    constructor
    · rintro ⟨hx,hy⟩
      refine ⟨1,?_,funext fun i => ?_⟩
      · rw [first_eq]; rfl
      · fin_cases i
        · exact hx
        · exact hy
    · rintro ⟨x,hx,hz⟩
      rw [first_eq] at hx
      exact ⟨(congrFun hz 0).trans (congrArg Subtype.val hx),congrFun hz 1⟩
  apply GammaBaseDescent.to_gamma G _ _ hFull'
  rintro z ⟨x,hx,hz⟩ i
  fin_cases i
  · exact (congrFun hz 0).symm ▸ x.property
  · exact (congrFun hz 1).symm ▸ (position x).property

theorem definable_cell (G : GammaParameters.Base (M := M)) :
    DefinableCellData G (boundaryCell (M := M)) position paradigm :=
  DefinableParadigms.cellData G _ _ _ cellData nonempty (pair_definable G) (position_definable G)

theorem first_not_open (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ¬ PaperBalls.IsOpenBall (rawSet (first (boundaryCell (M := M)))) := by
  intro h
  have hi := SeparationFunctions.open_infinite h00 δ hδ h
  apply hi
  rw [raw_first]
  exact Set.finite_singleton _

theorem not_balanced (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (u : RV (M := M)) : ¬ IsBalanced (boundaryCell (M := M)) position u paradigm :=
  fun h => first_not_open h00 δ hδ h.1

/-- The unnumbered open-polydisc assertion after 4.7 needs a boundary
qualification: the allowed first 1-cell can be a singleton. -/
theorem not_open_polydisc (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ¬ ∃ D E : Set (VF (M := M)), boundaryCell = D ×ˢ E ∧
      PaperBalls.IsOpenBall (rawSet D) ∧ PaperBalls.IsOpenBall (rawSet E) := by
  rintro ⟨D,E,hDE,hD,_⟩
  obtain ⟨p,hp⟩ := nonempty (M := M)
  have hpDE : p.1 ∈ D ∧ p.2 ∈ E := by
    change p ∈ D ×ˢ E
    exact hDE ▸ hp
  have hFirst : first (boundaryCell (M := M)) = D := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact (show q ∈ D ×ˢ E from hDE ▸ hq).1
    · intro hx
      exact ⟨(x,p.2),hDE.symm ▸ ⟨hx,hpDE.2⟩,rfl⟩
  apply first_not_open h00 δ hδ
  rwa [hFirst]

end IntegrationInACVF.Section4.OpenPolydiscBoundary
