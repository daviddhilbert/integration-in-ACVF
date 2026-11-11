import IntegrationSection4.BalancedFibres
import IntegrationSection3ACVF.GammaLinearity
import IntegrationSection3ACVF.MaximalOpenClasses
import Section3.GammaParameters

/-! Definitions 4.5 and 4.7 on the existing VF/RV/Gamma carriers.
Projection domains, positioning graphs and both balanced fibre identities
are explicit. Geometric cells and original-base definable cells are separate
predicates; neither definition assumes a cell-decomposition theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.Cells

open BalancedFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rawSet (D : Set (VF (M := M))) : Set M := Subtype.val '' D

def rawMap (f : VF (M := M) → VF (M := M)) (x : M) : M :=
  if hx : iVF x then (f ⟨x,hx⟩).val else iVFZero

theorem rawMap_on (f : VF (M := M) → VF (M := M)) (x : VF (M := M)) :
    rawMap f x.val = (f x).val := by
  rw [rawMap,dif_pos x.property]
  rfl

theorem rawMap_vf (f : VF (M := M) → VF (M := M)) (D : Set (VF (M := M))) :
    ∀ x ∈ rawSet D, iVF (rawMap f x) := by
  rintro _ ⟨x,_,rfl⟩
  rw [rawMap_on]
  exact (f x).property

def first (R : Set (VF (M := M) × VF (M := M))) : Set (VF (M := M)) := Prod.fst '' R
def second (R : Set (VF (M := M) × VF (M := M))) : Set (VF (M := M)) := Prod.snd '' R

def IsOneCell (D : Set (VF (M := M))) : Prop :=
  (∃ x : VF (M := M), D = {x}) ∨
    (PaperBalls.IsOpenBall (rawSet D) ∧ ∃ t : RV (M := M), ∀ x ∈ D, rv x = t)

def IsBalanced (R : Set (VF (M := M) × VF (M := M)))
    (f : VF (M := M) → VF (M := M)) (t₁ t₂ : RV (M := M)) : Prop :=
  PaperBalls.IsOpenBall (rawSet (first R)) ∧ PaperBalls.IsOpenBall (rawSet (second R)) ∧
    HasBalancedFibres (first R) (second R) R f t₁ t₂ ∧
    MaximalOpenClasses.OpenToOpen (rawSet (first R)) (rawMap f) ∧
    ∃ s : Values.Gamma (M := M),
      GammaLinearity.GammaLinear (rawSet (first R)) (rawMap f) (rawMap_vf f (first R)) s

def PositioningCase (R : Set (VF (M := M) × VF (M := M)))
    (f : VF (M := M) → VF (M := M)) (t : RV (M := M)) : Prop :=
  (∀ a ∈ first R, ∀ b ∈ first R, f a = f b) ∨
    (Set.InjOn f (first R) ∧ MaximalOpenClasses.OpenToOpen (rawSet (first R)) (rawMap f) ∧
      ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius (rawSet (f '' first R)) r ∧
        (↑(Values.vrv t) : PaperBalls.Radius (M := M)) ≤ r) ∨
    ∃ t₁ : RV (M := M), IsBalanced R f t₁ t

structure CellData (R : Set (VF (M := M) × VF (M := M)))
    (position : VF (M := M) → VF (M := M)) (paradigm : RV (M := M)) : Prop where
  rv_polydisc : ∃ t₁ t₂ : RV (M := M), ∀ p ∈ R, rv p.1 = t₁ ∧ rv p.2 = t₂
  first_cell : IsOneCell (first R)
  fibres : ∀ a ∈ first R, fibre R a = translatedRV paradigm (position a)
  positioning : PositioningCase R position paradigm

def IsTwoCell (R : Set (VF (M := M) × VF (M := M))) : Prop :=
  ∃ position : VF (M := M) → VF (M := M), ∃ paradigm : RV (M := M), CellData R position paradigm

def pairCodes (R : Set (VF (M := M) × VF (M := M))) : Set (Fin 2 → M) :=
  {z | ∃ p ∈ R, z = ![p.1.val,p.2.val]}

def positionCodes (D : Set (VF (M := M))) (position : VF (M := M) → VF (M := M)) :
    Set (Fin 2 → M) := {z | ∃ a ∈ D, z = ![a.val,(position a).val]}

def DefinableOneCell (G : GammaParameters.Base (M := M)) (D : Set (VF (M := M))) : Prop :=
  IsOneCell D ∧ GammaParameters.DefinableAtBase G .vf (rawSet D)

def DefinableCellData (G : GammaParameters.Base (M := M))
    (R : Set (VF (M := M) × VF (M := M))) (position : VF (M := M) → VF (M := M))
    (paradigm : RV (M := M)) : Prop :=
  CellData R position paradigm ∧
    GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (pairCodes R) ∧
    GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes (first R) position) ∧
    GammaParameters.DefinableAtBase G .rv {paradigm.val} ∧
    (∀ t₁, IsBalanced R position t₁ paradigm → GammaParameters.DefinableAtBase G .rv {t₁.val})

def DefinableTwoCell (G : GammaParameters.Base (M := M))
    (R : Set (VF (M := M) × VF (M := M))) : Prop :=
  ∃ position : VF (M := M) → VF (M := M), ∃ paradigm : RV (M := M),
    DefinableCellData G R position paradigm

/-- The graph assertion following Definition 4.7, for every positioning
alternative and the actual absorbing RV fibre. -/
theorem graph_of_zero_paradigm {R : Set (VF (M := M) × VF (M := M))}
    {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}
    (h : CellData R f t) (ht : t = rv (0 : VF (M := M))) :
    R = {p | p.1 ∈ first R ∧ p.2 = f p.1} := by
  ext p
  constructor
  · intro hp
    have ha : p.1 ∈ first R := ⟨p,hp,rfl⟩
    have hb : p.2 ∈ fibre R p.1 := hp
    rw [h.fibres p.1 ha,ht,translatedRV_zero] at hb
    exact ⟨ha,hb⟩
  · rintro ⟨ha,hb⟩
    change p.2 ∈ fibre R p.1
    rw [h.fibres p.1 ha,ht,translatedRV_zero]
    exact hb

end IntegrationInACVF.Section4.Cells
