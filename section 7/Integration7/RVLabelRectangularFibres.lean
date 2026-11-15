import Integration7.RVLabelRectanglePartitions
import IntegrationSection4.ParameterizedCells

/-! The definable RV-label partition has the claimed literal fibres:
the rectangular part is a product of its two projections, and each part
contains a whole original labelled fibre or none of it. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}

theorem relation_eq_projection_product_iff (R : Set (VF (M := M) × VF (M := M))) :
    R = Cells.first R ×ˢ Cells.second R ↔ ∀ p ∈ R, ∀ q ∈ R, (p.1,q.2) ∈ R := by
  constructor
  · intro h p hp q hq
    exact h.symm ▸ (show (p.1,q.2) ∈ Cells.first R ×ˢ Cells.second R from ⟨⟨p,hp,rfl⟩,⟨q,hq,rfl⟩⟩)
  · intro h
    ext p
    constructor
    · intro hp
      exact ⟨⟨p,hp,rfl⟩,⟨p,hp,rfl⟩⟩
    · rintro ⟨⟨x,hx,hxp⟩,⟨y,hy,hyp⟩⟩
      exact (Prod.ext hxp hyp : (x.1,y.2)=p) ▸ h x hx y hy

set_option maxHeartbeats 1000000 in
theorem nonrectangle_labels_iff_fibre_not_product (A : Set (Point (M := M) 2 m))
    (r : Fin m → RV (M := M)) :
    (Fin.elim0,r) ∈ nonrectangleRVLabels A ↔
      ParameterizedCells.twoFibre A r ≠ Cells.first (ParameterizedCells.twoFibre A r) ×ˢ
        Cells.second (ParameterizedCells.twoFibre A r) := by
  classical
  have hFlip (x : Fin 2 → VF (M := M)) : (pairPoint (x 1) (x 0)).1 = x := by
    funext i
    fin_cases i <;> rfl
  refine (nonrectangle_rv_labels_iff A r).trans ?_
  refine Iff.trans ?_ (not_congr (relation_eq_projection_product_iff (ParameterizedCells.twoFibre A r))).symm
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩ hProduct
    have hxR : (x 1,x 0) ∈ ParameterizedCells.twoFibre A r := by
      change ((pairPoint (x 1) (x 0)).1,r) ∈ A
      exact (congrArg (fun z => (z,r) ∈ A) (hFlip x)).mpr hx
    have hyR : (y 1,y 0) ∈ ParameterizedCells.twoFibre A r := by
      change ((pairPoint (y 1) (y 0)).1,r) ∈ A
      exact (congrArg (fun z => (z,r) ∈ A) (hFlip y)).mpr hy
    exact hxy (hProduct (y 1,y 0) hyR (x 1,x 0) hxR)
  · intro hNot
    push_neg at hNot
    obtain ⟨p,hp,q,hq,hpq⟩ := hNot
    exact ⟨(pairPoint q.1 q.2).1,(pairPoint p.1 p.2).1,hq,hp,hpq⟩

theorem rectangular_part_fibre (A : Set (Point (M := M) 2 m)) (r : Fin m → RV (M := M)) :
    ParameterizedCells.twoFibre (rectangularRVPart A) r =
      if (Fin.elim0,r) ∈ nonrectangleRVLabels A then ∅ else ParameterizedCells.twoFibre A r := by
  classical
  by_cases h : (Fin.elim0,r) ∈ nonrectangleRVLabels A <;>
    ext p <;> simp only [ParameterizedCells.twoFibre,rectangularRVPart,Set.mem_setOf_eq,
      Set.mem_sdiff,h,ite_true,ite_false,Set.mem_empty_iff_false,and_false,and_true,not_true_eq_false,not_false_eq_true]

theorem nonrectangular_part_fibre (A : Set (Point (M := M) 2 m)) (r : Fin m → RV (M := M)) :
    ParameterizedCells.twoFibre (nonrectangularRVPart A) r =
      if (Fin.elim0,r) ∈ nonrectangleRVLabels A then ParameterizedCells.twoFibre A r else ∅ := by
  classical
  by_cases h : (Fin.elim0,r) ∈ nonrectangleRVLabels A <;>
    ext p <;> simp only [ParameterizedCells.twoFibre,nonrectangularRVPart,Set.mem_setOf_eq,
      Set.mem_inter_iff,h,ite_true,ite_false,Set.mem_empty_iff_false,and_false,and_true]

theorem rectangular_part_fibre_is_product (A : Set (Point (M := M) 2 m)) (r : Fin m → RV (M := M)) :
    let R := ParameterizedCells.twoFibre (rectangularRVPart A) r
    R = Cells.first R ×ˢ Cells.second R := by
  classical
  intro R
  by_cases h : (Fin.elim0,r) ∈ nonrectangleRVLabels A
  · have hR : R = ∅ := (rectangular_part_fibre A r).trans (if_pos h)
    rw [hR]
    exact (relation_eq_projection_product_iff _).mpr (fun p hp => False.elim hp)
  · have hR : R = ParameterizedCells.twoFibre A r := (rectangular_part_fibre A r).trans (if_neg h)
    have hProduct := not_not.mp (fun hn => h ((nonrectangle_labels_iff_fibre_not_product A r).mpr hn))
    exact hR.trans (hProduct.trans (congrArg (fun Q => Cells.first Q ×ˢ Cells.second Q) hR.symm))

end IntegrationInACVF.Section7
