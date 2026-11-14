import IntegrationSection4.BalancedBallClasses
import Mathlib.Logic.Equiv.Set

/-! The two actual translation bijections of a balanced two-cell onto
the product domains used in the two opposite contraction orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.BalancedFibres
open IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {D E : Set (VF (M := M))} {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

def balancedPositionEquiv (h : HasBalancedFibres D E R f r t) : D ≃ E :=
  h.bijective.equiv f

theorem balanced_position_inverse_value (h : HasBalancedFibres D E R f r t) (b : E) :
    f ((balancedPositionEquiv h).symm b).val = b.val :=
  congrArg Subtype.val ((balancedPositionEquiv h).apply_symm_apply b)

def balancedVerticalTranslationEquiv (h : HasBalancedFibres D E R f r t) :
    R ≃ D × {z : VF (M := M) | rv z = t} where
  toFun p := (⟨p.val.1,(h.subset p.property).1⟩,
    ⟨p.val.2-f p.val.1,(Set.ext_iff.mp (h.vertical p.val.1 (h.subset p.property).1) p.val.2).mp p.property⟩)
  invFun q := ⟨(q.1.val,q.2.val+f q.1.val),by
    apply (Set.ext_iff.mp (h.vertical q.1.val q.1.property) _).mpr
    change rv (q.2.val+f q.1.val-f q.1.val) = t
    rw [add_sub_cancel_right]
    exact q.2.property⟩
  left_inv p := Subtype.ext (Prod.ext (by rfl) (sub_add_cancel _ _))
  right_inv q := Prod.ext (Subtype.ext rfl) (Subtype.ext (add_sub_cancel_right _ _))

def balancedHorizontalTranslationEquiv (h : HasBalancedFibres D E R f r t)
    (hD : IntegrationInACVF.Section3ACVF.PaperBalls.IsOpenBall (rawSet D)) :
    R ≃ {z : VF (M := M) | rv z = r} × E where
  toFun p := by
    let b : E := ⟨p.val.2,(h.subset p.property).2⟩
    let a := (balancedPositionEquiv h).symm b
    have hR : f a.val ∈ fibre R p.val.1 :=
      (balanced_position_inverse_value h b).symm ▸ p.property
    have hr := (Set.ext_iff.mp (h.horizontal p.val.1 (h.subset p.property).1) a.val).mp ⟨a.property,hR⟩
    exact (⟨p.val.1-a.val,hr⟩,b)
  invFun q := by
    let a := (balancedPositionEquiv h).symm q.2
    have hr : rv (q.1.val+a.val-a.val) = r := by
      rw [add_sub_cancel_right]
      exact q.1.property
    have hA : q.1.val+a.val ∈ D := BalancedBallClasses.positive_class_subset h hD a.val a.property hr
    have hR := ((Set.ext_iff.mp (h.horizontal (q.1.val+a.val) hA) a.val).mpr hr).2
    exact ⟨(q.1.val+a.val,q.2.val),(balanced_position_inverse_value h q.2) ▸ hR⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (sub_add_cancel _ _) rfl
  right_inv q := by
    apply Prod.ext
    · exact Subtype.ext (add_sub_cancel_right _ _)
    · exact Subtype.ext rfl

theorem balanced_vertical_translation_value
    (h : HasBalancedFibres D E R f r t) (p : R) :
    ((balancedVerticalTranslationEquiv h p).1.val,(balancedVerticalTranslationEquiv h p).2.val) =
      (p.val.1,p.val.2-f p.val.1) := rfl

theorem balanced_horizontal_translation_value
    (h : HasBalancedFibres D E R f r t)
    (hD : IntegrationInACVF.Section3ACVF.PaperBalls.IsOpenBall (rawSet D)) (p : R) :
    ((balancedHorizontalTranslationEquiv h hD p).1.val,(balancedHorizontalTranslationEquiv h hD p).2.val) =
      (p.val.1-((balancedPositionEquiv h).symm ⟨p.val.2,(h.subset p.property).2⟩).val,p.val.2) := rfl

end IntegrationInACVF.Section7
