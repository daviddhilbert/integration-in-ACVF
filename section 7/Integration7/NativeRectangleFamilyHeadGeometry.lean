import Integration7.RVLabelRectangularFibres
import Integration7.UniformBalancedHorizontalCentres

/-! Literal geometry of a rectangle family with shared RV labels.
Once a head value belongs to the labelled head projection, membership
depends only on the other VF coordinate and those same RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {m : ℕ}

def RectangularRVFibres (H : Set (Point (M := M) 2 m)) : Prop :=
  ∀ r : Fin m → RV (M := M),
    let R := ParameterizedCells.twoFibre H r
    R = Cells.first R ×ˢ Cells.second R

theorem rectangular_rv_fibres_mix {H : Set (Point (M := M) 2 m)} (hH : RectangularRVFibres H)
    (p q : H) (hRV : p.val.2=q.val.2) : (![vfAt p.val 0,vfAt q.val 1],p.val.2) ∈ H := by
  let r := p.val.2
  have hp : (vfAt p.val 1,vfAt p.val 0) ∈ ParameterizedCells.twoFibre H r := by
    have hv : (pairPoint (vfAt p.val 1) (vfAt p.val 0)).1 = p.val.1 := by
      funext i
      fin_cases i <;> rfl
    exact (congrArg (fun x => (x,r) ∈ H) hv).mpr p.property
  have hq : (vfAt q.val 1,vfAt q.val 0) ∈ ParameterizedCells.twoFibre H r := by
    have hv : ((pairPoint (vfAt q.val 1) (vfAt q.val 0)).1,r) = q.val := by
      apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · exact hRV
    exact (congrArg (fun x => x ∈ H) hv).mpr q.property
  exact (relation_eq_projection_product_iff _).mp (hH r) _ hq _ hp

set_option maxHeartbeats 1000000 in
theorem rectangle_family_head_membership_uniform
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    (p q : Point (M := M) 2 m)
    (hp : coordinateProject 0 p ∈ carrier (Map.image (coordinateProjectMap 0 H)))
    (hq : coordinateProject 0 q ∈ carrier (Map.image (coordinateProjectMap 0 H)))
    (hRV : p.2=q.2) (hTail : vfAt p 1=vfAt q 1) : p ∈ carrier H ↔ q ∈ carrier H := by
  have forward (p q : Point (M := M) 2 m)
      (hq : coordinateProject 0 q ∈ carrier (Map.image (coordinateProjectMap 0 H)))
      (hRV : p.2=q.2) (hTail : vfAt p 1=vfAt q 1) (hpH : p ∈ carrier H) : q ∈ carrier H := by
    obtain ⟨a,ha⟩ := hq
    have haHead := congrArg (fun z : Point (M := M) 1 m => vfAt z 0) ha
    have haRV := congrArg (fun z : Point (M := M) 1 m => z.2) ha
    have hm := rectangular_rv_fibres_mix hRect a ⟨p,hpH⟩ (haRV.trans hRV.symm)
    have he : (![vfAt a.val 0,vfAt p 1],a.val.2) = q := by
      apply Prod.ext
      · funext i
        fin_cases i
        · exact haHead
        · exact hTail
      · exact haRV
    exact (congrArg (fun z => z ∈ carrier H) he).mp hm
  exact ⟨forward p q hq hRV hTail,forward q p hp hRV.symm hTail.symm⟩

end IntegrationInACVF.Section7
