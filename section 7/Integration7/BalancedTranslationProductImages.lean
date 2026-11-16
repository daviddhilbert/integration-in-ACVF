module

public import Integration7.MatchedBalancedBallRestrictions
public import IntegrationSection4.BalancedBallClasses

@[expose] public section

/-! Exact product images of the two balanced translations. These
formulas use complete balanced fibres, so they apply to the matching
prepared rows and identify the entire translated domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {D E : Set (VF (M := M))} {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

theorem balanced_vertical_translation_product
    (hR : BalancedFibres.HasBalancedFibres D E R f r t) :
    (fun p : VF (M := M) × VF (M := M) => (p.1,p.2-f p.1)) '' R =
      D ×ˢ {u : VF (M := M) | rv u = t} := by
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    have ha := (hR.subset hp).1
    exact ⟨ha,(Set.ext_iff.mp (hR.vertical p.1 ha) p.2).mp hp⟩
  · rintro ⟨ha,hu⟩
    have hDiff : (q.2+f q.1)-f q.1 = q.2 := add_sub_cancel_right _ _
    refine ⟨(q.1,q.2+f q.1),?_,Prod.ext rfl hDiff⟩
    apply (Set.ext_iff.mp (hR.vertical q.1 ha) (q.2+f q.1)).mpr
    change rv ((q.2+f q.1)-f q.1) = t
    rwa [hDiff]

theorem balanced_horizontal_translation_product
    (hR : BalancedFibres.HasBalancedFibres D E R f r t)
    (hD : PaperBalls.IsOpenBall (Cells.rawSet D))
    (g : VF (M := M) → VF (M := M)) (hInv : ∀ y ∈ E, g y ∈ D ∧ f (g y) = y) :
    (fun p : VF (M := M) × VF (M := M) => (p.2,p.1-g p.2)) '' R =
      E ×ˢ {u : VF (M := M) | rv u = r} := by
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨ha,hb⟩ := hR.subset hp
    obtain ⟨hg,hfg⟩ := hInv p.2 hb
    refine ⟨hb,(Set.ext_iff.mp (hR.horizontal p.1 ha) (g p.2)).mp ⟨hg,?_⟩⟩
    change (p.1,f (g p.2)) ∈ R
    rwa [hfg]
  · rintro ⟨hb,hu⟩
    obtain ⟨hg,hfg⟩ := hInv q.1 hb
    let a := q.2+g q.1
    have hDiff : a-g q.1 = q.2 := add_sub_cancel_right _ _
    have hTag : rv (a-g q.1) = r := hDiff.symm ▸ hu
    have ha : a ∈ D := BalancedBallClasses.positive_class_subset hR hD (g q.1) hg hTag
    have hRel := ((Set.ext_iff.mp (hR.horizontal a ha) (g q.1)).mpr hTag).2
    change (a,f (g q.1)) ∈ R at hRel
    rw [hfg] at hRel
    exact ⟨(a,q.1),hRel,Prod.ext rfl hDiff⟩

end IntegrationInACVF.Section7
