import Integration7.RectangleFamilyPreparedGeometry
import Integration7.TwoCoordinateSaturation

/-! Preparing the labelled head of a rectangle family preserves
saturation of its other VF coordinate. Thus the second preparation
does not destroy the saturation established by the first. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m r : ℕ}

set_option maxHeartbeats 1200000 in
theorem rectangle_family_prepared_target_tail_saturated
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hD : IsRVPullback (carrier D)) (hTail : TailSaturated (carrier H)) :
    TailSaturated (carrier (rectangleFamilyHeadPreparation H hRect T hD).target) := by
  let P := rectangleFamilyHeadPreparation H hRect T hD
  intro b hb x hx
  obtain ⟨p,hp⟩ := P.bijective.2 ⟨b,hb⟩
  have hpTail := (rectangle_family_prepared_tail H hRect T hD p).symm.trans
    (congrArg (fun z : P.target => vfAt z.val 1) hp)
  have hx' : rv x=rv (vfAt p.val 1) := hx.trans (congrArg rv hpTail).symm
  let a : H := ⟨replace 1 p.val x,hTail p.val p.property x hx'⟩
  have haHead : coordinateProject 0 a.val=coordinateProject 0 p.val := Prod.ext (by funext i; rfl) rfl
  have hHeads := rectangle_family_prepared_head_depends_on_projection H hRect T hD a p haHead
  have hHead := congrArg (fun z : Point (M := M) 1 r => vfAt z 0) hHeads
  have hLabels := congrArg (fun z : Point (M := M) 1 r => z.2) hHeads
  have hpHead := congrArg (fun z : P.target => vfAt z.val 0) hp
  have hpLabels := congrArg (fun z : P.target => z.val.2) hp
  have hValue : (P.map a).val=replace 1 b x := by
    apply Prod.ext
    · funext i
      fin_cases i
      · exact hHead.trans hpHead
      · exact rectangle_family_prepared_tail H hRect T hD a
    · exact hLabels.trans hpLabels
  exact (congrArg (fun z => z ∈ carrier P.target) hValue).mp (P.map a).property

end IntegrationInACVF.Section7
