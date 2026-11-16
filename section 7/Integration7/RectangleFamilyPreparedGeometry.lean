module

public import Integration7.NativeRectangleFamilyStandardContractions
public import IntegrationSection5.RelativeLabelPreservation

@[expose] public section

/-! A rectangle-family preparation acts only on the labelled head
projection. Its target remains a rectangle family, including all shared
RV labels; this permits preparation of the second coordinate next. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m r : ℕ}
variable (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
variable {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
variable (hD : IsRVPullback (carrier D))

theorem rectangle_family_prepared_head_depends_on_projection (p q : H)
    (he : coordinateProject 0 p.val = coordinateProject 0 q.val) :
    coordinateProject 0 ((rectangleFamilyHeadPreparation H hRect T hD).map p).val =
      coordinateProject 0 ((rectangleFamilyHeadPreparation H hRect T hD).map q).val := by
  let U := PresentedSet.univ (pointSpace (M := M) 1 0) S
  let hSub := rectangle_family_ambient_source_subset H
  have hLeft : nativeUnaryProductLeftMap (Map.image (coordinateProjectMap 0 H)) U ⟨p.val,hSub p.property⟩ =
      nativeUnaryProductLeftMap (Map.image (coordinateProjectMap 0 H)) U ⟨q.val,hSub q.property⟩ := Subtype.ext he
  have hOut := congrArg (fun a => (T.toMap a).val) hLeft
  have hVF := congrArg Prod.fst hOut
  have hRV := congrArg Prod.snd hOut
  apply Prod.ext
  · funext i
    exact congrFun hVF 0
  · exact hRV

theorem rectangle_family_prepared_tail (p : H) :
    vfAt ((rectangleFamilyHeadPreparation H hRect T hD).map p).val 1 = vfAt p.val 1 := rfl

set_option maxHeartbeats 1600000 in
theorem rectangle_family_prepared_target_rectangular :
    RectangularRVFibres (carrier (rectangleFamilyHeadPreparation H hRect T hD).target) := by
  let P := rectangleFamilyHeadPreparation H hRect T hD
  apply rectangular_rv_fibres_of_mix
  intro b c hRV
  obtain ⟨p,hp⟩ := P.bijective.2 b
  obtain ⟨q,hq⟩ := P.bijective.2 c
  have hOld : p.val.2=q.val.2 := by
    funext i
    let j := suffixIndex (specialRelative_rvArity_le P.special) i
    have hpOld := specialRelative_oldLabels P.special p i
    have hqOld := specialRelative_oldLabels P.special q i
    have hpLabel := congrArg (fun z : P.target => z.val.2 j) hp
    have hqLabel := congrArg (fun z : P.target => z.val.2 j) hq
    exact hpOld.symm.trans (hpLabel.trans ((congrFun hRV j).trans (hqLabel.symm.trans hqOld)))
  let a : H := ⟨(![vfAt p.val 0,vfAt q.val 1],p.val.2),rectangular_rv_fibres_mix hRect p q hOld⟩
  have haHead : coordinateProject 0 a.val = coordinateProject 0 p.val := Prod.ext (by funext i; rfl) rfl
  have hHeads := rectangle_family_prepared_head_depends_on_projection H hRect T hD a p haHead
  have hHead := congrArg (fun z : Point (M := M) 1 r => vfAt z 0) hHeads
  have hLabels := congrArg (fun z : Point (M := M) 1 r => z.2) hHeads
  have hpHead := congrArg (fun z : P.target => vfAt z.val 0) hp
  have hpLabels := congrArg (fun z : P.target => z.val.2) hp
  have hqTail := congrArg (fun z : P.target => vfAt z.val 1) hq
  have hTail : vfAt (P.map a).val 1 = vfAt c.val 1 :=
    (rectangle_family_prepared_tail H hRect T hD a).trans
      ((rectangle_family_prepared_tail H hRect T hD q).symm.trans hqTail)
  have hValue : (P.map a).val = (![vfAt b.val 0,vfAt c.val 1],b.val.2) := by
    apply Prod.ext
    · funext i
      fin_cases i
      · exact hHead.trans hpHead
      · exact hTail
    · exact hLabels.trans hpLabels
  exact (congrArg (fun z => z ∈ carrier P.target) hValue).mp (P.map a).property

end IntegrationInACVF.Section7
