module

public import Integration7.RectangleFamilyPreparedGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Exact target membership for a prepared rectangle family. The two
unary factors share their original labels, recovered from the suffix
of the prepared head labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m r : ℕ}
variable (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
variable {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
variable (hD : IsRVPullback (carrier D))

theorem rectangle_family_prepared_head_value (p : H) :
    coordinateProject 0 ((rectangleFamilyHeadPreparation H hRect T hD).map p).val =
      (T.toMap ⟨coordinateProject 0 p.val,⟨p,rfl⟩⟩).val := by
  apply Prod.ext
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  · rfl

set_option maxHeartbeats 1600000 in
theorem rectangle_family_prepared_target_carrier (q : Point (M := M) 2 r) :
    q ∈ carrier (rectangleFamilyHeadPreparation H hRect T hD).target ↔
      coordinateProject 0 q ∈ carrier D ∧
      ((fun _ : Fin 1 => vfAt q 1),q.2 ∘ suffixIndex (special_chain_rvArity_le T.chain)) ∈
        carrier (Map.image (coordinateProjectMap 1 H)) := by
  let P := rectangleFamilyHeadPreparation H hRect T hD
  constructor
  · intro hq
    obtain ⟨p,hp⟩ := P.bijective.2 ⟨q,hq⟩
    have he := congrArg Subtype.val hp
    have hHead := (rectangle_family_prepared_head_value H hRect T hD p).symm.trans
      (congrArg (coordinateProject 0) he)
    refine ⟨(congrArg (fun z : Point (M := M) 1 r => z ∈ carrier D) hHead).mp
      (T.toMap ⟨coordinateProject 0 p.val,⟨p,rfl⟩⟩).property,⟨p,?_⟩⟩
    apply Prod.ext
    · funext i
      exact (rectangle_family_prepared_tail H hRect T hD p).symm.trans
        (congrArg (fun z : Point (M := M) 2 r => vfAt z 1) he)
    · funext i
      have hOld := specialRelative_oldLabels P.special p i
      have h := congrArg (fun z : Point (M := M) 2 r =>
        z.2 (suffixIndex (special_chain_rvArity_le T.chain) i)) he
      exact hOld.symm.trans h
  · rintro ⟨hHead,hTail⟩
    let d : D := ⟨coordinateProject 0 q,hHead⟩
    let a := T.inverseMap d
    have haLabels : a.val.2 = q.2 ∘ suffixIndex (special_chain_rvArity_le T.chain) := by
      funext i
      exact (special_oldLabels T a i).symm.trans
        (congrArg (fun z : D => z.val.2 (suffixIndex (special_chain_rvArity_le T.chain) i))
          (T.apply_inverse d))
    obtain ⟨c,hc⟩ := a.property
    obtain ⟨b,hb⟩ := hTail
    have hcRV := congrArg (fun z : Point (M := M) 1 m => z.2) hc
    have hbRV := congrArg (fun z : Point (M := M) 1 m => z.2) hb
    have hOld : c.val.2=b.val.2 := hcRV.trans (haLabels.trans hbRV.symm)
    let p : H := ⟨(![vfAt c.val 0,vfAt b.val 1],c.val.2),rectangular_rv_fibres_mix hRect c b hOld⟩
    have hpa : (⟨coordinateProject 0 p.val,⟨p,rfl⟩⟩ : Map.image (coordinateProjectMap 0 H)) = a :=
      Subtype.ext hc
    have hPreparedHead : coordinateProject 0 (P.map p).val = coordinateProject 0 q := by
      rw [rectangle_family_prepared_head_value H hRect T hD p,hpa,T.apply_inverse]
    have h0 := congrArg (fun z : Point (M := M) 1 r => vfAt z 0) hPreparedHead
    have hRV := congrArg (fun z : Point (M := M) 1 r => z.2) hPreparedHead
    have h1 := congrArg (fun z : Point (M := M) 1 m => vfAt z 0) hb
    have he : (P.map p).val = q := by
      apply Prod.ext
      · funext i
        fin_cases i
        · exact h0
        · exact (rectangle_family_prepared_tail H hRect T hD p).trans h1
      · exact hRV
    exact (congrArg (fun z : Point (M := M) 2 r => z ∈ carrier P.target) he).mp (P.map p).property

end IntegrationInACVF.Section7
