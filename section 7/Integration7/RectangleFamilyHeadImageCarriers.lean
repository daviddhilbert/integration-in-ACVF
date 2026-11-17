module

public import Integration7.RectangleFamilyPreparedTargetCarriers

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! After contracting the prepared head, the remaining unary domain
is the original labelled tail constrained by the entire head RV key. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m r : ℕ}

def rectangleHeadOldLabelIndex {H : DefSet (M := M) S 2 m} {D : DefSet (M := M) S 1 r}
    (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D) : Fin m → Fin (1+r) :=
  Fin.natAdd 1 ∘ suffixIndex (special_chain_rvArity_le T.chain)

set_option maxHeartbeats 1600000 in
theorem rectangle_family_head_image_carrier
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hD : IsRVPullback (carrier D)) (q : Point (M := M) 1 (1+r)) :
    q ∈ carrier (rectangleFamilyHeadPreparation H hRect T hD).contractedSet ↔
      retainVFLabels (rectangleHeadOldLabelIndex T) q ∈ carrier (Map.image (coordinateProjectMap 1 H)) ∧
      (Fin.elim0,q.2) ∈ carrier (headImage D) := by
  change q ∈ carrier (headImage (rectangleFamilyHeadPreparation H hRect T hD).target) ↔ _
  rw [headImage_carrier]
  constructor
  · rintro ⟨p,hp,hq⟩
    have h := (rectangle_family_prepared_target_carrier H hRect T hD p).mp hp
    constructor
    · have he : retainVFLabels (rectangleHeadOldLabelIndex T) q =
          ((fun _ : Fin 1 => vfAt p 1),p.2 ∘ suffixIndex (special_chain_rvArity_le T.chain)) := by
        rw [← hq]
        apply Prod.ext
        · funext i
          fin_cases i
          rfl
        · funext i
          change Fin.append (fun _ : Fin 1 => rv (vfAt p 0)) p.2
            (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) i)) =
              p.2 (suffixIndex (special_chain_rvArity_le T.chain) i)
          exact Fin.append_right _ _ _
      exact (congrArg (fun z : Point (M := M) 1 m =>
        z ∈ carrier (Map.image (coordinateProjectMap 1 H))) he).mpr h.2
    · rw [headImage_carrier]
      have hr := congrArg (fun z : Point (M := M) 1 (1+r) => z.2) hq
      exact ⟨coordinateProject 0 p,h.1,Prod.ext (Subsingleton.elim _ _) hr⟩
  · rintro ⟨hTail,hHead⟩
    rw [headImage_carrier] at hHead
    obtain ⟨d,hd,hKey⟩ := hHead
    have hRV := congrArg Prod.snd hKey
    let p : Point (M := M) 2 r := (![vfAt d 0,vfAt q 0],d.2)
    have hp : p ∈ carrier (rectangleFamilyHeadPreparation H hRect T hD).target := by
      apply (rectangle_family_prepared_target_carrier H hRect T hD p).mpr
      constructor
      · have he : coordinateProject 0 p = d := Prod.ext (by funext i; fin_cases i; rfl) rfl
        exact (congrArg (fun z : Point (M := M) 1 r => z ∈ carrier D) he).mpr hd
      · have he : ((fun _ : Fin 1 => vfAt p 1),p.2 ∘ suffixIndex (special_chain_rvArity_le T.chain)) =
            retainVFLabels (rectangleHeadOldLabelIndex T) q := by
          apply Prod.ext (by funext i; fin_cases i; rfl)
          funext i
          have hi := congrFun hRV (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) i))
          change d.2 (suffixIndex (special_chain_rvArity_le T.chain) i) =
            q.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) i))
          simpa only [headKey,Fin.append_right] using hi
        exact (congrArg (fun z : Point (M := M) 1 m =>
          z ∈ carrier (Map.image (coordinateProjectMap 1 H))) he).mpr hTail
    exact ⟨p,hp,Prod.ext (by funext i; fin_cases i; rfl) hRV⟩

end IntegrationInACVF.Section7
