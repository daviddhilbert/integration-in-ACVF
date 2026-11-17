module

public import Integration7.RVLabelFocusLifts
public import IntegrationSection6.MixedCoordinatePointMaps
public import IntegrationSection5.GammaGraphOperations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The carried-label focus construction keeps complete graphs over
the original Gamma base; extra real presentation names are not promoted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m l : ℕ}

theorem gamma_retain_vf_labels_graph (H : DefSet (M := M) S n l)
    (ρ : Fin m → Fin l) (hH : GammaSetDefinable B (carrier H)) :
    GammaGraphDefinable B (pointMapGraph (retainVFLabelsMap ρ H)) := by
  let Q := mixedCoordinatePointMap (id : Fin n → Fin n) ρ B.real
  have h := (gammaLogicInput B).restrict_graph hH ((gammaLogicInput B).real_map_graph Q)
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨hp,u,rfl,he⟩
    refine ⟨⟨u.val,hp⟩,rfl,?_⟩
    exact (Prod.ext (funext fun _ => rfl) rfl).trans he
  · rintro ⟨u,rfl,he⟩
    refine ⟨u.property,⟨u.val,Set.mem_univ _⟩,rfl,?_⟩
    exact (Prod.ext (funext fun _ => rfl) rfl).trans he

theorem gamma_retain_vf_labels_preimage (ρ : Fin m → Fin l)
    (D : Set (Point (M := M) n m)) (hD : GammaSetDefinable B D) :
    GammaSetDefinable B {p : Point (M := M) n l | retainVFLabels ρ p ∈ D} := by
  let Q := mixedCoordinatePointMap (id : Fin n → Fin n) ρ B.real
  have h := (gammaLogicInput B).preimage_real Q hD
  convert h using 1
  ext p
  constructor
  · intro hp
    refine ⟨⟨p,Set.mem_univ _⟩,rfl,?_⟩
    exact hp
  · rintro ⟨u,rfl,hu⟩
    exact hu

theorem gamma_rv_label_focus_lift
    {A : DefSet (M := M) S n m} {H : DefSet (M := M) S n l}
    {j : Fin n} {k : Fin m} (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A)
    (hH : GammaSetDefinable B (carrier H)) (hD : GammaFocusDefinable B D) :
    GammaFocusDefinable B (rvLabelFocusLift D ρ hHA) := by
  refine ⟨(gammaLogicInput B).inter (gamma_retain_vf_labels_preimage ρ D.locus hD.1)
    ((gammaLogicInput B).hull hH),?_⟩
  have h := (gammaLogicInput B).comp_graph (gamma_retain_vf_labels_graph H ρ hH) hD.2
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨z,⟨u,rfl,he⟩,hz,hc⟩
    have hz' : retainVFLabels ρ u.val = z := he
    subst z
    exact ⟨⟨u.property,hz.2,subset_hull (carrier H) u.property⟩,hc⟩
  · rintro ⟨⟨hp,hOld,hHull⟩,hc⟩
    exact ⟨retainVFLabels ρ p,⟨⟨p,hp⟩,rfl,rfl⟩,⟨hHA p hp,hOld⟩,hc⟩

end IntegrationInACVF.Section7
