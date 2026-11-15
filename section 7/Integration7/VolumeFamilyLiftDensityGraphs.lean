import Integration7.SelectedFamilyFullLifts
import Integration7.VFVolumeBijections

/-! Taking the density graph commutes with realizing the selected RV
tuple by a full VF tail, through an actual VF-preserving volume bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

theorem selected_family_full_lift_density_graph_carrier
    (F : SelectedVFVolumeFamily C n a k) :
    F.fullLift.densityGraph.domain.carrier = F.densityGraph.fullLift.domain.carrier := by
  ext w
  constructor
  · rintro ⟨p,rfl⟩
    apply (mem_selected_rv_vf_tail_lift F.densityGraph.domain F.densityGraph.selected _).mpr
    constructor
    · exact ⟨selectedRVVFTailProjection F.domain F.selected p,rfl⟩
    · have h := (mem_selected_rv_vf_tail_lift F.domain F.selected p.val).mp p.property
      change tupleRV (p.val.1 ∘ Fin.natAdd n) =
        Fin.append p.val.2 (F.fullLift.form.map p).val ∘ (Fin.castAdd 1 ∘ F.selected)
      funext i
      simpa only [Function.comp_apply,Fin.append_left] using congrFun h.2 i
  · intro hw
    have h := (mem_selected_rv_vf_tail_lift F.densityGraph.domain F.densityGraph.selected w).mp hw
    obtain ⟨u,hu⟩ := h.1
    change (u.val.1,Fin.append u.val.2 (F.form.map u).val) = (w.1 ∘ Fin.castAdd (k+1),w.2) at hu
    have hx := congrArg Prod.fst hu
    have hr := congrArg Prod.snd hu
    change u.val.1 = w.1 ∘ Fin.castAdd (k+1) at hx
    change Fin.append u.val.2 (F.form.map u).val = w.2 at hr
    have hA : (w.1 ∘ Fin.castAdd (k+1),u.val.2) ∈ F.domain.carrier := by
      rw [← hx]
      exact u.property
    have hρ : w.2 ∘ F.densityGraph.selected = u.val.2 ∘ F.selected := by
      funext i
      change w.2 (Fin.castAdd 1 (F.selected i)) = u.val.2 (F.selected i)
      simpa only [Fin.append_left] using (congrFun hr (Fin.castAdd 1 (F.selected i))).symm
    let p : F.fullLift.domain := ⟨(w.1,u.val.2),
      (mem_selected_rv_vf_tail_lift F.domain F.selected _).mpr ⟨hA,h.2.trans hρ⟩⟩
    have hProj : selectedRVVFTailProjection F.domain F.selected p = u :=
      Subtype.ext (Prod.ext hx.symm rfl)
    refine ⟨p,?_⟩
    change (w.1,Fin.append u.val.2 (F.fullLift.form.map p).val) = w
    have hLabels : Fin.append u.val.2 (F.fullLift.form.map p).val = w.2 := by
      calc
        Fin.append u.val.2 (F.fullLift.form.map p).val = Fin.append u.val.2 (F.form.map u).val := by
          change Fin.append u.val.2 (F.form.map (selectedRVVFTailProjection F.domain F.selected p)).val = _
          rw [hProj]
        _ = w.2 := hr
    exact Prod.ext rfl hLabels

def selectedFamilyFullLiftDensityGraphBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k) :
    VFVolumeBijection F.fullLift.densityGraph F.densityGraph.fullLift := by
  let h := selected_family_full_lift_density_graph_carrier F
  let f : Map F.fullLift.densityGraph.domain F.densityGraph.fullLift.domain := Map.inclusion h.le
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      have hv := congrArg Subtype.val he
      exact Subtype.ext hv
    · intro p
      exact ⟨⟨p.val,h.ge p.property⟩,rfl⟩
  refine VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl) ?_
  intro p
  calc
    F.fullLift.densityGraph.form.value p = p.val.2 (Fin.last a) := densityGraph_form_last F.fullLift p
    _ = F.densityGraph.fullLift.form.value (f p) :=
      (densityGraphPullback_form_last F.form
        (selectedRVVFTailProjection F.densityGraph.domain F.densityGraph.selected (f p))).symm

def volumeFamilyFullLiftGraphBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k) :
    VFVolumeBijection F.fullLift F.densityGraph.fullLift :=
  (volumeDensityGraphBijection hc C F.fullLift).trans hc C (selectedFamilyFullLiftDensityGraphBijection hc F)

end IntegrationInACVF.Section7
