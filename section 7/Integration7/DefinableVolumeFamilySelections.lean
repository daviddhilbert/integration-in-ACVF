import Integration7.DefinableVFVolumeFamilies
import Integration7.MixedRVMapGraphs

/-! Every definable positive volume family has a genuine selected-label
presentation, by retaining its volume tuple as new RV labels. The old
labels and the original density are kept by a definable inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def DefinableVFVolumeFamily.toSelected (F : DefinableVFVolumeFamily C n a k) :
    SelectedVFVolumeFamily C n (a+(k+1)) k where
  domain := mixedRVMapGraph F.volume
  selected := Fin.natAdd a
  finite_selected x t := by
    apply (F.finite_volume x t).of_injOn (f := fun r => r ∘ Fin.castAdd (k+1))
    · rintro r ⟨hr,ht⟩
      let q : mixedRVMapGraph F.volume := ⟨(x,r),hr⟩
      let p := mixedRVMapGraphProjection F.volume q
      have hp : p.val=(x,r ∘ Fin.castAdd (k+1)) := mixed_rv_map_graph_projection_value F.volume q
      have hv : (F.volume p).val=r ∘ Fin.natAdd a := mixed_rv_map_graph_retained_tuple F.volume q
      exact ⟨p,hp,hv.trans ht⟩
    · rintro r ⟨hr,ht⟩ s ⟨hs,hu⟩ he
      funext i
      refine Fin.addCases (m := a) (n := k+1) (fun j => ?_) (fun j => ?_) i
      · exact congrFun he j
      · exact (congrFun ht j).trans (congrFun hu j).symm
  form := F.form.pullback (mixedRVMapGraphProjection F.volume)

theorem DefinableVFVolumeFamily.toSelected_density
    (F : DefinableVFVolumeFamily C n a k) (q : F.toSelected.domain) :
    F.toSelected.form.value q = F.form.value (mixedRVMapGraphProjection F.volume q) := rfl

theorem DefinableVFVolumeFamily.toSelected_volume
    (F : DefinableVFVolumeFamily C n a k) (q : F.toSelected.domain) :
    (F.volume (mixedRVMapGraphProjection F.volume q)).val = q.val.2 ∘ F.toSelected.selected :=
  mixed_rv_map_graph_retained_tuple F.volume q

theorem mixed_rv_map_graph_projection_append
    {S : Set M} {n a d : ℕ} {A : DefSet (rawMixedSpace (M := M) n a) S}
    (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) (p : A) :
    mixedRVMapGraphProjection g ((appendMixedRVMap g).toImage p) = p :=
  Map.inverse_apply (appendMixedRVMap g).toImage (append_mixed_rv_map_to_image_bijective g) p

end IntegrationInACVF.Section7
