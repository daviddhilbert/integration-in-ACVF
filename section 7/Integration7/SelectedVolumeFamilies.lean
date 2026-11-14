import Integration7.VFRVVolumeFibres
import Integration7.VolumeDensityGraphs

/-! Actual positive selected RV families over a VF base. Only fibres
with the selected labels fixed are required to be finite. Adding the
density graph preserves that precise finiteness condition. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

structure SelectedVFVolumeFamily (C : BaseContext M) (n a k : ℕ) where
  domain : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)
  selected : Fin (k + 1) → Fin a
  finite_selected : ∀ (x : Fin n → VFType (M := M)) (t : Fin (k + 1) → CanonicalRV.RVSort M),
    {r : Fin a → CanonicalRV.RVSort M | (x, r) ∈ domain.carrier ∧ r ∘ selected = t}.Finite
  form : VolumeForm domain

def SelectedVFVolumeFamily.rowObject {C : BaseContext M} (F : SelectedVFVolumeFamily C n a k)
    (x : Fin n → VFType (M := M)) :
    PositiveRVVolumeObject (M := M) ((C.base : Set M) ∪ Set.range (fun i => (x i).val)) k :=
  vfRVVolumeFibre F.form F.selected F.finite_selected x

@[simp] theorem SelectedVFVolumeFamily.rowObject_density {C : BaseContext M}
    (F : SelectedVFVolumeFamily C n a k) (x : Fin n → VFType (M := M))
    (r : (F.rowObject x).underlying.obj.domain) :
    (F.rowObject x).form.value r = F.form.value ⟨(x, r.val), r.property⟩ := rfl

@[simp] theorem SelectedVFVolumeFamily.rowObject_volume {C : BaseContext M}
    (F : SelectedVFVolumeFamily C n a k) (x : Fin n → VFType (M := M))
    (r : (F.rowObject x).underlying.obj.domain) :
    (F.rowObject x).underlying.obj.value r = r.val ∘ F.selected := rfl

def SelectedVFVolumeFamily.densityGraph {C : BaseContext M} (F : SelectedVFVolumeFamily C n a k) :
    SelectedVFVolumeFamily C n (a + 1) k where
  domain := volumeDensityGraph F.form
  selected := Fin.castAdd 1 ∘ F.selected
  finite_selected x t := by
    apply (F.finite_selected x t).of_injOn (f := fun r => r ∘ Fin.castAdd 1)
    · rintro r ⟨hr, ht⟩
      let q : volumeDensityGraph F.form := ⟨(x, r), hr⟩
      have hp := (densityGraphProjection F.form q).property
      rw [densityGraphProjection_value] at hp
      exact ⟨hp, ht⟩
    · rintro r ⟨hr, _⟩ s ⟨hs, _⟩ he
      let p : volumeDensityGraph F.form := ⟨(x, r), hr⟩
      let q : volumeDensityGraph F.form := ⟨(x, s), hs⟩
      have hpq : densityGraphProjection F.form p = densityGraphProjection F.form q :=
        Subtype.ext ((densityGraphProjection_value F.form p).trans
          ((congrArg (fun t => (x, t)) he).trans (densityGraphProjection_value F.form q).symm))
      have h := congrArg (appendDensityMap F.form).toImage hpq
      simp only [densityGraphProjection, Map.apply_inverse] at h
      exact congrArg (fun q : volumeDensityGraph F.form => q.val.2) h
  form := F.form.pullback (densityGraphProjection F.form)

theorem SelectedVFVolumeFamily.densityGraph_form_last {C : BaseContext M}
    (F : SelectedVFVolumeFamily C n a k) (q : F.densityGraph.domain) :
    F.densityGraph.form.value q = q.val.2 (Fin.last a) :=
  densityGraphPullback_form_last F.form q

end IntegrationInACVF.Section7
