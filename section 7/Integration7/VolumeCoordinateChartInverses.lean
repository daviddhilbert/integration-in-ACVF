module

public import Integration7.SelectedIntegralCoordinateCharts
public import Integration7.FiniteVolumeIsoMaps

@[expose] public section

/-! Inverse formulas for finite volume coordinate charts, with the
common coordinate permutation and unchanged density kept explicit. -/
noncomputable section
open CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem finite_volume_coordinate_chart_inverse
    {U V : PositiveRVVolumeObject (M := M) S k} (f : U.underlying ≅ V.underlying)
    (e : Equiv.Perm (Fin (k+1)))
    (h : ∀ u, V.underlying.obj.value (finiteIsoMap f u) = U.underlying.obj.value u ∘ e)
    (v : V.underlying.obj.domain) :
    U.underlying.obj.value (finiteIsoMap f.symm v) = V.underlying.obj.value v ∘ e.symm := by
  funext i
  have h' := congrFun (h (finiteIsoMap f.symm v)) (e.symm i)
  simpa only [finiteIsoMap_apply_symm,Function.comp_apply,e.apply_symm_apply] using h'.symm

theorem finite_volume_density_chart_inverse
    {U V : PositiveRVVolumeObject (M := M) S k} (f : U.underlying ≅ V.underlying)
    (h : ∀ u, V.form.value (finiteIsoMap f u) = U.form.value u)
    (v : V.underlying.obj.domain) :
    U.form.value (finiteIsoMap f.symm v) = V.form.value v := by
  simpa only [finiteIsoMap_apply_symm] using (h (finiteIsoMap f.symm v)).symm

end IntegrationInACVF.Section7
