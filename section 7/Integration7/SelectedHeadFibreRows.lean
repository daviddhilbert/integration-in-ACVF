import Integration7.SelectedVolumeHeadFibres
import Integration7.SelectedVolumeRowContexts
import Integration7.VolumeRelabeling
import Section4.RVIsoTools

/-! The row of the actual frozen unary family is the original row,
with its same labels and density, in a proved containing context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem head_fibre_row_context_contains (C D : BaseContext M)
    (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (y : Fin 1 → VFType (M := M)) :
    ((vfParameterVolumeContext C (Fin.cons (y 0) x)).base : Set M) ⊆
      ((vfParameterVolumeContext D y).base : Set M) := by
  have hDDy : (D.base : Set M) ⊆ ((vfParameterVolumeContext D y).base : Set M) :=
    fun _ h => vfParameterVolumeContext_contains D y (Or.inl h)
  apply Substructure.closure_le.mpr
  rintro z (hz | ⟨i,rfl⟩)
  · exact hDDy (hD (vfParameterVolumeContext_contains C x (Or.inl hz)))
  · refine Fin.cases ?_ (fun j => ?_) i
    · exact vfParameterVolumeContext_contains D y (Or.inr (Set.mem_range_self 0))
    · exact hDDy (hD (vfParameterVolumeContext_contains C x (Or.inr (Set.mem_range_self j))))

def selectedHeadFibreRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (y : Fin 1 → VFType (M := M)) :
    RVVolumeIso ((F.rowInContext (Fin.cons (y 0) x)).extend (head_fibre_row_context_contains C D x hD y))
      (((F.headFibre x).extendContext hD).rowInContext y) := by
  let U := (F.rowInContext (Fin.cons (y 0) x)).extend (head_fibre_row_context_contains C D x hD y)
  let V := ((F.headFibre x).extendContext hD).rowInContext y
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient
    (U := U.underlying) (V := V.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain
      U.underlying.obj.volume V.underlying.obj.volume rfl (fun _ => rfl))
  exact RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext D y) e
    (fun _ => rfl) (fun _ => rfl)

end IntegrationInACVF.Section7
