module

public import Integration7.SelectedVolumeFamilies
public import Integration7.SelectedRVVFTailLifts
public import Section4.VFProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Genuine VF realizations of positive RV-valued families. The new VF
tail realizes the selected RV volume tuple, retains the original density,
and has the expected dimension bound on smaller-dimensional base loci. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d k : ℕ}

theorem selected_rv_vf_tail_lift_dim_le
    (A : DefSet (rawMixedSpace (M := M) n a) S) (ρ : Fin d → Fin a) :
    vfDim (rawRVSpace (M := M) 1) (selectedRVVFTailLift A ρ) ≤
      vfDim (rawRVSpace (M := M) 1) A + d := by
  let B := selectedRVVFTailLift A ρ
  let R := vfSelect (Fin.natAdd n : Fin d → Fin (n+d)) B
  let H := (selectedRVVFTailProjection A ρ).pair R
  have hH : Function.Injective H := by
    intro x y he
    have h := congrArg Subtype.val he
    apply Subtype.ext
    apply Prod.ext
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · exact congrArg (fun w => w.1.1 j) h
      · exact congrArg (fun w => w.2.1 j) h
    · exact congrArg (fun w => w.1.2) h
  have hA := (vfDim_le_iff (rawRVSpace (M := M) 1) A (vfDim (rawRVSpace (M := M) 1) A)).mp le_rfl
  have hR := mixed_has_dimension_bound (rawRVSpace (M := M) 1)
    (DefSet.univ (rawMixedSpace (M := M) d a) S)
  exact Nat.sInf_le (Dimension.HasDim.of_finiteFibres rawVFSpace
    (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1)) H
    (Map.finiteFibres_of_injective hH) (hA.prod (rawRVSpace (M := M) 1) hR))

def SelectedVFVolumeFamily.fullLift {C : BaseContext M} (F : SelectedVFVolumeFamily C n a k) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) (n+k) where
  arity := a
  domain := selectedRVVFTailLift (n := n) (d := k+1) F.domain F.selected
  finite_labels := selected_rv_vf_tail_lift_finite_labels F.domain F.selected F.finite_selected
  form := F.form.pullback (selectedRVVFTailProjection F.domain F.selected)

theorem SelectedVFVolumeFamily.fullLift_density {C : BaseContext M}
    (F : SelectedVFVolumeFamily C n a k) (p : F.fullLift.domain) :
    F.fullLift.form.value p = F.form.value (selectedRVVFTailProjection F.domain F.selected p) := rfl

theorem SelectedVFVolumeFamily.fullLift_dimension_le {C : BaseContext M}
    (F : SelectedVFVolumeFamily C n a k) :
    vfDim (rawRVSpace (M := M) 1) F.fullLift.domain ≤ vfDim (rawRVSpace (M := M) 1) F.domain + (k+1) :=
  selected_rv_vf_tail_lift_dim_le F.domain F.selected

theorem SelectedVFVolumeFamily.fullLift_small_of_small_domain {C : BaseContext M}
    (F : SelectedVFVolumeFamily C n a k) (hF : vfDim (rawRVSpace (M := M) 1) F.domain < n) :
    vfDim (rawRVSpace (M := M) 1) F.fullLift.domain < (n+k)+1 :=
  F.fullLift_dimension_le.trans_lt (by omega)

end IntegrationInACVF.Section7
