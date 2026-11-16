module

public import Integration7.VolumeFamilyLiftDensityGraphs
public import Integration7.CanonicalVolumeFamilyIntegrals
public import Integration7.VolumeFamilyBaseExceptions
public import Integration7.ConstantCoordinateDensityObjects
public import Integration7.AllDegreeVFVolumeClassProducts

@[expose] public section

/-! The canonical native realization and the literal full VF family
lift agree, with the density graph and arithmetic degree identifications
made explicit. This connects cofull base restriction to the family integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (VF RV carrier)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem native_coordinate_volume_objects_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M} {p q a : ℕ} (h : p=q)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (p+1) a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (q+1) a)
    (hAB : B = nativeVFArityCast (congrArg Nat.succ h) A)
    (hfinA : ∀ x : Fin (p+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin (q+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B)) (δ : Fin a)
    (hω : ∀ x, ω.value x = x.val.2 δ) (hπ : ∀ x, π.value x = x.val.2 δ) :
    HEq (nativeMixedVFVolumeObject hc A hfinA ω) (nativeMixedVFVolumeObject hc B hfinB π) := by
  subst B
  cases h
  have hForm : ω=π := volume_form_eq_of_value_eq (fun x => (hω x).trans (hπ x).symm)
  cases hForm
  rfl

theorem family_realization_degree_eq (n k : ℕ) : (n+1)+k = (k+1)+n := by omega

theorem family_density_graph_full_lift_realization_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    HEq F.densityGraph.fullLift (F.canonicalVFRealization hc) := by
  let A := nativeMixedVolumeDomain hc F.densityGraph.domain
  let L := nativeSelectedRVVFTailLift hc A F.densityGraph.selected
  let B := nativeProgramSelectedRVVFTailLift hc A F.densityGraph.selected
  have hfinL := native_selected_rv_vf_tail_lift_finite_labels hc A F.densityGraph.selected F.densityGraph.finite_selected
  have hfinB := native_program_selected_rv_vf_tail_finite_labels hc A F.densityGraph.selected F.densityGraph.finite_selected
  let ω : VolumeForm (rawSpecialSet hc L) := F.densityGraph.fullLift.form
  let π : VolumeForm (rawSpecialSet hc B) := (F.canonicalVFRealization hc).form
  have hω : ∀ p, ω.value p = p.val.2 (Fin.last a) := by
    intro p
    exact densityGraphPullback_form_last F.form
      (selectedRVVFTailProjection F.densityGraph.domain F.densityGraph.selected p)
  have hπ : ∀ p, π.value p = p.val.2 (Fin.last a) := fun _ => rfl
  exact native_coordinate_volume_objects_heq hc (family_realization_degree_eq n k) L B rfl hfinL hfinB ω π
    (Fin.last a) hω hπ

theorem family_full_lift_class_realization_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    HEq (positiveVFVolumeIsoClass hc C F.fullLift)
      (positiveVFVolumeIsoClass hc C (F.canonicalVFRealization hc)) := by
  have hGraph := (positiveVFVolumeIsoClass_eq_iff hc C).mpr
    ⟨VFVolumeIso.of_bijection (volumeFamilyFullLiftGraphBijection hc F)⟩
  have hNative := dependent_degree_map_heq (fun j => positiveVFVolumeIsoClass hc C (k := j))
    (family_realization_degree_eq n k) (family_density_graph_full_lift_realization_heq hc F)
  exact (heq_of_eq hGraph).trans hNative

theorem selected_family_canonical_integral_full_lift
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    HEq (selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F)
      (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C F.fullLift)) := by
  have hE := dependent_degree_map_heq
    (fun j => positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := j))
    (family_realization_degree_eq n k) (family_full_lift_class_realization_heq hc C F)
  exact (heq_of_eq (selected_family_canonical_integral_realization hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F)).trans hE.symm

theorem selected_family_canonical_integral_remove_small_base
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (E : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawVFSpace (M := M) (n+1))
      (C.base : Set M))
    (hE : SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) E < n+1) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F =
      selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated (F.outsideBase E) := by
  have hFull := congrArg (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1)
    (full_volume_lift_class_outside_base hc F E hE)
  exact eq_of_heq ((selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F).trans
    ((heq_of_eq hFull).trans
      (selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (F.outsideBase E)).symm))

end IntegrationInACVF.Section7
