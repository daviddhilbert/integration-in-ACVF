module

public import Integration7.RawStandardVolumeObjects
public import Integration7.NativeCoordinateDensityVolumeIsomorphisms

@[expose] public section

/-! The canonical tail completion and the original selected contraction
are genuinely RV volume isomorphic, retaining the original density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV VF carrier rvObjectDomain)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d r : ℕ}

def selectedTailCompletionVolumeObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {s : Fin a → RV (M := M) | (x,s) ∈ carrier A ∧ s ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ)
    {V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 r}
    (E : OrderedContractionProgram (C.base : Set M) (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) (d+n) :=
  rawStandardVolumeObject (n := d+n) hc C Ξ (nativeProgramSelectedRVVFTailLift (n := n+1) (d := d) hc A ρ)
    (native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin) δ
    (fun p hp => native_program_selected_rv_vf_tail_density_nonzero hc A ρ δ
      (fun q => hδ q.val q.property) ⟨p,hp⟩)
    (selectedRVVFTailStandardContraction hc T ρ E)

def selectedVFTailVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {s : Fin a → RV (M := M) | (x,s) ∈ carrier A ∧ s ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ)
    {V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 r}
    (E : OrderedContractionProgram (C.base : Set M) (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V)
    (hVF : ∀ p, (E.naturalMap p).val.1 = p.val.1)
    (hCon : SpecialTransformations.Section5.Contractible E.toMap) :
    RVVolumeIso (selectedTailCompletionVolumeObject hc C Ξ A ρ hfin δ hδ T E)
      (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T) := by
  let W := selectedTailCompletionVolumeObject hc C Ξ A ρ hfin δ hδ T E
  let Z := selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T
  let f := canonicalSelectedTailRVProjection hc T.target (suffixIndex T.program.rvArity_le ∘ ρ) E
  let g : Map W.underlying.obj.domain Z.underlying.obj.domain := rawVolumeLabelMap hc f
  have hg : Function.Bijective g := raw_volume_label_map_bijective hc f
    (canonical_selected_tail_rv_projection_bijective hc T.target _ E hCon)
  have hcoord : ∀ u, Z.underlying.obj.value (g u) = W.underlying.obj.value u := by
    intro u
    change (rawVolumeLabelMap hc f u).val ∘ selectedStandardVolumeIndex T ρ =
      u.val ∘ (selectedRVVFTailStandardContraction hc T ρ E).volumeIndex
    rw [raw_volume_label_map_value]
    exact selected_rv_vf_tail_standard_volume hc T ρ E hVF _
  have hφ : ∀ u, Z.form.value (g u) = W.form.value u := by
    intro u
    change (rawVolumeLabelMap hc f u).val (suffixIndex T.program.rvArity_le δ) =
      u.val (suffixIndex (selectedRVVFTailStandardContraction hc T ρ E).program.rvArity_le δ)
    rw [raw_volume_label_map_value]
    exact selected_rv_vf_tail_standard_density hc T ρ E _ δ
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection g hg hcoord)) hcoord hφ

end IntegrationInACVF.Section7
