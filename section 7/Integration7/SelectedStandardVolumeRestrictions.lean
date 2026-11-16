module

public import Integration7.SelectedStandardVolumeObjects
public import Integration7.StandardTargetRestrictionPresentations
public import Integration7.VolumeRestrictionIdentifications

@[expose] public section

/-! Restricting a standard contraction by old RV labels retains the
literal selected volume coordinates and density. Only finiteness after
fixing the selected tuple is needed; full RV-label finiteness is not assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV Point GammaSetDefinable carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {n a b d : ℕ}

theorem standard_restriction_selected_volume_index
    {S : Set M} {U A : SpecialTransformations.Section5.DefSet (M := M) S (n+1) a}
    {σ : Equiv.Perm (Fin (n+1))} {T : StandardContraction U σ}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 0 T.arity}
    (D : StandardTargetRestrictionPresentation (G := G) T A B) (ρ : Fin d → Fin a) :
    selectedStandardVolumeIndex D.contraction ρ = selectedStandardVolumeIndex T ρ := by
  rw [selectedStandardVolumeIndex,selectedStandardVolumeIndex,D.volumeIndex]

theorem selectedStandardRestrictionVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (U A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (_hU : GammaSetDefinable G (carrier U))
    (ρ : Fin d → Fin a) (δ : Fin a)
    (hδU : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hδA : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfinU : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinA : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (τ : Fin b → Fin a) (R : Set (Point (M := M) 0 b)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable G T.program)
    (D : StandardTargetRestrictionPresentation (G := G) T A
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (τ j)) R hR hNames)) :
    let X := selectedStandardVolumeObject hc C Ξ U ρ δ hδU hfinU T
    let Y := selectedStandardVolumeObject hc C Ξ A ρ δ hδA hfinA D.contraction
    ∃ hSub : Y.underlying.obj.domain.carrier ⊆ X.underlying.obj.domain.carrier,
      Nonempty (RVVolumeIso Y (X.restrict Y.underlying.obj.domain hSub)) := by
  intro X Y
  have hSub : Y.underlying.obj.domain.carrier ⊆ X.underlying.obj.domain.carrier := by
    intro r hr
    have hp := (mem_rawVolumeContractionLabels hc D.contraction.target r).mp hr
    exact (mem_rawVolumeContractionLabels hc T.target r).mpr hp.1
  refine ⟨hSub,⟨?_⟩⟩
  let Z := X.restrict Y.underlying.obj.domain hSub
  have hCoord (r : Y.underlying.obj.domain) :
      Z.underlying.obj.value ((Map.id Y.underlying.obj.domain) r) = Y.underlying.obj.value r := by
    change r.val ∘ selectedStandardVolumeIndex T ρ = r.val ∘ selectedStandardVolumeIndex D.contraction ρ
    rw [standard_restriction_selected_volume_index D ρ]
  let e := rvFiniteIsoOfAmbient (U := Y.underlying) (V := Z.underlying)
    (rvIsoOfVolumePreservingBijection (U := Y.underlying.obj) (V := Z.underlying.obj)
      (Map.id _) Function.bijective_id hCoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc C e hCoord (fun _ => rfl)

end IntegrationInACVF.Section7
