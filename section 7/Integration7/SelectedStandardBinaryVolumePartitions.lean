module

public import Integration7.SelectedStandardVolumeRestrictions
public import Integration7.VolumePartition
public import Integration7.VolumeCoproductIsomorphism

@[expose] public section

/-! Complementary old-label cuts partition the actual selected-volume
object of one standard contraction. Finiteness is required only after the
selected volume tuple is fixed, with no VF/Gamma generation assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV Point GammaSetDefinable carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {n a b d : ℕ}

theorem selected_standard_binary_restriction_volume_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (U A B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hU : GammaSetDefinable G (carrier U))
    (ρ : Fin d → Fin a) (δ : Fin a)
    (hδU : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hδA : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hδB : ∀ p ∈ carrier B, (p.2 δ).val ≠ iRVZero)
    (hfinU : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinA : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hfinB : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier B ∧ r ∘ ρ = t}.Finite)
    (τ : Fin b → Fin a) (R : Set (Point (M := M) 0 b)) (hR : GammaSetDefinable G R)
    (hRc : GammaSetDefinable G (Set.univ \ R)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable G T.program)
    (DA : StandardTargetRestrictionPresentation (G := G) T A
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (τ j)) R hR hNames))
    (DB : StandardTargetRestrictionPresentation (G := G) T B
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (τ j)) (Set.univ \ R) hRc hNames)) :
    let X := selectedStandardVolumeObject hc C Ξ U ρ δ hδU hfinU T
    let Y := selectedStandardVolumeObject hc C Ξ A ρ δ hδA hfinA DA.contraction
    let Z := selectedStandardVolumeObject hc C Ξ B ρ δ hδB hfinB DB.contraction
    Nonempty (RVVolumeIso (Y.coprod Z) X) := by
  intro X Y Z
  obtain ⟨hA,⟨eA⟩⟩ := selectedStandardRestrictionVolumeIso hc C Ξ U A hU ρ δ hδU hδA hfinU hfinA
    τ R hR hNames T hT DA
  obtain ⟨hB,⟨eB⟩⟩ := selectedStandardRestrictionVolumeIso hc C Ξ U B hU ρ δ hδU hδB hfinU hfinB
    τ (Set.univ \ R) hRc hNames T hT DB
  have hComplement : Z.underlying.obj.domain.carrier =
      (X.underlying.obj.domain.sdiff Y.underlying.obj.domain).carrier := by
    ext r
    change r ∈ (rawVolumeContractionLabels hc DB.contraction.target).carrier ↔
      r ∈ (rawVolumeContractionLabels hc T.target).carrier ∧
        r ∉ (rawVolumeContractionLabels hc DA.contraction.target).carrier
    rw [mem_rawVolumeContractionLabels,mem_rawVolumeContractionLabels,mem_rawVolumeContractionLabels]
    change (_ ∧ ((_,_) ∈ Set.univ ∧ (_,_) ∉ R)) ↔ (_ ∧ ¬ (_ ∧ (_,_) ∈ R))
    simp only [Set.mem_univ,true_and]
    tauto
  let eC := volumeRestrictionCarrierIso hc C X Z.underlying.obj.domain
    (X.underlying.obj.domain.sdiff Y.underlying.obj.domain) hB Set.sdiff_subset hComplement
  exact ⟨(eA.coprod hc C (eB.trans hc C eC)).trans hc C
    (volumeComplementPartitionIso hc C X Y.underlying.obj.domain hA)⟩
end IntegrationInACVF.Section7
