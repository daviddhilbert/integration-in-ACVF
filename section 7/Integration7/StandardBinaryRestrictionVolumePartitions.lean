module

public import Integration7.StandardRestrictionVolumeIdentifications
public import Integration7.CommonContextVolumePartitions

@[expose] public section

/-! Complementary target restrictions of one actual standard
contraction partition its normalized coordinate-density volume object.
Both restricted sources may use their own native presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k a d : ℕ}

set_option maxHeartbeats 3000000 in
theorem standard_binary_restriction_volume_partition {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M))
    (U A B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (hU : GammaSetDefinable G (carrier U)) (hA : GammaSetDefinable G (carrier A))
    (hB : GammaSetDefinable G (carrier B))
    (hfinU : ∀ x : Fin (k+1) → SpecialTransformations.Section5.VF (M := M),
      {r : Fin a → SpecialTransformations.Section5.RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinA : ∀ x : Fin (k+1) → SpecialTransformations.Section5.VF (M := M),
      {r : Fin a → SpecialTransformations.Section5.RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin (k+1) → SpecialTransformations.Section5.VF (M := M),
      {r : Fin a → SpecialTransformations.Section5.RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (ρ : Fin d → Fin a) (R : Set (Point (M := M) 0 d)) (hR : GammaSetDefinable G R)
    (hRc : GammaSetDefinable G (Set.univ \ R)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    {σ : Equiv.Perm (Fin (k+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable G T.program)
    (DA : StandardTargetRestrictionPresentation (G := G) T A
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (ρ j)) R hR hNames))
    (DB : StandardTargetRestrictionPresentation (G := G) T B
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (ρ j)) (Set.univ \ R) hRc hNames))
    (δ : Fin a) (hδU : ∀ p : U, (p.val.2 δ).val ≠ iRVZero)
    (hδA : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hδB : ∀ p : B, (p.val.2 δ).val ≠ iRVZero) :
    let X := retainedDensityContractionGammaObject hκ hs hreal hc C hGC U hU hfinU δ hδU T hT
    let Y := retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfinA δ hδA DA.contraction DA.gamma
    let Z := retainedDensityContractionGammaObject hκ hs hreal hc C hGC B hB hfinB δ hδB DB.contraction DB.gamma
    ∃ e : RVVolumeIso (Y.val.coprod Z.val) X.val, e.GammaDefinable G := by
  intro X Y Z
  have hSubA : Y.val.underlying.obj.domain.carrier ⊆ X.val.underlying.obj.domain.carrier :=
    fun r hr => ((DA.normalized_carrier hT ρ R hR hNames r).mp hr).1
  have hSubB : Z.val.underlying.obj.domain.carrier ⊆ X.val.underlying.obj.domain.carrier :=
    fun r hr => ((DB.normalized_carrier hT ρ (Set.univ \ R) hRc hNames r).mp hr).1
  have hComplement : Z.val.underlying.obj.domain.carrier =
      (X.val.underlying.obj.domain.sdiff Y.val.underlying.obj.domain).carrier := by
    ext r
    change r ∈ carrier (SpecialTransformations.Section5.rvObjectDomain DB.contraction.normalizedObject) ↔
      r ∈ carrier (SpecialTransformations.Section5.rvObjectDomain T.normalizedObject) ∧
        r ∉ carrier (SpecialTransformations.Section5.rvObjectDomain DA.contraction.normalizedObject)
    have ha := DA.normalized_carrier hT ρ R hR hNames r
    have hb := DB.normalized_carrier hT ρ (Set.univ \ R) hRc hNames r
    rw [ha,hb]
    change (_ ∧ ((_,_) ∈ Set.univ ∧ (_,_) ∉ R)) ↔ (_ ∧ ¬ (_ ∧ (_,_) ∈ R))
    simp only [Set.mem_univ,true_and]
    tauto
  obtain ⟨eA,heA⟩ := standard_restriction_volume_identification hκ hs hreal hc C hGC U A
    hU hA hfinU hfinA ρ R hR hNames T hT DA δ hδU hδA
  obtain ⟨eB,heB⟩ := standard_restriction_volume_identification hκ hs hreal hc C hGC U B
    hU hB hfinU hfinB ρ (Set.univ \ R) hRc hNames T hT DB δ hδU hδB
  let eC := volumeRestrictionCarrierIso hc C X.val Z.val.underlying.obj.domain
    (X.val.underlying.obj.domain.sdiff Y.val.underlying.obj.domain) hSubB Set.sdiff_subset hComplement
  have heC := gamma_volume_restriction_carrier_iso hc C X.val X.property Z.val.underlying.obj.domain
    (X.val.underlying.obj.domain.sdiff Y.val.underlying.obj.domain) hSubB Set.sdiff_subset hComplement
    Z.property.coordinates.domain
  let ePair := eA.coprod hc C (eB.trans hc C eC)
  have hePair := heA.coprod hc C G (heB.trans hc C G heC)
  let ePartition := volumeComplementPartitionIso hc C X.val Y.val.underlying.obj.domain hSubA
  have hePartition := gamma_actual_volume_complement_partition hc C X.val X.property
    Y.val.underlying.obj.domain hSubA Y.property.coordinates.domain
  exact ⟨ePair.trans hc C ePartition,hePair.trans hc C G hePartition⟩

end IntegrationInACVF.Section7
