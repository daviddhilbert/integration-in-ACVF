module

public import Integration7.GammaGenericRVJacobianFromGraphs
public import Integration7.GammaEssentialCoordinateGraphs
public import Integration7.BlowupHeadJacobianAlmostEverywhere

@[expose] public section

/-! The elementary-blowup head Jacobian can be chosen with its full
original-Gamma graph. The empty head retains its actual determinant one. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable)

namespace IntegrationInACVF.Section7.ElementaryBlowup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem exists_headJacobian_after_blowup_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V WU WV : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (B : SpecialTransformations.Section3.GammaParameters.Base (M := M))
    (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV) (f : RVVolumeIso U V)
    (hUΓ : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 (k+1)) =>
      U.underlying.obj.volume.graph p.2 q.2))
    (hVΓ : GammaGraphDefinable B (fun (p : Point (M := M) 0 V.underlying.obj.arity) (q : Point (M := M) 0 (k+1)) =>
      V.underlying.obj.volume.graph p.2 q.2))
    (hfΓ : f.GammaDefinable B) :
    ∃ J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)),
      GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 1) =>
        ∃ u : U.essential.obj.domain, u.val = p.2 ∧ (J u).val = q.2) ∧
      RVAlmostEverywhere WU.essential.obj.domain (k + 1) (fun w =>
        IsRVJacobianAt
          (volumeCorrespondence (finiteIsoMap (blowupHeadIso C f b.admissible c.admissible))).carrier
          (U.essential.obj.value (Map.prodFst _ _ (b.essentialChartMap w)) ∘ Fin.castSucc)
          (V.essential.obj.value (finiteIsoMap f.iso (Map.prodFst _ _ (b.essentialChartMap w))) ∘ Fin.castSucc)
          ((J (Map.prodFst _ _ (b.essentialChartMap w))).val 0)) := by
  cases k with
  | zero =>
    let J := rvScalarOne U.essential.obj.domain
    have hJΓ := gamma_real_rv_map_graph hc B J
      (rvScalarOne (DefSet.univ (rawRVSpace (M := M) U.underlying.obj.arity) B.real))
      (gamma_essential_volume_domain U hUΓ) (fun _ => rfl)
    refine ⟨J,hJΓ,?_⟩
    let D := DefSet.empty (rawRVSpace (M := M) WU.essential.obj.arity) (C.base : Set M)
    have hd : rvDim D = 0 := (rvDim_eq_zero_iff_finite D).mpr Set.finite_empty
    refine ⟨D, Set.empty_subset _, ?_, ?_⟩
    · rw [hd]
      decide
    · intro w _
      change IsRVJacobianAt _ _ _ 1
      apply isRVJacobianAt_zero_arity
      exact ⟨Map.prodFst _ _ (b.essentialChartMap w), rfl⟩
  | succ l =>
    obtain ⟨J, D, hD, hd, hJ,hJΓ⟩ := exists_gamma_generic_RVJacobian_of_graphs hc C (Nat.zero_lt_succ l) B
      (blowupHeadIso C f b.admissible c.admissible)
      (fun u i => U.essential_nonzero u i.castSucc)
      (fun v i => V.essential_nonzero v i.castSucc)
      (gamma_blowup_head_coordinate_graph hc C U b.admissible hUΓ)
      (gamma_blowup_head_coordinate_graph hc C V c.admissible hVΓ) hfΓ
    have hbase : RVAlmostEverywhere U.essential.obj.domain (l + 1) (fun u =>
        IsRVJacobianAt
          (volumeCorrespondence (finiteIsoMap (blowupHeadIso C f b.admissible c.admissible))).carrier
          (U.essential.obj.value u ∘ Fin.castSucc)
          (V.essential.obj.value (finiteIsoMap f.iso u) ∘ Fin.castSucc) ((J u).val 0)) :=
      ⟨D, hD, hd, hJ⟩
    exact ⟨J,hJΓ,b.head_ae_pullback hbase⟩

end IntegrationInACVF.Section7.ElementaryBlowup
