module

public import Integration7.StandardRestrictionVolumeIdentifications
public import Integration7.GammaVolumeThreePartPartitions

@[expose] public section

/-! Three actual target restriction presentations partition the
normalized volume object whenever their old-label predicates form a
disjoint cover. No change of the specified contraction is involved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable carrier RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k a d : ℕ}

set_option maxHeartbeats 3200000 in
theorem standard_ternary_restriction_volume_partition {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (A : Fin 3 → SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (hU : GammaSetDefinable G (carrier U)) (hA : ∀ i, GammaSetDefinable G (carrier (A i)))
    (hfinU : ∀ x : Fin (k+1) → SpecialTransformations.Section5.VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinA : ∀ i, ∀ x : Fin (k+1) → SpecialTransformations.Section5.VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier (A i)}.Finite)
    (ρ : Fin d → Fin a) (R : Fin 3 → Set (Point (M := M) 0 d))
    (hR : ∀ i, GammaSetDefinable G (R i))
    (hCoverR : (R 0 ∪ R 1) ∪ R 2 = Set.univ) (hDisjR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    {σ : Equiv.Perm (Fin (k+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable G T.program)
    (D : ∀ i, StandardTargetRestrictionPresentation (G := G) T (A i)
      (rvLabelCut T.target (gamma_program_final_set T.program hT)
        (fun j => suffixIndex T.program.rvArity_le (ρ j)) (R i) (hR i) hNames))
    (δ : Fin a) (hδU : ∀ p : U, (p.val.2 δ).val ≠ iRVZero)
    (hδA : ∀ i, ∀ p : A i, (p.val.2 δ).val ≠ iRVZero) :
    let X := retainedDensityContractionGammaObject hκ hs hreal hc C hGC U hU hfinU δ hδU T hT
    let Y := fun i => retainedDensityContractionGammaObject hκ hs hreal hc C hGC
      (A i) (hA i) (hfinA i) δ (hδA i) (D i).contraction (D i).gamma
    ∃ e : RVVolumeIso (((Y 0).val.coprod (Y 1).val).coprod (Y 2).val) X.val,
      e.GammaDefinable G := by
  intro X Y
  let tag (r : Fin ((k+1)+T.arity) → RV (M := M)) : Point (M := M) 0 d :=
    (Fin.elim0,r ∘ (fun j => FiniteRV.contractionOldLabelIndex T (ρ j)))
  have hMem (i : Fin 3) (r : Fin ((k+1)+T.arity) → RV (M := M)) :
      r ∈ (Y i).val.underlying.obj.domain.carrier ↔
        r ∈ X.val.underlying.obj.domain.carrier ∧ tag r ∈ R i :=
    (D i).normalized_carrier hT ρ (R i) (hR i) hNames r
  have hSub (i : Fin 3) : (Y i).val.underlying.obj.domain.carrier ⊆ X.val.underlying.obj.domain.carrier :=
    fun r hr => ((hMem i r).mp hr).1
  have hCover : X.val.underlying.obj.domain.carrier =
      ((Y 0).val.underlying.obj.domain.carrier ∪ (Y 1).val.underlying.obj.domain.carrier) ∪
        (Y 2).val.underlying.obj.domain.carrier := by
    ext r
    constructor
    · intro hr
      have ht : tag r ∈ (R 0 ∪ R 1) ∪ R 2 := by rw [hCoverR]; exact Set.mem_univ _
      rcases ht with (ht | ht) | ht
      · exact Or.inl (Or.inl ((hMem 0 r).mpr ⟨hr,ht⟩))
      · exact Or.inl (Or.inr ((hMem 1 r).mpr ⟨hr,ht⟩))
      · exact Or.inr ((hMem 2 r).mpr ⟨hr,ht⟩)
    · rintro ((hr | hr) | hr)
      · exact hSub 0 hr
      · exact hSub 1 hr
      · exact hSub 2 hr
  have hDisj (i j : Fin 3) (hne : i ≠ j) :
      Disjoint (Y i).val.underlying.obj.domain.carrier (Y j).val.underlying.obj.domain.carrier := by
    apply Set.disjoint_left.mpr
    intro r hi hj
    exact Set.disjoint_left.mp (hDisjR hne) ((hMem i r).mp hi).2 ((hMem j r).mp hj).2
  obtain ⟨e0,he0⟩ := standard_restriction_volume_identification hκ hs hreal hc C hGC U (A 0)
    hU (hA 0) hfinU (hfinA 0) ρ (R 0) (hR 0) hNames T hT (D 0) δ hδU (hδA 0)
  obtain ⟨e1,he1⟩ := standard_restriction_volume_identification hκ hs hreal hc C hGC U (A 1)
    hU (hA 1) hfinU (hfinA 1) ρ (R 1) (hR 1) hNames T hT (D 1) δ hδU (hδA 1)
  obtain ⟨e2,he2⟩ := standard_restriction_volume_identification hκ hs hreal hc C hGC U (A 2)
    hU (hA 2) hfinU (hfinA 2) ρ (R 2) (hR 2) hNames T hT (D 2) δ hδU (hδA 2)
  obtain ⟨eP,heP⟩ := gamma_volume_three_part_partition hc C X.val X.property
    (Y 0).val.underlying.obj.domain (Y 1).val.underlying.obj.domain (Y 2).val.underlying.obj.domain
    (hSub 0) (hSub 1) (hSub 2) hCover (hDisj 0 1 (by decide))
    (hDisj 0 2 (by decide)) (hDisj 1 2 (by decide))
    (Y 0).property.coordinates.domain (Y 1).property.coordinates.domain (Y 2).property.coordinates.domain
  let e := (e0.coprod hc C e1).coprod hc C e2
  have he := (he0.coprod hc C G he1).coprod hc C G he2
  exact ⟨e.trans hc C eP,he.trans hc C G heP⟩

end IntegrationInACVF.Section7
