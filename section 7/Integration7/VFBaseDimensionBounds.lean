module

public import Integration7.SelectedFamilyFullLifts
public import Integration7.ScalarRVAlgebra

@[expose] public section

/-! RV labels add no VF dimension to a definable base locus. These
bounds keep small exceptional base sets small after lifting RV families. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

theorem pure_vf_has_dimension_bound (E : DefSet (rawVFSpace (M := M) n) S) :
    HasVFDimLE (rawRVSpace (M := M) 1) E n := by
  let H := ((Map.id E).toUniv.pair (rvScalarOne E)).toUniv
  refine ⟨n,le_rfl,.rv 1,H,Map.finiteFibres_of_injective ?_⟩
  intro x y he
  exact Subtype.ext (congrArg (fun w => w.val.1) he)

theorem mixed_domain_vf_dim_le_base
    (A : DefSet (rawMixedSpace (M := M) n a) S) (E : DefSet (rawVFSpace (M := M) n) S)
    (hAE : ∀ p : A, p.val.1 ∈ E.carrier) :
    vfDim (rawRVSpace (M := M) 1) A ≤ vfDim (rawRVSpace (M := M) 1) E := by
  let L := (Map.fst (rawVFSpace (M := M) n) (rawRVSpace a) S A).corestrict hAE
  let R := vfSelect (Fin.elim0 : Fin 0 → Fin n) A
  let H := L.pair R
  have hH : Function.Injective H := by
    intro x y he
    have h := congrArg Subtype.val he
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun w => w.2.2) h
    exact Subtype.ext (Prod.ext h1 h2)
  have hE : HasVFDimLE (rawRVSpace (M := M) 1) E (vfDim (rawRVSpace (M := M) 1) E) :=
    Dimension.dim_attained rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
    (⟨n,pure_vf_has_dimension_bound E⟩ : ∃ i, HasVFDimLE (rawRVSpace (M := M) 1) E i)
  have hR := mixed_has_dimension_bound (rawRVSpace (M := M) 1)
    (DefSet.univ (rawMixedSpace (M := M) 0 a) S)
  exact Nat.sInf_le (Dimension.HasDim.of_finiteFibres rawVFSpace
    (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1)) H
    (Map.finiteFibres_of_injective hH) (hE.prod (rawRVSpace (M := M) 1) hR))

theorem selected_family_full_lift_small_over_small_base
    {C : SpecialTransformations.Section3.BaseContext M} {k : ℕ}
    (F : SelectedVFVolumeFamily C n a k) (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (hFE : ∀ p : F.domain, p.val.1 ∈ E.carrier)
    (hE : vfDim (rawRVSpace (M := M) 1) E < n) :
    vfDim (rawRVSpace (M := M) 1) F.fullLift.domain < (n+k)+1 :=
  F.fullLift_small_of_small_domain ((mixed_domain_vf_dim_le_base F.domain E hFE).trans_lt hE)

end IntegrationInACVF.Section7
