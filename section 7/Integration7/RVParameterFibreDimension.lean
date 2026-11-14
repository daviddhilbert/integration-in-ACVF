import Integration7.RVParameterFibres
import Integration7.RVFibreDimensionBound

/-! The base-plus-fibre RV dimension bound for literal parameter tuples.
The fibre in the map's original ambient space injects into the tail fibre. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {p a d k : ℕ}

theorem rvDim_lt_base_add_tuple_fibre
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : DefSet (rawRVSpace (M := M) (p+a)) (C.base : Set M))
    (B : DefSet (rawRVSpace (M := M) p) (C.base : Set M))
    (hAB : ∀ u : A, u.val ∘ Fin.castAdd a ∈ B.carrier)
    (hB : rvDim B ≤ d)
    (hFibre : ∀ t : B, rvDim (rvTupleFibre A t.val) < k+1) : rvDim A < (d+k)+1 := by
  let f : Map A B := ((rvCoordinateSelectMap _ (Fin.castAdd a)).restrict
    (Set.subset_univ A.carrier)).corestrict hAB
  apply rvDim_lt_base_add_positive_fibre hc C f hB
  intro t
  let F := rvMapFibre f t
  have hHead (u : F) : u.val ∘ Fin.castAdd a = t.val := by
    obtain ⟨v,hv,hvt⟩ := u.property
    have he : (f v).val = t.val := congrArg Subtype.val hvt
    change v.val ∘ Fin.castAdd a = t.val at he
    exact hv ▸ he
  let g : Map F (rvTupleFibre A t.val) :=
    ((rvCoordinateSelectMap _ (Fin.natAdd p)).restrict (Set.subset_univ F.carrier)).corestrict (by
      intro u
      have he := (Fin.append_castAdd_natAdd (f := u.val)).symm
      change u.val = Fin.append (u.val ∘ Fin.castAdd a) (u.val ∘ Fin.natAdd p) at he
      rw [hHead u] at he
      change Fin.append t.val (u.val ∘ Fin.natAdd p) ∈ A.carrier
      rw [← he]
      obtain ⟨v,hv,_⟩ := u.property
      exact hv ▸ v.property)
  have hg : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    have ht : u.val ∘ Fin.natAdd p = v.val ∘ Fin.natAdd p := congrArg Subtype.val huv
    funext i
    refine Fin.addCases (m := p) (n := a) (fun i => ?_) (fun i => ?_) i
    · exact congrFun ((hHead u).trans (hHead v).symm) i
    · exact congrFun ht i
  exact (rvDim_le_of_finite_map g (Map.finiteFibres_of_injective hg)).trans_lt (hFibre t)

end IntegrationInACVF.Section7
