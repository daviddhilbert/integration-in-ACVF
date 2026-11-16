module

public import IntegrationSection6.RawFiniteContractions
public import IntegrationSection6.RawContractionDomain

@[expose] public section

/-! The checked finite contraction theorem on the literal final RV
labels, before first-volume normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a : ℕ}

theorem raw_standard_volume_fibres_finite {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
    (hGS : G.real ⊆ S) {A : DefSet (M := M) S n a}
    (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction A σ) (hT : GammaProgramDefinable G T.program)
    (t : Fin n → RV (M := M)) :
    {r : Fin T.arity → RV (M := M) | (Fin.elim0,r) ∈ carrier T.target ∧ r ∘ T.volumeIndex = t}.Finite := by
  let F := FiniteRV.gammaRawFiniteContraction hκ hs hreal hGS hA hfin T hT
  have hF := F.finite_volume ⟨t,Set.mem_univ _⟩
  let g := fun u : rvObjectDomain F.object => u.val
  apply (hF.image g).subset
  rintro r ⟨hr,ht⟩
  let u : rvObjectDomain F.object := ⟨r,(rawContractionDomain_iff T (Fin.elim0,r)).mpr hr⟩
  refine ⟨u,?_,rfl⟩
  exact Subtype.ext ht

end IntegrationInACVF.Section7
